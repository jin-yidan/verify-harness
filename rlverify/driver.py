"""RLVerify driver: Claude Code-driven verification pipeline.

Instead of calling an external LLM API, this exposes each pipeline step
as a method that Claude Code invokes with its own reasoning. Keeps the
infrastructure (retriever, compiler, corpus growth) intact.

Usage in a Claude Code session:
    from rlverify.driver import VerifyDriver
    d = VerifyDriver()

    # Search library
    d.search("mixed f-divergence decomposition")

    # Compile a proof
    d.compile('''
    import RLGeneralization.Concentration.FDivergence
    open Finset BigOperators
    theorem foo ... := by exact ...
    ''')

    # Run a full fixture with Claude Code driving each step
    d.begin("chi_squared_po")
    d.resolve("mixed_divergence_decomp", library="fMixDiv_eq_half_chiSq_add_kl")
    d.resolve("chi_sq_nonneg", novel=True)
    d.formalize("chi_sq_nonneg", statement="...", proof="...")
    d.assemble(statement="...", proof="...")
    d.finish()
"""

from __future__ import annotations

import json
import hashlib
import re
import subprocess
from dataclasses import asdict, dataclass, field, fields
from pathlib import Path

from .lean import (
    STANDARD_AXIOMS,
    AxiomClosure,
    LeanResult,
    StructuralAudit,
    check_axiom_closure,
    find_axioms,
    has_sorry_token,
    verify_lean_code,
)
from .vacuity import is_id_shaped
from .verdict import VERIFIED_CLASS, verdict_class, gate_failures
from .retriever import (
    Premise,
    PremiseRetriever,
    corpus_entry_text,
    near_match_scan,
)

ROOT = Path(__file__).resolve().parent.parent
DEFAULT_CORPUS = ROOT / "rlverify" / "corpus.jsonl"

#: A plausible qualified Lean identifier (what resolve(library=/instantiation=)
#: accepts) — free-text citations must go through named_result= instead.
_IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_'!?]*(\.[A-Za-z_«][A-Za-z0-9_'!?»]*)*")


@dataclass
class LemmaResult:
    name: str
    kind: str = "novel"  # library | instantiation | prior | novel | violation | circular
    depends_on: list[str] = field(default_factory=list)
    dependencies_declared: bool = False
    library_match: str = ""
    library_source_file: str = ""
    library_source_line: int = 0
    library_statement: str = ""
    library_import: str = ""
    library_found_in_repo: bool = False
    named_result: str = ""  # textbook citation (Sion, Brouwer, ...) — never a corpus match
    prior_name: str = ""
    prior_artifact: str = ""
    circular_with: str = ""  # block whose conclusion this block's justification presupposes
    statement: str = ""
    proof: str = ""
    code: str = ""
    compiled: bool = False
    discharged: bool = False  # proved through formalize/discharge, not only inline assembly
    vacuity_risk: str = ""  # deterministic/heuristic anti-vacuity finding
    compile_error: str = ""
    note: str = ""  # violation reason / free-form block annotation
    citation_invalid: bool = False  # external library/instantiation id failed #check
    skipped: str = ""  # non-empty ⟺ deliberately not formalized (downstream of a failed block)
    near_match: dict = field(default_factory=dict)  # log-arg scan result
    near_match_adjudication: str = ""
    anti_vacuity_checks: dict = field(default_factory=dict)
    discharge_attempts: int = 0
    source_excerpt: str = ""  # exact excerpt of the submitted proof this block formalizes
    source_excerpt_sha256: str = ""
    source_excerpt_verified: bool = False
    source_char_start: int = -1
    source_char_end: int = -1
    source_byte_start: int = -1
    source_byte_end: int = -1
    input_sha256: str = ""
    formal_signature: str = ""
    hypotheses: list[str] = field(default_factory=list)
    hypotheses_declared: bool = False
    discharge_certificate_sha256: str = ""
    trusted_rechecked: bool = False
    artifact: str = ""


@dataclass
class Refutation:
    """A scoped Lean negative certificate.

    ``kernel_backed`` is DERIVED, never asserted: True ⟺ the counterexample
    compiled AND its kernel closure is clean (no sorryAx, no custom axioms).
    Kernel closure alone does not determine what was refuted.  The trusted
    scope/kind/semantic fields below must also establish whether the artifact
    refutes the main theorem, invalidates one submitted proof step, or merely
    witnesses a well-definedness issue.
    """
    block: str                # the block whose inference this refutes
    description: str          # the refuted claim, verbatim (mandatory)
    theorem: str = ""         # qualified name of the refuting theorem
    code: str = ""
    compiled: bool = False
    kernel_axioms: list[str] = field(default_factory=list)
    kernel_backed: bool = False
    artifact: str = ""        # runs/<fixture>_<ts>_refute_<block>.lean
    error: str = ""
    quarantined: bool = False  # trusted semantic audit rejected this candidate
    # Trusted-parent classification.  Agent-created candidates start unscoped
    # and therefore can never refute the main theorem merely by compiling.
    target_scope: str = "UNSCOPED"
    finding_kind: str = "UNCLASSIFIED"
    premises_satisfied: bool = False
    objects_well_defined: bool = False
    conclusion_negated: bool = False
    statement_faithful: bool = False


@dataclass
class StepCertificate:
    """A positive Lean certificate for one disputed proof inference.

    This is confirmation evidence only: it can clear a triage suspicion, but
    it does not verify the full theorem or bypass the normal proof workflow.
    """
    block: str
    description: str
    theorem: str = ""
    code: str = ""
    compiled: bool = False
    kernel_axioms: list[str] = field(default_factory=list)
    kernel_backed: bool = False
    artifact: str = ""
    error: str = ""
    quarantined: bool = False


@dataclass
class VerifyResult:
    fixture: str
    workflow_contract_version: int = 2
    workflow_provenance: dict = field(default_factory=dict)
    lemmas: list[LemmaResult] = field(default_factory=list)
    main_statement: str = ""
    main_proof: str = ""
    main_code: str = ""
    compiled: bool = False
    compile_error: str = ""
    novel_added: list[str] = field(default_factory=list)
    axioms: list[str] = field(default_factory=list)
    kernel_axioms: list[str] = field(default_factory=list)
    kernel_closure_checked: bool = False
    has_sorry_ax: bool = False
    sketch_code: str = ""
    sketch_verified: bool = False
    sketch_expected_blocks: list[str] = field(default_factory=list)
    structural_mode: bool = False
    structural_code: str = ""
    structural_compiled: bool = False
    structural_placeholders: list[str] = field(default_factory=list)
    structural_independent_discharged: list[str] = field(default_factory=list)
    structural_error: str = ""
    structural_trusted_recheck: dict = field(default_factory=dict)
    structural_artifact: str = ""
    preflight: dict = field(default_factory=dict)
    discharge_order: list[str] = field(default_factory=list)
    falsifications: list[dict] = field(default_factory=list)
    verdict: str = ""         # agent-established early-exit verdict (set_verdict)
    verdict_reason: str = ""
    verdict_block: str = ""   # the verdict-deciding block (set_verdict block=)
    verdict_evidence: str = ""  # "" | "audit" | "kernel" — always derived
    refutations: list[Refutation] = field(default_factory=list)
    step_certificates: list[StepCertificate] = field(default_factory=list)
    triage: dict = field(default_factory=dict)  # Phase 0 prose triage record
    hypothesis_audit: dict = field(default_factory=dict)  # sealed, prioritization-only
    invocation_audits: list[dict] = field(default_factory=list)
    backtranslations: list[dict] = field(default_factory=list)  # sealed audit records
    main_unformalizable: str = ""  # reason the MAIN statement can't be stated in Lean
    audit_warnings: list[str] = field(default_factory=list)  # finish()-time coverage gaps
    gate_downgrade: bool = False  # strict mode: VERIFIED downgraded for missing gate coverage
    trusted_recheck: dict = field(default_factory=dict)
    proof_faithfulness: str = ""  # submitted-proof | alternative-proof | unassessed
    proof_faithfulness_detail: list[str] = field(default_factory=list)
    library_evaluations: list[dict] = field(default_factory=list)
    library_searches: list[dict] = field(default_factory=list)
    axiom_lifecycle: list[dict] = field(default_factory=list)
    decomposition_sha256: str = ""

    def to_dict(self) -> dict:
        return asdict(self)

    def kernel_custom_axioms(self) -> list[str]:
        """Non-standard axioms in the kernel closure (excluding sorryAx)."""
        return [a for a in self.kernel_axioms
                if a != "sorryAx" and a not in STANDARD_AXIOMS]


@dataclass
class LibrarySearchResult:
    """Outcome of a type-directed (`exact?`) library search."""
    found: bool
    suggestion: str = ""     # the full `exact <term>` suggestion
    head_symbol: str = ""    # first identifier of the suggested term
    package: str = ""        # RLGeneralization | SLT | Mathlib | ""
    elapsed: float = 0.0
    error: str = ""          # non-empty when the statement failed to elaborate
    inconclusive: bool = False  # exact? did not finish (timeout / heartbeat budget) — novelty NOT cleared


class VerifyDriver:
    """Driver for Claude Code-driven verification."""

    def __init__(self, corpus_path: str | Path | None = None,
                 strict_gates: bool = False):
        # strict_gates: ON for harness/untrusted sessions — a VERIFIED-class
        # verdict with any unmet flaw-hunting gate (the finish() audit_warnings)
        # is DOWNGRADED to UNVERIFIED/UNGATED. OFF (default) for trusted-local
        # Claude Code so existing behaviour is unchanged: the warnings stay
        # advisory. See rlverify/verdict.py and HARNESS_IMPLEMENTATION.md W1.
        self._strict_gates = strict_gates
        self.corpus_path = Path(corpus_path) if corpus_path else DEFAULT_CORPUS
        # Run records + session journals. Non-default corpora (tests) get a
        # directory next to their corpus so they never pollute repo runs/.
        self.runs_dir = (ROOT / "runs" if self.corpus_path == DEFAULT_CORPUS
                         else self.corpus_path.parent / "runs")
        self.retriever = PremiseRetriever(self.corpus_path)
        self._result: VerifyResult | None = None
        self._last_result: VerifyResult | None = None  # read-only after finish()
        self._last_finished: str | None = None  # run record of the last finish()
        self._amend_path: Path | None = None  # set by amend(): finish() overwrites it in place
        self._module_built_cache: dict[str, bool] = {}
        self._repl = None  # lazy ReplSession — see repl_verify()
        self._log("init", f"loaded {len(self.retriever)} premises from {self.corpus_path.name}")

    # ----- Standardized output -----
    #
    # Every pipeline event prints ONE line in a fixed grammar:
    #
    #     [PHASE     ] BLOCK                        GLYPH STATUS — detail
    #
    # Phases: init | begin | triage | resolve | gate | falsify | sketch |
    #         discharge | compile | refute | assemble | library | verdict
    # Glyphs: ✓ success   ✗ failure/refuted   ~ instantiation   ? novel
    #         · info/skipped   ⚠ warning
    #
    # `d.status()` renders the live per-block table at any point in a session;
    # `d.finish()` ends with a fixed-format summary block (grep `Verdict`).

    _LOG_PHASE_W = 10
    _LOG_BLOCK_W = 28

    @staticmethod
    def _log(phase: str, msg: str, block: str = "") -> None:
        tag = f"[{phase:<{VerifyDriver._LOG_PHASE_W}}]"
        if block:
            print(f"{tag} {block:<{VerifyDriver._LOG_BLOCK_W}} {msg}")
        else:
            print(f"{tag} {msg}")

    #: Verdicts the agent may establish without formalization (early exits,
    #: per /verify-full-process Rule 7 + paper-mode CIRCULAR). VERIFIED verdicts can NOT
    #: be set manually — they come from the kernel audit in assemble().
    EARLY_EXIT_VERDICTS = frozenset({
        "UNVERIFIED/SUSPECTED",
        "UNVERIFIED/WRONG",
        "UNVERIFIED/INCOMPLETE",
        "UNVERIFIED/MISMATCH",
        "UNVERIFIED/HYPOTHESIS_VIOLATION",
        "UNVERIFIED/PROOF_INVALID",
        "UNVERIFIED/CIRCULAR",
    })

    def set_verdict(self, verdict: str, reason: str, block: str = "") -> None:
        """Record an agent-established early-exit verdict in the run record.

        Use when the proof dies before formalization (counterexample,
        hypothesis violation, circular dependency, ...). The verdict and its
        justification are persisted to the runs/ JSON, dominate
        the session verdict line, and make verdict types aggregatable.

        Pass ``block`` to name the verdict-deciding block. The evidence
        level is DERIVED: ``verdict_evidence == "kernel"`` only when that
        block carries a kernel-backed refutation (see ``refute``); otherwise
        ``"audit"``. A refutation on a different block never upgrades the
        verdict.
        """
        if self._result is None:
            raise RuntimeError("No active session. Call begin() first.")
        if verdict not in self.EARLY_EXIT_VERDICTS:
            raise ValueError(
                f"set_verdict accepts only {sorted(self.EARLY_EXIT_VERDICTS)} "
                "— VERIFIED verdicts come from the kernel audit in assemble()")
        if not reason.strip():
            raise ValueError("set_verdict requires a justification reason")
        self._result.verdict = verdict
        self._result.verdict_reason = reason.strip()
        self._result.verdict_block = block
        self._derive_verdict_evidence()
        self._persist()
        tag = " [kernel-backed]" if self._result.verdict_evidence == "kernel" else ""
        self._log("verdict", f"✗ {verdict}{tag} — {self._result.verdict_reason}")

    def record_triage(self, suspects: list[dict], all_clear: bool) -> None:
        """Persist the Phase 0 prose-triage output in the run record.

        ``suspects``: [{"step": ..., "suspicion": ..., "severity": ...}].
        Triage PRIORITIZES, never decides: it has no effect on the verdict
        line by design — it exists so the report's reconciliation table and
        the benchmark anchoring metric are computable from the record.
        Inconsistent input (all_clear with suspects, or neither) is rejected:
        on malformed subagent output, fail toward all_clear=False.
        """
        if self._result is None:
            raise RuntimeError("No active session. Call begin() first.")
        if all_clear and suspects:
            raise ValueError("all_clear=True is inconsistent with a non-empty "
                             "suspect list")
        for s in suspects:
            if not isinstance(s, dict) or "step" not in s or "suspicion" not in s:
                raise ValueError(
                    "each suspect needs at least {'step', 'suspicion'} "
                    f"(got {s!r}) — on malformed triage output, re-prompt once, "
                    "else record all_clear=False, suspects=[]")
        self._result.triage = {"suspects": suspects, "all_clear": bool(all_clear)}
        self._persist()
        if all_clear:
            self._log("triage", "· all clear — ZERO weight; run every gate in "
                                "full regardless")
        else:
            self._log("triage", f"· {len(suspects)} suspect(s) — prioritize, "
                                "never skip:")
            for s in suspects:
                sev = f" [{s['severity']}]" if s.get("severity") else ""
                self._log("triage", f"  step {s['step']}{sev}: "
                                    f"{str(s['suspicion'])}")

    BACKTRANSLATION_VERDICTS = frozenset({"MATCH", "NOTE", "MISMATCH"})

    def record_backtranslation(
        self,
        target: str,
        verdict: str,
        notes: str = "",
        categories: dict | None = None,
        purpose: str = "",
    ) -> dict:
        """Persist a sealed back-translation audit outcome in the run record.

        ``target`` names what was audited: a block name, ``"main"`` for the
        input's main theorem, a refutation theorem name, or an ``add_novel``
        candidate. ``verdict`` is the rubric outcome: MATCH, NOTE (benign
        formalization choice), or MISMATCH (blocking — fix the statement or
        carry the discrepancy into the session verdict). ``categories`` is
        the optional per-category rubric dict (quantifiers / relation /
        constants / hypotheses / object types).

        ``finish()`` warns when a verdict-deciding kernel-backed refutation
        or an assembled main theorem has no recorded back-translation —
        the audit is mandatory for verdict-bearing statements.
        """
        if self._result is None:
            raise RuntimeError("No active session. Call begin() first.")
        verdict = verdict.upper()
        if verdict not in self.BACKTRANSLATION_VERDICTS:
            raise ValueError(
                f"verdict must be one of {sorted(self.BACKTRANSLATION_VERDICTS)}")
        rec = {"target": target, "verdict": verdict, "notes": notes,
               "categories": categories or {}}
        if purpose:
            rec["purpose"] = purpose
        self._result.backtranslations.append(rec)
        self._persist()
        glyph = {"MATCH": "✓", "NOTE": "·", "MISMATCH": "✗"}[verdict]
        self._log("audit", f"{glyph} back-translation {verdict}"
                           + (f" — {notes[:80]}" if notes else ""), block=target)
        if verdict == "MISMATCH":
            self._log("audit", "  → blocking: fix the Lean statement and "
                               "re-audit, or carry into the verdict", block=target)
        return rec

    def skip(self, name: str, reason: str) -> LemmaResult:
        """Mark a block as deliberately not formalized, with the reason.

        Use ONLY for blocks downstream of a failed/refuted block (the
        dependency rule). Independent correct blocks may never be skipped —
        that is the salvage rule; leave them pending and they will show as
        GAP until formalized.
        """
        if self._result is None:
            raise RuntimeError("No active session. Call begin() first.")
        if not reason.strip():
            raise ValueError("skip requires a reason (which failed block "
                             "this depends on)")
        lemma = self._find_lemma(name)
        if lemma is None:
            lemma = LemmaResult(name=name)
            self._result.lemmas.append(lemma)
        lemma.skipped = reason.strip()
        self._log("resolve", f"· skipped — {lemma.skipped}", block=name)
        self._persist()
        return lemma

    def main_unformalizable(self, reason: str) -> None:
        """Record that the MAIN theorem statement cannot be stated in Lean.

        For INCOMPLETE verdicts whose conclusion needs missing
        infrastructure (e.g. a.s. convergence of stochastic iterates),
        sketch/assemble/kernel-closure are structurally impossible — this
        renders them as ``n/a`` in status()/finish() instead of the
        misleading "not run" / "closure not obtained". Cleared by a
        successful ``assemble()``.
        """
        if self._result is None:
            raise RuntimeError("No active session. Call begin() first.")
        if not reason.strip():
            raise ValueError("main_unformalizable requires a reason (which "
                             "infrastructure is missing for the statement)")
        self._result.main_unformalizable = reason.strip()
        self._log("assemble", "· main statement not formalizable — "
                              f"{self._result.main_unformalizable}")
        self._persist()

    def _reconcile_corpus_blocks(self) -> None:
        """Mark novel session blocks that already live in the corpus.

        ``add_novel`` kernel-gates everything it registers, so a corpus
        lemma carrying a session block's name IS verified — even when it
        was added by a different process than the one holding the session
        (the historic GAP-mislabeling failure mode). Called by status()
        and finish() before rendering block states.
        """
        r = self._result or self._last_result
        if r is None:
            return
        for l in r.lemmas:
            if l.compiled or l.skipped or l.kind != "novel":
                continue
            hit = self._corpus_has(name=l.name)
            if hit:
                l.compiled = True
                l.note = f"kernel-verified in corpus: {hit}"
                self._log("library", f"· reconciled from corpus — {hit}",
                          block=l.name)

    @staticmethod
    def _block_state(lemma: LemmaResult, falsify_verdict: str) -> tuple[str, str]:
        """(glyph, label) for one block — single source for status/finish.

        Distinguishes deliberate skips (downstream of a failed block) from
        genuine gaps (unformalized blocks, incl. salvage-pending ones).
        """
        if falsify_verdict == "REFUTED":
            return "✗", "refuted"
        if lemma.kind in ("violation", "circular"):
            return "✗", lemma.kind
        if lemma.compiled:
            return "✓", "compiled"
        if lemma.citation_invalid:
            # The cited external id failed #check — not a usable resolution.
            return "✗", "bad citation"
        if lemma.kind == "library":
            return "✓", "library"
        if lemma.skipped:
            return "·", f"skipped — {lemma.skipped}"
        if lemma.named_result:
            # Textbook citation with no formalization: a documented
            # infrastructure gap, distinct from an unaddressed block.
            return "·", "named result — not formalized"
        return "✗", "GAP"

    def _derive_verdict_evidence(self) -> None:
        """Recompute verdict_evidence — called whenever verdict or
        refutations change, so refute-after-set_verdict still upgrades."""
        r = self._result
        if r is None or not r.verdict:
            return
        from .verdict import evidence_tier

        tier = evidence_tier(r.to_dict())
        r.verdict_evidence = (
            "kernel" if tier == "kernel"
            else "certificate" if tier == "certificate"
            else "audit"
        )

    def _verdict_string(self) -> str:
        """Single source of truth for the session verdict line.

        Falls back to the last finished session after ``finish()``.
        """
        r = self._result or self._last_result
        if r is None:
            return "NO ACTIVE SESSION"
        if r.gate_downgrade:
            return ("UNVERIFIED/UNGATED — strict mode: required flaw-hunting "
                    "gates missing; see audit warnings")
        if r.has_sorry_ax:
            return "UNVERIFIED — sorryAx in kernel closure"
        if r.verdict:
            effective = verdict_class(r.to_dict())
            if effective == "UNVERIFIED/SUSPECTED":
                return (
                    "UNVERIFIED/SUSPECTED [audit-only] — "
                    f"{r.verdict}: {r.verdict_reason}"
                )
            tag = f" [{r.verdict_evidence}]" if r.verdict_evidence else ""
            return f"{effective}{tag} — {r.verdict_reason}"
        classified_refutations = [
            ref for ref in r.refutations if ref.kernel_backed
        ]
        if classified_refutations:
            effective = verdict_class(r.to_dict())
            blocks = [ref.block for ref in classified_refutations]
            return f"{effective} — certified finding(s): {blocks}"
        refuted = [f["block"] for f in r.falsifications
                   if f.get("verdict") == "REFUTED"]
        if refuted:
            return (
                "UNVERIFIED/SUSPECTED [audit-only] — reported numeric "
                f"counterexample(s) lack an independent checker: {refuted}"
            )
        if r.structural_mode:
            if (r.structural_trusted_recheck or {}).get("compiled"):
                return (
                    "UNVERIFIED/INCOMPLETE — COMPILES MODULO PLACEHOLDERS "
                    f"{r.structural_placeholders}; conditional structure only"
                )
            return (
                "UNVERIFIED/INCOMPLETE — structural continuation did not "
                "produce a trusted conditional compile"
            )
        if r.compiled:
            custom = r.kernel_custom_axioms()
            if custom:
                return f"VERIFIED MODULO AXIOMS {custom}"
            if r.kernel_closure_checked or r.kernel_axioms:
                if r.proof_faithfulness == "alternative-proof":
                    return (
                        "VERIFIED/ALTERNATIVE-PROOF — theorem kernel-verified; "
                        "the submitted proof was not faithfully discharged"
                    )
                return "VERIFIED (kernel closure standard)"
            if r.axioms:
                return f"VERIFIED MODULO AXIOMS {r.axioms} (regex only — kernel check missing)"
            return "COMPILED — kernel closure missing; do not report VERIFIED"
        return "HAS GAPS / UNVERIFIED — see block table"

    def status(self) -> None:
        """Render the live session state: one row per block + falsifications.

        After ``finish()`` the last finished session is rendered (read-only)
        instead of "no active session".
        """
        r = self._result or self._last_result
        finished = self._result is None and self._last_result is not None
        if r is None:
            print("[status    ] no active session — call begin() first")
            return
        self._reconcile_corpus_blocks()
        falsify_by_block = {f.get("block"): f.get("verdict", "?")
                            for f in r.falsifications}
        head = f"=== status: {r.fixture}{' (finished)' if finished else ''} ==="
        print(head)
        print(f"{'block':<{self._LOG_BLOCK_W}} {'kind':<14} {'falsify':<8} "
              f"{'state':<22} match/notes")
        for l in r.lemmas:
            glyph, state = self._block_state(l, falsify_by_block.get(l.name, ""))
            fal = falsify_by_block.get(l.name, "—")
            note = (l.library_match or l.named_result
                    or (l.compile_error.splitlines()[0][:50]
                        if l.compile_error else ""))
            if l.kind in ("violation", "circular"):
                note = f"{l.library_match or l.circular_with} — {l.note}"
            print(f"{l.name:<{self._LOG_BLOCK_W}} {l.kind:<14} {fal:<8} "
                  f"{glyph + ' ' + state:<22} {note}")
        if r.main_unformalizable and not r.compiled:
            print(f"{'sketch/assembled':<{self._LOG_BLOCK_W}} "
                  f"n/a — main statement not formalizable "
                  f"({r.main_unformalizable})")
        else:
            print(f"{'sketch':<{self._LOG_BLOCK_W}} "
                  f"{'✓ checked' if r.sketch_code else '— not run'}")
            print(f"{'assembled':<{self._LOG_BLOCK_W}} "
                  f"{'✓' if r.compiled else '✗'}")
        if r.structural_mode:
            structural = (
                "✓ COMPILES MODULO PLACEHOLDERS"
                if (r.structural_trusted_recheck or {}).get("compiled")
                or r.structural_compiled
                else "— pending"
            )
            print(f"{'structural':<{self._LOG_BLOCK_W}} {structural}")
            print(f"{'placeholders':<{self._LOG_BLOCK_W}} "
                  f"{r.structural_placeholders or '(none named)'}")
            print(f"{'independent discharged':<{self._LOG_BLOCK_W}} "
                  f"{r.structural_independent_discharged or '(none)'}")
        print(f"verdict{'' if finished else ' (so far)'}: {self._verdict_string()}")

    # ----- Search & Inspect -----

    def show(self, premise_id: str) -> Premise | None:
        """Show full details of a premise by ID (or partial match)."""
        for p in self.retriever.premises:
            if premise_id in p.id:
                print(f"ID: {p.id}")
                print(f"Source: {p.source_file}:{p.source_line}")
                print(f"Import: {p.import_path()}")
                print(f"Statement:\n{p.statement}")
                if p.docstring:
                    print(f"Doc: {p.docstring[:200]}")
                return p
        print(f"Not found: {premise_id}")
        return None

    def grep(self, pattern: str, top_k: int = 20) -> list[Premise]:
        """Search premises by substring match on ID or statement.

        ID matches rank before statement-only matches; theorems from
        modules that are not built (no .olean) rank last and are marked.
        """
        pattern_lower = pattern.lower()
        id_matches, stmt_matches = [], []
        for p in self.retriever.premises:
            if pattern_lower in p.id.lower():
                id_matches.append(p)
            elif pattern_lower in p.statement.lower():
                stmt_matches.append(p)
        all_matches = id_matches + stmt_matches
        all_matches.sort(key=lambda p: not self.module_built(p))
        total = len(all_matches)
        matches = all_matches[:top_k]
        if matches:
            self.retriever.record_retrieval([p.id for p in matches])
        for i, p in enumerate(matches, 1):
            built_note = "" if self.module_built(p) else "  [NOT BUILT — cannot import]"
            vac_note = ("  [ID-SHAPED — assumes its conclusion; not library coverage]"
                        if is_id_shaped(p.statement) else "")
            print(f"  {i:2d}. {p.id}{built_note}{vac_note}")
            print(f"      {p.signature_oneline()[:100]}")
        if total > top_k:
            print(f"  ... {total - top_k} more matches (pass top_k= to see them)")
        return matches

    def hybrid_search(self, query: str, top_k: int = 10) -> list[Premise]:
        """BM25-ranked search over the corpus (id, tags, docstring, statement)."""
        hits = self.retriever.hybrid_search(query, top_k=top_k)
        for i, h in enumerate(hits, 1):
            built_note = "" if self.module_built(h) else "  [NOT BUILT — cannot import]"
            vac_note = ("  [ID-SHAPED — assumes its conclusion; not library coverage]"
                        if is_id_shaped(h.statement) else "")
            print(f"  {i:2d}. [{h.score:.4f}] {h.id}{built_note}{vac_note}")
            print(f"      {h.signature_oneline()[:100]}")
        return hits

    def module_built(self, premise: Premise) -> bool:
        """Check whether a premise's module has a compiled .olean.

        Theorems from unbuilt modules exist in the corpus but cannot be
        imported. Only meaningful for the default corpus; test corpora
        are assumed valid.
        """
        if self.corpus_path != DEFAULT_CORPUS:
            return True
        import_path = premise.import_path()
        if not import_path:
            return True
        cached = self._module_built_cache.get(import_path)
        if cached is not None:
            return cached
        olean = (
            ROOT / ".lake" / "build" / "lib" / "lean"
            / import_path.replace(".", "/")
        ).with_suffix(".olean")
        result = olean.exists()
        self._module_built_cache[import_path] = result
        return result

    def reuse_stats(self) -> dict:
        """Print and return corpus reuse statistics."""
        stats = self.retriever.retrieval_stats()
        print(f"=== Corpus Reuse Stats ===")
        print(f"Total premises:    {stats['total_premises']}")
        print(f"Ever retrieved:    {stats['ever_retrieved']} ({stats['retrieval_rate']:.1%})")
        print(f"Ever matched:      {stats['ever_matched']} ({stats['match_rate']:.1%})")
        print(f"Never retrieved:   {stats['never_retrieved']}")
        if stats['top_matched']:
            print(f"\nMost matched:")
            for pid, count in stats['top_matched']:
                name = pid.split('.')[-1]
                print(f"  {count:4d}x  {name}")
        return stats

    # ----- Compile -----

    def compile(self, code: str, quiet: bool = False) -> LeanResult:
        """Compile Lean 4 code. Returns success/error.

        Tip: narrow imports compile ~6x faster than `import RLGeneralization`
        (which pulls the whole library plus Mathlib).
        """
        result = verify_lean_code(code)
        if result.success:
            if not quiet:
                self._log("compile", f"✓ compiles ({result.elapsed:.0f}s)")
        else:
            if not quiet:
                self._log("compile", f"✗ failed ({result.elapsed:.0f}s):")
                for line in result.errors.splitlines()[:10]:
                    print(f"  {line[:120]}")
                if result.goals:
                    self._log("compile", f"  {len(result.goals)} unsolved goal "
                                         "block(s) in result.goals")
        return result

    def repl_verify(self, code: str, allow_sorry: bool = False,
                    quiet: bool = False) -> LeanResult:
        """Fast-path check via a persistent REPL (iteration only).

        First call pays a one-time warmup (~30-60 s: import Mathlib +
        RLGeneralization); later calls return in well under a second even
        with maximal imports. ``code`` must NOT contain import lines — the
        warm environment already has Mathlib + RLGeneralization opened.

        Trust note: verdict-bearing gates (library_search, pre-add_novel
        re-runs, kernel closure) deliberately stay on ``compile`` /
        ``verify_lean_code`` — a fresh process per check — so certified
        results never depend on REPL session state.
        """
        if self._repl is None:
            from .repl import ReplSession
            self._repl = ReplSession()
            if not quiet:
                self._log("compile", "starting REPL session (one-time warmup)…")
        result = self._repl.check(code, allow_sorry=allow_sorry)
        if not quiet:
            glyph = "✓" if result.success else "✗"
            self._log("compile", f"{glyph} repl check ({result.elapsed:.1f}s)")
            if not result.success:
                for line in result.errors.splitlines()[:10]:
                    print(f"  {line[:120]}")
        return result

    def compile_statement(
        self,
        statement: str,
        imports: list[str] | None = None,
        opens: str = "Finset BigOperators",
    ) -> LeanResult:
        """Check that a statement elaborates (proof stubbed with sorry).

        Success means the SIGNATURE is well-formed — not that the theorem
        is proven. If the imports don't provide the default ``Finset``/
        ``BigOperators`` namespaces, pass ``opens`` (possibly ``""``).
        """
        import_block = "\n".join(f"import {m}" for m in (imports or ["RLGeneralization"]))
        open_stmt = f"open {opens}\n\n" if opens.strip() else ""
        code = f"{import_block}\n\n{open_stmt}{statement} := by sorry"
        result = verify_lean_code(code, allow_sorry=True)
        if result.success:
            self._log("compile", f"✓ statement elaborates ({result.elapsed:.0f}s) "
                                 "— proof still needed")
        else:
            self._log("compile", f"✗ statement invalid ({result.elapsed:.0f}s):")
            for line in result.errors.splitlines()[:10]:
                print(f"  {line[:120]}")
        return result

    _TRY_THIS_RE = re.compile(
        r"Try this:\s*\n?\s*(?:\[apply\]\s*)?exact\s+([^\n]+)")

    def library_search(
        self,
        statement: str,
        imports: list[str] | None = None,
        opens: str = "Finset BigOperators",
        max_heartbeats: int = 400_000,
        timeout: int = 180,
        fast: bool = True,
    ) -> LibrarySearchResult:
        """Type-directed dedup: compile `<statement> := by exact?`.

        The formal statement is the query — `exact?` searches everything
        imported (default: ALL of Mathlib + RLGeneralization + deps), so it
        catches duplicates that keyword search misses. ~13–16 s warm.

        ``found=True`` means a library proof EXISTS: the block is a
        library/instantiation match, not novel — do not formalize it, and
        never pass it to add_novel. ``found=False`` is weaker: exact?
        matches up to unification only and misses shape variants (n-ary vs
        binary, Finset.range vs Fintype, < vs ≤) — keep textual search too.

        ``inconclusive=True`` is different from both: exact? did NOT finish
        within its heartbeat budget / ``timeout`` — it neither found a proof
        nor ruled one out, so novelty is NOT cleared. The search is bounded by
        ``set_option maxHeartbeats`` so it terminates DETERMINISTICALLY rather
        than running to the wall-clock kill; narrow ``imports=`` to the few
        Mathlib modules the statement needs for a fast, conclusive answer.
        """
        selected_imports = imports or ["Mathlib", "RLGeneralization"]
        import_block = "\n".join(f"import {m}" for m in selected_imports)
        # Bound exact?'s own search: a heartbeat budget makes it exhaust
        # deterministically (a clean "budget reached" error) instead of hanging
        # until verify_lean_code's subprocess timeout — which used to surface as
        # errors="timeout" and get misreported below as an elaboration failure.
        body = (f"open {opens}\n\n"
                f"set_option maxHeartbeats {max_heartbeats} in\n"
                f"{statement} := by exact?")
        code = f"{import_block}\n\n{body}"
        # Resolution is a search/prioritization phase, not final evidence. A
        # persistent imported environment removes repeated 13–16s startup cost
        # across blocks; all verdict-bearing discharged code is still checked
        # by a fresh Lean process and kernel closure at assembly.
        use_repl = fast and set(selected_imports).issubset(
            {"Mathlib", "RLGeneralization"}
        )
        if use_repl:
            try:
                result = self.repl_verify(body, quiet=True)
            except Exception as exc:
                self._log(
                    "gate",
                    f"⚠ REPL search unavailable ({type(exc).__name__}); "
                    "falling back to fresh Lean",
                )
                result = verify_lean_code(code, timeout=timeout)
        else:
            result = verify_lean_code(code, timeout=timeout)

        if result.success:
            m = self._TRY_THIS_RE.search(result.output)
            suggestion = m.group(1).strip() if m else ""
            head = suggestion.split()[0].lstrip("(@") if suggestion else ""
            package = self._locate_package(head) if head else ""
            label = f"{package}.{head.split('.')[-1]}" if package else (head or "?")
            self._log("gate", f"✗ DUPLICATE ({result.elapsed:.0f}s) — exact? "
                              f"found {label}")
            if suggestion:
                self._log("gate", f"  proof: exact {suggestion}")
            self._log("gate", "  → resolve as library/instantiation; do not "
                              "formalize or add_novel")
            return LibrarySearchResult(
                found=True, suggestion=suggestion, head_symbol=head,
                package=package, elapsed=result.elapsed,
            )

        if "could not close the goal" in result.errors:
            self._log("gate", f"✓ no library proof found ({result.elapsed:.0f}s) "
                              "— novel plausible (shape variants not detected)")
            return LibrarySearchResult(found=False, elapsed=result.elapsed)

        errs = result.errors or ""
        if (errs.strip() == "timeout"
                or "maximum number of heartbeats" in errs
                or "deterministic" in errs and "timeout" in errs):
            self._log("gate", f"⚠ library_search INCONCLUSIVE ({result.elapsed:.0f}s) "
                              f"— exact? did not finish within its budget "
                              f"({max_heartbeats} heartbeats / {timeout}s); novelty "
                              "NOT cleared. Narrow `imports=` to the few Mathlib "
                              "modules the statement needs for a conclusive search.")
            return LibrarySearchResult(
                found=False, inconclusive=True, elapsed=result.elapsed,
                error="inconclusive: exact? budget exhausted (timeout / heartbeats)",
            )

        self._log("gate", f"⚠ statement did not elaborate ({result.elapsed:.0f}s) "
                          "— fix it before classifying the block:")
        for line in result.errors.splitlines()[:6]:
            print(f"  {line[:120]}")
        return LibrarySearchResult(
            found=False, elapsed=result.elapsed,
            error=result.errors[:1500] or "statement did not elaborate",
        )

    def _locate_package(self, head_symbol: str) -> str:
        """Best-effort: which package defines the suggested lemma."""
        name = head_symbol.split(".")[-1]
        for p in self.retriever.premises:
            if p.id == head_symbol or p.id.split(".")[-1] == name:
                return "RLGeneralization"
        for pkg_dir in (ROOT / ".lake" / "packages").glob("*"):
            if pkg_dir.name.lower() in ("mathlib", "batteries", "aesop"):
                continue
            try:
                hit = subprocess.run(
                    ["grep", "-rlE", "--include=*.lean",
                     rf"(theorem|lemma|def) {re.escape(name)}\b", str(pkg_dir)],
                    capture_output=True, text=True, timeout=30,
                )
                if hit.returncode == 0 and hit.stdout.strip():
                    return pkg_dir.name
            except (subprocess.TimeoutExpired, OSError):
                continue
        return "Mathlib"

    # ----- Audit -----

    def audit_structure(
        self,
        lean_code: str,
        expected_lemma_ids: list[str],
        theorem_name: str = "",
    ) -> StructuralAudit:
        """Static check: sorry/axiom presence and expected lemma usage.

        Pass ``theorem_name`` to additionally run the kernel-level
        `#print axioms` closure check (sees sorries/axioms hidden in
        imports, which the regex checks cannot).
        """
        audit = StructuralAudit(expected_lemmas=list(expected_lemma_ids))

        if has_sorry_token(lean_code):
            audit.has_sorry = True
            audit.verdict = "flag"

        audit.axioms = find_axioms(lean_code)
        if audit.axioms:
            audit.verdict = "flag"

        for lemma_id in expected_lemma_ids:
            short_name = lemma_id.split(".")[-1]
            if lemma_id in lean_code or short_name in lean_code:
                audit.used_lemmas.append(lemma_id)
            else:
                audit.missing_lemmas.append(lemma_id)

        if audit.missing_lemmas:
            audit.verdict = "flag"

        if theorem_name:
            closure = check_axiom_closure(lean_code, theorem_name)
            if not closure.ok:
                audit.verdict = "flag"  # fail closed
            else:
                if closure.has_sorry_ax:
                    audit.has_sorry = True
                    audit.verdict = "flag"
                if closure.custom:
                    audit.axioms = sorted(set(audit.axioms) | set(closure.custom))
                    audit.verdict = "flag"

        return audit

    # ----- Sketch -----

    _DECL_NAME_RE = re.compile(
        r"^\s*(?:private\s+|protected\s+|noncomputable\s+)*"
        r"(?:theorem|lemma|def)\s+([A-Za-z_][A-Za-z0-9_'.]*)"
    )

    def sketch(self, code: str, expected_blocks: list[str]) -> LeanResult:
        """Compile a sorried skeleton; success machine-checks the decomposition.

        The skeleton is the FULL proof file with every non-library block as
        `private lemma block_i ... := sorry` and the main theorem proven from
        the blocks with explicit glue. If it compiles, the conclusion really
        follows from the stated blocks — no gap, no circularity.

        Enforced here: every name in ``expected_blocks`` must occur ≥2 times
        in the code (declaration + at least one use). A skeleton whose glue
        tactic ignores a block "passes" while certifying nothing — that is
        a FAIL, not a pass.

        Skeleton-OK ≠ blocks-OK: the sorried statements can still be false.
        On failure, ``result.goals`` shows which implication is missing —
        diagnose decomposition gap vs fixable glue bug; never auto-verdict.
        """
        if self._result is not None:
            by_name = {lemma.name: lemma for lemma in self._result.lemmas}
            unknown = sorted({
                dep
                for lemma in self._result.lemmas
                for dep in lemma.depends_on
                if dep not in by_name
            })
            visiting: set[str] = set()
            visited: set[str] = set()
            cycle: list[str] = []

            def visit(name: str, path: list[str]) -> bool:
                if name in visiting:
                    start = path.index(name) if name in path else 0
                    cycle.extend(path[start:] + [name])
                    return True
                if name in visited:
                    return False
                visiting.add(name)
                path.append(name)
                for dep in by_name.get(name, LemmaResult(name)).depends_on:
                    if dep in by_name and visit(dep, path):
                        return True
                path.pop()
                visiting.remove(name)
                visited.add(name)
                return False

            for block_name in by_name:
                if visit(block_name, []):
                    break
            if unknown or cycle:
                detail = (
                    f"unknown dependencies: {unknown}" if unknown
                    else "dependency cycle: " + " → ".join(cycle)
                )
                if cycle:
                    self.set_verdict(
                        "UNVERIFIED/CIRCULAR", detail,
                        block=cycle[0] if cycle else "",
                    )
                result = LeanResult(success=False, errors=detail)
                self._result.sketch_code = code
                self._result.sketch_verified = False
                self._result.sketch_expected_blocks = list(expected_blocks)
                self._persist()
                self._log("sketch", f"✗ canonical DAG invalid — {detail}")
                return result

            block_ir = [
                {
                    "name": lemma.name,
                    "kind": lemma.kind,
                    "depends_on": lemma.depends_on,
                    "hypotheses": lemma.hypotheses,
                    "statement": lemma.statement,
                    "formal_signature": lemma.formal_signature,
                    "input_sha256": lemma.input_sha256,
                    "source_char_start": lemma.source_char_start,
                    "source_char_end": lemma.source_char_end,
                    "source_excerpt_sha256": lemma.source_excerpt_sha256,
                }
                for lemma in sorted(
                    self._result.lemmas, key=lambda item: item.name
                )
            ]
            self._result.decomposition_sha256 = hashlib.sha256(
                json.dumps(
                    {"schema_version": 1, "blocks": block_ir},
                    sort_keys=True,
                    separators=(",", ":"),
                ).encode()
            ).hexdigest()
            self._persist()

        result = verify_lean_code(code, allow_sorry=True)
        if not result.success:
            if self._result is not None:
                self._result.sketch_code = code
                self._result.sketch_verified = False
                self._result.sketch_expected_blocks = list(expected_blocks)
                self._persist()
            self._log("sketch", f"✗ skeleton failed ({result.elapsed:.0f}s) — "
                                "decomposition gap OR glue bug; inspect before verdict:")
            for line in result.errors.splitlines()[:10]:
                print(f"  {line[:120]}")
            if result.goals:
                self._log("sketch", f"  {len(result.goals)} unsolved goal block(s) "
                                    "in result.goals — the missing implication(s)")
            return result

        unused = [b for b in expected_blocks
                  if len(re.findall(rf"\b{re.escape(b)}\b", code)) < 2]
        if unused:
            result.success = False
            result.errors = (
                "vacuous glue: block(s) declared but never used in the "
                f"assembly: {unused}"
            )
            if self._result is not None:
                self._result.sketch_code = code
                self._result.sketch_verified = False
                self._result.sketch_expected_blocks = list(expected_blocks)
                self._persist()
            self._log("sketch", f"✗ vacuous glue — skeleton does NOT use: {unused}")
            self._log("sketch", "  the glue closed the goal without these blocks; "
                                "decomposition NOT certified — name every block "
                                "explicitly (exact/calc/linarith [block...])")
            return result

        decls = self._sorry_decl_names(code, result.sorry_lines)
        self._log("sketch", f"✓ skeleton compiles ({result.elapsed:.0f}s) — "
                            "decomposition machine-checked (blocks still sorried)")
        if decls:
            self._log("sketch", f"  to discharge ({len(decls)}): {', '.join(decls)}")
        if self._result is not None:
            self._result.sketch_code = code
            self._result.sketch_verified = True
            self._result.sketch_expected_blocks = list(expected_blocks)
            self._persist()
        return result

    def _sorry_decl_names(self, code: str, sorry_lines: list[int]) -> list[str]:
        """Map sorry-warning line numbers to declaration names."""
        lines = code.splitlines()
        names: list[str] = []
        for ln in sorry_lines:
            for li in range(min(ln, len(lines)) - 1, -1, -1):
                m = self._DECL_NAME_RE.match(lines[li])
                if m:
                    if m.group(1) not in names:
                        names.append(m.group(1))
                    break
        return names

    def structural_assemble(
        self,
        code: str,
        placeholder_blocks: list[str],
    ) -> LeanResult:
        """Compile a conditional proof with gaps only in named failed blocks.

        Unlike ``sketch()``, this is not allowed to leave every novel block as
        ``sorry``.  The source must contain exactly the requested placeholders,
        must use each placeholder in the downstream proof, and may not declare
        custom axioms.  Every resolved novel/instantiation block independent of
        the placeholders must already have passed ``discharge``.

        A success establishes only ``the main theorem follows modulo these
        placeholders``.  It is never a theorem-verification verdict.
        """
        if self._result is None:
            raise RuntimeError("No active session. Call begin() first.")
        placeholders = list(dict.fromkeys(str(b).strip()
                                          for b in placeholder_blocks
                                          if str(b).strip()))
        result = verify_lean_code(code, allow_sorry=True)
        errors: list[str] = []
        known = {lemma.name for lemma in self._result.lemmas}
        unknown = [name for name in placeholders if name not in known]
        if not placeholders:
            errors.append("at least one named placeholder block is required")
        if unknown:
            errors.append(f"unknown placeholder block(s): {unknown}")
        custom_axioms = find_axioms(code)
        if custom_axioms:
            errors.append(
                "custom axiom declarations are forbidden; use visible `sorry` "
                f"only in named placeholders: {custom_axioms}")

        sorry_decls = self._sorry_decl_names(code, result.sorry_lines)
        declared = [
            match.group(1)
            for line in code.splitlines()
            if (match := self._DECL_NAME_RE.match(line))
        ]
        if declared and declared[-1] in sorry_decls:
            errors.append(
                f"the final/main declaration may not be a placeholder: "
                f"{declared[-1]}")
        missing = [name for name in placeholders if name not in sorry_decls]
        extra = [name for name in sorry_decls if name not in placeholders]
        if missing:
            errors.append(f"named placeholder(s) do not contain `sorry`: {missing}")
        if extra:
            errors.append(f"unnamed `sorry` declaration(s): {extra}")
        unused = [name for name in placeholders
                  if len(re.findall(rf"\b{re.escape(name)}\b", code)) < 2]
        if unused:
            errors.append(f"placeholder block(s) are not used downstream: {unused}")

        deps = {lemma.name: list(lemma.depends_on)
                for lemma in self._result.lemmas}

        def depends_on_placeholder(name: str, seen: set[str] | None = None) -> bool:
            if name in placeholders:
                return True
            seen = set() if seen is None else seen
            if name in seen:
                return False
            seen.add(name)
            return any(depends_on_placeholder(dep, seen) for dep in deps.get(name, []))

        independent = [
            lemma for lemma in self._result.lemmas
            if lemma.kind in ("novel", "instantiation")
            and not lemma.skipped
            and lemma.name not in placeholders
            and not depends_on_placeholder(lemma.name)
        ]
        undischarged = [lemma.name for lemma in independent if not lemma.discharged]
        if undischarged:
            errors.append(
                "independent block(s) must pass discharge before structural "
                f"assembly: {undischarged}")

        if not result.success:
            errors.insert(0, result.errors or "Lean compilation failed")
        if errors:
            result.success = False
            result.errors = "; ".join(errors)

        rec = self._result
        rec.structural_mode = True
        rec.structural_code = code
        rec.structural_compiled = bool(result.success)
        rec.structural_placeholders = placeholders
        rec.structural_independent_discharged = [
            lemma.name for lemma in independent if lemma.discharged
        ]
        rec.structural_error = result.errors if not result.success else ""
        self._persist()

        if result.success:
            self._log(
                "assemble",
                "✓ STRUCTURAL-OK — conditional proof compiles with exactly "
                f"{len(placeholders)} named placeholder(s): "
                f"{', '.join(placeholders)}",
            )
        else:
            self._log("assemble", f"✗ structural assembly rejected — {result.errors}")
        return result

    # ----- Session Management -----

    # ----- Session persistence (in-progress journal) -----
    #
    # Session state used to live only in this Python process: an add_novel
    # in one process followed by finish() in another mislabeled
    # kernel-verified blocks as GAP. Every mutation now journals the live
    # session to runs/<fixture>.inprogress.json; resume() reloads it in a
    # fresh process; finish() removes it.

    def _journal_path(self, fixture_name: str) -> Path:
        self.runs_dir.mkdir(exist_ok=True)
        return self.runs_dir / f"{fixture_name}.inprogress.json"

    def _persist(self) -> None:
        """Journal the live session state (no-op without a session)."""
        if self._result is None:
            return
        try:
            self._journal_path(self._result.fixture).write_text(
                json.dumps(self._result.to_dict(), indent=2,
                           ensure_ascii=False) + "\n")
        except OSError as e:  # journaling must never break the pipeline
            self._log("begin", f"⚠ could not journal session: {e}")

    def begin(self, fixture_name: str) -> VerifyResult:
        """Start a new verification session for a fixture.

        If an in-progress journal exists for this fixture (a previous
        process began but never finished), warn — ``resume()`` continues
        that session; ``begin()`` overwrites it.
        """
        if self._journal_path(fixture_name).exists():
            self._log("begin", f"⚠ in-progress journal exists for "
                               f"'{fixture_name}' — resume() continues it; "
                               "begin() starts fresh and overwrites it")
        self._result = VerifyResult(fixture=fixture_name)
        self._amend_path = None  # a fresh session writes a new record
        self._log("begin", f"session: {fixture_name}")
        self._persist()
        return self._result

    def resume(self, fixture_name: str) -> VerifyResult:
        """Reload an in-progress session journaled by a previous process."""
        path = self._journal_path(fixture_name)
        if not path.exists():
            raise FileNotFoundError(
                f"no in-progress journal for '{fixture_name}' — call begin()")
        self._result = _verify_result_from_dict(json.loads(path.read_text()))
        self._amend_path = None  # resuming a journal writes a new record on finish
        self._log("begin", f"resumed session: {fixture_name} "
                           f"({len(self._result.lemmas)} block(s) journaled)")
        return self._result

    def amend(self, fixture_name: str) -> VerifyResult:
        """Reopen the most recent FINISHED run record to correct/extend it.

        ``finish()`` removes the in-progress journal, so a later process
        cannot ``resume()``. ``amend()`` loads the latest saved
        ``runs/<fixture>_<ts>.json`` back into a live session. Make
        corrections (``formalize``, ``add_novel(block=...)``,
        ``record_backtranslation``, ...), then call ``finish()`` again — it
        OVERWRITES the same record in place (same timestamped filename), so
        amending does not proliferate duplicate records for one fixture.
        """
        candidates = sorted(
            p for p in self.runs_dir.glob(f"{fixture_name}_*.json")
            if not p.name.endswith(".inprogress.json"))
        if not candidates:
            raise FileNotFoundError(
                f"no finished run record for '{fixture_name}' in "
                f"{self.runs_dir} — nothing to amend (use begin()/resume())")
        src = candidates[-1]  # timestamped names sort chronologically
        self._result = _verify_result_from_dict(json.loads(src.read_text()))
        self._amend_path = src
        self._persist()  # re-create the journal so the session is live again
        self._log("begin", f"amending finished record: {_relpath(src)} "
                           f"({len(self._result.lemmas)} block(s))")
        return self._result

    def resolve(
        self,
        name: str,
        *,
        library: str = "",
        instantiation: str = "",
        prior: str = "",
        prior_code: str = "",
        prior_artifact: str = "",
        named_result: str = "",
        violation: str = "",
        circular: str = "",
        reason: str = "",
        novel: bool = False,
        statement_nl: str = "",
        depends_on: list[str] | None = None,
        source_excerpt: str = "",
        source_excerpt_verified: bool = False,
        source_char_start: int = -1,
        source_char_end: int = -1,
        source_byte_start: int = -1,
        source_byte_end: int = -1,
        input_sha256: str = "",
        formal_signature: str = "",
        hypotheses: list[str] | None = None,
    ) -> LemmaResult:
        """Record how a building block is resolved.

        ``library=`` / ``instantiation=`` take a QUALIFIED IDENTIFIER and are
        validated: a corpus hit is recorded for reuse tracking; an identifier
        not in the corpus is accepted with a loud ⚠ (external — e.g. Mathlib;
        Phase 3 must compile against it); free text (spaces, slashes, ...) is
        REJECTED — cite textbook results via ``named_result=`` instead.

        ``prior=`` records an exact kernel-verified component supplied by a
        trusted paper-session sidecar. Its source is included in this run's
        final assembly and recompiled by the parent harness.

        ``named_result="Sion's minimax theorem (Sion 1958)"`` records an
        instantiation of a well-known named theorem that has no library id.
        It never enters reuse stats; if the block is load-bearing it must go
        through the Axiom lifecycle or be formalized.

        ``violation="lemma_id", reason="..."`` records a HYPOTHESIS_VIOLATION
        block: the cited library lemma is correct, but the proof applies it
        to an argument that provably violates a stated hypothesis. Pair it
        with ``d.set_verdict("UNVERIFIED/HYPOTHESIS_VIOLATION", ...)``.

        ``circular="block_name", reason="..."`` records a CIRCULAR block: this
        block's justification presupposes the conclusion of ``block_name``
        (from the same decomposition), which in turn (transitively) invokes
        this block — a dependency cycle, possibly hidden by a conditional
        conclusion ("on the event E"). Pair it with
        ``d.set_verdict("UNVERIFIED/CIRCULAR", ...)``.
        """
        lemma = LemmaResult(name=name)
        lemma.depends_on = list(depends_on or [])
        lemma.dependencies_declared = depends_on is not None
        # Preserve raw Unicode and whitespace: character/byte offsets are part
        # of the source-correspondence certificate and become meaningless if
        # the excerpt is normalized after capture.
        lemma.source_excerpt = source_excerpt
        lemma.source_excerpt_sha256 = (
            hashlib.sha256(lemma.source_excerpt.encode()).hexdigest()
            if lemma.source_excerpt else ""
        )
        lemma.source_excerpt_verified = bool(
            lemma.source_excerpt and source_excerpt_verified
        )
        lemma.source_char_start = int(source_char_start)
        lemma.source_char_end = int(source_char_end)
        lemma.source_byte_start = int(source_byte_start)
        lemma.source_byte_end = int(source_byte_end)
        lemma.input_sha256 = str(input_sha256)
        lemma.formal_signature = str(formal_signature)
        lemma.hypotheses = list(hypotheses or [])
        lemma.hypotheses_declared = hypotheses is not None
        if prior:
            if not prior_code.strip():
                raise ValueError("prior= requires runner-owned verified Lean source")
            lemma.kind = "prior"
            lemma.prior_name = prior
            lemma.prior_artifact = prior_artifact
            lemma.code = prior_code
            lemma.compiled = True
            lemma.discharged = True
            lemma.trusted_rechecked = True
            self._log(
                "resolve",
                f"✓ prior paper component — {prior}",
                block=name,
            )
        elif library or instantiation:
            ident = library or instantiation
            kind = "library" if library else "instantiation"
            if not _IDENT_RE.fullmatch(ident):
                raise ValueError(
                    f"{kind}= must be a qualified identifier, got {ident!r} — "
                    "for textbook citations (Sion, Brouwer, ...) use "
                    "named_result=; for facts with no name, novel=True")
            lemma.kind = kind
            lemma.library_match = ident
            glyph = "✓" if library else "~"
            if self._record_match(ident):
                self._log("resolve", f"{glyph} {kind} — {ident}", block=name)
                hit = next((p for p in self.retriever.premises
                            if p.id == ident or p.id.endswith(f".{ident}")),
                           None)
                if hit is not None:
                    lemma.library_source_file = hit.source_file
                    lemma.library_source_line = int(hit.source_line or 0)
                    lemma.library_statement = hit.statement
                    lemma.library_import = hit.import_path()
                    lemma.library_found_in_repo = True
                if hit is not None and is_id_shaped(hit.statement):
                    lemma.citation_invalid = True
                    lemma.note = ("cited lemma is ID-SHAPED (conclusion ≡ "
                                  "hypothesis) — it assumes what it claims")
                    self._log("resolve",
                              f"⚠ {ident} is ID-SHAPED — its conclusion is "
                              "one of its own hypotheses; citing it is "
                              "camouflage, not library coverage. Treat this "
                              "block as novel.", block=name)
            else:
                exists = self._validate_external(ident)
                if exists is True:
                    lemma.note = "external id — validated by #check"
                    self._log("resolve",
                              f"{glyph} {kind} — {ident} (external, #check ✓)",
                              block=name)
                elif exists is False:
                    lemma.citation_invalid = True
                    lemma.note = "external id — NOT FOUND by #check"
                    self._log("resolve",
                              f"⚠ {kind} — {ident} NOT FOUND by #check under "
                              "Mathlib+RLGeneralization — likely a wrong "
                              "name; fix the citation before Phase 3",
                              block=name)
                else:  # checker unavailable
                    lemma.note = "external id — not in corpus, unvalidated at resolve time"
                    self._log("resolve",
                              f"⚠ {kind} — {ident} NOT IN CORPUS (external?); "
                              "Phase 3 must compile against it", block=name)
        elif named_result:
            lemma.kind = "instantiation"
            lemma.named_result = named_result
            self._log("resolve", f"~ instantiation of named result — "
                                 f"{named_result} (not corpus-tracked)", block=name)
        elif violation:
            if not reason.strip():
                raise ValueError(
                    "violation resolutions require reason= (which hypothesis, "
                    "which argument, why it is violated)")
            lemma.kind = "violation"
            lemma.library_match = violation
            lemma.note = reason.strip()
            self._record_match(violation)
            self._log("resolve",
                      f"✗ HYPOTHESIS_VIOLATION — {violation}: {lemma.note}",
                      block=name)
        elif circular:
            if not reason.strip():
                raise ValueError(
                    "circular resolutions require reason= (whose conclusion "
                    "is presupposed, and where — e.g. which conditional "
                    "conclusion was invoked unconditionally)")
            lemma.kind = "circular"
            lemma.circular_with = circular
            lemma.note = reason.strip()
            self._log("resolve",
                      f"✗ CIRCULAR — presupposes {circular}: {lemma.note}",
                      block=name)
        else:
            lemma.kind = "novel"
            self._log("resolve", "? novel — must be formalized", block=name)
        lemma.statement = statement_nl
        self._near_match_check(lemma, name, statement_nl)
        if self._result:
            matching = [
                index for index, prior in enumerate(self._result.lemmas)
                if prior.name == name
            ]
            if matching:
                prior = self._result.lemmas[matching[0]]
                if prior.discharged or prior.trusted_rechecked:
                    raise ValueError(
                        f"cannot re-resolve discharged/trusted block {name!r}; "
                        "use a new block name so certificates remain stable"
                    )
                self._result.lemmas[matching[0]] = lemma
                # Contract-v2 records created by older agents could already
                # contain duplicates. Collapse unresolved duplicates while the
                # block is being explicitly corrected.
                self._result.lemmas = [
                    item for index, item in enumerate(self._result.lemmas)
                    if item.name != name or index == matching[0]
                ]
                self._log("resolve", "· updated existing unresolved block",
                          block=name)
            else:
                self._result.lemmas.append(lemma)
            self._persist()
        return lemma

    def _near_match_check(self, lemma: LemmaResult, name: str,
                          statement_nl: str) -> None:
        """Resolve-time log-argument scan against the nearest library lemmas.

        Surfaces constant/log-argument discrepancies mechanically (the
        "library witness" check). Annotates, never suppresses: `differs`
        and `agrees` are both shown; silence proves nothing.
        """
        if not statement_nl.strip():
            if lemma.kind in ("library", "instantiation", "prior", "violation",
                              "circular"):
                self._log("gate", "⚠ no statement_nl — near-match scan skipped",
                          block=name)
            return
        query = f"{name.replace('_', ' ')} {statement_nl}"
        hits = self.retriever.hybrid_search(query, top_k=8)
        scan = near_match_scan(statement_nl, hits)
        lemma.near_match = scan
        if not scan["claim_log_args"]:
            return
        if not (scan["differs"] or scan["substitutions"]):
            if scan["agrees"]:
                self._log("gate", f"· near-match scan: {len(scan['agrees'])} "
                                  "library log-arg agreement(s), 0 differ",
                          block=name)
            return
        claim = ",".join("{" + ",".join(a) + "}" for a in scan["claim_log_args"])
        self._log("gate", f"⚠ near-match log-arg scan — block log {claim}",
                  block=name)
        for a in scan["agrees"]:
            self._log("gate", f"  agrees:  {a['id'].split('.')[-1]} "
                              f"log {[','.join(s) for s in a['log_args']]}")
        for dif in scan["differs"]:
            d0 = dif["diffs"][0]
            what = (f"block missing: {{{','.join(d0['missing'])}}}"
                    if d0["missing"] else
                    f"block extra: {{{','.join(d0['extra'])}}}")
            self._log("gate", f"  differs: {dif['id'].split('.')[-1]} "
                              f"log {{{','.join(d0['lemma_log'])}}} ({what})")
        for s in scan["substitutions"]:
            self._log("gate", f"  similar: {s['id'].split('.')[-1]} "
                              f"log {[','.join(x) for x in s['log_args']]}")
        self._log("gate", "  → adjudicate every `differs` line in the report "
                          "(why the differing factor does/doesn't belong)")

    def refute(
        self,
        block: str,
        code: str,
        description: str,
        theorem_name: str = "",
        *,
        target_scope: str = "UNSCOPED",
        finding_kind: str = "UNCLASSIFIED",
        premises_satisfied: bool = False,
        objects_well_defined: bool = False,
        conclusion_negated: bool = False,
        statement_faithful: bool = False,
    ) -> Refutation:
        """Formalize a scoped Lean negative certificate.

        ``description`` must state the refuted claim verbatim — it ties the
        counterexample to the block and is persisted for audit. The
        A main-theorem counterexample should assert
        *premises-hold ∧ objects-defined ∧ ¬conclusion* for a concrete
        instance.  Proof-step certificates instead target the exact disputed
        inference.  Unspecified classifications stay ``UNSCOPED`` and cannot
        support a top-level ``WRONG`` verdict.

        ``kernel_backed`` is derived fail-closed: True only when the code
        compiles AND its kernel closure is ⊆ {propext, Classical.choice,
        Quot.sound}. Failed attempts are still recorded (the verdict simply
        stays audit-only).  Scope and semantic booleans are supplied only by a
        trusted parent after statement comparison; compiling an auxiliary
        lemma cannot upgrade them. Refutations are paper-specific negative
        facts: never add_novel them.
        """
        if self._result is None:
            raise RuntimeError("No active session. Call begin() first.")
        if not description.strip():
            raise ValueError(
                "refute requires description= (the refuted claim, verbatim)")

        ref = Refutation(
            block=block,
            description=description.strip(),
            target_scope=target_scope,
            finding_kind=finding_kind,
            premises_satisfied=premises_satisfied,
            objects_well_defined=objects_well_defined,
            conclusion_negated=conclusion_negated,
            statement_faithful=statement_faithful,
        )

        if has_sorry_token(code):
            ref.error = "code contains a sorry token"
            self._log("refute", "✗ rejected — counterexample contains `sorry`",
                      block=block)
            self._result.refutations.append(ref)
            self._persist()
            return ref
        declared_axioms = find_axioms(code)
        if declared_axioms:
            ref.error = f"code declares axiom(s): {declared_axioms}"
            self._log("refute", f"✗ rejected — counterexample declares "
                                f"axiom(s): {declared_axioms}", block=block)
            self._result.refutations.append(ref)
            self._persist()
            return ref

        name = theorem_name
        if not name:
            m = re.search(r"(?:theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_'.]*)", code)
            name = m.group(1) if m else ""
        if not name:
            ref.error = "no theorem/lemma declaration found in code"
            self._log("refute", "✗ no theorem declaration found in the "
                                "counterexample code", block=block)
            self._result.refutations.append(ref)
            self._persist()
            return ref

        result = self.compile(code)
        ref.code = code
        ref.compiled = result.success
        if not result.success:
            ref.error = result.errors[:1500]
            self._log("refute", f"✗ counterexample failed to compile "
                                f"({result.elapsed:.0f}s) — verdict stays "
                                "audit-only", block=block)
            self._result.refutations.append(ref)
            self._persist()
            self._derive_verdict_evidence()
            return ref

        qualified = _qualified_decl_name(code, name)
        ref.theorem = qualified
        closure = check_axiom_closure(code, qualified)
        if not closure.ok:
            ref.error = f"kernel closure check failed: {closure.error[:300]}"
            self._log("refute", f"⚠ closure check failed for '{qualified}' — "
                                "verdict stays audit-only", block=block)
        else:
            ref.kernel_axioms = closure.axioms
            if closure.has_sorry_ax or closure.custom:
                taint = ("sorryAx" if closure.has_sorry_ax
                         else f"custom axiom(s) {closure.custom}")
                ref.error = f"closure tainted: {taint}"
                self._log("refute", f"✗ closure of '{qualified}' tainted "
                                    f"({taint}) — NOT kernel-backed", block=block)
            else:
                ref.kernel_backed = True
                self._log("refute", f"✓ kernel-backed — {qualified} closes over "
                                    "standard axioms only", block=block)
        self._result.refutations.append(ref)
        self._derive_verdict_evidence()
        self._persist()
        return ref

    def certify_step(
        self,
        block: str,
        code: str,
        description: str,
        theorem_name: str = "",
    ) -> StepCertificate:
        """Propose a positive Lean certificate for a disputed inference.

        The trusted parent later recompiles this source and checks that its
        formal statement faithfully matches the exact submitted excerpt.
        Success here therefore records a candidate, not a full-proof verdict.
        """
        if self._result is None:
            raise RuntimeError("No active session. Call begin() first.")
        if not description.strip():
            raise ValueError(
                "certify_step requires description= (the exact disputed "
                "claim, verbatim)")

        cert = StepCertificate(block=block, description=description.strip())
        if has_sorry_token(code):
            cert.error = "code contains a sorry token"
        else:
            declared_axioms = find_axioms(code)
            if declared_axioms:
                cert.error = f"code declares axiom(s): {declared_axioms}"
        if cert.error:
            self._log("confirm", f"✗ rejected — {cert.error}", block=block)
            self._result.step_certificates.append(cert)
            self._persist()
            return cert

        name = theorem_name
        if not name:
            match = re.search(
                r"(?:theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_'.]*)", code)
            name = match.group(1) if match else ""
        if not name:
            cert.error = "no theorem/lemma declaration found in code"
            self._log("confirm", f"✗ {cert.error}", block=block)
            self._result.step_certificates.append(cert)
            self._persist()
            return cert

        result = self.compile(code)
        cert.code = code
        cert.compiled = result.success
        if not result.success:
            cert.error = result.errors[:1500]
        else:
            cert.theorem = _qualified_decl_name(code, name)
            closure = check_axiom_closure(code, cert.theorem)
            if not closure.ok:
                cert.error = (
                    f"kernel closure check failed: {closure.error[:300]}")
            else:
                cert.kernel_axioms = closure.axioms
                if closure.has_sorry_ax or closure.custom:
                    taint = (
                        "sorryAx" if closure.has_sorry_ax
                        else f"custom axiom(s) {closure.custom}"
                    )
                    cert.error = f"closure tainted: {taint}"
                else:
                    cert.kernel_backed = True

        marker = "✓" if cert.kernel_backed else "✗"
        detail = (
            f"kernel-backed candidate — {cert.theorem}"
            if cert.kernel_backed else
            f"candidate not kernel-backed ({cert.error})"
        )
        self._log("confirm", f"{marker} {detail}", block=block)
        self._result.step_certificates.append(cert)
        self._persist()
        return cert

    def record_falsification(self, report) -> dict:
        """Record a falsification-gate outcome in the run record.

        ``report`` is a ``rlverify.falsify.FalsifyReport`` (or an equivalent
        dict). REFUTED is an audit finding unless a trusted deterministic
        checker has independently validated its serialized certificate;
        PASSED carries zero verification weight.
        """
        rec = report.to_dict() if hasattr(report, "to_dict") else dict(report)
        verdict = rec.get("verdict", "?")
        block = rec.get("block", "?")
        marker = "✗" if verdict == "REFUTED" else "·"
        detail = report.summary() if hasattr(report, "summary") else verdict
        self._log("falsify", f"{marker} {detail}", block=block)
        if self._result is not None:
            self._result.falsifications.append(rec)
            self._persist()
        return rec

    def formalize(
        self,
        name: str,
        statement: str,
        proof: str,
        imports: list[str] | None = None,
        opens: str = "Finset BigOperators",
    ) -> LemmaResult:
        """Formalize a novel lemma: provide statement + proof, compile it.

        If the imports don't provide the default ``Finset``/``BigOperators``
        namespaces, pass ``opens`` (possibly ``""``). Pass the SAME ``opens``
        to ``assemble`` later — it re-adds its own open line after stripping
        per-lemma ones.

        The proof may be a tactic block (default, wrapped in ``:= by``) OR a
        bare term (e.g. an instantiation ``M.some_lemma a b c``). If the
        ``:= by`` form fails to compile, the same proof is retried as a term
        (``:= proof``); whichever compiles is recorded. This makes term-mode
        instantiation proofs work without a separate flag.
        """
        import_block = "\n".join(f"import {m}" for m in (imports or ["RLGeneralization"]))
        open_stmt = f"open {opens}\n\n" if opens.strip() else ""
        code = f"{import_block}\n\n{open_stmt}{statement} := by\n  {proof}"

        result = self.compile(code)
        if not result.success:
            # Retry as a term-mode proof — instantiation proofs are naturally
            # terms (`:= M.lemma args`), which the `:= by` wrapper rejects.
            term_code = f"{import_block}\n\n{open_stmt}{statement} :=\n  {proof}"
            term_result = self.compile(term_code)
            if term_result.success:
                code, result = term_code, term_result
        lemma = self._find_lemma(name)
        if lemma:
            lemma.statement = statement
            lemma.proof = proof
            lemma.code = code
            lemma.compiled = result.success
            lemma.discharged = result.success
            lemma.discharge_certificate_sha256 = (
                hashlib.sha256(code.encode()).hexdigest()
                if result.success else ""
            )
            lemma.compile_error = result.errors if not result.success else ""
            if not result.success and self._result is not None:
                self._result.discharge_order = [
                    b for b in self._result.discharge_order if b != name
                ]
            self._persist()

        if result.success:
            lemma = lemma or LemmaResult(name=name)
            lemma.discharged = True
            if self._result is not None:
                # Record the first successful discharge. Re-proving a dependency
                # later must not make an already-valid topological order appear
                # inverted.
                if name not in self._result.discharge_order:
                    self._result.discharge_order.append(name)
                self._persist()
            self._log("discharge", f"✓ formalized ({result.elapsed:.0f}s)", block=name)
        else:
            self._log("discharge", f"✗ compile failed ({result.elapsed:.0f}s) — "
                                   "see errors above", block=name)
        return lemma or LemmaResult(name=name, compiled=result.success)

    def assemble(
        self,
        statement: str,
        proof: str,
        imports: list[str] | None = None,
        novel_code: str = "",
        opens: str = "Finset BigOperators",
    ) -> VerifyResult:
        """Assemble and compile the main theorem with all building blocks.

        Per-lemma ``open`` lines are stripped and replaced by a single
        ``opens`` line — pass the same ``opens`` used in ``formalize``.
        """
        if not self._result:
            self._result = VerifyResult(fixture="unknown")

        import_block = "\n".join(f"import {m}" for m in (imports or ["RLGeneralization"]))
        open_stmt = f"open {opens}" if opens.strip() else ""

        # Collect novel lemma code from formalized lemmas
        if not novel_code:
            parts = []
            for l in self._result.lemmas:
                if l.kind != "library" and l.compiled and l.code:
                    # Strip imports/opens from individual lemma code
                    lines = l.code.splitlines()
                    body_lines = [
                        ln for ln in lines
                        if not ln.startswith("import ") and not ln.startswith("open ")
                    ]
                    parts.append("\n".join(body_lines).strip())
            novel_code = "\n\n".join(parts)

        # Build final file
        sections = [s for s in (import_block, open_stmt) if s]
        if novel_code:
            sections.append(novel_code)
        sections.append(f"{statement} := by\n  {proof}")
        code = "\n\n".join(sections)

        name_m = re.search(
            r"(?:theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_'.]*)", statement)
        closure = (
            check_axiom_closure(code, name_m.group(1)) if name_m else None
        )
        # A subprocess-backed closure check compiles the exact augmented file,
        # so reuse that result instead of compiling the same source twice.
        # Mocked/legacy closure objects have no compile_result and retain the
        # old fallback, which also keeps third-party integrations compatible.
        result = (
            closure.compile_result
            if closure is not None and closure.compile_result is not None
            else self.compile(code)
        )
        if closure is not None and closure.compile_result is not None:
            if result.success:
                self._log("compile", f"✓ compiles + kernel audit "
                                     f"({result.elapsed:.0f}s, one pass)")
            else:
                self._log("compile", f"✗ compile/kernel pass failed "
                                     f"({result.elapsed:.0f}s)")
        self._result.main_statement = statement
        self._result.main_proof = proof
        self._result.main_code = code
        self._result.compiled = result.success
        self._result.compile_error = result.errors if not result.success else ""
        self._result.axioms = find_axioms(code)
        if result.success:
            self._result.main_unformalizable = ""  # it just got stated
            # Back-fill block status: the file compiled with allow_sorry=False,
            # so every theorem/lemma DECLARED in it genuinely compiled. A block
            # proved inside the assembled file (not via formalize()) would
            # otherwise stay GAP. Mark any such block compiled.
            # Strip comments first so a commented-out declaration cannot
            # falsely mark a block compiled (over-stripping only leaves a block
            # as GAP — conservative, never a false positive).
            uncommented = re.sub(r"/-.*?-/", "", code, flags=re.DOTALL)
            uncommented = re.sub(r"--[^\n]*", "", uncommented)
            declared = set(re.findall(
                r"(?:^|\n)\s*(?:private\s+|protected\s+|noncomputable\s+)*"
                r"(?:theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_']*)", uncommented))
            for l in self._result.lemmas:
                if not l.compiled and l.name in declared:
                    l.compiled = True
                    if not l.code:
                        l.code = code
                    self._log("assemble",
                              f"· back-filled compiled (declared in assembled file)",
                              block=l.name)

        if result.success:
            if closure is not None and closure.ok:
                self._result.kernel_closure_checked = True
                self._result.kernel_axioms = closure.axioms
                self._result.has_sorry_ax = closure.has_sorry_ax
                if closure.has_sorry_ax:
                    self._log("assemble",
                              "✗ UNVERIFIED — kernel reports sorryAx in the "
                              f"closure of {closure.theorem} (a sorry in this "
                              "file or its imports); compile success does not help")
                elif closure.custom:
                    self._log("assemble",
                              f"⚠ kernel closure has {len(closure.custom)} "
                              f"non-standard axiom(s): {closure.custom}")
                    self._log("assemble",
                              "  → VERIFIED MODULO AXIOMS — register each in "
                              "axiom_backlog.md + back-translation audit")
                else:
                    self._log("assemble",
                              "✓ VERIFIED — kernel closure ⊆ "
                              "{propext, Classical.choice, Quot.sound}")
                # Regex sees declared-but-UNUSED axioms the closure omits.
                dead = [a for a in self._result.axioms
                        if a not in closure.axioms]
                if dead:
                    self._log("assemble",
                              f"⚠ declared but unused axiom(s): {dead} — remove them")
            else:
                self._result.kernel_closure_checked = False
                err = closure.error if closure is not None else "no theorem name found in statement"
                self._log("assemble",
                          f"⚠ kernel axiom check FAILED ({err[:200]}) — regex "
                          "fallback only; do NOT report VERIFIED without a closure")
                if self._result.axioms:
                    self._log("assemble",
                              f"  regex found axiom(s): {self._result.axioms}")
        else:
            self._log("assemble", "✗ assembly failed — see compile errors above")
        self._persist()
        return self._result

    def finish(self, save: bool = True) -> VerifyResult:
        """Finalize session: save the Lean output and a JSON run record.

        Novel lemmas are NOT auto-added to the corpus here — library
        growth must go through ``add_novel`` so each lemma passes the
        Phase 5 generality gate explicitly.
        """
        if not self._result:
            raise RuntimeError("No active session. Call begin() first.")
        self._reconcile_corpus_blocks()

        r = self._result
        # Audit-coverage warnings — computed BEFORE the record is saved, so
        # the JSON carries its own incompleteness flags (audit_warnings) and
        # the agent sees them while the session can still be amended.
        r.audit_warnings = []
        falsify_by_block = {f.get("block"): f.get("verdict", "?")
                            for f in r.falsifications}
        # Gate-coverage: every novel/instantiation block not deliberately
        # skipped needs a recorded falsification outcome (SKIPPED counts).
        ungated = [l.name for l in r.lemmas
                   if l.kind in ("novel", "instantiation")
                   and not l.skipped and l.name not in falsify_by_block]
        if ungated:
            r.audit_warnings.append(
                f"{len(ungated)} block(s) have no recorded falsification-gate "
                f"outcome: {', '.join(ungated)} — record PASSED/VACUOUS/"
                "SKIPPED via record_falsification")
        bt_targets = {b["target"] for b in r.backtranslations}
        # Mandatory-audit enforcement: verdict-bearing statements need a
        # recorded sealed back-translation (see /verify-full-process Phase 3).
        for ref in r.refutations:
            if not ref.kernel_backed:
                continue
            covered = any(
                t in (ref.block, ref.theorem)
                or (ref.theorem and ref.theorem.endswith(f".{t}"))
                for t in bt_targets)
            if not covered:
                r.audit_warnings.append(
                    f"kernel-backed refutation '{ref.theorem or ref.block}' "
                    "has NO recorded back-translation audit — mandatory for "
                    "verdict-bearing statements")
        if r.compiled and "main" not in bt_targets:
            r.audit_warnings.append(
                "assembled main theorem has NO recorded back-translation "
                "audit (target='main') — mandatory before reporting VERIFIED")
        for b in r.backtranslations:
            if b["verdict"] == "MISMATCH":
                r.audit_warnings.append(
                    f"back-translation MISMATCH on '{b['target']}' — the "
                    "formalization is unfaithful; the verdict must carry it")
        # Library additions are verdict-bearing statements too.
        for name in r.novel_added:
            if name not in bt_targets:
                r.audit_warnings.append(
                    f"library addition '{name}' has NO recorded "
                    "back-translation audit — mandatory for add_novel "
                    "candidates")
        for w in r.audit_warnings:
            self._log("finish", f"⚠ {w}")

        # Strict-gate enforcement (harness/untrusted sessions only). The
        # warnings above are advisory for trusted local runs; here they become
        # verdict-affecting: a VERIFIED-class verdict with any coverage gap is
        # downgraded to UNVERIFIED/UNGATED. The class decision uses the single
        # verdict authority (rlverify/verdict.py), not a fourth inline copy.
        # Use gate_failures() (the single authority), not r.audit_warnings:
        # the latter omits the sealed-triage requirement, so strict mode would
        # otherwise disagree with harness/enforce on a triage-less VERIFIED.
        r.gate_downgrade = bool(
            self._strict_gates
            and verdict_class(r.to_dict()) in VERIFIED_CLASS
            and gate_failures(r.to_dict()))
        if r.gate_downgrade:
            self._log("finish", "⚠ strict mode: VERIFIED downgraded to "
                                "UNVERIFIED/UNGATED — required gates missing "
                                "(see warnings above)")

        artifacts: list[str] = []
        if save:
            from datetime import datetime
            run_dir = self.runs_dir
            run_dir.mkdir(exist_ok=True)
            ts = datetime.now().strftime("%Y%m%d_%H%M%S")
            if self._result.main_code:
                out_code = self._result.main_code
                name_m = re.search(
                    r"(?:theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_'.]*)",
                    self._result.main_statement,
                )
                if name_m and "#print axioms" not in out_code:
                    # Reproducible certificate: anyone can re-check with
                    # `lake env lean runs/<file>.lean` and read the closure.
                    out_code = (out_code.rstrip()
                                + f"\n\n#print axioms {name_m.group(1)}\n")
                out_path = run_dir / f"{self._result.fixture}_{ts}.lean"
                out_path.write_text(out_code)
                artifacts.append(_relpath(out_path))
            for lemma in self._result.lemmas:
                if not (lemma.compiled and lemma.code):
                    continue
                block_code = lemma.code
                qualified = _qualified_decl_name(block_code, lemma.name)
                if qualified and "#print axioms" not in block_code:
                    block_code = (
                        block_code.rstrip()
                        + f"\n\n#print axioms {qualified}\n"
                    )
                safe_block = re.sub(
                    r"[^A-Za-z0-9_.-]+", "_", lemma.name
                ).strip("._-") or "block"
                block_path = (
                    run_dir
                    / f"{self._result.fixture}_{ts}_block_{safe_block}.lean"
                )
                block_path.write_text(block_code)
                lemma.artifact = _relpath(block_path)
                artifacts.append(lemma.artifact)
            for ref in self._result.refutations:
                if not (ref.compiled and ref.code):
                    continue
                ref_code = ref.code
                if ref.theorem and "#print axioms" not in ref_code:
                    ref_code = (ref_code.rstrip()
                                + f"\n\n#print axioms {ref.theorem}\n")
                ref_path = (run_dir
                            / f"{self._result.fixture}_{ts}_refute_{ref.block}.lean")
                ref_path.write_text(ref_code)
                ref.artifact = _relpath(ref_path)
                artifacts.append(ref.artifact)
            record_path = run_dir / f"{self._result.fixture}_{ts}.json"
            record_path.write_text(
                json.dumps(self._result.to_dict(), indent=2, ensure_ascii=False) + "\n"
            )
            artifacts.append(_relpath(record_path))

        # Fixed-format summary block (grep `Verdict` for the one-line result).
        lib = sum(1 for l in r.lemmas if l.kind == "library")
        inst = sum(1 for l in r.lemmas if l.kind == "instantiation")
        novel = sum(1 for l in r.lemmas if l.kind == "novel")
        violations = sum(1 for l in r.lemmas if l.kind == "violation")
        circulars = sum(1 for l in r.lemmas if l.kind == "circular")
        fal = [f.get("verdict") for f in r.falsifications]
        # Honest gap accounting: refuted / violation / circular / skipped
        # blocks are resolved outcomes, not gaps. Only genuinely-unformalized blocks
        # (incl. salvage-pending instantiations) count.
        states = {l.name: self._block_state(l, falsify_by_block.get(l.name, ""))
                  for l in r.lemmas}
        gaps = [n for n, (_, s) in states.items() if s == "GAP"]
        skipped = [n for n, (_, s) in states.items() if s.startswith("skipped")]

        print(f"=================== RLVerify: {r.fixture} ===================")
        print(f"Verdict     : {self._verdict_string()}")
        counts = (f"{lib} library, {inst} instantiation, {novel} novel"
                  + (f", {violations} violation" if violations else "")
                  + (f", {circulars} circular" if circulars else ""))
        print(f"Blocks      : {len(r.lemmas)} total — {counts}; "
              f"{len(gaps)} gap(s)"
              + (f", {len(skipped)} skipped (downstream)" if skipped else ""))
        for l in r.lemmas:
            glyph, state = states[l.name]
            note = (l.library_match or l.named_result
                    or falsify_by_block.get(l.name, ""))
            if l.kind in ("violation", "circular"):
                note = f"{l.library_match or l.circular_with} — {l.note}"
            print(f"  {glyph} {l.name:<{self._LOG_BLOCK_W}} {l.kind:<14} "
                  f"{state:<10} {note}")
        if gaps:
            self._log("finish", f"⚠ {len(gaps)} unformalized block(s): "
                                f"{', '.join(gaps)} — if independent and "
                                "correct, the salvage rule requires formalizing"
                                " them (skip() is only for dependents of a "
                                "failed block)")
        if r.falsifications:
            print(f"Falsify     : {fal.count('REFUTED')} refuted / "
                  f"{fal.count('PASSED')} passed / {fal.count('VACUOUS')} vacuous / "
                  f"{fal.count('SKIPPED')} skipped")
        # An early-exit verdict (theorem refutation, proof failure,
        # definedness gap, circularity, ...) means work stopped before
        # assembly — sketch/kernel are n/a, not negligently skipped.
        early_exit = bool(r.verdict) and not r.compiled
        if r.main_unformalizable and not r.compiled:
            print(f"Sketch      : n/a — main statement not formalizable "
                  f"({r.main_unformalizable})")
        elif early_exit and not r.sketch_code:
            print(f"Sketch      : n/a — early-exit verdict ({r.verdict}); "
                  "nothing to sketch")
        else:
            print(f"Sketch      : {'✓ decomposition machine-checked' if r.sketch_code else '— not run'}")
        if r.refutations:
            kb = sum(1 for ref in r.refutations if ref.kernel_backed)
            print(f"Refute      : {kb} kernel-backed / {len(r.refutations)} attempted")
        bt_summary = (f"{len(r.backtranslations)} recorded "
                      f"({', '.join(sorted(bt_targets))})"
                      if r.backtranslations else "(none)")
        print(f"Backtransl. : {bt_summary}")
        if r.audit_warnings:
            print(f"Warnings    : {len(r.audit_warnings)} audit-coverage "
                  "warning(s) — see ⚠ lines above (persisted in the record)")
        if r.main_unformalizable and not r.compiled:
            print(f"Kernel      : n/a — main statement not formalizable "
                  f"({r.main_unformalizable})")
        elif early_exit and not r.kernel_axioms:
            print(f"Kernel      : n/a — early-exit verdict ({r.verdict}); "
                  "nothing assembled (refutation closures, if any, are "
                  "kernel-checked separately — see Refute line)")
        else:
            print(f"Kernel      : {', '.join(r.kernel_axioms) if r.kernel_axioms else '— closure not obtained'}")
        print(f"Novel added : {', '.join(r.novel_added) if r.novel_added else '(none)'}")
        print(f"Artifacts   : {', '.join(artifacts) if artifacts else '(not saved)'}")
        print("=" * (50 + len(r.fixture)))

        result = self._result
        self._last_finished = artifacts[-1] if artifacts else r.fixture
        self._last_result = result  # status()/_verdict_string() fall back here
        self._result = None
        # The session is finalized in runs/ — drop the in-progress journal.
        self._journal_path(r.fixture).unlink(missing_ok=True)
        return result

    # ----- Corpus Growth -----

    def _corpus_has(self, entry_id: str = "", name: str = "") -> str:
        """Return the id of an existing premise that collides, or ''.

        Collision = exact id match, or any premise whose final component
        equals ``name`` (same lemma added under a different path).
        """
        for p in self.retriever.premises:
            if entry_id and p.id == entry_id:
                return p.id
            if name and p.id.split(".")[-1] == name:
                return p.id
        return ""

    def _add_to_corpus(
        self,
        lemma: LemmaResult,
        source_file: str | None = None,
        docstring: str = "",
        reuse_reason: str = "",
        generalized_from: str = "",
    ) -> bool:
        """Add a novel formalized lemma to the corpus and source tree.

        Returns False (without writing) on a duplicate id/name.
        """
        if source_file is None:
            # No separate "novel" category: every lemma needs a topic
            # directory (enforced upstream by add_novel's target_dir check).
            self._log("library", "✗ not added — no source_file (topic "
                      "directory) given")
            return False
        entry_id = source_file.replace(".lean", "").replace("/", ".") + f".{lemma.name}"

        existing = self._corpus_has(entry_id=entry_id, name=lemma.name)
        if existing:
            self._log("library", f"✗ not added — corpus already has: {existing}")
            return False

        entry = {
            "id": entry_id,
            "kind": "theorem",
            "statement": lemma.statement,
            "status": "formalized",
            "tags": ["library-expansion"],
            "source_file": source_file,
            "source_line": 1,
            "docstring": docstring,
            "reusable": True,
            "reuse_reason": reuse_reason,
            "generalized_from": generalized_from,
        }

        if self.corpus_path == DEFAULT_CORPUS:
            out_path = ROOT / source_file
            out_path.parent.mkdir(parents=True, exist_ok=True)
            out_path.write_text(lemma.code + "\n")
            if not self._register_in_build(source_file):
                out_path.unlink(missing_ok=True)
                return False

        with open(self.corpus_path, "a") as f:
            f.write(json.dumps(entry) + "\n")
        self.retriever.add_premise(entry)
        return True

    def _register_in_build(self, source_file: str) -> bool:
        """Register a new module in RLGeneralization.lean and build it.

        Refuses files that import the root module (circular import), and
        rolls back the registration if `lake build` of the module fails
        (e.g. name collision with an existing library declaration).
        """
        root_lean = ROOT / "RLGeneralization.lean"
        if not root_lean.exists():
            return True
        import_module = source_file.replace(".lean", "").replace("/", ".")
        import_line = f"import {import_module}"

        module_code = (ROOT / source_file).read_text()
        if re.search(r"^import\s+RLGeneralization\s*$", module_code, re.MULTILINE):
            print(
                f"[driver] ✗ {source_file} imports the root module "
                "`RLGeneralization` — registering it would create an import "
                "cycle. Use specific imports (RLGeneralization.X.Y or Mathlib)."
            )
            return False

        content = root_lean.read_text()
        already_registered = import_line in content
        if not already_registered:
            new_content = content if content.endswith("\n") else content + "\n"
            new_content += import_line + "\n"
            root_lean.write_text(new_content)

        try:
            build = subprocess.run(
                ["lake", "build", import_module],
                capture_output=True, text=True, timeout=600, cwd=str(ROOT),
            )
        except subprocess.TimeoutExpired:
            build = None

        if build is None or build.returncode != 0:
            if not already_registered:
                root_lean.write_text(content)
            err = "timeout" if build is None else (build.stdout + build.stderr)[-1500:]
            self._log("library", f"✗ `lake build {import_module}` failed — registration rolled back:")
            for line in err.splitlines()[-8:]:
                print(f"  {line[:120]}")
            return False

        self._log("library", f"✓ registered and built {import_module}")
        self._module_built_cache.pop(import_module, None)
        return True

    def add_novel(
        self,
        name: str,
        statement: str = "",
        proof: str = "",
        imports: list[str] | None = None,
        code: str | None = None,
        target_dir: str | None = None,
        docstring: str = "",
        block: str = "",
        reusable: bool = False,
        reuse_reason: str = "",
        generalized_from: str = "",
    ) -> bool:
        """Compile and add a novel lemma to the corpus and source tree.

        Two modes:
        - **code mode** (preferred): pass ``code`` with the full compilable
          Lean file content. The corpus statement is extracted from the
          code automatically (or pass ``statement`` to override).
        - **legacy mode**: pass ``statement`` (theorem signature without
          ``:= by``) and ``proof`` (tactic body without leading ``by``).
          The code is assembled automatically.

        ``target_dir`` is REQUIRED: the topic directory the lemma belongs to
        (e.g. ``Concentration``, ``Optimization``, ``MDP``). There is no
        separate "novel" category — every lemma lives in the topic directory
        where a human would look for it.

        ``docstring`` should be a one-line natural-language description —
        it is indexed for search, so additions without one are hard to
        find with natural-language queries.

        ``block`` (optional) names the session block this lemma was
        generalized from when the lemma name differs from the block name
        (the usual case). It links the kernel-verified corpus lemma back to
        that block so the block is not reported as a GAP.

        Shared-library promotion is deliberately stricter than saving a run
        artifact. Callers must explicitly attest ``reusable=True`` and give a
        non-empty ``reuse_reason`` explaining plausible cross-proof use.
        Paper-specific glue remains in the run record but is not promoted.

        Rejects code containing `axiom` declarations (the library holds only
        proven results) and duplicate names/ids.
        """
        if not target_dir or target_dir in ("Novel", "RLVerify"):
            self._log("library",
                      "✗ not added — target_dir is required and must be a "
                      "topic directory (Concentration, Optimization, MDP, "
                      "...); there is no separate 'novel' category")
            return False
        if not reusable:
            self._record_library_evaluation(
                name, "SKIPPED-NOT-REUSABLE",
                reuse_reason or "no reusable-library assessment supplied",
                generalized_from or block,
            )
            self._log(
                "library",
                "· not added — run artifact retained, but shared-library "
                "promotion requires reusable=True",
            )
            return False
        if not reuse_reason.strip():
            self._record_library_evaluation(
                name, "REJECTED-MISSING-ASSESSMENT",
                "reusable=True requires a concrete cross-proof reuse reason",
                generalized_from or block,
            )
            self._log(
                "library",
                "✗ not added — reusable=True requires reuse_reason= explaining "
                "why another proof could plausibly use this generalized lemma",
            )
            return False
        if code is None:
            import_block = "\n".join(
                f"import {m}" for m in (imports or ["RLGeneralization"])
            )
            proof_body = proof.lstrip()
            if proof_body.startswith("by"):
                proof_body = proof_body[2:].lstrip("\n")
            indented = "\n".join(
                ("  " + line) if line.strip() else line
                for line in proof_body.split("\n")
            )
            code = f"{import_block}\n\n{statement} := by\n{indented}"

        axioms = find_axioms(code)
        if axioms:
            self._log("library", f"✗ not added — code declares axiom(s): {axioms}; "
                      "the library accepts only proven theorems")
            return False

        if not statement:
            statement = extract_signature(code, name)
            if not statement:
                self._log("library", f"✗ could not extract the signature of '{name}' "
                          "from the code — pass statement= explicitly")
                return False

        if not docstring:
            doc_m = re.search(r"/--\s*(.*?)\s*-/", code, re.DOTALL)
            if doc_m:
                docstring = " ".join(doc_m.group(1).split())[:500]
            else:
                self._record_library_evaluation(
                    name, "REJECTED-NOT-FINDABLE",
                    "reusable lemmas require a natural-language docstring",
                    generalized_from or block,
                )
                self._log(
                    "library",
                    "✗ not added — reusable lemmas require a docstring "
                    "(docstring= or /-- ... -/) for future retrieval",
                )
                return False

        result = self.compile(code)
        if not result.success:
            return False

        # Kernel-closure gate: an in-file sorry/axiom is caught above, but a
        # lemma IMPORTING a sorried module compiles cleanly with no token in
        # this file — only the kernel sees it. Refuse tainted closures so the
        # corpus never holds a lemma that is not actually proven.
        qualified = _qualified_decl_name(code, name)
        closure = check_axiom_closure(code, qualified)
        if not closure.ok:
            self._log("library",
                      f"✗ not added — kernel closure check failed for "
                      f"'{qualified}': {closure.error[:160]}")
            return False
        if closure.has_sorry_ax or closure.custom:
            taint = ("sorryAx" if closure.has_sorry_ax
                     else f"custom axiom(s) {closure.custom}")
            self._log("library",
                      f"✗ not added — kernel closure of '{qualified}' is "
                      f"tainted ({taint}); a sorry/axiom hides in this file "
                      "or its imports")
            return False

        if target_dir:
            camel = "".join(w.capitalize() for w in name.split("_"))
            source_file = f"RLGeneralization/{target_dir}/{camel}.lean"
        else:
            source_file = None

        lemma = LemmaResult(
            name=name, kind="novel", statement=statement,
            proof=proof, code=code, compiled=True,
        )
        if not self._add_to_corpus(
            lemma,
            source_file=source_file,
            docstring=docstring,
            reuse_reason=reuse_reason.strip(),
            generalized_from=(generalized_from or block).strip(),
        ):
            return False
        self._record_library_evaluation(
            name, "ADDED-REUSABLE", reuse_reason.strip(),
            generalized_from or block,
        )
        if self._result is not None:
            self._result.novel_added.append(name)
            # Link to the session block of the same name: the corpus gate
            # just kernel-verified this code, so the block is discharged
            # even if formalize() was never called for it.
            session_lemma = self._find_lemma(name)
            if session_lemma is not None and not session_lemma.compiled:
                session_lemma.compiled = True
                session_lemma.statement = statement
                session_lemma.proof = proof
                session_lemma.code = code
                session_lemma.compile_error = ""
                self._log("library", "✓ session block marked compiled "
                          "(kernel-clean closure via add_novel)", block=name)
            # A block is normally GENERALIZED before being added (the block
            # `recursion_solve` becomes the lemma `le_div_one_sub_of_le_add_mul`).
            # Without an explicit link, that block stays GAP forever even though
            # its content is now kernel-verified in the corpus. `block=` names it.
            if block and block != name:
                origin = self._find_lemma(block)
                if origin is not None and not origin.compiled:
                    origin.compiled = True
                    origin.code = code
                    origin.note = f"generalized to corpus lemma: {name}"
                    origin.compile_error = ""
                    self._log("library", f"✓ origin block '{block}' marked "
                              f"compiled (generalized to {name})", block=block)
                elif origin is None:
                    self._log("library", f"⚠ block='{block}' not found among "
                              "session blocks — nothing to link")
            self._persist()
        elif self._last_finished:
            self._log("library",
                      f"⚠ '{name}' added AFTER finish() — not reflected in "
                      f"{self._last_finished}; call add_novel before finish()")
        self._log("library", f"✓ added novel lemma: {name}")
        return True

    def _record_library_evaluation(
        self,
        name: str,
        outcome: str,
        reason: str,
        generalized_from: str = "",
    ) -> None:
        if self._result is None:
            return
        self._result.library_evaluations.append({
            "name": name,
            "outcome": outcome,
            "reason": reason.strip(),
            "generalized_from": generalized_from.strip(),
        })
        self._persist()

    # ----- Helpers -----

    def _find_lemma(self, name: str) -> LemmaResult | None:
        if not self._result:
            return None
        for l in self._result.lemmas:
            if l.name == name:
                return l
        return None

    def _validate_external(self, ident: str) -> bool | None:
        """``#check`` an external (non-corpus) identifier at resolve time.

        Uses the warm REPL when its binary exists (sub-second after the
        one-time warmup; the warm env opens Mathlib + RLGeneralization),
        falling back to a fresh ``import Mathlib`` compile (~10s). Returns
        True/False on a definitive answer, None when no checker ran —
        callers keep the old "unvalidated" warning in that case.

        Skipped (None) for non-default corpora: unit tests use tiny fake
        corpora and must not pay real Lean compiles (same carve-out as
        ``module_built``).
        """
        if self.corpus_path != DEFAULT_CORPUS:
            return None
        try:
            from .repl import REPL_BIN
            if REPL_BIN.exists():
                r = self.repl_verify(f"#check @{ident}", quiet=True)
                return bool(r.success)
        except Exception:
            pass
        try:
            r = self.compile(f"import Mathlib\n\n#check @{ident}", quiet=True)
            return bool(r.success)
        except Exception:
            return None

    def _record_match(self, qualified_name: str) -> bool:
        """Record a successful library resolution for reuse stats.

        Returns True iff the id resolved to a corpus premise — False means
        the citation is external (or wrong) and was NOT tracked.
        """
        for p in self.retriever.premises:
            if p.id == qualified_name or p.id.endswith(f".{qualified_name}"):
                self.retriever.record_match(p.id)
                return True
        return False


def _relpath(path: Path) -> str:
    """Repo-relative path when under ROOT, absolute otherwise (test dirs)."""
    try:
        return str(path.relative_to(ROOT))
    except ValueError:
        return str(path)


def _dataclass_from_dict(cls, data: dict):
    """Construct ``cls`` from a dict, ignoring unknown keys (forward compat)."""
    names = {f.name for f in fields(cls)}
    return cls(**{k: v for k, v in data.items() if k in names})


def _verify_result_from_dict(data: dict) -> VerifyResult:
    """Rebuild a journaled VerifyResult (see ``VerifyDriver.resume``)."""
    base = {
        k: v for k, v in data.items()
        if k not in ("lemmas", "refutations", "step_certificates")
    }
    # Records created before workflow contract v2 had no dependency/sketch/
    # discharge provenance. Keep them readable without retroactively inventing
    # phase failures; a new harness run stamps v2 before enforcement.
    base.setdefault("workflow_contract_version", 1)
    result = _dataclass_from_dict(VerifyResult, base)
    result.lemmas = [_dataclass_from_dict(LemmaResult, l)
                     for l in data.get("lemmas", [])]
    result.refutations = [_dataclass_from_dict(Refutation, r)
                          for r in data.get("refutations", [])]
    result.step_certificates = [
        _dataclass_from_dict(StepCertificate, certificate)
        for certificate in data.get("step_certificates", [])
    ]
    return result


def _qualified_decl_name(code: str, name: str) -> str:
    """Fully qualified name of a declaration, tracking `namespace` blocks.

    `#print axioms` needs the qualified name; a lemma declared inside
    `namespace Foo` is `Foo.<name>`.
    """
    stack: list[str] = []
    decl_re = re.compile(
        rf"^\s*(?:private\s+|protected\s+|noncomputable\s+)*"
        rf"(?:theorem|lemma|def)\s+{re.escape(name)}\b"
    )
    for line in code.splitlines():
        if decl_re.match(line):
            return ".".join(stack + [name])
        m = re.match(r"^namespace\s+([A-Za-z_][A-Za-z0-9_'.]*)", line)
        if m:
            stack.append(m.group(1))
            continue
        m = re.match(r"^end\s+([A-Za-z_][A-Za-z0-9_'.]*)", line)
        if m and stack and stack[-1] == m.group(1):
            stack.pop()
    return name


def extract_signature(code: str, name: str) -> str:
    """Extract a theorem/lemma signature (up to the top-level `:=`) from code.

    Returns '' if the declaration is not found.
    """
    lines = code.splitlines()
    decl_re = re.compile(
        rf"^\s*(?:private\s+|protected\s+|noncomputable\s+)*(?:theorem|lemma)\s+{re.escape(name)}\b"
    )
    start = next((i for i, ln in enumerate(lines) if decl_re.match(ln)), None)
    if start is None:
        return ""

    sig_lines: list[str] = []
    depth = 0
    for li in range(start, min(start + 100, len(lines))):
        line = lines[li]
        col = 0
        while col < len(line):
            if line.startswith("--", col):
                line = line[:col]
                break
            ch = line[col]
            if ch in "({[⟨":
                depth += 1
            elif ch in ")}]⟩":
                depth = max(depth - 1, 0)
            elif (
                ch == ":" and depth == 0
                and col + 1 < len(line) and line[col + 1] == "="
            ):
                sig_lines.append(line[:col].rstrip())
                return "\n".join(sig_lines).strip()
            col += 1
        sig_lines.append(line)
    return ""
