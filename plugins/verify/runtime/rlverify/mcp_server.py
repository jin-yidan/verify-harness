"""W2 — MCP server exposing RLVerify to a bring-your-own agent.

Design points (from the plan + reviews):
- **Coarse, pipeline-ordered tools** (not a 1:1 mirror of ~25 driver methods):
  begin → search → library_search → resolve_block(with dependencies) →
  falsify_block → compile → sketch → dependency-ordered discharge → assemble
  → finalize. The order is the procedure; the workflow contract records and
  enforces its structural gates.
- **Sandbox by default**: ``enable_sandbox()`` routes every driver compile
  through the W0 sandbox, fail-closed. The SERVER owns ``corpus_path`` (always a
  snapshot, never the live corpus) so an untrusted agent cannot mutate the real
  library or point the driver at the default tree (W0/W2 review).
- **Strict gates**: the driver runs with ``strict_gates=True`` and ``finalize``
  re-runs ``enforce`` so a VERIFIED with missing gate coverage is downgraded.
  Triage, hypothesis audit, and back-translation are injected by trusted runner
  code; falsification remains agent-attested unless the trusted-local sampler
  path is explicitly enabled.

``HarnessSession`` is protocol-agnostic and unit-tested directly; the FastMCP
wrapper at the bottom is a thin transport.
"""
from __future__ import annotations

import os
import json
import hashlib
import re
import atexit
import shutil
import subprocess
import tempfile
import time
from pathlib import Path

from harness.telemetry import append_phase
from .driver import VerifyDriver
from .lean import ROOT
from .sandbox import enable_sandbox
from .vacuity import is_id_shaped, split_top_level
from .verdict import (
    WORKFLOW_CONTRACT_VERSION,
    enforce,
    evidence_tier,
    falsify_summary,
    workflow_phase_failures,
)

DEFAULT_CORPUS = ROOT / "rlverify" / "corpus.jsonl"
_SOURCE_ROOTS = tuple(
    path.resolve()
    for path in (
        ROOT / "RLGeneralization",
        ROOT / ".lake" / "packages" / "mathlib" / "Mathlib",
        ROOT / ".lake" / "packages" / "batteries" / "Batteries",
    )
    if path.is_dir()
)
_SOURCE_FILES = {(ROOT / "RLGeneralization.lean").resolve()}


class HarnessSession:
    """One verification session for an untrusted agent, fully confined."""

    def __init__(self, corpus_path: str | None = None, sandbox: bool | None = None):
        # Sandbox = "do I trust the Lean being compiled?". Default ON (untrusted
        # BYO agent). A LOCAL user running a TRUSTED agent on their OWN proof can
        # opt out (RLVERIFY_SANDBOX=0) for speed / non-macOS — same trust posture
        # as the /verify-full-process skill, which has no sandbox. Fail-closed when on.
        if sandbox is None:
            sandbox = os.environ.get("RLVERIFY_SANDBOX", "1") != "0"
        self.sandboxed = sandbox
        if sandbox:
            enable_sandbox()
        # The server owns the corpus path. Default to a private snapshot so the
        # agent can never write the real library (driver only writes the source
        # tree when corpus_path == the default) nor see other runs.
        if corpus_path is None:
            corpus_path = os.environ.get("RLVERIFY_CORPUS")
        # NEVER let the agent-facing driver hold the live corpus: that path
        # re-enables the source-tree write + `lake build` in add_novel
        # (driver only writes when corpus_path == DEFAULT_CORPUS). If unset or
        # pointed at the default, force a private snapshot.
        if corpus_path is None or Path(corpus_path).resolve() == DEFAULT_CORPUS.resolve():
            snap = tempfile.mktemp(prefix="rlverify_corpus_", suffix=".jsonl")
            shutil.copy(DEFAULT_CORPUS, snap)
            corpus_path = snap
        self.d = VerifyDriver(corpus_path=corpus_path, strict_gates=True)
        self.original_proof = ""
        self.prior_verified: dict[str, dict] = {}
        try:
            run_root = Path(corpus_path).parent
            saved_input = json.loads((run_root / "input.json").read_text())
            self.original_proof = str(saved_input.get("proof") or "")
            upstream = json.loads(
                (run_root / "upstream_verified.json").read_text()
            )
            for entry in upstream.get("verified") or []:
                if not isinstance(entry, dict):
                    continue
                name = str(entry.get("name") or "").strip()
                code = str(entry.get("code") or "").strip()
                if name and code and not entry.get("context_only"):
                    self.prior_verified[name] = dict(entry)
        except (OSError, ValueError, AttributeError):
            pass
        self._begun = False

    def _phase_order_error(self, tool: str) -> str | None:
        """Fail closed when an agent skips the command's begin-first rule."""
        if self._begun and self.d._result is not None:
            return None
        return f"✗ PHASE ORDER — call begin before {tool}"

    @staticmethod
    def _dependency_errors(rec) -> list[str]:
        """Return deterministic dependency-graph errors for the live record."""
        lemmas = list(rec.lemmas)
        names = {lemma.name for lemma in lemmas}
        errors: list[str] = []
        undeclared = [
            lemma.name for lemma in lemmas if not lemma.dependencies_declared
        ]
        if undeclared:
            errors.append(f"dependencies not declared for {undeclared}")
        unknown = [
            f"{lemma.name}->{dep}"
            for lemma in lemmas
            for dep in lemma.depends_on
            if dep not in names
        ]
        if unknown:
            errors.append(f"unknown dependency edge(s) {unknown}")
        graph = {
            lemma.name: list(lemma.depends_on)
            for lemma in lemmas
        }
        visiting: set[str] = set()
        visited: set[str] = set()

        def visit(name: str, path: list[str]) -> list[str] | None:
            if name in visiting:
                start = path.index(name) if name in path else 0
                return path[start:] + [name]
            if name in visited:
                return None
            visiting.add(name)
            for dep in graph.get(name, []):
                if dep not in graph:
                    continue
                cycle = visit(dep, path + [name])
                if cycle:
                    return cycle
            visiting.remove(name)
            visited.add(name)
            return None

        for name in graph:
            cycle = visit(name, [])
            if cycle:
                errors.append(
                    "dependency cycle " + " -> ".join(cycle)
                )
                break
        return errors

    def _emit_phase(
        self,
        phase: str,
        *,
        started: float,
        status: str,
        blocks: list[str] | None = None,
        detail: str = "",
        evidence: str = "AGENT_EXECUTION",
        artifacts: dict[str, str] | None = None,
    ) -> None:
        """Persist agent-side progress without upgrading trusted evidence."""
        try:
            append_phase(
                self.d.corpus_path.parent,
                phase,
                status=status,
                wall_s=time.monotonic() - started,
                detail=detail,
                evidence=evidence,
                blocks=blocks,
                artifacts=artifacts,
                producer="agent_mcp",
            )
        except OSError:
            pass

    # --- pipeline-ordered coarse tools ------------------------------------

    def begin(self, fixture: str) -> str:
        if os.environ.get("RLVERIFY_RESUME") == "1":
            try:
                self.d.resume(fixture)
            except FileNotFoundError:
                # A prior attempt may have failed at the backend capability
                # gate before creating an agent journal. Saved theorem input is
                # resumable, but the proof session must begin fresh.
                self.d.begin(fixture)
                self.d._result.workflow_contract_version = (
                    WORKFLOW_CONTRACT_VERSION
                )
                self.d._persist()
                self._begun = True
                return (
                    f"session '{fixture}' started fresh (saved input resumed, "
                    "but no proof journal existed)"
                )
            self.d._result.workflow_contract_version = WORKFLOW_CONTRACT_VERSION
            self.d._persist()
            self._begun = True
            return (f"session '{fixture}' resumed (strict gates ON, sandboxed "
                    "compiles; continue from status())")
        self.d.begin(fixture)
        self.d._result.workflow_contract_version = WORKFLOW_CONTRACT_VERSION
        self.d._persist()
        self._begun = True
        return f"session '{fixture}' started (strict gates ON, sandboxed compiles)"

    def record_triage(self, suspects: list[dict], all_clear: bool) -> str:
        """TRUSTED injection (runner-only, not an MCP tool). Stamps the
        provenance the gate requires; an agent has no path to call this."""
        self.d.record_triage(suspects=suspects, all_clear=all_clear)
        self.d._result.triage["executed_by"] = "harness"
        return f"triage recorded (harness): {len(suspects)} suspect(s), all_clear={all_clear}"

    def record_hypothesis_audit(self, audit: dict) -> str:
        """TRUSTED injection (runner-only) of the sealed hypothesis audit.

        The audit remains prioritization-only, but persisting it in the run
        record makes the legacy phase reviewable instead of leaving it in an
        ephemeral sidecar.
        """
        if self.d._result is None:
            raise RuntimeError("No active session. Call begin() first.")
        rec = dict(audit or {})
        rec["executed_by"] = "harness"
        self.d._result.hypothesis_audit = rec
        self.d._persist()
        findings = rec.get("findings") or []
        return (f"hypothesis audit recorded (harness): "
                f"overall={rec.get('overall', 'UNCERTAIN')}, "
                f"{len(findings)} finding(s)")

    def record_backtranslation(self, target: str, verdict: str,
                               notes: str = "", purpose: str = "") -> str:
        """TRUSTED injection of a sealed back-translation outcome (runner-only).
        Stamps provenance so it satisfies the gate; agents have no path here."""
        if self.d._result is not None:
            self.d._result.backtranslations = [
                b for b in self.d._result.backtranslations
                if not (b.get("target") == target and b.get("executed_by") == "harness")
            ]
            self.d._persist()
        if verdict.upper() == "GATE_ERROR":
            # The sealed grader timed out / crashed (backtranslate.back_translate
            # returns GATE_ERROR). The FROZEN driver's writer rejects it (only
            # MATCH/NOTE/MISMATCH), yet verdict.gate_failures already KNOWS how to
            # read a GATE_ERROR record (fail-safe downgrade — "grader error, not a
            # proof defect"). So append it here, in the harness layer, bypassing
            # the driver's validation — NOT by widening the frozen
            # driver.BACKTRANSLATION_VERDICTS. Without this the runner crashes with
            # an uncaught ValueError AFTER the full agent spend.
            if self.d._result is None:
                raise RuntimeError("No active session. Call begin() first.")
            rec = {"target": target, "verdict": "GATE_ERROR", "notes": notes,
                   "categories": {}, "purpose": purpose,
                   "executed_by": "harness"}
            self.d._result.backtranslations.append(rec)
            self.d._persist()
            return f"back-translation recorded (harness): {target} = GATE_ERROR (grader failed)"
        rec = self.d.record_backtranslation(
            target=target, verdict=verdict, notes=notes, purpose=purpose)
        rec["executed_by"] = "harness"  # the returned dict IS the appended one
        self.d._persist()
        return f"back-translation recorded (harness): {target} = {verdict}"

    def search(self, query: str, limit: int = 8) -> str:
        """Library search: substring + BM25, merged."""
        if denied := self._phase_order_error("search"):
            return denied
        lines: list[str] = []
        try:
            for hit in (self.d.grep(query) or [])[:limit]:
                lines.append(f"grep  {hit}")
        except Exception:
            pass
        try:
            for hit in (self.d.hybrid_search(query) or [])[:limit]:
                lines.append(f"bm25  {hit}")
        except Exception:
            pass
        return "\n".join(lines) or "(no results)"

    def source_search(self, query: str, limit: int = 20) -> str:
        """Read-only exact-text search over trusted Lean source trees.

        This recovers the useful repository-inspection ability of a foreground
        skill without giving the untrusted proof agent shell access or access
        to journals, credentials, reports, or arbitrary workspace files.
        """
        if denied := self._phase_order_error("source_search"):
            return denied
        needle = query.strip()
        if not needle:
            return "✗ source_search query is empty"
        if len(needle) > 500:
            return "✗ source_search query exceeds 500 characters"
        cap = max(1, min(int(limit), 100))
        roots = [str(path) for path in _SOURCE_ROOTS]
        roots.extend(str(path) for path in _SOURCE_FILES if path.is_file())
        if not roots:
            return "(trusted Lean source trees are unavailable)"
        rg = shutil.which("rg")
        if not rg:
            return "✗ source_search requires ripgrep (rg)"
        try:
            result = subprocess.run(
                [
                    rg,
                    "-n",
                    "-F",
                    "--no-heading",
                    "--color",
                    "never",
                    "--glob",
                    "*.lean",
                    "--",
                    needle,
                    *roots,
                ],
                cwd=ROOT,
                capture_output=True,
                text=True,
                timeout=15,
                check=False,
            )
        except (OSError, subprocess.TimeoutExpired) as exc:
            return f"✗ source_search failed: {type(exc).__name__}: {exc}"
        rows: list[str] = []
        for line in result.stdout.splitlines():
            path_text, separator, rest = line.partition(":")
            if not separator:
                continue
            try:
                display = str(Path(path_text).resolve().relative_to(ROOT))
            except ValueError:
                display = path_text
            rows.append(f"{display}:{rest}")
            if len(rows) >= cap:
                break
        return "\n".join(rows) or "(no source matches)"

    @staticmethod
    def _trusted_source_path(value: str) -> Path | None:
        candidate = Path(value)
        if not candidate.is_absolute():
            candidate = ROOT / candidate
        try:
            resolved = candidate.resolve(strict=True)
        except (OSError, RuntimeError):
            return None
        if resolved.suffix != ".lean":
            return None
        if resolved in _SOURCE_FILES:
            return resolved
        if any(resolved.is_relative_to(root) for root in _SOURCE_ROOTS):
            return resolved
        return None

    def source_read(self, path: str, start_line: int = 1,
                    end_line: int = 240) -> str:
        """Read a bounded line range from a trusted Lean source file only."""
        if denied := self._phase_order_error("source_read"):
            return denied
        resolved = self._trusted_source_path(path)
        if resolved is None:
            return (
                "✗ source_read accepts only existing .lean files under "
                "RLGeneralization, Mathlib, or Batteries"
            )
        start = max(1, int(start_line))
        end = min(max(start, int(end_line)), start + 399)
        try:
            lines = resolved.read_text(errors="replace").splitlines()
        except OSError as exc:
            return f"✗ source_read failed: {exc}"
        selected = lines[start - 1:end]
        display = resolved.relative_to(ROOT)
        body = "\n".join(
            f"{number:>6}  {line}"
            for number, line in enumerate(selected, start=start)
        )
        return f"{display}:{start}-{min(end, len(lines))}\n{body}"

    def library_search(
        self,
        block: str,
        statement: str,
        imports: list[str] | None = None,
    ) -> str:
        """Run the type-directed ``exact?`` reuse gate and persist its result."""
        if self.d._result is None:
            return "✗ PHASE ORDER — call begin first"
        result = self.d.library_search(
            statement,
            imports=imports or None,
            opens="",
        )
        record = {
            "block": block,
            "statement": statement,
            "found": bool(result.found),
            "suggestion": result.suggestion,
            "head_symbol": result.head_symbol,
            "package": result.package,
            "elapsed": result.elapsed,
            "error": result.error,
            "inconclusive": bool(result.inconclusive),
            "executed_by": "harness",
        }
        prior = [
            row for row in self.d._result.library_searches
            if row.get("block") != block
        ]
        self.d._result.library_searches = prior + [record]
        self.d._persist()
        if result.found:
            return (
                f"FOUND repository/library proof for {block}: "
                f"{result.suggestion or result.head_symbol}; "
                f"package={result.package or 'unknown'}. "
                "Classify as library or instantiation, not novel."
            )
        if result.inconclusive:
            return (
                f"INCONCLUSIVE type-directed search for {block}: "
                f"{result.error}. Novelty is not cleared."
            )
        if result.error:
            return (
                f"INVALID formal search statement for {block}: {result.error}"
            )
        return (
            f"NO exact type-directed match for {block}; novel remains plausible "
            "(textual/shape-variant search is still required)."
        )

    def status(self) -> str:
        """Return resumable workflow-v2 state without emitting a verdict."""
        rec = self.d._result or self.d._last_result
        if rec is None:
            return "no active session — call begin() first"
        data = rec.to_dict()
        falsify = {
            f.get("block"): f.get("verdict", "?")
            for f in data.get("falsifications", [])
        }
        evaluated = {
            str(row.get("generalized_from") or row.get("name") or "")
            for row in data.get("library_evaluations", [])
            if isinstance(row, dict)
        }
        lines = [
            f"session: {data.get('fixture', '?')}",
            f"workflow contract: v{data.get('workflow_contract_version', 1)}",
        ]
        for lemma in data.get("lemmas", []):
            deps = lemma.get("depends_on") or []
            dep_label = ",".join(deps) if lemma.get("dependencies_declared") else "MISSING"
            lines.append(
                f"- {lemma.get('name', '?')}: kind={lemma.get('kind', '?')}; "
                f"depends_on={dep_label or '[]'}; "
                f"falsify={falsify.get(lemma.get('name'), '—')}; "
                f"discharged={'yes' if lemma.get('discharged') else 'no'}; "
                f"anti_vacuity={'yes' if lemma.get('anti_vacuity_checks') else 'no'}; "
                f"library_evaluated={'yes' if lemma.get('name') in evaluated else 'no'}"
                + (f"; vacuity={lemma.get('vacuity_risk')}"
                   if lemma.get("vacuity_risk") else ""))
        lines.append(
            f"sketch: {'verified' if data.get('sketch_verified') else 'missing/failed'}"
            f"; expected={data.get('sketch_expected_blocks') or []}")
        lines.append(f"discharge order: {data.get('discharge_order') or []}")
        gaps = workflow_phase_failures(data)
        lines.append("workflow gaps: " + ("; ".join(gaps) if gaps else "none"))
        return "\n".join(lines)

    # Detection path: the agent must be able to report a candidate theorem or
    # proof flaw, not only build toward VERIFIED.  Agent labels remain
    # non-decisive until the trusted parent scopes and matches the evidence.
    _FAILURE_VERDICTS = {
        "WRONG": "UNVERIFIED/WRONG",
        "INCOMPLETE": "UNVERIFIED/INCOMPLETE",
        "MISMATCH": "UNVERIFIED/MISMATCH",
        "HYPOTHESIS_VIOLATION": "UNVERIFIED/HYPOTHESIS_VIOLATION",
        "PROOF_INVALID": "UNVERIFIED/PROOF_INVALID",
        "CIRCULAR": "UNVERIFIED/CIRCULAR",
    }

    def refute(self, block: str, code: str, description: str) -> str:
        """Compile a Lean COUNTEREXAMPLE to a block's inference — the kernel-
        backed analog of assemble for the failure side. ``code`` should declare
        a theorem asserting *premises-hold ∧ ¬conclusion* on a concrete instance;
        ``description`` is the refuted claim verbatim. ``kernel_backed`` is
        DERIVED fail-closed (compiles AND clean axiom closure), never asserted.

        For a disputed proof inference, follow with
        ``report_failure("PROOF_INVALID", reason, block=<same block>)``.
        ``WRONG`` is reserved for a witness against the complete submitted
        theorem. In either case, kernel closure authenticates only this Lean
        proposition; the trusted parent must still match its scope and
        premises before it can determine a verdict. A failed compile is still
        recorded and remains audit-only."""
        if denied := self._phase_order_error("refute"):
            return denied
        ref = self.d.refute(block, code, description)
        if ref.kernel_backed:
            return (f"✓ KERNEL-BACKED refutation of {block} — counterexample "
                    "compiled, closure clean. Report PROOF_INVALID for a "
                    "submitted inference and WRONG only for the complete "
                    "theorem; trusted scope matching decides the verdict.")
        return (f"✗ refutation NOT kernel-backed ({ref.error or 'closure not clean'}) "
                f"— fix the counterexample or fall back to an audit-only "
                f"report_failure.")

    def certify_step(self, block: str, code: str, description: str) -> str:
        """Compile a positive certificate for the exact disputed inference.

        The trusted parent still performs a fresh closure check and sealed
        statement match before this can clear a triage suspicion.
        """
        if denied := self._phase_order_error("certify_step"):
            return denied
        cert = self.d.certify_step(block, code, description)
        if cert.kernel_backed:
            return (
                f"✓ KERNEL-BACKED positive candidate for {block} — "
                "stop and let the trusted parent check the exact statement "
                "match."
            )
        return (
            f"✗ positive candidate NOT kernel-backed "
            f"({cert.error or 'closure not clean'}) — fix it or leave the "
            "finding unresolved."
        )

    def report_failure(self, kind: str, reason: str, block: str = "") -> str:
        """Record a DETECTED flaw as an early-exit verdict (the detection axis).

        kind ∈ {WRONG, INCOMPLETE, MISMATCH, HYPOTHESIS_VIOLATION,
        PROOF_INVALID, CIRCULAR}.
        Use when the proof is invalid/unjustifiable — e.g. a step interchanges
        limit and expectation without domination (HYPOTHESIS_VIOLATION /
        INCOMPLETE), or a cited lemma is misapplied. `reason` is mandatory and
        is carried into the verdict. The verdict still cannot be VERIFIED — only
        the kernel grants that — but it CAN be a precise failure."""
        if denied := self._phase_order_error("report_failure"):
            return denied
        v = self._FAILURE_VERDICTS.get(kind.upper())
        if v is None:
            return f"unknown failure kind {kind!r}; use one of {list(self._FAILURE_VERDICTS)}"
        self.d.set_verdict(v, reason=reason, block=block)
        return f"recorded {v}: {reason}"

    def main_unformalizable(self, reason: str) -> str:
        """Record a terminal INCOMPLETE result for missing formal infrastructure.

        This is distinct from an agent silently returning without work. It
        explains why no main Lean statement, sketch, or kernel closure can be
        produced and gives the runner a durable mathematical non-pass.
        """
        if denied := self._phase_order_error("main_unformalizable"):
            return denied
        self.d.main_unformalizable(reason)
        self.d.set_verdict(
            "UNVERIFIED/INCOMPLETE",
            reason=reason,
            block="main",
        )
        return (
            "recorded UNVERIFIED/INCOMPLETE: main statement is not "
            f"formalizable with the available infrastructure — {reason}"
        )

    def resolve_block(self, name: str, statement_nl: str, kind: str = "novel",
                      library: str | None = None,
                      instantiation: str | None = None,
                      prior: str | None = None,
                      depends_on: list[str] | None = None,
                      source_excerpt: str = "",
                      source_char_start: int = -1,
                      source_char_end: int = -1,
                      formal_signature: str = "",
                      hypotheses: list[str] | None = None) -> str:
        if denied := self._phase_order_error("resolve_block"):
            return denied
        started = time.monotonic()
        if kind == "novel":
            if not formal_signature.strip():
                return (
                    "✗ CLASSIFICATION — a novel block requires an elaborated "
                    "formal_signature and a recorded library_search"
                )
            search = next(
                (
                    row for row in reversed(
                        self.d._result.library_searches
                        if self.d._result is not None else []
                    )
                    if row.get("block") == name
                    and row.get("statement") == formal_signature
                ),
                None,
            )
            if search is None:
                return (
                    "✗ CLASSIFICATION — run library_search on this exact "
                    "formal_signature before classifying the block as novel"
                )
            if search is not None and search.get("found"):
                return (
                    "✗ CLASSIFICATION — library_search found "
                    f"{search.get('suggestion') or search.get('head_symbol')}; "
                    "classify this block as library or instantiation"
                )
            if search.get("inconclusive") or search.get("error"):
                return (
                    "✗ CLASSIFICATION — type-directed search was inconclusive "
                    "or the formal statement was invalid; novelty is not cleared"
                )
        prior_entry: dict = {}
        if kind == "prior":
            prior_name = str(prior or name).strip()
            prior_entry = self.prior_verified.get(prior_name) or {}
            if not prior_entry:
                return (
                    f"✗ CLASSIFICATION — {prior_name!r} is not an exact "
                    "runner-supplied verified paper dependency"
                )
            prior_statement = str(prior_entry.get("statement") or "").strip()
            if (
                formal_signature.strip()
                and prior_statement
                and formal_signature.strip() != prior_statement
            ):
                return (
                    "✗ CLASSIFICATION — prior formal_signature differs from "
                    f"the runner-owned statement for {prior_name!r}"
                )
        excerpt = source_excerpt
        proof = self.original_proof
        start = int(source_char_start)
        end = int(source_char_end)
        if start >= 0 or end >= 0:
            excerpt_verified = bool(
                0 <= start <= end <= len(proof)
                and proof[start:end] == excerpt
            )
        else:
            # Backward-compatible inference is accepted only for a unique raw
            # occurrence; repeated generic excerpts require explicit spans.
            occurrences = [
                match.start()
                for match in re.finditer(re.escape(excerpt), proof)
            ] if excerpt and proof else []
            excerpt_verified = len(occurrences) == 1
            if excerpt_verified:
                start = occurrences[0]
                end = start + len(excerpt)
        byte_start = (
            len(proof[:start].encode("utf-8")) if excerpt_verified else -1
        )
        byte_end = (
            len(proof[:end].encode("utf-8")) if excerpt_verified else -1
        )
        kw = {"statement_nl": statement_nl}
        if kind == "prior":
            kw["prior"] = str(prior or name)
            kw["prior_code"] = str(prior_entry.get("code") or "")
            kw["prior_artifact"] = str(prior_entry.get("artifact") or "")
        elif kind == "library" and library:
            kw["library"] = library
        elif kind == "instantiation" and instantiation:
            kw["instantiation"] = instantiation
        else:
            kw["novel"] = True
        kw["depends_on"] = depends_on
        kw["source_excerpt"] = excerpt
        kw["source_excerpt_verified"] = excerpt_verified
        kw["source_char_start"] = start if excerpt_verified else -1
        kw["source_char_end"] = end if excerpt_verified else -1
        kw["source_byte_start"] = byte_start
        kw["source_byte_end"] = byte_end
        kw["input_sha256"] = hashlib.sha256(proof.encode()).hexdigest()
        kw["formal_signature"] = formal_signature
        kw["hypotheses"] = hypotheses
        self.d.resolve(name, **kw)
        lemma = self.d._find_lemma(name)
        self._emit_phase(
            "resolve",
            started=started,
            status="COMPLETED",
            blocks=[name],
            detail=f"{kind}; source span verified={excerpt_verified}",
            evidence="AGENT_SEARCH",
            artifacts={
                "block_ir_sha256": hashlib.sha256(
                    json.dumps(
                        lemma.__dict__ if lemma is not None else kw,
                        sort_keys=True,
                        default=str,
                    ).encode()
                ).hexdigest()
            },
        )
        deps = ", ".join(depends_on or []) or "none"
        declared = "declared" if depends_on is not None else "MISSING"
        mapping = (
            "exact proof excerpt verified"
            if excerpt_verified
            else "MISSING/UNMATCHED proof excerpt"
        )
        hyp = "declared" if hypotheses is not None else "MISSING"
        return (
            f"resolved {name} ({kind}); dependencies {declared}: {deps}; "
            f"{mapping}; hypotheses {hyp}"
        )

    def adjudicate_near_match(self, block: str, reason: str) -> str:
        """Persist the command's mandatory decision on differing log arguments."""
        if denied := self._phase_order_error("adjudicate_near_match"):
            return denied
        lemma = self.d._find_lemma(block)
        if lemma is None:
            return f"✗ unknown block {block!r}"
        if not (lemma.near_match or {}).get("differs"):
            return (
                f"✗ {block} has no recorded near-match difference to adjudicate"
            )
        if not reason.strip():
            return "✗ adjudication requires a concrete mathematical reason"
        lemma.near_match_adjudication = reason.strip()
        self.d._persist()
        return f"recorded near-match adjudication for {block}: {reason.strip()}"

    def audit_invocation(
        self,
        caller: str,
        invoked: str,
        hypotheses: list[str],
        checks: list[str],
        outcome: str,
        reason: str,
        conditioning: str = "",
    ) -> str:
        """Persist the complete hypothesis audit for one actual graph edge."""
        if denied := self._phase_order_error("audit_invocation"):
            return denied
        rec = self.d._result
        by_name = {lemma.name: lemma for lemma in rec.lemmas}
        lemma = by_name.get(caller)
        if lemma is None:
            return f"✗ unknown caller block {caller!r}"
        allowed = set(lemma.depends_on)
        if lemma.kind in {"library", "instantiation"}:
            selected = lemma.library_match or lemma.named_result
            if selected:
                allowed.add(selected)
        if invoked not in allowed:
            return (
                f"✗ {caller}->{invoked} is not a persisted dependency or "
                "selected library invocation"
            )
        normalized = outcome.strip().upper()
        if normalized not in {
            "CLEAR", "HYPOTHESIS_VIOLATION", "CIRCULAR", "UNCERTAIN"
        }:
            return "✗ invalid audit outcome"
        if not reason.strip():
            return "✗ invocation audit requires a concrete reason"
        if len(checks) != len(hypotheses):
            return (
                "✗ checks must contain one result for every listed hypothesis "
                f"({len(hypotheses)} hypotheses, {len(checks)} checks)"
            )
        row = {
            "caller": caller,
            "invoked": invoked,
            "hypotheses": list(hypotheses),
            "checks": list(checks),
            "outcome": normalized,
            "reason": reason.strip(),
            "conditioning": conditioning.strip(),
            "executed_by": "agent",
        }
        rec.invocation_audits = [
            item for item in rec.invocation_audits
            if not (
                item.get("caller") == caller
                and item.get("invoked") == invoked
            )
        ] + [row]
        self.d._persist()
        return (
            f"recorded hypothesis audit for {caller}->{invoked}: "
            f"{normalized}"
        )

    _AUDIT_OUTCOMES = {"PASS", "RISK", "NOT_APPLICABLE"}

    def audit_block(
        self,
        block: str,
        hypothesis_minimality: str,
        independence: str,
        statement_claim: str,
        satisfiability: str,
        notes: str = "",
    ) -> str:
        """Record all four anti-vacuity checks required by the full process.

        These entries are agent audit evidence. The trusted parent separately
        recompiles the block and runs sealed statement back-translation.
        """
        if denied := self._phase_order_error("audit_block"):
            return denied
        lemma = self.d._find_lemma(block)
        if lemma is None:
            return f"✗ unknown block {block!r}"
        if lemma.kind != "novel":
            return "✗ anti-vacuity audit is mandatory only for novel blocks"
        values = {
            "hypothesis_minimality": hypothesis_minimality.upper(),
            "independence": independence.upper(),
            "statement_claim": statement_claim.upper(),
            "satisfiability": satisfiability.upper(),
        }
        invalid = {
            key: value for key, value in values.items()
            if value not in self._AUDIT_OUTCOMES
        }
        if invalid:
            return (
                "✗ anti-vacuity outcomes must be PASS, RISK, or "
                f"NOT_APPLICABLE; invalid={invalid}"
            )
        if any(value == "RISK" for value in values.values()) and not notes.strip():
            return "✗ an anti-vacuity RISK requires explanatory notes"
        lemma.anti_vacuity_checks = {
            **values,
            "notes": notes.strip(),
            "executed_by": "agent",
        }
        self.d._persist()
        return (
            f"recorded complete anti-vacuity audit for {block}: "
            + ", ".join(f"{key}={value}" for key, value in values.items())
        )

    def evaluate_library_candidate(
        self,
        block: str,
        reusable: bool,
        reason: str,
        generalized_name: str = "",
        target_dir: str = "",
        docstring: str = "",
        generalized_code: str = "",
    ) -> str:
        """Evaluate a discharged novel block for shared-library growth.

        The agent-facing server records the curation proposal but cannot write
        the live source tree. Trusted parent promotion consumes eligible
        proposals after rechecking reuse search, statement match, and closure.
        """
        if denied := self._phase_order_error("evaluate_library_candidate"):
            return denied
        lemma = self.d._find_lemma(block)
        if lemma is None:
            return f"✗ unknown block {block!r}"
        if lemma.kind != "novel" or not lemma.discharged:
            return (
                "✗ library evaluation requires a successfully discharged "
                "novel block"
            )
        if not reason.strip():
            return "✗ library evaluation requires a concrete reason"
        if reusable and not (
            generalized_name.strip()
            and target_dir.strip()
            and docstring.strip()
            and generalized_code.strip()
        ):
            return (
                "✗ reusable candidates require generalized_name, target_dir, "
                "docstring, and a complete generalized_code file"
            )
        generalized_statement = ""
        if reusable:
            from .driver import extract_signature, find_axioms

            generalized_statement = extract_signature(
                generalized_code, generalized_name.strip()
            )
            if not generalized_statement:
                return (
                    "✗ generalized_code does not declare generalized_name "
                    f"{generalized_name!r}"
                )
            if find_axioms(generalized_code):
                return "✗ reusable candidates may not declare custom axioms"
            search = next(
                (
                    item for item in reversed(
                        self.d._result.library_searches
                    )
                    if item.get("block") == generalized_name.strip()
                    and item.get("statement") == generalized_statement
                ),
                None,
            )
            if search is None:
                return (
                    "✗ re-run library_search with block=generalized_name on "
                    "the exact generalized signature before promotion"
                )
            if (
                search.get("found")
                or search.get("inconclusive")
                or search.get("error")
            ):
                return (
                    "✗ generalized candidate did not clear the final exact "
                    "library reuse search"
                )
        row = {
            "name": generalized_name.strip() or block,
            "outcome": (
                "PROPOSED-REUSABLE"
                if reusable else "SKIPPED-NOT-REUSABLE"
            ),
            "reason": reason.strip(),
            "generalized_from": block,
            "target_dir": target_dir.strip(),
            "docstring": docstring.strip(),
            "statement": generalized_statement,
            "source_code": generalized_code if reusable else "",
            "source_sha256": (
                hashlib.sha256(generalized_code.encode()).hexdigest()
                if reusable else ""
            ),
            "backtranslation": "",
            "backtranslation_reason": "",
            "executed_by": "agent",
        }
        self.d._result.library_evaluations = [
            item for item in self.d._result.library_evaluations
            if str(item.get("generalized_from") or item.get("name")) != block
        ] + [row]
        self.d._persist()
        return (
            f"recorded library evaluation for {block}: {row['outcome']} — "
            f"{row['reason']}"
        )

    def register_axiom_lifecycle(
        self,
        name: str,
        statement: str,
        claimed_meaning: str,
        reference: str,
        backlog_entry: str,
        hypotheses_checked: bool,
    ) -> str:
        """Record the four required facts for a permitted named-result axiom."""
        if denied := self._phase_order_error("register_axiom_lifecycle"):
            return denied
        required = {
            "name": name,
            "statement": statement,
            "claimed_meaning": claimed_meaning,
            "reference": reference,
            "backlog_entry": backlog_entry,
        }
        missing = [key for key, value in required.items() if not value.strip()]
        if missing:
            return f"✗ axiom lifecycle missing required field(s): {missing}"
        row = {
            **{key: value.strip() for key, value in required.items()},
            "hypotheses_checked": bool(hypotheses_checked),
            "backtranslation": "",
            "backtranslation_reason": "",
            "backlog_verified": False,
            "executed_by": "agent",
        }
        self.d._result.axiom_lifecycle = [
            item for item in self.d._result.axiom_lifecycle
            if item.get("name") != name.strip()
        ] + [row]
        self.d._persist()
        return (
            f"recorded axiom lifecycle candidate for {name}; trusted parent "
            "will match and back-translate the exact declaration"
        )

    def falsify_block(self, block: str, verdict: str, instances: int = 0,
                      hyp_satisfied: int = 0, claim: str = "") -> str:
        if denied := self._phase_order_error("falsify_block"):
            return denied
        from .falsify import FalsifyReport
        # AGENT-ATTESTED: these numbers are supplied by the untrusted agent, not
        # executed by the harness, so the record is stamped executed_by="agent".
        # PASSED carries zero verification weight regardless; a REFUTED here is
        # corroborated by the separate kernel-backed `refute` path, not by these
        # numbers. (Trusted-executed falsification is tracked separately.)
        rec = self.d.record_falsification(FalsifyReport(
            block=block, verdict=verdict, instances=instances,
            hyp_satisfied=hyp_satisfied, claim=claim, executed_by="agent"))
        return f"falsification gate on {block}: {verdict} (agent-attested)"

    def falsify_run(self, block: str, sampler_code: str, n: int = 200_000,
                    seed: int = 0) -> str:
        """Execute generated sampler code only through the confined runner.

        The harness derives the numeric outcome, but the model authored both
        the tested formula and any ``recheck`` function. Consequently a hit is
        audit evidence until a separate deterministic checker validates the
        serialized witness; it never earns certificate evidence here.
        """
        if denied := self._phase_order_error("falsify_run"):
            return denied
        started = time.monotonic()
        from .falsify import FalsifyReport
        from verify_app.confined_python import (
            ConfinedPythonUnavailable,
            UnsafeSampler,
            run_confined_sampler,
        )
        try:
            confined = run_confined_sampler(sampler_code, n=n, seed=seed)
        except (ConfinedPythonUnavailable, UnsafeSampler, ValueError) as e:
            self._emit_phase(
                "falsify", started=started, status="REFUSED",
                blocks=[block], detail=str(e), evidence="NONE")
            return f"✗ confined sampler refused (not recorded): {e}"
        verdict = (
            "PASSED" if confined.verdict == "NO_COUNTEREXAMPLE"
            else confined.verdict
        )
        rep = FalsifyReport(
            block=block,
            verdict=verdict,
            instances=confined.instances,
            hyp_satisfied=confined.hyp_satisfied,
            violations=confined.violations,
            max_violation=confined.max_violation,
            certificate=confined.certificate,
            reason=(
                "dep|confined|agent-authored formula; independent checker absent"
                if verdict == "REFUTED" else ""
            ),
            executed_by="harness",
        )
        self.d.record_falsification(rep)
        self._emit_phase(
            "falsify",
            started=started,
            status=rep.verdict,
            blocks=[block],
            detail=(
                f"{rep.hyp_satisfied} hypothesis-satisfied instance(s); "
                "agent-authored formula"
            ),
            evidence="AUDIT",
            artifacts={
                "sampler_sha256": hashlib.sha256(
                    sampler_code.encode()
                ).hexdigest()
            },
        )
        return (f"falsification gate on {rep.block}: {rep.verdict} "
                f"(HARNESS-executed in confinement; {rep.hyp_satisfied} "
                "hyp-satisfied; audit-only until independently checked)")

    def compile(self, code: str) -> str:
        """Sandboxed iteration compile (not verdict-bearing)."""
        if denied := self._phase_order_error("compile"):
            return denied
        if os.environ.get("RLVERIFY_CAPABILITY_SMOKE") == "1":
            # Probe the actual inner confiner directly. Warming a persistent
            # REPL just to establish backend readiness adds 30–60 seconds and
            # can hide nested-sandbox failures behind its longer warmup.
            from .sandbox import safe_verify
            r = safe_verify(code, timeout=30)
        else:
            r = self.d.compile(code)
        if r.success:
            return "✓ compiles"
        return f"✗ compile failed:\n{(r.errors or r.output)[:1500]}"

    def sketch(self, skeleton_code: str, expected_blocks: list[str]) -> str:
        """Compile the sorried skeleton and surface the contract's 3-way outcome
        (verify-output-contract.md): DECOMPOSITION-OK / DECOMPOSITION-GAP /
        GLUE-BUG. The driver's LeanResult already distinguishes these; the wrapper
        no longer collapses them to binary. The gap-vs-glue call on a plain
        compile failure is left to the agent (the driver's "never auto-verdict"
        rule) — we hand it the unsolved goals to diagnose, not a guess."""
        rec = self.d._result
        if rec is None:
            return "✗ PHASE ORDER — call begin and resolve blocks first"
        graph_errors = self._dependency_errors(rec)
        if graph_errors:
            return (
                "✗ PHASE ORDER — decomposition graph must be complete and "
                f"acyclic before sketch: {'; '.join(graph_errors)}"
            )
        required_edges = {
            (lemma.name, dep)
            for lemma in rec.lemmas
            for dep in lemma.depends_on
        }
        required_edges.update({
            (
                lemma.name,
                lemma.library_match or lemma.named_result,
            )
            for lemma in rec.lemmas
            if lemma.kind in {"library", "instantiation"}
            and (lemma.library_match or lemma.named_result)
        })
        audits = {
            (row.get("caller"), row.get("invoked")): row
            for row in rec.invocation_audits
        }
        missing_audits = sorted(required_edges - set(audits))
        unsafe_audits = sorted(
            edge for edge in required_edges
            if edge in audits
            and audits[edge].get("outcome") != "CLEAR"
        )
        if missing_audits or unsafe_audits:
            return (
                "✗ PHASE ORDER — complete the hypothesis audit for every "
                "invocation before sketch; "
                f"missing={missing_audits}, unresolved={unsafe_audits}"
            )
        active = [
            lemma for lemma in rec.lemmas
            if lemma.kind in {"novel", "instantiation"} and not lemma.skipped
        ]
        missing_dependencies = [
            lemma.name for lemma in rec.lemmas
            if not lemma.dependencies_declared
        ]
        falsified = {row.get("block") for row in rec.falsifications}
        missing_falsify = [
            lemma.name for lemma in active if lemma.name not in falsified
        ]
        if missing_dependencies or missing_falsify:
            return (
                "✗ PHASE ORDER — sketch requires complete dependency and "
                "falsification records; "
                f"dependencies missing={missing_dependencies}, "
                f"falsification missing={missing_falsify}"
            )
        started = time.monotonic()
        r = self.d.sketch(skeleton_code, expected_blocks=expected_blocks)
        self._emit_phase(
            "sketch",
            started=started,
            status="COMPLETED" if getattr(r, "success", False) else "FAILED",
            blocks=expected_blocks,
            detail=getattr(r, "errors", "")[:300],
            evidence="AGENT_COMPILE",
            artifacts={
                "skeleton_sha256": hashlib.sha256(
                    skeleton_code.encode()
                ).hexdigest()
            },
        )
        if getattr(r, "success", False):
            return "✓ DECOMPOSITION-OK — skeleton compiles, every block used; decomposition machine-checked"
        errors = getattr(r, "errors", "") or ""
        # The driver forces success=False with this exact prefix when the glue
        # closed the goal WITHOUT using some blocks — a definitive glue bug
        # (the blocks may be fine; the assembly ignored them).
        if errors.startswith("vacuous glue"):
            return ("✗ GLUE-BUG (vacuous glue) — the skeleton compiled but ignored "
                    f"block(s): {errors}. Name every block explicitly in the glue "
                    "(exact/calc/linarith [block …]); the decomposition is NOT certified.")
        # Plain compile failure: gap (blocks insufficient) vs fixable glue —
        # indistinguishable to the compiler. Surface the missing implications.
        goals = getattr(r, "goals", []) or []
        head = "\n".join(f"  • {g[:200]}" for g in goals[:5]) if goals else "  (no structured goals; see errors)"
        detail = errors.splitlines()[0][:200] if errors else ""
        return ("✗ DECOMPOSITION-GAP or GLUE-BUG — skeleton did not compile. "
                f"{len(goals)} unsolved goal block(s) (the missing implication(s)):\n{head}\n"
                f"  error: {detail}\n"
                "Inspect: blocks insufficient ⇒ DECOMPOSITION-GAP; blocks fine but "
                "assembly wrong ⇒ GLUE-BUG. Do NOT auto-verdict.")

    @staticmethod
    def _norm_proof(proof: str) -> str:
        """The driver wraps `:= by\\n  {proof}`, indenting only the FIRST line, so
        a multi-line tactic proof breaks unless every line sits at a consistent
        tactic-block column. Agents pass proofs with NO continuation indent OR a
        pre-applied one (both seen live: ucb_radius_antitone) — a naive
        prepend mis-handles the pre-indented case. Robust normalization: strip
        the first line (the driver supplies its 2-space indent), then dedent the
        continuation block to remove whatever uniform indent the agent used and
        re-indent it by 2 — preserving any RELATIVE nesting (·/case/<;>) while
        fixing the base column."""
        import textwrap
        lines = proof.split("\n")
        if len(lines) <= 1:
            return proof.strip()
        first = lines[0].strip()
        rest = textwrap.indent(textwrap.dedent("\n".join(lines[1:])), "  ")
        return first + "\n" + rest

    def discharge(self, block: str, statement: str, proof: str,
                  imports: list[str]) -> str:
        rec = self.d._result
        if rec is None:
            return "✗ PHASE ORDER — call begin first"
        graph_errors = self._dependency_errors(rec)
        if graph_errors:
            return (
                "✗ PHASE ORDER — dependency graph is invalid: "
                + "; ".join(graph_errors)
            )
        lemma = self.d._find_lemma(block)
        if lemma is None and rec.lemmas:
            return f"✗ unknown block {block!r}"
        by_name = {item.name: item for item in rec.lemmas}
        unresolved_dependencies = [
            dep for dep in (lemma.depends_on if lemma is not None else [])
            if dep in by_name
            and by_name[dep].kind not in {"library", "prior"}
            and not by_name[dep].discharged
        ]
        if unresolved_dependencies:
            return (
                "✗ PHASE ORDER — discharge dependencies first: "
                f"{unresolved_dependencies}"
            )
        active = [
            lemma for lemma in rec.lemmas
            if lemma.kind in {"novel", "instantiation"} and not lemma.skipped
        ]
        # A full-process run must machine-check its decomposition before
        # discharging novel blocks.  Keep the standalone discharge tool usable:
        # it intentionally operates on one supplied block without a prior DAG.
        if active and not rec.sketch_verified:
            return (
                "✗ PHASE ORDER — discharge is available only after a "
                "DECOMPOSITION-OK sketch"
            )
        if lemma is not None and lemma.discharge_attempts >= 5:
            return (
                f"✗ DISCHARGE-RETRY-LIMIT — {block} has already used five "
                "compile attempts. Record the precise gap or decompose it into "
                "smaller independently checkable blocks before continuing."
            )
        if lemma is not None:
            lemma.discharge_attempts += 1
            self.d._persist()
        started = time.monotonic()
        r = self.d.formalize(block, statement=statement, proof=self._norm_proof(proof),
                             imports=imports, opens="")
        self._emit_phase(
            "discharge",
            started=started,
            status="COMPLETED" if getattr(r, "success", False) else "FAILED",
            blocks=[block],
            detail=getattr(r, "errors", "")[:300],
            evidence="AGENT_COMPILE",
            artifacts={
                "statement_sha256": hashlib.sha256(
                    statement.encode()
                ).hexdigest()
            },
        )
        if not getattr(r, "success", False):
            return f"✗ {block} not closed:\n{getattr(r,'errors','')[:1200]}"
        # C2: a block can COMPILE yet prove something trivial/weaker than the
        # claim. Surface the contract's COMPILED-VACUOUS-RISK from the cheap,
        # deterministic checks the harness can do at discharge time (id-shaped +
        # an independence smell). Recompile-based hypothesis-minimality stays
        # agent-side (the profile's anti-vacuity note). The id-shaped finding is
        # deterministic and becomes a workflow-v2 gate; the independence smell
        # remains a surfaced warning.
        risk = self._vacuity_risk(statement, proof)
        lemma = self.d._find_lemma(block)
        if lemma is not None:
            lemma.vacuity_risk = risk or ""
            self.d._persist()
        if risk:
            return (f"⚠ {block} COMPILED-VACUOUS-RISK — {risk}. It compiled, but may "
                    "prove something trivial or weaker than the claim; verify before "
                    "relying on it (re-compile with a hypothesis removed — still "
                    "compiling ⇒ that hypothesis is unused).")
        # Name the coverage so "COMPILED" isn't misread as full anti-vacuity
        # clearance: only id-shape + the independence smell ran here.
        return (f"✓ {block} formalized (COMPILED — id-shape & independence checks "
                "clean; hypothesis-minimality & statement-claim contract are yours to verify)")

    # Computation/normalization tactics that close a goal WITHOUT consulting the
    # local hypotheses — a lone one of these on a hypothesis-bearing statement is
    # an independence smell (the hypotheses may be inert). simp/aesop/linarith are
    # EXCLUDED: they legitimately use the local context.
    _TRIVIAL_CLOSERS = {"norm_num", "decide", "rfl", "trivial", "positivity", "native_decide"}
    # Tokens that mark a binder type as a PROPOSITION (a real hypothesis) rather
    # than a data/parameter binder. `(a b : ℝ)` / `{n : ℕ}` are NOT hypotheses, so
    # an identity over them closed by `norm_num` must not be flagged (the review's
    # demonstrated false positive). `→` is excluded — it is also the function-type
    # arrow, so it cannot distinguish a hypothesis from a data binder.
    _PROP_TOKENS = ("=", "≤", "<", "≥", ">", "≠", "∈", "∉", "⊆", "⊂", "∧", "∨",
                    "↔", "∃", "∀", "¬", "∣", "≈", "≅")

    @staticmethod
    def _vacuity_risk(statement: str, proof: str) -> "str | None":
        # 1. id-shaped: the conclusion equals a hypothesis ⇒ the block assumes its
        #    own conclusion (the proof is `exact h`). Deterministic, no false pos.
        if is_id_shaped(statement):
            return "the statement assumes its own conclusion (a hypothesis equals the goal)"
        # 2. independence smell (heuristic): a lone computational closer despite
        #    declared PROP hypotheses suggests the hypotheses are unused. Count only
        #    Prop-shaped binders, not data/parameter binders (else any identity over
        #    parameters closed by `norm_num` would false-flag).
        parsed = split_top_level(statement)
        binder_types = parsed[0] if parsed else []
        nhyps = sum(1 for t in binder_types
                    if any(tok in t for tok in HarnessSession._PROP_TOKENS))
        toks = (proof or "").strip().split()
        if nhyps >= 1 and len(toks) == 1 and "\n" not in (proof or "").strip() \
                and toks[0] in HarnessSession._TRIVIAL_CLOSERS:
            return (f"closed by a lone `{toks[0]}` despite {nhyps} declared "
                    "hypothesis(es) — check they are actually used (independence smell)")
        return None

    def _enforced_line(self, result=None) -> str:
        """The ONLY place a verdict is emitted to the agent — always through
        strict enforcement, so no raw VERIFIED can leak before the gates pass.
        (`finish()` nulls `_result`, so callers pass the returned result.)

        Surfaces the falsification breakdown + depth so the BYO user can judge
        whether the flaw-hunt was real — a shallow-but-present PASSED is no
        longer invisible on this (otherwise thin) surface."""
        rec = result or self.d._result or self.d._last_result
        d = rec.to_dict()
        v = enforce(d, strict=True)
        out = [f"VERDICT: {v['verdict']}"]
        if v["downgraded"]:
            out.append(f"  (downgraded from {v['base_verdict']})")
        if v["gate_failures"]:
            out.append("  gate gaps: " + "; ".join(v["gate_failures"]))
        faithfulness = d.get("proof_faithfulness") or "unassessed"
        out.append(f"  proof faithfulness: {faithfulness}")
        for detail in (d.get("proof_faithfulness_detail") or [])[:5]:
            out.append(f"    - {detail}")
        # Execution-safety provenance: was the agent-authored Lean compiled under
        # the W0 sandbox? OFF (RLVERIFY_SANDBOX=0, the only non-macOS path) drops
        # the untrusted-code guarantee, so the verdict trusts the proof source +
        # the agent. Surfacing-only — NOT a gate (it never enters gate_failures /
        # verdict_class), so it labels the run without downgrading it. Closes the
        # honesty gap where an unsandboxed run was indistinguishable from a
        # confined one on every durable surface.
        if not self.sandboxed:
            out.append("  ⚠ UNSANDBOXED (RLVERIFY_SANDBOX=0): untrusted-code "
                       "guarantee OFF — this verdict trusts the proof source and "
                       "the driving agent")
        audit = d.get("hypothesis_audit") or {}
        if audit:
            out.append(
                "  hypothesis audit: "
                f"{audit.get('overall', 'UNCERTAIN')} "
                f"({len(audit.get('findings') or [])} finding(s), "
                "prioritization-only)")
        # A1b: the contract EVIDENCE tier the run ESTABLISHED (≠ the verdict — a
        # UNGATED can read `evidence: kernel` with the gates still missing). Placed
        # AFTER the downgrade/gate-gaps lines so "why it's not verified" sits next
        # to the verdict and the evidence tier reads as the subordinate note it is.
        out.append(f"  evidence: {evidence_tier(d)}")
        fs = falsify_summary(d)
        if fs["total"]:
            c = fs["counts"]
            out.append(f"  falsify: {c['REFUTED']} refuted / {c['PASSED']} passed "
                       f"/ {c['VACUOUS']} vacuous / {c['SKIPPED']} skipped")
            if fs["passed_depths"]:
                depths = ", ".join(f"{b}={hs}" for b, hs in fs["passed_depths"])
                out.append(f"    PASSED depth (hyp-satisfied instances): {depths}")
            if fs["shallow"]:
                out.append("  ⚠ SHALLOW falsification (zero verification weight; "
                           f"thin flaw-hunt): {', '.join(fs['shallow'])}")
            # Provenance: which falsifications were harness-executed (trusted)
            # vs agent-attested (the agent's word). Honesty on the thin surface.
            out.append(f"    falsify provenance: {fs['harness_executed']} "
                       f"harness-executed / {len(fs['attested'])} agent-attested")
            if fs["attested"]:
                out.append("  ⚠ AGENT-ATTESTED falsification (numbers not verified "
                           f"by the harness): {', '.join(fs['attested'])}")
        return "\n".join(out)

    def assemble(self, statement: str, proof: str, imports: list[str]) -> str:
        # Do NOT return the driver's raw _verdict_string here: at assemble time
        # gate_downgrade is unset, so it would hand the agent a "VERIFIED" that
        # finalize would downgrade. Emit the gate-enforced line instead.
        rec = self.d._result
        if rec is None:
            return "✗ PHASE ORDER — call begin first"
        graph_errors = self._dependency_errors(rec)
        if graph_errors:
            return (
                "✗ PHASE ORDER — dependency graph is invalid: "
                + "; ".join(graph_errors)
            )
        active = [
            lemma for lemma in rec.lemmas
            if lemma.kind in {"novel", "instantiation"} and not lemma.skipped
        ]
        falsified = {row.get("block") for row in rec.falsifications}
        missing_falsify = [
            lemma.name for lemma in active if lemma.name not in falsified
        ]
        missing_discharge = [
            lemma.name for lemma in active if not lemma.discharged
        ]
        missing_audit = [
            lemma.name for lemma in active
            if lemma.kind == "novel"
            and not lemma.anti_vacuity_checks
        ]
        unadjudicated = [
            lemma.name for lemma in rec.lemmas
            if (lemma.near_match or {}).get("differs")
            and not lemma.near_match_adjudication
        ]
        if active and (
            not rec.sketch_verified
            or missing_falsify
            or missing_discharge
            or missing_audit
            or unadjudicated
        ):
            return (
                "✗ PHASE ORDER — assemble blocked until surviving non-library "
                "blocks pass falsification, DECOMPOSITION-OK sketch, and "
                "topological discharge; "
                f"sketch={rec.sketch_verified}, "
                f"falsification missing={missing_falsify}, "
                f"discharge missing={missing_discharge}, "
                f"anti-vacuity missing={missing_audit}, "
                f"near-match adjudication missing={unadjudicated}"
            )
        started = time.monotonic()
        self.d.assemble(statement=statement, proof=self._norm_proof(proof),
                        imports=imports, opens="")
        rec = self.d._result
        self._emit_phase(
            "assemble",
            started=started,
            status="COMPLETED" if rec and rec.compiled else "FAILED",
            blocks=[lemma.name for lemma in (rec.lemmas if rec else [])],
            detail="agent assembly; trusted parent recheck still required",
            evidence="AGENT_COMPILE",
            artifacts={
                "source_sha256": hashlib.sha256(
                    (rec.main_code if rec else "").encode()
                ).hexdigest()
            },
        )
        line = self._enforced_line()
        pending_library = [
            lemma.name for lemma in rec.lemmas
            if lemma.kind == "novel"
            and lemma.discharged
            and not any(
                str(row.get("generalized_from") or row.get("name") or "")
                == lemma.name
                for row in rec.library_evaluations
            )
        ]
        if pending_library:
            line += (
                "\n  next: run evaluate_library_candidate for "
                f"{pending_library}, then stop; the harness finalizes"
            )
        return line

    def structural_assemble(self, code: str,
                            placeholder_blocks: list[str]) -> str:
        """Compile the remaining proof modulo explicit failed-block gaps.

        This is a conditional structure check, never a verification verdict.
        It rejects custom axioms, unnamed sorries, unused placeholders, and
        independent unresolved blocks.
        """
        result = self.d.structural_assemble(code, placeholder_blocks)
        if result.success:
            return (
                "✓ COMPILES MODULO PLACEHOLDERS — downstream structure is "
                "machine-checked, but the theorem remains unverified because "
                f"these block(s) are assumed: {', '.join(placeholder_blocks)}"
            )
        return f"✗ STRUCTURAL ASSEMBLY FAILED — {result.errors}"

    def finalize(self) -> str:
        r = self.d.finish()
        return self._enforced_line(r)


# --------------------------------------------------------------------------
# FastMCP transport (thin). `python -m rlverify.mcp_server` runs it over stdio.
# --------------------------------------------------------------------------

# NOTE: the advisory IDE path (repo `.mcp.json` + RLVERIFY_ADVISORY=1 server
# instructions) was retired 2026-07-04 — CLI-only v1, HARNESS_DESIGN.md §10.2.
# This server is runner-internal plumbing: the runner/CLI path injects the full
# profile into the task prompt itself, so no `instructions=` are attached here.


def build_mcp():
    from mcp.server.fastmcp import FastMCP

    mcp = FastMCP("rlverify")
    session = HarnessSession()
    confirmation_mode = (
        os.environ.get("RLVERIFY_VERIFICATION_MODE") == "confirmation"
    )

    def _confirmation_denied(tool: str) -> str | None:
        if not confirmation_mode:
            return None
        return (
            f"✗ {tool} is unavailable during targeted confirmation. "
            "Use only begin, status, search, compile, refute, certify_step, "
            "and report_failure; stop after the narrow disputed step."
        )

    @mcp.tool()
    def begin(fixture: str) -> str:
        """Start a verification session. Call FIRST."""
        return session.begin(fixture)

    # NOTE: triage and back-translation are NOT agent tools. They are executed
    # by trusted runner code (harness/triage.py, harness/backtranslate.py) and
    # injected via HarnessSession.record_triage / the driver — so a lying agent
    # cannot fabricate them. Exposing record_triage as a tool would re-open the
    # W1 attestation hole; it is deliberately absent here.

    @mcp.tool()
    def search(query: str) -> str:
        """Search the theorem library (substring + keyword)."""
        return session.search(query)

    @mcp.tool()
    def source_search(query: str, limit: int = 20) -> str:
        """Read-only exact-text search over RLGeneralization, Mathlib, and
        Batteries Lean source. Use it to inspect nearby declarations and proof
        idioms without shell or arbitrary filesystem access."""
        return session.source_search(query, limit)

    @mcp.tool()
    def source_read(path: str, start_line: int = 1,
                    end_line: int = 240) -> str:
        """Read at most 400 lines from a trusted Lean source path returned by
        source_search. Journals and arbitrary workspace files are inaccessible."""
        return session.source_read(path, start_line, end_line)

    @mcp.tool()
    def library_search(
        block: str,
        statement: str,
        imports: list[str] | None = None,
    ) -> str:
        """Type-directed repository/Mathlib reuse search for one formal block.

        Run this before classifying an elaborated block as novel. A found proof
        requires library/instantiation classification.
        """
        if denied := _confirmation_denied("library_search"):
            return denied
        return session.library_search(block, statement, imports)

    @mcp.tool()
    def status() -> str:
        """Inspect dependency, sketch, discharge, and remaining workflow state."""
        return session.status()

    @mcp.tool()
    def refute(block: str, code: str, description: str) -> str:
        """Compile a scoped-candidate negative certificate. `code` declares a
        theorem: premises-hold ∧ objects-defined ∧ ¬conclusion on a concrete
        instance; `description` = the exact refuted excerpt. Kernel closure
        proves only that Lean proposition. Follow a proof-step witness with
        report_failure('PROOF_INVALID', …); use WRONG only for the complete
        submitted theorem. The trusted parent decides the final scope."""
        return session.refute(block, code, description)

    @mcp.tool()
    def certify_step(block: str, code: str, description: str) -> str:
        """Compile a positive Lean proof of the exact disputed inference.
        `description` must be a contiguous verbatim excerpt of the submission.
        This may clear the suspicion after trusted recheck; it does not verify
        the full theorem."""
        return session.certify_step(block, code, description)

    @mcp.tool()
    def report_failure(kind: str, reason: str, block: str = "") -> str:
        """Report a candidate flaw, not just unfinished work.
        kind ∈ {WRONG, PROOF_INVALID, INCOMPLETE, MISMATCH,
        HYPOTHESIS_VIOLATION, CIRCULAR}. Use PROOF_INVALID when a submitted
        inference fails but the theorem may remain true. Use WRONG only for a
        well-defined counterexample to the complete theorem. A preceding
        `refute` supplies an artifact, but trusted scope matching—not the
        agent's label or kernel closure alone—determines the final verdict."""
        return session.report_failure(kind, reason, block)

    @mcp.tool()
    def main_unformalizable(reason: str) -> str:
        """Report that the exact main statement cannot be represented with the
        available Lean/Mathlib infrastructure. This is a terminal
        UNVERIFIED/INCOMPLETE result, not permission to weaken the statement."""
        if denied := _confirmation_denied("main_unformalizable"):
            return denied
        return session.main_unformalizable(reason)

    @mcp.tool()
    def resolve_block(name: str, statement_nl: str, kind: str = "novel",
                      library: str = "", instantiation: str = "",
                      prior: str = "",
                      depends_on: list[str] | None = None,
                      source_excerpt: str = "",
                      source_char_start: int = -1,
                      source_char_end: int = -1,
                      formal_signature: str = "",
                      hypotheses: list[str] | None = None) -> str:
        """Classify a proof block and declare its block dependencies.

        Pass depends_on=[] explicitly for a root block. New strict-workflow
        sessions require a dependency declaration for every block.
        """
        if denied := _confirmation_denied("resolve_block"):
            return denied
        return session.resolve_block(
            name,
            statement_nl,
            kind,
            library=library or None,
            instantiation=instantiation or None,
            prior=prior or None,
            depends_on=depends_on,
            source_excerpt=source_excerpt,
            source_char_start=source_char_start,
            source_char_end=source_char_end,
            formal_signature=formal_signature,
            hypotheses=hypotheses,
        )

    @mcp.tool()
    def falsify_block(block: str, verdict: str, instances: int = 0,
                      hyp_satisfied: int = 0, claim: str = "") -> str:
        """Record the numeric falsification-gate outcome for a block (AGENT-
        ATTESTED — your numbers, not harness-verified). Use `falsify_run` for a
        confined harness execution; it still remains audit-only until a
        separate deterministic checker validates the witness."""
        if denied := _confirmation_denied("falsify_block"):
            return denied
        return session.falsify_block(block, verdict, instances, hyp_satisfied, claim)

    @mcp.tool()
    def falsify_run(block: str, sampler_code: str, n: int = 200_000,
                    seed: int = 0) -> str:
        """Execute agent-authored sampler code in the confined runner.
        `sampler_code` defines sample/hypotheses/lhs/rhs (+ optional recheck).
        A found witness is audit-only: same-author cross-validation is not an
        independent mathematical certificate."""
        if denied := _confirmation_denied("falsify_run"):
            return denied
        return session.falsify_run(block, sampler_code, n, seed)

    @mcp.tool()
    def adjudicate_near_match(block: str, reason: str) -> str:
        """Explain why each recorded near-match log/constant difference does or
        does not belong. Required whenever resolve reports `differs:`."""
        if denied := _confirmation_denied("adjudicate_near_match"):
            return denied
        return session.adjudicate_near_match(block, reason)

    @mcp.tool()
    def audit_invocation(
        caller: str,
        invoked: str,
        hypotheses: list[str],
        checks: list[str],
        outcome: str,
        reason: str,
        conditioning: str = "",
    ) -> str:
        """Audit one actual dependency/library invocation. List every
        hypothesis in order and provide one check result per hypothesis.
        Record dropped conditioning explicitly. Every invocation must be CLEAR
        before sketch; otherwise report the classified failure."""
        if denied := _confirmation_denied("audit_invocation"):
            return denied
        return session.audit_invocation(
            caller,
            invoked,
            hypotheses,
            checks,
            outcome,
            reason,
            conditioning,
        )

    @mcp.tool()
    def compile(code: str) -> str:
        """Sandbox-compile Lean code (iteration; not verdict-bearing)."""
        return session.compile(code)

    @mcp.tool()
    def sketch(skeleton_code: str, expected_blocks: list[str]) -> str:
        """Compile the sorried skeleton — machine-checks the decomposition.
        Returns the 3-way outcome: DECOMPOSITION-OK / DECOMPOSITION-GAP / GLUE-BUG
        (a vacuous glue that ignores a block is flagged GLUE-BUG; a plain compile
        failure surfaces the unsolved goals for you to diagnose gap vs glue)."""
        if denied := _confirmation_denied("sketch"):
            return denied
        return session.sketch(skeleton_code, expected_blocks)

    @mcp.tool()
    def discharge(block: str, statement: str, proof: str,
                  imports: list[str]) -> str:
        """Prove one block (replace its sorry). A compiled block that assumes its
        own conclusion, or is closed by a lone computational tactic despite
        declared hypotheses, is flagged COMPILED-VACUOUS-RISK (a warning, not a
        verdict — verify it isn't weaker than the claim)."""
        if denied := _confirmation_denied("discharge"):
            return denied
        return session.discharge(block, statement, proof, imports)

    @mcp.tool()
    def audit_block(
        block: str,
        hypothesis_minimality: str,
        independence: str,
        statement_claim: str,
        satisfiability: str,
        notes: str = "",
    ) -> str:
        """Record all four mandatory anti-vacuity checks for a discharged novel
        block. Outcomes are PASS, RISK, or NOT_APPLICABLE. A RISK must be
        resolved before the block can support verification."""
        if denied := _confirmation_denied("audit_block"):
            return denied
        return session.audit_block(
            block,
            hypothesis_minimality,
            independence,
            statement_claim,
            satisfiability,
            notes,
        )

    @mcp.tool()
    def assemble(statement: str, proof: str, imports: list[str]) -> str:
        """Assemble + kernel-audit the full proof. Returns the verdict line."""
        if denied := _confirmation_denied("assemble"):
            return denied
        return session.assemble(statement, proof, imports)

    @mcp.tool()
    def evaluate_library_candidate(
        block: str,
        reusable: bool,
        reason: str,
        generalized_name: str = "",
        target_dir: str = "",
        docstring: str = "",
        generalized_code: str = "",
    ) -> str:
        """Mandatory Phase 5 evaluation for every discharged novel block.
        If reusable=true, propose a generalized name, topic directory, and
        searchable docstring. The trusted parent rechecks any promotion."""
        if denied := _confirmation_denied("evaluate_library_candidate"):
            return denied
        return session.evaluate_library_candidate(
            block,
            reusable,
            reason,
            generalized_name,
            target_dir,
            docstring,
            generalized_code,
        )

    @mcp.tool()
    def register_axiom_lifecycle(
        name: str,
        statement: str,
        claimed_meaning: str,
        reference: str,
        backlog_entry: str,
        hypotheses_checked: bool,
    ) -> str:
        """Register a temporary named-result axiom's exact statement,
        mathematical meaning, citation, backlog entry, and completed hypothesis
        audit. The trusted parent checks the declaration and back-translation."""
        if denied := _confirmation_denied("register_axiom_lifecycle"):
            return denied
        return session.register_axiom_lifecycle(
            name,
            statement,
            claimed_meaning,
            reference,
            backlog_entry,
            hypotheses_checked,
        )

    @mcp.tool()
    def structural_assemble(code: str, placeholder_blocks: list[str]) -> str:
        """Compile a conditional full proof with `sorry` permitted only in the
        named failed blocks. Independent blocks must already be discharged.
        This can establish COMPILES MODULO PLACEHOLDERS, never VERIFIED."""
        if denied := _confirmation_denied("structural_assemble"):
            return denied
        return session.structural_assemble(code, placeholder_blocks)

    @mcp.tool()
    def finalize() -> str:
        """Finish: enforce gate coverage and emit the final verdict."""
        if denied := _confirmation_denied("finalize"):
            return denied
        return session.finalize()

    return mcp


def main() -> None:
    pid_path = None
    corpus = os.environ.get("RLVERIFY_CORPUS")
    if corpus:
        pid_dir = Path(corpus).parent / "mcp_pids"
        pid_dir.mkdir(parents=True, exist_ok=True)
        pid_path = pid_dir / str(os.getpid())
        pid_path.write_text(str(os.getpid()))
        atexit.register(pid_path.unlink, missing_ok=True)
    try:
        build_mcp().run()
    finally:
        if pid_path is not None:
            pid_path.unlink(missing_ok=True)


if __name__ == "__main__":
    main()
