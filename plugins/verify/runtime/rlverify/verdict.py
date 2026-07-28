"""Single verdict authority for the RLVerify pipeline (W1 consolidation).

Before this module the verdict *class* logic lived in two hand-synced copies —
``VerifyDriver._verdict_string`` (driver.py) and ``effective_verdict``
(benchmarks/score.py, whose docstring literally said "Mirror of …"). The
harness adds a third consumer (the MCP server, W2) plus a gate-enforcement
layer, so the review required this be consolidated into ONE importable
authority rather than triplicated.

This module owns three things, all operating on a plain run-record ``dict``
(``VerifyResult.to_dict()`` or a loaded ``runs/*.json``):

1. ``verdict_class`` — the canonical verdict-class decision. ``score.py``
   delegates to it; the driver's renderer is sync-tested against it.
2. ``gate_failures`` — the flaw-hunting gate-coverage check (sealed triage,
   per-block falsification, sealed back-translation) plus workflow-contract-v2
   structure (declared acyclic dependencies, sketch, ordered discharge, and
   deterministic anti-vacuity). The driver (strict mode), harness CLI, and MCP
   server all share it.
3. ``enforce`` — turn coverage gaps into a verdict *downgrade* in strict mode
   (VERIFIED-class + any gate failure → UNVERIFIED/UNGATED). Strict mode is ON
   for untrusted/harness sessions and OFF for trusted-local runs.
"""
from __future__ import annotations

try:  # normal package import
    from .lean import STANDARD_AXIOMS
except ImportError:  # pragma: no cover - allow `python rlverify/verdict.py`
    STANDARD_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})

# Verdict classes that assert success and therefore require gate coverage.
# COMPILED / HAS GAPS are already weaker-than-verified and are left as-is.
VERIFIED_CLASS = {
    "VERIFIED",
    "VERIFIED MODULO AXIOMS",
    "VERIFIED/ALTERNATIVE-PROOF",
}
WORKFLOW_CONTRACT_VERSION = 4


def is_main_theorem_refutation(ref: dict) -> bool:
    """Whether one negative Lean artifact decides the submitted theorem.

    Kernel closure authenticates only the Lean proposition that compiled.  The
    remaining fields are trusted-parent stamps binding that proposition to the
    complete submitted theorem, its premises, and its well-defined objects.
    """
    return bool(
        ref.get("kernel_backed")
        and not ref.get("quarantined")
        and ref.get("target_scope") == "MAIN_THEOREM"
        and ref.get("finding_kind") == "COUNTEREXAMPLE"
        and ref.get("premises_satisfied") is True
        and ref.get("objects_well_defined") is True
        and ref.get("conclusion_negated") is True
        and ref.get("statement_faithful") is True
    )


def _scoped_kernel_refutations(run: dict, *kinds: str) -> list[dict]:
    allowed = set(kinds)
    return [
        ref for ref in run.get("refutations", [])
        if ref.get("kernel_backed")
        and not ref.get("quarantined")
        and (not allowed or ref.get("finding_kind") in allowed)
    ]


def _has_deterministic_definedness_gap(run: dict) -> bool:
    preflight = run.get("preflight") or {}
    return bool(
        preflight.get("status") == "CONFIRMED_WELL_DEFINEDNESS_GAP"
        and any(
            finding.get("validator")
            == "deterministic-well-definedness-v1"
            and finding.get("target_scope") == "WELL_DEFINEDNESS"
            and finding.get("finding_kind") in {
                "MISSING_HYPOTHESIS", "UNDEFINED_TERM"
            }
            for finding in preflight.get("findings") or []
            if isinstance(finding, dict)
        )
    )


def _main_statement_mismatch(run: dict) -> bool:
    return any(
        row.get("executed_by") == "harness"
        and row.get("target") == "main"
        and row.get("verdict") == "MISMATCH"
        for row in run.get("backtranslations", [])
        if isinstance(row, dict)
    )


def has_independent_refutation_certificate(run: dict) -> bool:
    """Whether a falsification has a deterministic independent recheck.

    Merely executing agent-authored Python, including an agent-authored
    ``recheck`` function, is not independent evidence.  Producers must stamp
    both fields only after a separate deterministic checker validates the
    serialized witness.
    """
    return any(
        f.get("verdict") == "REFUTED"
        and f.get("executed_by") == "harness"
        and f.get("certificate_validated") is True
        and f.get("independent_checker") == "deterministic"
        and f.get("target_scope") == "MAIN_THEOREM"
        and f.get("premises_satisfied") is True
        and f.get("objects_well_defined") is True
        and f.get("statement_faithful") is True
        for f in run.get("falsifications", [])
    )


def workflow_phase_failures(run: dict) -> list[str]:
    """Structural gaps in the legacy-compatible phase workflow.

    Contract v2 applies only to new harness sessions. Older saved records do not
    acquire retroactive failures merely because they predate dependency,
    sketch, and discharge provenance fields.
    """
    try:
        contract_version = int(run.get("workflow_contract_version") or 1)
    except (TypeError, ValueError):
        return ["invalid workflow_contract_version in run record"]
    if contract_version < 2:
        return []

    lemmas = list(run.get("lemmas") or [])
    if not lemmas and contract_version < 4:
        return []

    fails: list[str] = []
    raw_names = [str(l.get("name", "")) for l in lemmas if l.get("name")]
    names = set(raw_names)
    duplicates = sorted({name for name in raw_names if raw_names.count(name) > 1})
    if duplicates:
        fails.append(f"duplicate block name(s) in dependency graph: {duplicates}")

    undeclared = [l.get("name") for l in lemmas
                  if not l.get("dependencies_declared")]
    if undeclared:
        fails.append(f"dependency list not declared for block(s): {undeclared}")

    unknown: list[str] = []
    graph: dict[str, list[str]] = {}
    for lemma in lemmas:
        name = str(lemma.get("name", ""))
        deps = [str(d) for d in (lemma.get("depends_on") or [])]
        graph[name] = deps
        for dep in deps:
            if dep not in names:
                unknown.append(f"{name}->{dep}")
    if unknown:
        fails.append(f"dependency graph references unknown block(s): {unknown}")

    # Textual dependency cycles are deterministically detectable. Conditional
    # cycles remain the sealed hypothesis audit's job.
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
        for dep in graph.get(name, []):
            if dep in graph and visit(dep, path + [name]):
                return True
        visiting.remove(name)
        visited.add(name)
        return False

    for name in graph:
        if visit(name, []) or cycle:
            break
    if cycle:
        fails.append("dependency graph contains cycle: " + " -> ".join(cycle))

    all_blocks = [
        l for l in lemmas
        if not l.get("skipped")
        and l.get("kind") not in ("violation", "circular")
    ]
    active = [
        l for l in lemmas
        if l.get("kind") in ("novel", "instantiation") and not l.get("skipped")
    ]
    active_names = {str(l.get("name", "")) for l in active}
    if contract_version >= 4:
        # The full-process command maps every claimed block—not only novel
        # ones—back to the immutable submitted proof and inventories every
        # assumption before proof search.
        unmapped_all = [
            l.get("name") for l in all_blocks
            if not l.get("source_excerpt_verified")
        ]
        if unmapped_all:
            fails.append(
                "block(s) lack an exact submitted-proof excerpt: "
                f"{unmapped_all}")
        undeclared_all = [
            l.get("name") for l in all_blocks
            if not l.get("hypotheses_declared")
        ]
        if undeclared_all:
            fails.append(
                "hypothesis list not declared for block(s): "
                f"{undeclared_all}")
        unadjudicated = [
            l.get("name") for l in all_blocks
            if (l.get("near_match") or {}).get("differs")
            and not str(l.get("near_match_adjudication") or "").strip()
        ]
        if unadjudicated:
            fails.append(
                "near-match log-argument difference(s) not adjudicated: "
                f"{unadjudicated}")
        required_edges = {
            (str(lemma.get("name", "")), str(dep))
            for lemma in all_blocks
            for dep in lemma.get("depends_on") or []
        }
        required_edges.update({
            (
                str(lemma.get("name", "")),
                str(
                    lemma.get("library_match")
                    or lemma.get("named_result")
                    or ""
                ),
            )
            for lemma in all_blocks
            if lemma.get("kind") in {"library", "instantiation"}
            and (
                lemma.get("library_match")
                or lemma.get("named_result")
            )
        })
        audits = {
            (
                str(row.get("caller", "")),
                str(row.get("invoked", "")),
            ): row
            for row in run.get("invocation_audits", [])
            if isinstance(row, dict)
        }
        missing_edges = sorted(required_edges - set(audits))
        if missing_edges:
            fails.append(
                "inter-block/library invocation(s) lack the complete "
                f"hypothesis audit: {missing_edges}")
        unsafe_edges = sorted(
            edge for edge in required_edges
            if edge in audits
            and str(audits[edge].get("outcome", "")).upper() != "CLEAR"
        )
        if unsafe_edges:
            fails.append(
                "invocation hypothesis audit has unresolved finding(s): "
                f"{unsafe_edges}")
    if active:
        if contract_version == 3:
            unmapped = [
                l.get("name") for l in active
                if not l.get("source_excerpt_verified")
            ]
            if unmapped:
                fails.append(
                    f"block(s) lack an exact submitted-proof excerpt: {unmapped}")
            undeclared_hypotheses = [
                l.get("name") for l in active
                if not l.get("hypotheses_declared")
            ]
            if undeclared_hypotheses:
                fails.append(
                    "hypothesis list not declared for block(s): "
                    f"{undeclared_hypotheses}")
        if contract_version >= 4:
            searches = {
                (str(row.get("block", "")), str(row.get("statement", "")))
                for row in run.get("library_searches", [])
                if isinstance(row, dict)
            }
            missing_reuse_gate = [
                l.get("name") for l in active
                if l.get("kind") == "novel"
                and (
                    str(l.get("name", "")),
                    str(l.get("formal_signature", "")),
                ) not in searches
            ]
            if missing_reuse_gate:
                fails.append(
                    "novel block(s) skipped mandatory type-directed "
                    f"library_search: {missing_reuse_gate}")

        if not run.get("sketch_verified"):
            fails.append(
                "no successful decomposition sketch for novel/instantiation block(s)")
        else:
            sketched = set(run.get("sketch_expected_blocks") or [])
            missing = sorted(active_names - sketched)
            if missing:
                fails.append(
                    f"successful sketch did not cover block(s): {missing}")

        undischarged = [l.get("name") for l in active if not l.get("discharged")]
        if undischarged:
            fails.append(
                f"block(s) were not discharged before assembly: {undischarged}")
        if contract_version >= 3:
            untrusted_discharge = [
                l.get("name") for l in active
                if l.get("discharged") and not l.get("trusted_rechecked")
            ]
            if untrusted_discharge:
                fails.append(
                    "discharged block certificate not independently rechecked: "
                    f"{untrusted_discharge}")

        order = list(run.get("discharge_order") or [])
        pos = {name: idx for idx, name in enumerate(order)}
        missing_order = sorted(active_names - set(order))
        if missing_order:
            fails.append(
                f"discharged block(s) missing from discharge order: {missing_order}")
        inversions: list[str] = []
        for lemma in active:
            name = str(lemma.get("name", ""))
            for dep in lemma.get("depends_on") or []:
                if dep in active_names and dep in pos and name in pos \
                        and pos[dep] >= pos[name]:
                    inversions.append(f"{name} before dependency {dep}")
        if inversions:
            fails.append(
                f"discharge order violates dependency graph: {inversions}")

        id_shaped = [
            l.get("name") for l in active
            if "assumes its own conclusion" in str(l.get("vacuity_risk", ""))
        ]
        if id_shaped:
            fails.append(
                f"deterministic anti-vacuity failure in block(s): {id_shaped}")
        if contract_version >= 4:
            required_checks = {
                "hypothesis_minimality",
                "independence",
                "statement_claim",
                "satisfiability",
            }
            missing_anti_vacuity: list[str] = []
            risky_anti_vacuity: list[str] = []
            for lemma in active:
                if lemma.get("kind") != "novel":
                    continue
                checks = lemma.get("anti_vacuity_checks") or {}
                if not required_checks.issubset(checks):
                    missing_anti_vacuity.append(str(lemma.get("name", "")))
                    continue
                if any(
                    str(checks.get(name, "")).upper() == "RISK"
                    for name in required_checks
                ):
                    risky_anti_vacuity.append(str(lemma.get("name", "")))
            if missing_anti_vacuity:
                fails.append(
                    "novel block(s) lack the complete anti-vacuity audit: "
                    f"{missing_anti_vacuity}")
            if risky_anti_vacuity:
                fails.append(
                    "novel block(s) have unresolved anti-vacuity risk: "
                    f"{risky_anti_vacuity}")

            evaluated = {
                str(row.get("generalized_from") or row.get("name") or "")
                for row in run.get("library_evaluations", [])
                if isinstance(row, dict)
            }
            unevaluated = [
                str(l.get("name", "")) for l in active
                if l.get("kind") == "novel"
                and l.get("discharged")
                and str(l.get("name", "")) not in evaluated
            ]
            if unevaluated:
                fails.append(
                    "verified novel block(s) were not evaluated for reusable "
                    f"library growth: {unevaluated}")

    if contract_version >= 4:
        custom_axioms = [
            axiom for axiom in run.get("kernel_axioms", [])
            if axiom not in STANDARD_AXIOMS and axiom != "sorryAx"
        ]
        lifecycle_rows = [
            row for row in run.get("axiom_lifecycle", [])
            if isinstance(row, dict)
        ]

        def lifecycle_for(name: str) -> dict:
            return next(
                (
                    row for row in lifecycle_rows
                    if str(row.get("name", "")) == name
                    or name.endswith(f".{row.get('name', '')}")
                ),
                {},
            )

        incomplete_axioms = [
            name for name in custom_axioms
            if not lifecycle_for(name)
            or not str(lifecycle_for(name).get("reference") or "").strip()
            or not str(lifecycle_for(name).get("backlog_entry") or "").strip()
            or lifecycle_for(name).get("backlog_verified") is not True
            or lifecycle_for(name).get("hypotheses_checked") is not True
            or lifecycle_for(name).get("backtranslation") not in {"MATCH", "NOTE"}
        ]
        if incomplete_axioms:
            fails.append(
                "custom axiom(s) lack the complete four-part lifecycle: "
                f"{incomplete_axioms}")

    return fails


def verdict_class(run: dict) -> str:
    """Canonical verdict class from a run record (record fields only).

    This is THE class logic; ``benchmarks/score.effective_verdict`` re-exports
    it and ``VerifyDriver._verdict_string`` is sync-tested to agree
    (tests/test_verdict_sync.py).
    """
    # A recorded strict-mode downgrade is definitive and must survive a reload:
    # the driver sets gate_downgrade in the saved record but leaves `verdict`
    # empty, so without this every consumer (scorer, MCP server, CLI) would
    # re-derive VERIFIED from the kernel fields and silently undo the downgrade.
    if run.get("gate_downgrade"):
        return "UNVERIFIED/UNGATED"
    if run.get("has_sorry_ax"):
        return "UNVERIFIED"
    if _main_statement_mismatch(run):
        return "UNVERIFIED/MISMATCH"
    if _has_deterministic_definedness_gap(run):
        return "UNVERIFIED/HYPOTHESIS_VIOLATION"
    if any(is_main_theorem_refutation(ref)
           for ref in run.get("refutations", [])):
        return "UNVERIFIED/WRONG"
    if has_independent_refutation_certificate(run):
        return "UNVERIFIED/WRONG"
    if _scoped_kernel_refutations(
        run, "MISSING_HYPOTHESIS", "UNDEFINED_TERM"
    ):
        return "UNVERIFIED/HYPOTHESIS_VIOLATION"
    if _scoped_kernel_refutations(run, "STATEMENT_MISMATCH"):
        return "UNVERIFIED/MISMATCH"
    if _scoped_kernel_refutations(run, "INVALID_INFERENCE"):
        return "UNVERIFIED/PROOF_INVALID"
    # Backward-compatible records may contain a clean auxiliary certificate
    # without trusted scope metadata.  That is mathematical evidence about the
    # auxiliary proposition only, not a theorem counterexample.
    if _scoped_kernel_refutations(run):
        return "UNVERIFIED/SUSPECTED"
    if run.get("verdict"):
        claimed = str(run["verdict"])
        if claimed in {
            "UNVERIFIED/WRONG",
            "UNVERIFIED/HYPOTHESIS_VIOLATION",
            "UNVERIFIED/CIRCULAR",
            "UNVERIFIED/MISMATCH",
        }:
            return "UNVERIFIED/SUSPECTED"
        return claimed
    if any(f.get("verdict") == "REFUTED" for f in run.get("falsifications", [])):
        return "UNVERIFIED/SUSPECTED"
    # Structural continuation intentionally assumes one or more named failed
    # blocks. Even if the conditional source compiles, it is not a proof of the
    # original theorem and must never enter a VERIFIED class.
    if run.get("structural_mode"):
        return "UNVERIFIED/INCOMPLETE"
    if run.get("compiled"):
        kernel = run.get("kernel_axioms", [])
        custom = [a for a in kernel
                  if a != "sorryAx" and a not in STANDARD_AXIOMS]
        if custom:
            return "VERIFIED MODULO AXIOMS"
        if run.get("kernel_closure_checked") or kernel:
            if run.get("proof_faithfulness") == "alternative-proof":
                return "VERIFIED/ALTERNATIVE-PROOF"
            return "VERIFIED"
        return "COMPILED"
    return "HAS GAPS"


# The contract EVIDENCE ladder (verify-output-contract.md), strongest → weakest.
# `certificate` requires a trusted deterministic checker to validate the
# serialized witness and stamp that fact. Harness execution, an agent-authored
# recheck, or a same-formula replay remains `audit-only`.
# `search-hit` is a per-phase tier (a bare resolve match), not a final tier.
EVIDENCE_LADDER = ("kernel", "certificate", "compile-only", "search-hit",
                   "audit-only", "none")


def evidence_tier(run: dict) -> str:
    """Evidence supporting the top-level verdict, not the strongest artifact."""
    cls = verdict_class(run)
    if cls == "UNVERIFIED/WRONG" and (
        any(is_main_theorem_refutation(r)
            for r in run.get("refutations", []))
    ):
        return "kernel"
    if cls == "UNVERIFIED/WRONG" and has_independent_refutation_certificate(run):
        return "certificate"
    if cls == "UNVERIFIED/PROOF_INVALID" and any(
        r.get("kernel_backed")
        and not r.get("quarantined")
        and r.get("target_scope") == "PROOF_STEP"
        and r.get("finding_kind") == "INVALID_INFERENCE"
        and r.get("premises_satisfied") is True
        and r.get("objects_well_defined") is True
        and r.get("conclusion_negated") is True
        and r.get("statement_faithful") is True
        for r in run.get("refutations", [])
    ):
        return "kernel"
    if cls in {
        "UNVERIFIED/HYPOTHESIS_VIOLATION",
        "UNVERIFIED/MISMATCH",
        "UNVERIFIED/CIRCULAR",
        "UNVERIFIED/SUSPECTED",
    }:
        return "audit-only"
    if run.get("has_sorry_ax"):
        return "kernel"
    if cls.startswith("VERIFIED") or cls == "UNVERIFIED/UNGATED":
        if run.get("compiled") and run.get("kernel_closure_checked"):
            return "kernel"
    if (run.get("structural_trusted_recheck") or {}).get("compiled"):
        return "compile-only"
    if run.get("compiled"):
        return "compile-only"
    if cls.startswith("UNVERIFIED"):
        return "audit-only"
    return "none"


def strongest_artifact_evidence(run: dict) -> str:
    """Strongest artifact anywhere in a run, independent of the verdict.

    This is diagnostic telemetry only.  It must never be substituted for
    :func:`evidence_tier`, which is scoped to the top-level conclusion.
    """
    if any(r.get("kernel_backed") for r in run.get("refutations", [])):
        return "kernel"
    if run.get("compiled") and run.get("kernel_closure_checked"):
        return "kernel"
    if run.get("has_sorry_ax"):
        return "kernel"
    if has_independent_refutation_certificate(run):
        return "certificate"
    if (run.get("structural_trusted_recheck") or {}).get("compiled"):
        return "compile-only"
    if run.get("compiled"):
        return "compile-only"
    return "audit-only" if run.get("refutations") else "none"


def gate_failures(run: dict) -> list[str]:
    """Flaw-hunting gate-coverage gaps for a run record.

    Extends ``driver.finish``'s ``audit_warnings`` computation (ungated
    novel/instantiation blocks, missing/ mismatched back-translations,
    uncovered kernel-backed refutations, uncovered library additions) and adds
    the sealed-triage and workflow-v2 requirements. Independent of whether the
    driver populated ``audit_warnings``, so it also holds for records an
    untrusted agent assembled itself.

    LIMITATION (the W1 headline — carried into W2/W3): this checks the
    PRESENCE of gate records, which are AGENT-AUTHORED. It fail-closes a
    VERIFIED whose record is structurally empty (gates simply not run), but a
    *lying* agent can fabricate ``triage={...}``, a ``PASSED`` falsification it
    never ran, or a ``MATCH`` back-translation it never did, and pass. Real
    enforcement requires the three gates to be EXECUTED BY TRUSTED HARNESS CODE
    with the outcome DERIVED (the model is ``Refutation.kernel_backed`` —
    derived, never asserted), not ingested as an agent label: the W2 server /
    W3 runner must run the falsification compile, the sealed triage call, and
    the back-translation judge itself. Until then this layer is a fail-closed
    backstop, not a guarantee.
    """
    fails: list[str] = []

    # 1. Sealed adversarial triage must have been recorded BY TRUSTED HARNESS
    #    CODE. The provenance stamp (executed_by="harness") is what converts the
    #    gate from attested to trusted-executed: an agent-written triage dict
    #    (the old W1 hole) lacks the stamp and is rejected. The driver defaults
    #    `triage` to {} (not None), so test truthiness, not `is None`.
    triage = run.get("triage")
    if not triage:
        fails.append("no sealed triage recorded")
    elif triage.get("executed_by") != "harness":
        fails.append("triage not harness-executed (agent-attested record rejected)")

    # 2. Every novel/instantiation block (not deliberately skipped) needs a
    #    recorded falsification outcome.
    gated = {f.get("block") for f in run.get("falsifications", [])}
    ungated = [l.get("name") for l in run.get("lemmas", [])
               if l.get("kind") in ("novel", "instantiation")
               and not l.get("skipped") and l.get("name") not in gated]
    if ungated:
        fails.append(f"ungated novel/instantiation block(s): {ungated}")

    # 3. Back-translation coverage of verdict-bearing statements. Only
    #    HARNESS-EXECUTED audits count (same provenance rule as triage); an
    #    agent-written MATCH cannot satisfy the gate.
    harness_bt = [b for b in run.get("backtranslations", [])
                  if b.get("executed_by") == "harness"]
    bt = {b.get("target") for b in harness_bt}
    if run.get("compiled") and "main" not in bt:
        fails.append("assembled main theorem has no harness-executed back-translation")
    for b in harness_bt:
        if b.get("verdict") == "GATE_ERROR":
            # The grader crashed/timed out — fail SAFE (still downgrades), but say
            # so distinctly: this is NOT evidence the formalization is unfaithful.
            fails.append(f"back-translation gate FAILED TO EXECUTE on '{b.get('target')}' "
                         "(grader error, not a proof defect — re-run)")
        elif (b.get("verdict") == "MISMATCH"
              and b.get("purpose") != "proof-step"):
            fails.append(f"back-translation MISMATCH on '{b.get('target')}'")
    for ref in run.get("refutations", []):
        if ref.get("kernel_backed"):
            theorem = ref.get("theorem") or ""
            # Match driver.finish's coverage rule exactly (incl. the dotted
            # suffix form Foo.myThm ~ target 'myThm') so the two never disagree.
            covered = any(
                t in (ref.get("block"), ref.get("theorem"))
                or (theorem and theorem.endswith(f".{t}"))
                for t in bt)
            if not covered:
                fails.append(
                    f"kernel-backed refutation '{ref.get('theorem') or ref.get('block')}'"
                    " has no recorded back-translation")
    for name in run.get("novel_added", []):
        if name not in bt:
            fails.append(f"library addition '{name}' has no recorded back-translation")

    fails.extend(workflow_phase_failures(run))
    return fails


# A PASSED falsification needs MIN_SATISFIED (1000) hyp-satisfying instances or
# it is auto-VACUOUS. Above that it still carries ZERO verification weight, but
# depth is an honesty signal: a PASSED that barely cleared 1000 exercised the
# claim far less than one with millions. Flag PASSED below this robustness floor
# as "shallow" so a BYO user can see a thin flaw-hunt.
SHALLOW_FALSIFY_FLOOR = 10_000


def falsify_summary(run: dict) -> dict:
    """Falsification breakdown for surfacing on the (thin) harness verdict line.

    Returns counts + per-PASSED depth + shallow flags. This is RENDERED, not
    gated: a PASSED carries zero verification weight, so its shallowness is not
    grounds to overturn a kernel-clean verdict — but it MUST be visible, or a
    weak agent's shallow-but-present falsification looks identical to a rigorous
    one on the only surface a BYO user reads."""
    fals = run.get("falsifications", [])
    counts = {"REFUTED": 0, "PASSED": 0, "VACUOUS": 0, "SKIPPED": 0}
    passed_depths: list[tuple[str, int]] = []
    shallow: list[str] = []
    # Provenance: how many falsifications were HARNESS-EXECUTED (trusted, the
    # outcome derived) vs AGENT-ATTESTED (numbers supplied by the untrusted
    # agent). `attested` blocks are listed so a BYO user sees which flaw-hunts
    # rest on the agent's word — the same honesty as the shallow-depth flag.
    attested: list[str] = []
    harness_executed = 0
    for f in fals:
        v = f.get("verdict", "?")
        counts[v] = counts.get(v, 0) + 1
        if f.get("executed_by") == "harness":
            harness_executed += 1
        else:
            attested.append(f.get("block", "?"))
        if v == "PASSED":
            hs = int(f.get("hyp_satisfied", 0))
            passed_depths.append((f.get("block", "?"), hs))
            if hs < SHALLOW_FALSIFY_FLOOR:
                shallow.append(f"{f.get('block', '?')}({hs})")
    return {"counts": counts, "passed_depths": passed_depths, "shallow": shallow,
            "attested": attested, "harness_executed": harness_executed,
            "total": len(fals)}


def enforce(run: dict, strict: bool = True) -> dict:
    """Return the enforced verdict for a run record.

    Result: ``{verdict, base_verdict, downgraded, gate_failures}``. In strict
    mode a VERIFIED-class base verdict with any gate failure becomes
    ``UNVERIFIED/UNGATED``.
    """
    base = verdict_class(run)
    fails = gate_failures(run)
    if strict and base in VERIFIED_CLASS and fails:
        return {"verdict": "UNVERIFIED/UNGATED", "base_verdict": base,
                "downgraded": True, "gate_failures": fails}
    return {"verdict": base, "base_verdict": base,
            "downgraded": False, "gate_failures": fails}
