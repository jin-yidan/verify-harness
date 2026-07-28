from __future__ import annotations

import time

from harness.hypothesis_audit import sealed_hypothesis_audit
from harness.runner import _make_corpus_lookup
from rlverify.mcp_server import DEFAULT_CORPUS

from ..backends.protocol import BackendBundle, BackendError
from ..types import ExecutionStatus, MathStatus, ResolvedInput, ResultCard
from .common import ensure_theorem_input


def run_hypotheses(value: ResolvedInput,
                   backend: BackendBundle) -> ResultCard:
    started = time.monotonic()
    try:
        resolved = ensure_theorem_input(value, backend)
        audit = sealed_hypothesis_audit(
            resolved.statement,
            resolved.proof,
            backend.call_model,
            lookup=_make_corpus_lookup(str(DEFAULT_CORPUS)),
        )
    except BackendError as exc:
        return ResultCard(
            ExecutionStatus.SYSTEM_ERROR,
            MathStatus.UNKNOWN,
            summary=str(exc),
            details=[f"Provider error category: {exc.category}"],
            elapsed_s=time.monotonic() - started,
        )
    except Exception as exc:
        return ResultCard(
            ExecutionStatus.SYSTEM_ERROR,
            MathStatus.UNKNOWN,
            summary=f"Hypothesis audit failed: {type(exc).__name__}: {exc}",
            elapsed_s=time.monotonic() - started,
        )

    overall = str(audit.get("overall") or "ERROR")
    # This sealed model pass prioritizes suspicious invocation sites; it does
    # not independently prove a violation or cycle.
    math = (
        MathStatus.SUSPECTED
        if overall in {"HYPOTHESIS_VIOLATION", "CIRCULAR", "UNCERTAIN"}
        else MathStatus.UNKNOWN
    )
    findings = audit.get("findings") or []
    details = []
    for finding in findings:
        if not isinstance(finding, dict):
            continue
        missed = finding.get("missed_hypothesis")
        detail = (
            f"{finding.get('outcome', 'UNKNOWN')}: "
            f"{finding.get('site', '?')} → {finding.get('invoked', '?')}"
        )
        if missed:
            detail += f"; missing/violated: {missed}"
        if finding.get("why"):
            detail += f" — {finding['why']}"
        details.append(detail)
    partial = bool(audit.get("partial"))
    if overall == "CLEAR" and not partial:
        summary = (
            "No hypothesis problem was found among the audited invocations. "
            "This does not prove the theorem."
        )
    elif overall == "CLEAR":
        summary = "No problem was found in the resolved subset; the audit was partial."
    elif overall == "ERROR":
        summary = str(audit.get("reason") or "The hypothesis audit could not run.")
    else:
        summary = f"Hypothesis audit outcome: {overall}."
    return ResultCard(
        ExecutionStatus.COMPLETED if overall != "ERROR"
        else ExecutionStatus.SYSTEM_ERROR,
        math,
        evidence=["AUDIT"],
        summary=summary,
        details=details,
        elapsed_s=time.monotonic() - started,
        actions=["Look for a counterexample", "Run full verification"],
        raw=audit,
    )
