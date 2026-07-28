from __future__ import annotations

import time

from harness.triage import sealed_triage

from ..backends.protocol import BackendBundle, BackendError
from ..types import ExecutionStatus, MathStatus, ResolvedInput, ResultCard
from .common import ensure_theorem_input


def run_triage(value: ResolvedInput, backend: BackendBundle) -> ResultCard:
    started = time.monotonic()
    try:
        resolved = ensure_theorem_input(value, backend)
        text = f"Theorem:\n{resolved.statement}\n\nProof:\n{resolved.proof}"
        result = sealed_triage(text, backend.call_model)
    except BackendError as exc:
        return ResultCard(
            ExecutionStatus.SYSTEM_ERROR,
            MathStatus.UNKNOWN,
            evidence=["NONE"],
            summary=str(exc),
            details=[f"Provider error category: {exc.category}"],
            elapsed_s=time.monotonic() - started,
        )
    except Exception as exc:
        return ResultCard(
            ExecutionStatus.SYSTEM_ERROR,
            MathStatus.UNKNOWN,
            evidence=["NONE"],
            summary=f"Triage failed: {type(exc).__name__}: {exc}",
            elapsed_s=time.monotonic() - started,
        )

    suspects = result.get("suspects") or []
    details = [
        f"Step {item.get('step', '?')} ({item.get('severity', 'unknown')}): "
        f"{item.get('suspicion', '')}"
        for item in suspects
        if isinstance(item, dict)
    ]
    partial = bool(result.get("partial"))
    if partial:
        execution = ExecutionStatus.SYSTEM_ERROR
        summary = (
            "Sealed triage could not complete reliably. No correctness "
            "conclusion was drawn."
        )
    elif suspects:
        execution = ExecutionStatus.COMPLETED
        summary = f"Triage found {len(suspects)} suspicious proof step(s)."
    else:
        execution = ExecutionStatus.COMPLETED
        summary = (
            "Triage found no obvious issue. This is prioritization-only and "
            "does not verify the proof."
        )
    return ResultCard(
        execution,
        MathStatus.UNKNOWN,
        evidence=["AUDIT"] if not partial else ["NONE"],
        summary=summary,
        details=details,
        actions=["Falsify a suspicious step", "Audit hypotheses", "Fully verify in Lean"],
        elapsed_s=time.monotonic() - started,
        raw=result,
    )
