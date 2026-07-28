from __future__ import annotations

import time
from pathlib import Path

from rlverify.falsify_run import (
    EXAMPLES_DIR,
    SamplerError,
    load_sampler,
    run_sampler,
)
from harness.falsify import generate_sampler_spec

from ..backends.protocol import BackendBundle
from ..confined_python import (
    ConfinedPythonUnavailable,
    UnsafeSampler,
    run_confined_sampler,
)
from ..types import ExecutionStatus, MathStatus, ResolvedInput, ResultCard


def run_falsify(value: ResolvedInput,
                 backend: BackendBundle) -> ResultCard:
    """Run only currently safe falsification modes.

    Model-generated Python remains disabled until the confined Python runner is
    implemented. Bundled samplers are trusted repository assets and provide the
    first prototype's deterministic end-to-end path.
    """
    started = time.monotonic()
    target = Path(value.target).expanduser() if value.target else None
    if target and _is_bundled_sampler(target):
        try:
            report = run_sampler(load_sampler(target), seed=0)
        except (SamplerError, OSError, ImportError, AttributeError) as exc:
            return ResultCard(
                ExecutionStatus.SYSTEM_ERROR,
                MathStatus.UNKNOWN,
                summary=f"Falsification sampler failed: {exc}",
                elapsed_s=time.monotonic() - started,
            )
        if report.verdict == "REFUTED":
            math = MathStatus.REFUTED
            evidence = ["EXACT_CERTIFICATE" if report.reason.startswith("ind|")
                        else "AUDIT"]
            summary = f"Counterexample found for {report.block}."
        elif report.verdict == "PASSED":
            math = MathStatus.NO_COUNTEREXAMPLE
            evidence = ["NONE"]
            summary = (
                "No counterexample was found at the recorded depth. "
                "This is not verification."
            )
        else:
            math = MathStatus.UNKNOWN
            evidence = ["NONE"]
            summary = "The sampled hypotheses were vacuous at this depth."
        details = [
            f"Claim: {report.claim}" if report.claim else "",
            (
                f"Instances: {report.instances}; hypotheses satisfied: "
                f"{report.hyp_satisfied}; violations: {report.violations}"
            ),
        ]
        if report.certificate:
            details.append(f"Witness: {report.certificate}")
        return ResultCard(
            ExecutionStatus.COMPLETED,
            math,
            evidence=evidence,
            summary=summary,
            details=[line for line in details if line],
            elapsed_s=time.monotonic() - started,
            actions=["Check the hypotheses", "Run full verification"],
            raw=report.to_dict() if hasattr(report, "to_dict") else report.__dict__,
        )

    claim = value.claim or value.statement or value.proof
    if not claim.strip():
        return ResultCard(
            ExecutionStatus.SYSTEM_ERROR,
            MathStatus.UNKNOWN,
            summary="No mathematical claim was supplied for falsification.",
        )
    try:
        spec = generate_sampler_spec(claim, backend.call_model)
        report = run_confined_sampler(spec.sampler_code)
    except ConfinedPythonUnavailable as exc:
        return ResultCard(
            ExecutionStatus.COMPLETED,
            MathStatus.UNKNOWN,
            evidence=["NONE"],
            summary=f"{exc}. No mathematical conclusion was drawn.",
            elapsed_s=time.monotonic() - started,
            actions=["Check the hypotheses", "Run full verification"],
        )
    except (UnsafeSampler, RuntimeError) as exc:
        return ResultCard(
            ExecutionStatus.COMPLETED,
            MathStatus.UNKNOWN,
            evidence=["NONE"],
            summary=f"The generated falsification test was rejected: {exc}",
            elapsed_s=time.monotonic() - started,
            actions=["Check the hypotheses", "Try a narrower claim"],
        )

    if report.verdict == "REFUTED":
        math = MathStatus.SUSPECTED
        evidence = ["AUDIT"]
        summary = (
            f"A generated sampler reported a counterexample for {spec.block}; "
            "an independent deterministic checker has not validated it."
        )
    elif report.verdict == "NO_COUNTEREXAMPLE":
        math = MathStatus.NO_COUNTEREXAMPLE
        evidence = ["NONE"]
        summary = (
            "No counterexample was found at the recorded depth. "
            "This is not verification."
        )
    else:
        math = MathStatus.UNKNOWN
        evidence = ["NONE"]
        summary = "The generated samples did not exercise the hypotheses adequately."
    details = [
        f"Claim tested: {spec.claim or claim}",
        (
            f"Instances: {report.instances}; hypotheses satisfied: "
            f"{report.hyp_satisfied}; violations: {report.violations}"
        ),
    ]
    if report.certificate:
        details.append(f"Witness: {report.certificate}")
    return ResultCard(
        ExecutionStatus.COMPLETED,
        math,
        evidence=evidence,
        summary=summary,
        details=details,
        elapsed_s=time.monotonic() - started,
        actions=["Check the hypotheses", "Run full verification"],
        raw=report.__dict__,
    )


def _is_bundled_sampler(path: Path) -> bool:
    try:
        return path.resolve().is_relative_to(EXAMPLES_DIR.resolve())
    except (OSError, ValueError):
        return False
