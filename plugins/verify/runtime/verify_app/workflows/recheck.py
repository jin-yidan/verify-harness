from __future__ import annotations

import subprocess
import time
from pathlib import Path

from ..types import ExecutionStatus, MathStatus, ResolvedInput, ResultCard


def run_recheck(value: ResolvedInput) -> ResultCard:
    started = time.monotonic()
    if not value.target:
        return ResultCard(
            ExecutionStatus.SYSTEM_ERROR,
            MathStatus.UNKNOWN,
            summary="Reference a saved .lean certificate with @file.",
        )
    path = Path(value.target).expanduser()
    if path.suffix.lower() != ".lean" or not path.exists():
        return ResultCard(
            ExecutionStatus.SYSTEM_ERROR,
            MathStatus.UNKNOWN,
            summary=f"Certificate not found or not a .lean file: {path}",
        )
    try:
        proc = subprocess.run(
            ["lake", "env", "lean", str(path.resolve())],
            capture_output=True,
            text=True,
            timeout=300,
            cwd=Path(__file__).resolve().parents[2],
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        return ResultCard(
            ExecutionStatus.SYSTEM_ERROR,
            MathStatus.UNKNOWN,
            summary=f"Could not run Lean: {exc}",
            elapsed_s=time.monotonic() - started,
        )
    output = (proc.stdout + "\n" + proc.stderr).strip()
    if proc.returncode == 0 and "sorryAx" not in output:
        math = MathStatus.VERIFIED
        summary = "The certificate recompiled successfully without sorryAx."
        evidence = ["LEAN_KERNEL"]
    else:
        math = MathStatus.INCOMPLETE
        summary = "Lean rejected the certificate or reported a forbidden placeholder."
        evidence = ["LEAN_KERNEL"]
    return ResultCard(
        ExecutionStatus.COMPLETED,
        math,
        evidence=evidence,
        summary=summary,
        details=[output[:2000]] if output else [],
        artifacts={"Certificate": str(path.resolve())},
        elapsed_s=time.monotonic() - started,
    )
