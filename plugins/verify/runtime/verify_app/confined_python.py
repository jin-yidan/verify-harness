from __future__ import annotations

import ast
import json
import os
import platform
import resource
import shutil
import subprocess
import sys
import tempfile
import textwrap
import time
from dataclasses import dataclass
from pathlib import Path


SANDBOX_EXEC = "/usr/bin/sandbox-exec"
_ALLOWED_IMPORTS = {
    "math", "random", "fractions", "decimal", "statistics",
    "itertools", "functools", "operator",
}
_FORBIDDEN_CALLS = {
    "open", "exec", "eval", "compile", "__import__", "input", "breakpoint",
    "getattr", "setattr", "delattr", "globals", "locals", "vars",
}
_FORBIDDEN_NAMES = {
    "os", "sys", "subprocess", "socket", "pathlib", "shutil", "ctypes",
    "requests", "urllib", "httpx", "pickle", "marshal",
}


class ConfinedPythonUnavailable(RuntimeError):
    pass


class UnsafeSampler(ValueError):
    pass


@dataclass
class ConfinedSamplerReport:
    verdict: str
    instances: int
    hyp_satisfied: int
    violations: int
    certificate: dict | None
    max_violation: float
    cross_validated: bool
    elapsed_s: float


def lint_sampler(code: str) -> list[str]:
    try:
        tree = ast.parse(code)
    except SyntaxError as exc:
        return [f"syntax error: {exc.msg} at line {exc.lineno}"]
    errors: list[str] = []
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            for alias in node.names:
                root = alias.name.split(".", 1)[0]
                if root not in _ALLOWED_IMPORTS:
                    errors.append(f"import {alias.name!r} is not allowed")
        elif isinstance(node, ast.ImportFrom):
            root = (node.module or "").split(".", 1)[0]
            if root not in _ALLOWED_IMPORTS:
                errors.append(f"import from {node.module!r} is not allowed")
        elif isinstance(node, ast.Name) and (
            node.id in _FORBIDDEN_NAMES or node.id.startswith("__")
        ):
            errors.append(f"name {node.id!r} is not allowed")
        elif isinstance(node, ast.Call):
            if isinstance(node.func, ast.Name) and node.func.id in _FORBIDDEN_CALLS:
                errors.append(f"call {node.func.id!r} is not allowed")
        elif isinstance(node, ast.Attribute) and node.attr.startswith("__"):
            errors.append(f"dunder attribute {node.attr!r} is not allowed")
    return sorted(set(errors))


def run_confined_sampler(code: str, *, n: int = 20_000, seed: int = 0,
                         tolerance: float = 1e-9,
                         timeout_s: int = 20) -> ConfinedSamplerReport:
    errors = lint_sampler(code)
    if errors:
        raise UnsafeSampler("; ".join(errors))
    if platform.system() != "Darwin" or not os.path.exists(SANDBOX_EXEC):
        raise ConfinedPythonUnavailable(
            "model-generated sampler execution is currently validated only on "
            "macOS with sandbox-exec"
        )
    if not 1 <= n <= 200_000:
        raise ValueError("sample count must be between 1 and 200000")
    if not 0 < tolerance < 1:
        raise ValueError("tolerance must be between 0 and 1")

    python = os.path.realpath(sys.executable)
    prefix = os.path.realpath(sys.prefix)
    scratch = Path(os.path.realpath(tempfile.mkdtemp(prefix="verify_sampler_")))
    script = scratch / "sampler.py"
    profile = scratch / "profile.sb"
    script.write_text(_script(code, n=n, seed=seed, tolerance=tolerance))
    profile.write_text(_profile(scratch, python, prefix))
    env = {
        "PATH": "/usr/bin:/bin",
        "HOME": str(scratch),
        "TMPDIR": str(scratch),
        "PYTHONNOUSERSITE": "1",
        "PYTHONHASHSEED": "0",
    }
    try:
        started = time.monotonic()
        try:
            proc = subprocess.run(
                [SANDBOX_EXEC, "-f", str(profile), python, "-I", str(script)],
                cwd=scratch,
                env=env,
                capture_output=True,
                text=True,
                timeout=timeout_s,
                preexec_fn=lambda: _child_setup(max(2, timeout_s - 1)),
            )
        except subprocess.TimeoutExpired as exc:
            raise UnsafeSampler(
                f"sampler exceeded its {timeout_s}s time limit"
            ) from exc
        elapsed = time.monotonic() - started
        if proc.returncode != 0:
            detail = (proc.stderr or proc.stdout).strip()[:1000]
            raise UnsafeSampler(f"sampler failed in confinement: {detail}")
        try:
            value = json.loads(proc.stdout)
        except ValueError as exc:
            raise UnsafeSampler("sampler did not return a valid report") from exc
        return ConfinedSamplerReport(
            verdict=str(value["verdict"]),
            instances=int(value["instances"]),
            hyp_satisfied=int(value["hyp_satisfied"]),
            violations=int(value["violations"]),
            certificate=value.get("certificate"),
            max_violation=float(value.get("max_violation") or 0.0),
            cross_validated=bool(value.get("cross_validated")),
            elapsed_s=elapsed,
        )
    finally:
        shutil.rmtree(scratch, ignore_errors=True)


def _child_setup(cpu_seconds: int) -> None:
    os.setsid()
    try:
        resource.setrlimit(resource.RLIMIT_CPU, (cpu_seconds, cpu_seconds + 1))
    except (OSError, ValueError):
        pass


def _profile(scratch: Path, python: str, prefix: str) -> str:
    home = Path.home()
    return f"""(version 1)
(deny default)
(allow process-fork)
(allow process-exec (literal "{python}"))
(allow sysctl-read)
(allow mach-lookup)
(deny network*)
(allow file-read-metadata)
(allow file-read* (require-all (subpath "/") (require-not (subpath "{home}"))))
(deny file-read* (subpath "/Users"))
(deny file-read* (subpath "/private/etc"))
(deny file-read* (subpath "/private/tmp"))
(deny file-read* (subpath "/private/var"))
(allow file-read* (subpath "{prefix}"))
(allow file-read* (subpath "{scratch}"))
(allow file-write* (subpath "{scratch}") (literal "/dev/null"))
"""


def _script(code: str, *, n: int, seed: int, tolerance: float) -> str:
    runner = f"""
import json as _verify_json
import math as _verify_math
import random as _verify_random

_verify_required = ("sample", "hypotheses", "lhs", "rhs")
for _verify_name in _verify_required:
    if not callable(globals().get(_verify_name)):
        raise RuntimeError("sampler missing callable " + _verify_name)

_verify_rng = _verify_random.Random({seed!r})
_verify_n = {n!r}
_verify_tol = {tolerance!r}
_verify_satisfied = 0
_verify_violations = 0
_verify_worst = None
_verify_gap = 0.0

for _verify_i in range(_verify_n):
    _verify_inst = sample(_verify_rng)
    if not bool(hypotheses(_verify_inst)):
        continue
    _verify_satisfied += 1
    _verify_lhs = float(lhs(_verify_inst))
    _verify_rhs = float(rhs(_verify_inst))
    if not (_verify_math.isfinite(_verify_lhs) and _verify_math.isfinite(_verify_rhs)):
        raise RuntimeError("sampler returned a non-finite value")
    _verify_scale = max(1.0, abs(_verify_lhs), abs(_verify_rhs))
    if _verify_lhs > _verify_rhs + _verify_tol * _verify_scale:
        _verify_violations += 1
        _verify_this_gap = _verify_lhs - _verify_rhs
        if _verify_worst is None or _verify_this_gap > _verify_gap:
            _verify_worst = _verify_inst
            _verify_gap = _verify_this_gap

_verify_cross = False
if _verify_worst is not None:
    _verify_recheck = globals().get("recheck")
    if callable(_verify_recheck):
        _verify_cross = bool(_verify_recheck(_verify_worst))
    else:
        _verify_l2 = float(lhs(_verify_worst))
        _verify_r2 = float(rhs(_verify_worst))
        _verify_scale2 = max(1.0, abs(_verify_l2), abs(_verify_r2))
        _verify_cross = _verify_l2 > _verify_r2 + _verify_tol * _verify_scale2

if _verify_worst is not None and _verify_cross:
    _verify_verdict = "REFUTED"
elif _verify_satisfied >= min(1000, _verify_n):
    _verify_verdict = "NO_COUNTEREXAMPLE"
else:
    _verify_verdict = "VACUOUS"

print(_verify_json.dumps({{
    "verdict": _verify_verdict,
    "instances": _verify_n,
    "hyp_satisfied": _verify_satisfied,
    "violations": _verify_violations,
    "certificate": _verify_worst if _verify_verdict == "REFUTED" else None,
    "max_violation": _verify_gap,
    "cross_validated": _verify_cross,
}}, sort_keys=True))
"""
    return code.rstrip() + "\n\n" + textwrap.dedent(runner)
