"""Lean 4 verification via subprocess."""

from __future__ import annotations

import os
import subprocess
import tempfile
import re
import time
from dataclasses import dataclass, field
from functools import lru_cache
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

VERIFY_DIR = ROOT / "rlverify" / ".verify_tmp"
VERIFY_DIR.mkdir(parents=True, exist_ok=True)

LEAN_TIMEOUT = 120


@lru_cache(maxsize=1)
def lean_capabilities() -> dict[str, bool]:
    """Feature-detect optional Lean acceleration/audit capabilities.

    Lean 4.32 introduced experimental incremental header snapshots; the pinned
    4.28 toolchain does not expose them, so callers must fall back cleanly.
    """
    try:
        lean_help = subprocess.run(
            ["lake", "env", "lean", "--help"],
            capture_output=True, text=True, timeout=20, cwd=str(ROOT),
        )
        help_text = lean_help.stdout + lean_help.stderr
    except (OSError, subprocess.TimeoutExpired):
        help_text = ""
    try:
        checker = subprocess.run(
            ["lake", "env", "leanchecker", "--fresh", "RLGeneralization"],
            capture_output=True, text=True, timeout=60, cwd=str(ROOT),
        )
        checker_fresh = checker.returncode == 0
    except (OSError, subprocess.TimeoutExpired):
        checker_fresh = False
    return {
        "json_diagnostics": "--json" in help_text,
        "incremental_headers": (
            "--incr-header-save" in help_text and "--incr-load" in help_text
        ),
        "leanchecker_fresh": checker_fresh,
    }


@dataclass
class LeanResult:
    success: bool
    errors: str = ""
    goals: list[str] = field(default_factory=list)
    elapsed: float = 0.0
    has_sorry: bool = False
    output: str = ""
    sorry_lines: list[int] = field(default_factory=list)
    kernel_rechecked: bool = False


@dataclass
class StructuralAudit:
    """Result of checking proof structure against expectations."""
    has_sorry: bool = False
    axioms: list[str] = field(default_factory=list)
    expected_lemmas: list[str] = field(default_factory=list)
    used_lemmas: list[str] = field(default_factory=list)
    missing_lemmas: list[str] = field(default_factory=list)
    verdict: str = "pass"  # "pass" | "flag"

    def to_dict(self) -> dict:
        return {
            "has_sorry": self.has_sorry,
            "axioms": self.axioms,
            "expected_lemmas": self.expected_lemmas,
            "used_lemmas": self.used_lemmas,
            "missing_lemmas": self.missing_lemmas,
            "verdict": self.verdict,
        }


def verify_lean_code(
    code: str,
    timeout: int = LEAN_TIMEOUT,
    allow_sorry: bool = False,
) -> LeanResult:
    """Write code to a temp file, run Lean, return result.

    With ``allow_sorry=True`` a file whose only defect is `sorry` counts as
    success (used for statement-validity checks where the proof is stubbed).
    """
    import uuid
    tmp = VERIFY_DIR / f"check_{uuid.uuid4().hex[:12]}.lean"
    tmp.write_text(code)
    start = time.monotonic()
    try:
        result = subprocess.run(
            ["lake", "env", "lean", str(tmp)],
            capture_output=True, text=True,
            timeout=timeout, cwd=str(ROOT),
        )
        elapsed = time.monotonic() - start
        combined = (result.stdout + "\n" + result.stderr).strip()
        if result.returncode == 0:
            has_sorry = ("declaration uses 'sorry'" in combined
                         or "declaration uses `sorry`" in combined)
            if has_sorry:
                # Lean prints no goal states for explicit `sorry`; goals are
                # only available on the unsolved-goals error path below.
                return LeanResult(
                    success=allow_sorry,
                    errors="" if allow_sorry else "has sorry",
                    elapsed=elapsed, has_sorry=True,
                    output=combined[:6000],
                    sorry_lines=_sorry_warning_lines(combined),
                )
            return LeanResult(success=True, elapsed=elapsed, output=combined[:6000])
        else:
            lines = [
                l for l in combined.splitlines()
                if "has local changes" not in l
                and "manifest out of date" not in l
            ]
            cleaned = "\n".join(lines)
            return LeanResult(
                success=False,
                errors=cleaned[:3000],
                goals=_extract_goal_blocks(cleaned),
                elapsed=elapsed,
                output=cleaned[:6000],
            )
    except subprocess.TimeoutExpired:
        return LeanResult(
            success=False, errors="timeout",
            elapsed=time.monotonic() - start,
        )
    finally:
        tmp.unlink(missing_ok=True)


_DIAGNOSTIC_RE = re.compile(r"^\S.*?:\d+:\d+:\s+(error|warning|info):")

_SORRY_WARN_RE = re.compile(r":(\d+):\d+:\s+warning: declaration uses [`']sorry[`']")


def _sorry_warning_lines(output: str) -> list[int]:
    """1-based source line numbers of `declaration uses sorry` warnings.

    Lean anchors the warning at the declaration identifier, so each line
    number points at (or into) the sorried declaration.
    """
    return [int(m.group(1)) for m in _SORRY_WARN_RE.finditer(output)]


def _extract_goal_blocks(output: str) -> list[str]:
    """Extract full goal states from `error: unsolved goals` diagnostics.

    Each diagnostic is followed by the pretty-printed goal context
    (hypotheses and ⊢ lines, possibly several `case` blocks) up to the
    next diagnostic line. Returns one block per unsolved-goals error.
    """
    blocks: list[str] = []
    current: list[str] | None = None
    for line in output.splitlines():
        if _DIAGNOSTIC_RE.match(line):
            if current is not None:
                blocks.append("\n".join(current).strip())
                current = None
            if "unsolved goals" in line:
                current = []
            continue
        if current is not None:
            current.append(line)
    if current is not None:
        blocks.append("\n".join(current).strip())
    return [b for b in blocks if b]


_AXIOM_RE = re.compile(r"^\s*(?:noncomputable\s+)?axiom\s+([A-Za-z_][A-Za-z0-9_'.]*)", re.MULTILINE)


def find_axioms(code: str) -> list[str]:
    """Return names of `axiom` declarations in the code."""
    return _AXIOM_RE.findall(code)


def has_sorry_token(code: str) -> bool:
    """Check for a `sorry` token in the source (word-boundary match)."""
    return re.search(r"\bsorry\b", code) is not None


# ---------------------------------------------------------------------------
# Kernel-level axiom closure (#print axioms)
# ---------------------------------------------------------------------------

#: Axioms every Mathlib-based proof may depend on. Anything else in the
#: closure is either `sorryAx` (a sorry somewhere in the dependency chain,
#: possibly in an imported file) or a custom axiom that weakens the verdict.
#: `Lean.ofReduceBool` / `Lean.trustCompiler` (from `native_decide`) are
#: deliberately NOT whitelisted — they extend the trusted base to the compiler.
STANDARD_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})

# DOTALL + [^\]]* is required: with ≥~5 axioms Lean's pretty-printer wraps
# the list across lines. Axiom order in the output is nondeterministic —
# classify by set membership, never by position.
_AXIOM_DEP_RE = re.compile(
    r"'(?P<name>[^']+)'\s+depends on axioms:\s*\[(?P<axioms>[^\]]*)\]", re.DOTALL)
_AXIOM_NONE_RE = re.compile(r"'(?P<name>[^']+)'\s+does not depend on any axioms")


@dataclass
class AxiomClosure:
    """Kernel-reported axiom closure of one theorem.

    ``ok=False`` means the check did not run or did not parse — callers must
    fail closed (treat as unverified), never as a pass.
    """
    theorem: str
    ok: bool
    axioms: list[str] = field(default_factory=list)
    standard: list[str] = field(default_factory=list)
    custom: list[str] = field(default_factory=list)
    has_sorry_ax: bool = False
    error: str = ""
    # Populated by subprocess-backed checks so callers can reuse the same Lean
    # invocation for compilation and closure audit. Omitted from to_dict()
    # because it is execution detail, not certificate evidence.
    compile_result: LeanResult | None = field(default=None, repr=False)

    def to_dict(self) -> dict:
        return {
            "theorem": self.theorem,
            "ok": self.ok,
            "axioms": self.axioms,
            "custom": self.custom,
            "has_sorry_ax": self.has_sorry_ax,
            "error": self.error,
        }


def _parse_axiom_closure(output: str, name: str) -> list[str] | None:
    """Extract the axiom list `#print axioms <name>` printed, or None."""
    for m in _AXIOM_DEP_RE.finditer(output):
        if m.group("name") == name:
            return [a.strip() for a in m.group("axioms").split(",") if a.strip()]
    for m in _AXIOM_NONE_RE.finditer(output):
        if m.group("name") == name:
            return []
    return None


def _classify_closure(theorem: str, axioms: list[str]) -> AxiomClosure:
    closure = AxiomClosure(theorem=theorem, ok=True, axioms=list(axioms))
    for a in axioms:
        if a == "sorryAx":
            closure.has_sorry_ax = True
        elif a in STANDARD_AXIOMS:
            closure.standard.append(a)
        else:
            closure.custom.append(a)
    return closure


def check_axiom_closure(
    code: str,
    theorem_name: str,
    timeout: int = LEAN_TIMEOUT,
) -> AxiomClosure:
    """Kernel-level audit: append `#print axioms <name>` and parse the closure.

    Unlike the regex checks, this sees through imports: a theorem proven
    from a sorried lemma in another module reports `sorryAx` here while
    showing a clean source file and exit code 0.

    Runs its own subprocess (NOT verify_lean_code, which returns early on
    the sorry warning before the closure line could be read). A file with
    sorry exits 0, so output is parsed regardless of return code.
    """
    return check_axiom_closures(code, [theorem_name], timeout)[theorem_name]


def check_axiom_closures(
    code: str,
    theorem_names: list[str],
    timeout: int = LEAN_TIMEOUT,
) -> dict[str, AxiomClosure]:
    """Compile once and audit one or more declarations' kernel closures.

    A nonzero Lean exit is always a failed audit, even if an independent later
    ``#print axioms`` happened to emit parseable output.  This closes a subtle
    fail-open bug in the former single-theorem implementation.
    """
    names = list(dict.fromkeys(str(name) for name in theorem_names if name))
    if not names:
        return {}
    import uuid
    commands = "\n".join(f"#print axioms {name}" for name in names)
    augmented = code.rstrip() + f"\n\n{commands}\n"
    tmp = VERIFY_DIR / f"axioms_{uuid.uuid4().hex[:12]}.lean"
    olean = tmp.with_suffix(".olean")
    ilean = tmp.with_suffix(".ilean")
    tmp.write_text(augmented)
    started = time.monotonic()
    checker_error = ""
    checker_ok = False
    try:
        lean_argv = ["lake", "env", "lean"]
        fresh_recheck = (
            os.environ.get("RLVERIFY_LEANCHECKER_FRESH", "0") == "1"
        )
        if fresh_recheck:
            lean_argv.extend(["-o", str(olean)])
        lean_argv.append(str(tmp))
        result = subprocess.run(
            lean_argv,
            capture_output=True, text=True,
            timeout=timeout, cwd=str(ROOT),
        )
        if fresh_recheck and result.returncode == 0:
            checker_env = dict(os.environ)
            checker_env["LEAN_PATH"] = os.pathsep.join(filter(None, [
                str(VERIFY_DIR), checker_env.get("LEAN_PATH", "")
            ]))
            checker = subprocess.run(
                ["lake", "env", "leanchecker", "--fresh", tmp.stem],
                capture_output=True,
                text=True,
                timeout=timeout,
                cwd=str(ROOT),
                env=checker_env,
            )
            checker_ok = checker.returncode == 0
            if not checker_ok:
                checker_error = (
                    checker.stdout + "\n" + checker.stderr
                ).strip()[-1500:]
    except subprocess.TimeoutExpired:
        compile_result = LeanResult(
            success=False, errors="timeout",
            elapsed=time.monotonic() - started,
        )
        return {
            name: AxiomClosure(
                theorem=name, ok=False, error="timeout",
                compile_result=compile_result,
            )
            for name in names
        }
    finally:
        tmp.unlink(missing_ok=True)
        olean.unlink(missing_ok=True)
        ilean.unlink(missing_ok=True)

    combined = (result.stdout + "\n" + result.stderr).strip()
    elapsed = time.monotonic() - started
    has_sorry = (
        "declaration uses 'sorry'" in combined
        or "declaration uses `sorry`" in combined
    )
    if result.returncode == 0 and not has_sorry:
        compile_result = LeanResult(
            success=not checker_error,
            errors=checker_error,
            elapsed=elapsed,
            output=combined[:6000],
            kernel_rechecked=checker_ok,
        )
    else:
        error = (
            "has sorry" if result.returncode == 0 and has_sorry
            else "\n".join(
                line for line in combined.splitlines()
                if "has local changes" not in line
                and "manifest out of date" not in line
            )[:3000]
        )
        compile_result = LeanResult(
            success=False,
            errors=error,
            goals=_extract_goal_blocks(error),
            elapsed=elapsed,
            has_sorry=has_sorry,
            output=combined[:6000],
            sorry_lines=_sorry_warning_lines(combined),
        )

    closures: dict[str, AxiomClosure] = {}
    for name in names:
        parsed = _parse_axiom_closure(combined, name)
        if result.returncode != 0 or checker_error:
            closures[name] = AxiomClosure(
                theorem=name,
                ok=False,
                error=compile_result.errors[-1500:] or "Lean exited nonzero",
                compile_result=compile_result,
            )
        elif parsed is None:
            closures[name] = AxiomClosure(
                theorem=name,
                ok=False,
                error=combined[-1500:] or "no #print axioms output",
                compile_result=compile_result,
            )
        else:
            closure = _classify_closure(name, parsed)
            closure.compile_result = compile_result
            closures[name] = closure
    return closures


def classify_lean_error(errors: str, goals: list[str] | None = None) -> str:
    """Build structured error context for retry prompts."""
    if not errors:
        return ""

    if errors == "timeout":
        return (
            "Previous attempt timed out (>120s). "
            "Simplify the proof: avoid heavy `simp` or `decide`, "
            "prefer `exact`, `apply`, `linarith`, `omega`."
        )

    if errors == "has sorry":
        return (
            "Previous attempt used `sorry` — proof is incomplete. "
            "Replace every sorry with a real proof of the remaining goal."
        )

    first_line = errors.split("\n")[0]

    if "unsolved goals" in errors:
        parts = ["Previous attempt left unsolved goals:"]
        for g in (goals or [])[:5]:
            parts.append(g)
            parts.append("")
        parts.append(
            "Keep the working tactic prefix and close the remaining "
            "goals listed above."
        )
        return "\n".join(parts)

    if "unknown identifier" in errors:
        match = re.search(r"unknown identifier '([^']+)'", errors)
        ident = match.group(1) if match else "?"
        return (
            f"Previous attempt failed: unknown identifier '{ident}'.\n"
            f"Check the available library declarations above and use exact names.\n"
            f"If it's an import issue, ensure the correct module is imported."
        )

    if "type mismatch" in errors:
        return (
            f"Previous attempt failed: type mismatch.\n"
            f"{first_line}\n"
            f"Ensure argument types match exactly. "
            f"Use coercions (e.g. Nat.cast, Real.ofNat) if needed."
        )

    if "tactic" in errors and "failed" in errors:
        return (
            f"Previous attempt: tactic failed.\n"
            f"{first_line}\n"
            f"Try alternative tactics: `linarith` for inequalities, "
            f"`omega` for nat/int, `ring` for algebra, `norm_num` for numerics."
        )

    return f"Previous attempt failed:\n{errors[:800]}\nFix the errors."


def make_verify_file(
    imports: list[str],
    theorem_code: str,
) -> str:
    """Build a complete Lean 4 file for verification."""
    import_block = "\n".join(f"import {m}" for m in imports)
    return f"""{import_block}

open Finset BigOperators

noncomputable section

{theorem_code}
"""
