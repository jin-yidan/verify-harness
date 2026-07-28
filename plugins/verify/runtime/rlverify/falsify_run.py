"""Run a falsification sampler from the command line — no Lean, no agent.

The falsification gate (``rlverify.falsify``) is pure Python: it searches for a
numeric counterexample to a single claim and, on a hit, re-verifies it on an
independent path. This module drives a *sampler file* through that gate and
prints the standard result card, so a fresh clone gets a real, deterministic,
kernel-independent result before installing Lean or an agent.

A **sampler** is a plain ``.py`` file exposing (claim: ``lhs(inst) <= rhs(inst)``):

    BLOCK = "block_name"
    CLAIM = "the inequality, verbatim"
    EXACT = False          # True => reverify in exact rational arithmetic
    N     = 200_000        # samples to draw (override with --n)
    TOL   = 1e-9           # relative tolerance (override with --tol)

    def sample(rng):       # rng is a stdlib random.Random
        return {...}       # one instance as a dict of plain numbers
    def hypotheses(inst):  # -> bool: does this instance satisfy the claim's hyps?
        ...
    def lhs(inst): ...     # pure Python (math, no numpy) so reverify is independent
    def rhs(inst): ...

    # OPTIONAL — an INDEPENDENT re-check of a counterexample (strongly advised):
    def recheck(inst): ... # -> bool: True iff this instance *violates* the claim,
                           # recomputed by a SEPARATE formula (e.g. the squared
                           # form, avoiding the sqrt in lhs/rhs).

Why ``recheck`` matters: ``reverify`` re-substitutes the certificate into the
*same* ``lhs``/``rhs`` used during the search, so on its own it only guards
against search-loop / accumulator-state bugs — NOT against a bug in the
``lhs``/``rhs`` formula itself. A counterexample confirmed by an independent
``recheck`` (or by exact ``lhs_exact``/``rhs_exact``) is genuinely
cross-validated; without one the card says so plainly rather than overclaiming.

Outcomes follow the gate's contract: REFUTED (re-verified counterexample —
load-bearing), PASSED (no counterexample in >= 1000 instances — zero weight),
VACUOUS (hypotheses rarely satisfied), SKIPPED (not for the runner; that is an
agent judgement that a claim is not numerically checkable).
"""

from __future__ import annotations

import importlib.util
import math
import random
from pathlib import Path

from .falsify import DEFAULT_TOL, MIN_SATISFIED, FalsifyReport, reverify, violates

EXAMPLES_DIR = Path(__file__).parent / "falsify_examples"


class SamplerError(RuntimeError):
    """A sampler callable crashed or produced a non-finite value.

    Raised instead of letting a raw traceback escape so the CLI can report
    "your sampler is broken on this input" cleanly (and show the input).
    """


def list_examples() -> list[str]:
    """Names of the bundled sampler examples (without the .py)."""
    if not EXAMPLES_DIR.is_dir():
        return []
    return sorted(p.stem for p in EXAMPLES_DIR.glob("*.py")
                  if not p.stem.startswith("_"))


def load_sampler(path: str | Path):
    """Import a sampler module from a file path."""
    path = Path(path)
    if not path.exists():
        raise FileNotFoundError(f"sampler file not found: {path}")
    spec = importlib.util.spec_from_file_location(f"_sampler_{path.stem}", path)
    if spec is None or spec.loader is None:
        raise ImportError(f"could not load sampler: {path}")
    mod = importlib.util.module_from_spec(spec)
    try:
        spec.loader.exec_module(mod)
    except KeyboardInterrupt:
        raise
    except BaseException as e:  # noqa: BLE001 — sampler top level is untrusted code
        raise SamplerError(
            f"sampler {path.name} failed at import: {type(e).__name__}: {e}"
        ) from e
    for attr in ("sample", "hypotheses", "lhs", "rhs"):
        if not callable(getattr(mod, attr, None)):
            raise AttributeError(f"sampler {path.name} is missing a callable '{attr}'")
    return mod


def _eval(fn, inst, name: str) -> float:
    """Call a numeric sampler hook, guarding against crashes and non-finite output."""
    try:
        v = float(fn(inst))
    except SamplerError:
        raise
    except Exception as e:  # noqa: BLE001 — surface ANY sampler bug cleanly
        raise SamplerError(f"{name}({inst}) raised {type(e).__name__}: {e}") from e
    if not math.isfinite(v):
        raise SamplerError(
            f"{name}({inst}) returned a non-finite value ({v}); fix the formula "
            "or tighten hypotheses() so this input is excluded")
    return v


def _confirm(mod, cert: dict, tol: float, exact: bool) -> tuple[bool, bool, str]:
    """Re-verify a candidate counterexample.

    Returns ``(confirmed, independent, note)``. When the sampler supplies an
    INDEPENDENT path (``recheck`` or ``lhs_exact``/``rhs_exact``) the certificate
    is cross-validated against a separate formula; otherwise it falls back to
    re-substituting the SAME ``lhs``/``rhs`` (which only guards against
    search/state bugs) and ``note`` says so plainly.
    """
    recheck = getattr(mod, "recheck", None)
    if callable(recheck):
        try:
            confirmed = bool(recheck(cert))
        except Exception as e:  # noqa: BLE001
            raise SamplerError(
                f"recheck({cert}) raised {type(e).__name__}: {e}") from e
        return confirmed, True, "independent recheck() (separate formula)"

    lhs_x, rhs_x = getattr(mod, "lhs_exact", None), getattr(mod, "rhs_exact", None)
    if callable(lhs_x) and callable(rhs_x):
        confirmed = reverify(cert, lhs_x, rhs_x, tolerance=tol, exact=exact)
        return confirmed, True, "independent lhs_exact/rhs_exact"

    confirmed = reverify(cert, mod.lhs, mod.rhs, tolerance=tol, exact=exact)
    return (confirmed, False,
            "re-substituted SAME lhs/rhs — guards search/state bugs only, "
            "NOT the lhs/rhs formula (add recheck() to cross-validate)")


def run_sampler(mod, n: int | None = None, seed: int = 0,
                tol: float | None = None) -> FalsifyReport:
    """Drive a sampler module through the falsification gate."""
    N = int(n if n is not None else getattr(mod, "N", 200_000))
    TOL = float(tol if tol is not None else getattr(mod, "TOL", DEFAULT_TOL))
    if N <= 0:
        raise SamplerError("n must be a positive integer")
    if not math.isfinite(TOL) or TOL <= 0:
        raise SamplerError("tol must be a finite positive number")
    exact = bool(getattr(mod, "EXACT", False))
    block = getattr(mod, "BLOCK", getattr(mod, "__name__", "block"))
    claim = getattr(mod, "CLAIM", "")

    rng = random.Random(seed)
    sampled = satisfied = violations = 0
    worst = None
    max_gap = 0.0
    for _ in range(N):
        try:
            inst = mod.sample(rng)
        except Exception as e:  # noqa: BLE001
            raise SamplerError(f"sample() raised {type(e).__name__}: {e}") from e
        sampled += 1
        try:
            satisfies = bool(mod.hypotheses(inst))
        except Exception as e:  # noqa: BLE001
            raise SamplerError(
                f"hypotheses({inst}) raised {type(e).__name__}: {e}") from e
        if not satisfies:
            continue
        satisfied += 1
        lhs_v, rhs_v = _eval(mod.lhs, inst, "lhs"), _eval(mod.rhs, inst, "rhs")
        if violates(lhs_v, rhs_v, TOL):
            violations += 1
            gap = lhs_v - rhs_v
            if worst is None or gap > max_gap:
                worst, max_gap = inst, gap

    # A violation only becomes REFUTED if it survives re-verification.
    if worst is not None:
        confirmed, independent, note = _confirm(mod, worst, TOL, exact)
        if confirmed:
            arith = "exact rational" if exact else "float"
            return FalsifyReport(
                block=block, verdict="REFUTED", claim=claim,
                instances=sampled, hyp_satisfied=satisfied,
                violations=violations, max_violation=max_gap,
                tolerance=TOL, certificate=worst, executed_by="harness",
                # reason carries the re-check provenance for the card (free text
                # on a REFUTED report); machine-parseable prefix "ind|dep".
                reason=f"{'ind' if independent else 'dep'}|{arith}|{note}")
    verdict = "PASSED" if satisfied >= MIN_SATISFIED else "VACUOUS"
    return FalsifyReport(block=block, verdict=verdict, claim=claim,
                         instances=sampled, hyp_satisfied=satisfied,
                         violations=violations, max_violation=max_gap,
                         tolerance=TOL, certificate=None, executed_by="harness")


_EVIDENCE = {"PASSED": "none", "VACUOUS": "none", "SKIPPED": "none"}
_WEIGHT = {"PASSED": "zero-weight", "VACUOUS": "zero-weight",
           "SKIPPED": "prioritization-only"}
_NEXT = {
    "PASSED": "/verify-sketch or /verify-discharge (a PASS proves nothing)",
    "VACUOUS": "investigate hypothesis satisfiability, then re-sample",
    "SKIPPED": "—",
}


def _fmt(v) -> str:
    if isinstance(v, float):
        return f"{v:.6g}"
    return str(v)


def render_card(report: FalsifyReport, seed: int | None = None) -> str:
    """The standard IDE-clear result card (fenced-block style)."""
    r = report
    certified = bool(
        r.verdict == "REFUTED"
        and r.certificate_validated
        and r.independent_checker == "deterministic"
    )
    evidence = (
        "certificate" if certified
        else "audit-only" if r.verdict == "REFUTED"
        else _EVIDENCE.get(r.verdict, "none")
    )
    weight = (
        "load-bearing" if certified
        else "prioritization-only" if r.verdict == "REFUTED"
        else _WEIGHT.get(r.verdict, "zero-weight")
    )
    lines = [
        f"/verify-falsify · {r.block}",
        f"OUTCOME      {r.verdict}",
        f"EVIDENCE     {evidence}",
        f"WEIGHT       {weight}",
        f"EXECUTED_BY  {r.executed_by}",
    ]
    if r.claim:
        lines.append(f"DETAIL       claim: {r.claim}")
    if r.verdict == "REFUTED":
        lines.append(f"             max gap {r.max_violation:.6g}")
    sampling = (f"SAMPLING     instances {r.instances} · hyp_satisfied "
                f"{r.hyp_satisfied} · violations {r.violations}")
    if seed is not None:
        sampling += f" · seed {seed}"
    lines.append(sampling)
    if r.certificate:
        cert = "  ".join(f"{k}={_fmt(v)}" for k, v in r.certificate.items())
        lines.append(f"CERTIFICATE  {cert}")
    else:
        lines.append("CERTIFICATE  —")
    # REFUTED carries re-check provenance in reason as "ind|dep|<arith>|<note>".
    if r.verdict == "REFUTED" and r.reason and "|" in r.reason:
        kind, arith, note = r.reason.split("|", 2)
        cross = "cross-validated" if kind == "ind" else "NOT cross-validated"
        lines.append(f"RECHECK      {cross} ({arith}) — {note}")
    if r.verdict == "VACUOUS" and r.reason:
        lines.append(f"REASON       {r.reason}")
    next_step = (
        "—   (independently certified refutation; skip dependents)"
        if certified
        else ("independently validate the witness or build a kernel refutation"
              if r.verdict == "REFUTED"
              else _NEXT.get(r.verdict, "—"))
    )
    lines.append(f"NEXT         {next_step}")
    return "\n".join(lines)
