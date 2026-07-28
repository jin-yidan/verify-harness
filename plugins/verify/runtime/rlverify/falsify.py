"""Numeric falsification gate: cheap counterexample search before formalizing.

A found counterexample is an audit finding until a trusted, independent
checker validates the serialized witness.  Formalization is the most expensive
way to discover a claim is false, but cheap execution must not be promoted into
mathematical refutation merely because agent-authored code reproduced itself.
The contract here keeps the gate honest:

- A PASSED verdict carries ZERO verification weight ("no counterexample in
  N instances", never "numerically verified").
- REFUTED is load-bearing only when ``certificate_validated`` is true and
  ``independent_checker`` names the trusted deterministic checker.
- PASSED requires ≥ MIN_SATISFIED hypothesis-satisfying instances, otherwise
  the verdict is forced to VACUOUS (the sampler never exercised the claim —
  also a signal the hypotheses may be contradictory).
- REFUTED requires a certificate that was re-verified by ``reverify`` — an
  independent pure-Python substitution, a separate code path from whatever
  (typically numpy-vectorized) sampler found it.
- Violation tests are relative-tolerance: exact-equality cases generate
  ~1e-15 float noise; a bare ``> 0`` test is forbidden.

The actual samplers are ad-hoc per claim (written by the verifying agent,
typically in /tmp); this module provides the report contract, the violation
test, and the certificate re-check.
"""

from __future__ import annotations

import math
from dataclasses import asdict, dataclass, field
from fractions import Fraction
from numbers import Real
from typing import Callable

#: Minimum hypothesis-satisfying instances for a PASSED verdict.
MIN_SATISFIED = 1000

DEFAULT_TOL = 1e-9

VERDICTS = ("REFUTED", "PASSED", "VACUOUS", "SKIPPED")


@dataclass
class FalsifyReport:
    """Outcome of a falsification run for one building block."""
    block: str
    verdict: str                      # REFUTED | PASSED | VACUOUS | SKIPPED
    claim: str = ""                   # the inequality actually checked, verbatim
    instances: int = 0
    hyp_satisfied: int = 0
    violations: int = 0
    max_violation: float = 0.0
    tolerance: float = DEFAULT_TOL
    certificate: dict | None = None   # re-verified counterexample inputs
    reason: str = ""                  # for SKIPPED / VACUOUS
    # Provenance, mirroring the triage/back-translation trust model: "agent" =
    # the numbers were SUPPLIED by the (untrusted) agent and are attested, not
    # verified; "harness" = the harness EXECUTED the falsification and DERIVED
    # the outcome. Only "harness" is trustworthy. Surfaced on the verdict line so
    # an attested flaw-hunt is never mistaken for an executed one.
    executed_by: str = "agent"
    # Set only by a trusted parent after independently validating the serialized
    # witness. Merely executing an agent-authored ``recheck`` function does not
    # satisfy this contract.
    certificate_validated: bool = False
    independent_checker: str = ""

    def __post_init__(self) -> None:
        if self.verdict not in VERDICTS:
            raise ValueError(f"verdict must be one of {VERDICTS}: {self.verdict!r}")
        if self.verdict == "PASSED" and self.hyp_satisfied < MIN_SATISFIED:
            self.verdict = "VACUOUS"
            self.reason = (
                f"only {self.hyp_satisfied} hypothesis-satisfying instances "
                f"(< {MIN_SATISFIED}) — claim never exercised; "
                "investigate hypothesis satisfiability"
            )
        if self.verdict == "REFUTED" and self.certificate is None:
            raise ValueError(
                "REFUTED requires a certificate re-verified with reverify() — "
                "an unreproduced violation may be a sampler bug"
            )

    def to_dict(self) -> dict:
        return asdict(self)

    def summary(self) -> str:
        if self.verdict == "REFUTED":
            strength = (
                "independently validated"
                if self.certificate_validated
                and self.independent_checker == "deterministic"
                else "audit-only candidate"
            )
            return (f"REFUTED — {strength}, gap {self.max_violation:.3g}: "
                    f"{self.certificate}")
        if self.verdict == "PASSED":
            return (f"PASSED — no counterexample in {self.hyp_satisfied} "
                    f"hypothesis-satisfying instances (zero verification weight)")
        return f"{self.verdict} — {self.reason}"


def violates(lhs: float, rhs: float, tolerance: float = DEFAULT_TOL) -> bool:
    """Relative-tolerance violation test for the claim ``lhs ≤ rhs``."""
    return (lhs - rhs) > tolerance * max(1.0, abs(rhs))


def _to_fraction(value):
    if isinstance(value, Fraction):
        return value
    if isinstance(value, bool):
        return value
    if isinstance(value, Real):
        return Fraction(value)  # exact binary representation of the float
    if isinstance(value, (list, tuple)):
        return type(value)(_to_fraction(v) for v in value)
    return value


def reverify(
    certificate: dict,
    lhs_fn: Callable[[dict], object],
    rhs_fn: Callable[[dict], object],
    tolerance: float = DEFAULT_TOL,
    exact: bool = False,
) -> bool:
    """Independently re-check a counterexample by direct substitution.

    ``lhs_fn``/``rhs_fn`` take the certificate dict and recompute both sides
    in pure Python (math.*, no numpy) — a separate code path from the
    vectorized sampler that found the violation.

    With ``exact=True`` all numeric certificate values are converted to
    ``Fraction`` and the comparison is exact (only valid when both sides are
    rational arithmetic — no exp/log/sqrt).
    """
    if exact:
        cert = {k: _to_fraction(v) for k, v in certificate.items()}
        return lhs_fn(cert) > rhs_fn(cert)
    lhs = float(lhs_fn(certificate))
    rhs = float(rhs_fn(certificate))
    if math.isnan(lhs) or math.isnan(rhs):
        return False
    return violates(lhs, rhs, tolerance)


# ---------------------------------------------------------------------------
# Exact enumeration for high-probability claims (finite-DP mold)
# ---------------------------------------------------------------------------
#
# The standard SKIP rule exempts high-probability claims from the gate — but
# claims of the form
#
#     P( ∃ arm i, ∃ t ≤ m :  |empirical mean of first t samples − μ_i| > r(t) )
#
# with finitely-valued rewards (Bernoulli WLOG for [0,1] refutation purposes)
# are EXACTLY computable: per-arm dynamic programming over (t, S_t), arms
# independent. If the exact failure probability exceeds the claimed δ for a
# concrete instance, the claim is REFUTED with an all-rational certificate.
#
# Soundness obligation (the one step the DP cannot check): the finitized
# event must be a SUBSET of the claimed bad event — e.g. restrict to the
# m = ⌊T/K⌋ phases the algorithm completes deterministically. The verifying
# agent must justify the subset relation in the report.

def exp_series_exceeds(x: Fraction, target: Fraction, terms: int = 60) -> bool:
    """Certify ``x > ln(target)`` in exact rational arithmetic.

    Uses the positive partial sum of the exponential series: for x ≥ 0,
    ``sum_{k<terms} x^k/k! < e^x``, so partial-sum > target ⟹ e^x > target
    ⟹ x > ln(target). One-sided and conservative — returning False means
    "not certified", never "false". Lets an irrational threshold like
    L = ln(2K/δ) enter a rational certificate via a rational upper bound
    L_up with exp_series_exceeds(L_up, 2K/δ).
    """
    x = Fraction(x)
    target = Fraction(target)
    if x < 0:
        raise ValueError("exp_series_exceeds requires x >= 0")
    term = Fraction(1)
    total = Fraction(1)
    for k in range(1, terms):
        term = term * x / k
        total += term
        if total > target:
            return True
    return total > target


def bernoulli_prefix_deviation(
    m: int,
    p: Fraction,
    violating: Callable[[int, int], bool],
) -> Fraction:
    """Exact ``P(∃ t ≤ m : violating(t, S_t))`` for Bernoulli(p) prefix sums.

    ``S_t`` is the number of successes in the first ``t`` i.i.d. Bernoulli(p)
    draws. Pure-integer DP over surviving (never-yet-violating) paths —
    suitable as the ``reverify`` re-check path (no numpy, no floats).

    ``violating(t, s)`` must be a CERTAIN test: if it errs, it must err
    toward False (under-counting failures), so the returned probability is
    a true lower bound and a refutation stays sound.
    """
    p = Fraction(p)
    if not (0 <= p <= 1):
        raise ValueError("p must be in [0, 1]")
    # alive[s] = P(S_t = s and no violation at any t' <= t)
    alive: dict[int, Fraction] = {0: Fraction(1)}
    dead = Fraction(0)
    for t in range(1, m + 1):
        nxt: dict[int, Fraction] = {}
        for s, prob in alive.items():
            for ds, w in ((1, p), (0, 1 - p)):
                if w == 0:
                    continue
                s2 = s + ds
                nxt[s2] = nxt.get(s2, Fraction(0)) + prob * w
        alive = {}
        for s, prob in nxt.items():
            if violating(t, s):
                dead += prob
            else:
                alive[s] = prob
    return dead
