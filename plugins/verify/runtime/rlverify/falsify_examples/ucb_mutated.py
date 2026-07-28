"""REFUTED example — the mutated UCB1 threshold (constant 8 -> 4).

The clean UCB1 proof needs s >= 8 ln t / Delta^2 for the contradiction
  2*sqrt(2 ln t / s) <= Delta.
The mutated proof weakens the threshold to s >= 4 ln t / Delta^2, which is
FALSE: at s = ceil(4 ln t / Delta^2) the left side is ~sqrt(2)*Delta > Delta.
The gate finds a concrete counterexample and re-verifies it.
"""

import math

BLOCK = "mutated_step4_contradiction"
CLAIM = "for s >= 4 ln t / Delta^2:  2*sqrt(2 ln t / s) <= Delta"
EXACT = False          # sqrt/log present -> float re-verification
N = 200_000
TOL = 1e-9


def sample(rng):
    Delta = rng.uniform(0.01, 1.0)
    t = rng.randint(2, 10**6)
    s_min = 4 * math.log(t) / Delta**2          # the mutated threshold
    s = math.ceil(s_min) + rng.randint(0, 4)    # any s >= the threshold
    return {"Delta": Delta, "t": t, "s": s}


def hypotheses(inst):
    D, t, s = inst["Delta"], inst["t"], inst["s"]
    return 0 < D <= 1 and t >= 2 and s >= 4 * math.log(t) / D**2


def lhs(inst):
    return 2 * math.sqrt(2 * math.log(inst["t"]) / inst["s"])


def rhs(inst):
    return inst["Delta"]


def recheck(inst):
    """Independent re-check: True iff this instance VIOLATES the claim.

    A SEPARATE formula from lhs/rhs — square both nonnegative sides to drop the
    sqrt: 2*sqrt(2 ln t / s) > Delta  <=>  8 ln t / s > Delta^2. Cross-validates
    the certificate against a different computation (catches a bug in lhs, not
    just in the search loop).
    """
    return 8 * math.log(inst["t"]) / inst["s"] > inst["Delta"] ** 2
