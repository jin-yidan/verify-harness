"""PASSED example — the correct UCB1 threshold (constant 8).

With the honest threshold s >= 8 ln t / Delta^2, the inequality
  2*sqrt(2 ln t / s) <= Delta
holds: 2*sqrt(2 ln t / s) <= 2*sqrt(2 ln t * Delta^2 / (8 ln t)) = Delta.
The gate finds no counterexample.

A PASS carries ZERO verification weight — it means "no counterexample in N
hypothesis-satisfying instances", never "proven". Only the Lean kernel proves it.
"""

import math

BLOCK = "clean_step4_contradiction"
CLAIM = "for s >= 8 ln t / Delta^2:  2*sqrt(2 ln t / s) <= Delta"
EXACT = False
N = 200_000
TOL = 1e-9


def sample(rng):
    Delta = rng.uniform(0.01, 1.0)
    t = rng.randint(2, 10**6)
    s_min = 8 * math.log(t) / Delta**2          # the correct threshold
    s = math.ceil(s_min) + rng.randint(0, 100)
    return {"Delta": Delta, "t": t, "s": s}


def hypotheses(inst):
    D, t, s = inst["Delta"], inst["t"], inst["s"]
    return 0 < D <= 1 and t >= 2 and s >= 8 * math.log(t) / D**2


def lhs(inst):
    return 2 * math.sqrt(2 * math.log(inst["t"]) / inst["s"])


def rhs(inst):
    return inst["Delta"]


def recheck(inst):
    """Independent re-check (squared form, no sqrt): True iff the claim is violated.

    2*sqrt(2 ln t / s) > Delta  <=>  8 ln t / s > Delta^2. (Never fires here —
    the corrected threshold s >= 8 ln t / Delta^2 makes the claim hold.)
    """
    return 8 * math.log(inst["t"]) / inst["s"] > inst["Delta"] ** 2
