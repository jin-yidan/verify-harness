#!/usr/bin/env python3
"""LIVE demo — a FLAWED RL proof is caught: the harness reaches UNVERIFIED/WRONG.

This is the tool's most convincing output: a plausible-looking proof of a FALSE
RL claim. A fluent reader (or a raw LLM) can be talked into accepting it; the
pipeline refuses and — when the counterexample is finitely checkable — backs the
verdict with a compiled Lean counterexample.

The claim below INVERTS a real fact. The UCB1 confidence radius √(2 ln t / s)
*decreases* as an arm is played more (more data ⇒ less uncertainty — the reason
UCB converges). This "theorem" claims the opposite, that it increases. It is
FALSE: with 2 ln t = 4, r(1) = √4 = 2 but r(4) = √1 = 1, so r(1) ≤ r(4) fails.
The "proof" hides the error in a confident-sounding story about exploitation.

Prerequisites + run: see live_verified.py (same setup).
  python harness/examples/live_wrong.py
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))

from harness.runner import run_verification, launch_agent
from harness.backends import get_backend
from harness.examples._demo_util import quiet, save_certificate, print_result, run_with_retry

STATEMENT = (
    "Theorem (false). Fix a round t with t ≥ 1 and let the UCB1 exploration "
    "bonus after s plays be r(s) = √(2 ln t / s). Then r is nondecreasing in the "
    "play count: for all real s, s' with 1 ≤ s ≤ s', we have r(s) ≤ r(s')."
)
PROOF = (
    "Proof. The exploration bonus rewards arms the learner commits to: as an arm "
    "is played more, the algorithm has invested more in it, so its accumulated "
    "bonus r(s) can only grow. Hence whenever s ≤ s', the arm played s' times "
    "carries at least as large a bonus, r(s) ≤ r(s'). ∎"
)
NL_CLAIM = (
    "For a fixed round t ≥ 1, the UCB1 confidence radius √(2 ln t / s) is "
    "nondecreasing in the play count s."
)

if __name__ == "__main__":
    print(f"\nVerifying:  {STATEMENT}")

    def attempt():
        with quiet("verifying with your Claude account"):
            return run_verification(
                "demo_ucb_radius_false",
                statement=STATEMENT,
                proof=PROOF,
                call_model=get_backend("claude", model="opus"),
                agent_drive=launch_agent(backend="claude", model="opus"),
                nl_claim=NL_CLAIM,
            )

    out = run_with_retry(attempt)  # retry once if the agent stalls (e.g. bad import)
    # On a kernel-backed WRONG, the saved certificate is the compiled COUNTEREXAMPLE;
    # the actual counterexample is shown in the explanation panel, read from the record.
    cert = save_certificate(out)
    print_result(out, expect="UNVERIFIED/WRONG", cert=cert)
