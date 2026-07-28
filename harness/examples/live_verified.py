#!/usr/bin/env python3
"""LIVE demo — a CORRECT RL theorem drives the harness to a kernel-closed VERIFIED.

The theorem is a real reinforcement-learning fact: the UCB1 exploration bonus
(confidence radius) shrinks as an arm is played more — the formal reason "more
data ⇒ less uncertainty" that makes UCB converge.

What this shows your audience:
  • a paper-style RL theorem + proof go in as plain text,
  • YOUR Claude account (headless) drives the MCP tools to formalize + prove it,
  • the trusted sealed gates (triage + back-translation) run in harness code,
  • the Lean KERNEL issues the verdict — VERIFIED means the axiom closure is
    ⊆ {propext, Classical.choice, Quot.sound}, reproducible with `lake env lean`.

Prerequisites (see harness/README.md):
  • `claude` CLI authenticated with YOUR account   (claude login)
  • `harness/setup.sh` has been run (Lean built, sandbox checked)
  • macOS (sandbox-exec) — or set RLVERIFY_SANDBOX=0 if you trust the agent
Run:
  python harness/examples/live_verified.py
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))

from harness.runner import run_verification, launch_agent
from harness.backends import get_backend
from harness.examples._demo_util import quiet, save_certificate, print_result, run_with_retry

# The input is INFORMAL math — the way a paper states it. You do NOT write Lean.
STATEMENT = (
    "Theorem (UCB confidence radius is monotone in the play count). "
    "Fix a round t with t ≥ 1, and let the UCB1 exploration bonus after s plays "
    "of an arm be r(s) = √(2 ln t / s). Then r is nonincreasing in the play "
    "count: for all real s, s' with 1 ≤ s ≤ s', we have r(s') ≤ r(s)."
)
PROOF = (
    "Proof. Since t ≥ 1, ln t ≥ 0, so the numerator 2 ln t is nonnegative. "
    "Given 1 ≤ s ≤ s', both s and s' are positive, and dividing the fixed "
    "nonnegative numerator by the larger denominator gives 2 ln t / s' ≤ "
    "2 ln t / s. The square root is monotone, so √(2 ln t / s') ≤ √(2 ln t / s), "
    "i.e. r(s') ≤ r(s). ∎"
)
NL_CLAIM = (
    "For a fixed round t ≥ 1, the UCB1 confidence radius √(2 ln t / s) is "
    "nonincreasing in the play count s: more plays never increase the bonus."
)

if __name__ == "__main__":
    print(f"\nVerifying:  {STATEMENT}")

    def attempt():
        with quiet("verifying with your Claude account"):
            return run_verification(
                "demo_ucb_radius_antitone",
                statement=STATEMENT,
                proof=PROOF,
                call_model=get_backend("claude", model="opus"),  # sealed-gate backend
                agent_drive=launch_agent(backend="claude", model="opus"),  # your account drives it
                nl_claim=NL_CLAIM,
            )

    out = run_with_retry(attempt)  # retry once if the agent stalls (e.g. bad import)
    cert = save_certificate(out)
    print_result(out, expect="VERIFIED", cert=cert)
