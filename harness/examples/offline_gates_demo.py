#!/usr/bin/env python3
"""OFFLINE demo — NO agent account, NO network, deterministic. Run anywhere.

This is the demo to show people when you want to explain WHY the harness is more
than "just call an LLM." It swaps the real agent + real model for fakes, so it
runs in seconds, but it exercises the REAL runner, the REAL journal handoff, the
REAL kernel compile, and the REAL enforcement logic.

It runs the SAME compiling proof twice and shows the harness's teeth:

  Run A — the trusted back-translation judges the formalization MATCH
          → VERIFIED (kernel-clean AND gates passed)

  Run B — the trusted back-translation judges MISMATCH (the Lean statement does
          not faithfully capture the claim)
          → UNVERIFIED/UNGATED  ── the verdict is DOWNGRADED even though the
            proof compiled. A raw "ask the LLM" workflow cannot do this: the
            faithfulness gate runs in TRUSTED harness code, not the agent's.

Run:
  python harness/examples/offline_gates_demo.py
(The two runs each do one real Lean compile, so allow a few seconds each.)
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))

from harness.runner import run_verification
from harness.examples._demo_util import quiet, save_certificate, print_result, _c

# A genuinely true, genuinely compiling statement (law of excluded middle).
STATEMENT = "theorem t : ∀ p : Prop, p ∨ ¬p"
PROOF = "by exact fun p => Classical.em p"
NL_CLAIM = "Every proposition either holds or its negation holds."


def fake_call_model(judge_verdict: str):
    """Stand-in for a sealed-gate LLM call. Dispatches on the sealed prompt text.
    The triage returns 'no suspects'; the back-translation judge returns whatever
    verdict we want to demonstrate (MATCH or MISMATCH)."""
    def call(prompt: str) -> str:
        if "adversarial reviewer" in prompt:                 # sealed triage
            return '{"suspects": [], "all_clear": true}'
        if "Render the" in prompt:                           # back-translation: render step
            return "for every proposition, it holds or its negation holds"
        if "Compare a CLAIM" in prompt:                      # back-translation: judge step
            return f'{{"verdict": "{judge_verdict}", "reason": "demo"}}'
        return ""
    return call


def fake_agent(fixture, statement, proof, corpus_path):
    """Stand-in for the untrusted agent. Models the REAL two-process path: the
    agent drives its OWN session and shares state with the runner ONLY through
    the journal under corpus_path — exactly like a live `claude -p` would."""
    from rlverify.mcp_server import HarnessSession
    a = HarnessSession(corpus_path=corpus_path)
    a.begin(fixture)
    a.assemble(statement=statement, proof="exact fun p => Classical.em p",
               imports=["Mathlib.Tactic"])


def run(label, judge_verdict):
    print(f"\n{_c(label, '1')}  (faithfulness gate will judge: {judge_verdict})")
    with quiet("running the harness"):
        out = run_verification(
            f"demo_offline_{judge_verdict.lower()}",
            statement=STATEMENT, proof=PROOF,
            call_model=fake_call_model(judge_verdict),
            agent_drive=fake_agent,
            nl_claim=NL_CLAIM,
        )
    return out


if __name__ == "__main__":
    print("\nSame compiling proof, two faithfulness outcomes — watch the verdict change.")
    out_a = run("Run A — faithful formalization", "MATCH")
    cert = save_certificate(out_a)            # Run A is VERIFIED — keep its certificate
    print_result(out_a, cert=cert, explain=False)  # fake agent → no meaningful "explanation"
    out_b = run("Run B — unfaithful formalization", "MISMATCH")
    print_result(out_b, explain=False)
    print(_c("  Takeaway:", "1") + " the proof COMPILED in both runs, yet the harness")
    print("  downgraded the second — the faithfulness gate runs in TRUSTED code the")
    print("  agent cannot bypass or fake. That enforcement is the harness's whole point.\n")
