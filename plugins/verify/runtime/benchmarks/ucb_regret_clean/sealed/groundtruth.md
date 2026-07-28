# Ground Truth: UCB1 Regret (clean control)

**No planted flaws.** This is Auer–Cesa-Bianchi–Fischer 2002, Theorem 1, in
its canonical correct form — including the two subtleties that flawed
variants get wrong:

- Step 5 applies Hoeffding only at FIXED (t, s) pairs (deterministic prefix
  index), with the union over the random play count handled explicitly by
  the triple summation in Step 6 — this is exactly the fix for the
  `ucb1_hoeffding_at_random_count` fixture's flaw.
- Step 2's threshold uses the correct constant 8 (so Step 4's contradiction
  $2\sqrt{2\ln t/s} \le \Delta_i$ for $s \ge 8\ln t/\Delta_i^2$ goes
  through: $4 \cdot 2 \ln t / s \le \Delta_i^2 \iff s \ge 8\ln t/\Delta_i^2$).

**Purpose**: false-positive detector. Any REFUTED falsification, any
violation block, or any UNVERIFIED/* verdict on this fixture is a scored
false positive. Probabilistic steps (5–6) are expected to resolve as library
matches or to be axiomatized under the lifecycle / left as honest
INCOMPLETE-of-infrastructure only if the library lacks them — the scorer
accepts VERIFIED, VERIFIED MODULO AXIOMS, COMPILED, and HAS GAPS (an honest
infrastructure gap), but no failure verdicts.

**Not Claude-authored**: the theorem and proof structure are from the
published literature (transcribed in `tests/proofs/ucb_regret.py`).
