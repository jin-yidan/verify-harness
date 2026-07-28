# Verify user-simulation benchmark

Two deliberately small end-to-end cases:

- `scalar_discount_contraction.md`: expected to survive falsification and admit
  a clean Lean proof.
- `constant_alpha_q_learning.md`: expected to fail at the sampled-fixed-point
  step, preferably before full discharge.

Measure wall time per durable phase, time to first visible phase event,
proof-agent retries, final evidence tier, and whether the mathematical outcome
matches the expectation. Agent-side compile/search events are progress only;
only trusted parent recheck/kernel events count as verdict evidence.

See [RESULTS.md](RESULTS.md) for the 2026-07-26 live Codex runs, discovered
failure modes, production artifact replays, timings, and remaining latency work.
