---
name: verify-falsify
description: "Duplicate of Claude /verify-falsify. Use when the user invokes /verify-falsify, $verify-falsify, or asks to run this RLVerify command. Standalone falsification gate — search for a numeric counterexample to a single mathematical claim and record a certificate-backed REFUTED / PASSED / VACUOUS / SKIPPED outcome"
---

# /verify-falsify — Codex Duplicate

This is a Codex skill duplicate of `.claude/commands/verify-falsify.md`. The Claude slash command name is `/verify-falsify`; in Codex, invoke it as `$verify-falsify` or write `/verify-falsify` in the prompt. Interpret Claude-specific Task/Bash references as workflow instructions and use Codex-native tools or the local RLVerify CLI.

Preserve the verification discipline from the original command: verify, do not repair; do not add hypotheses or proof steps; treat sealed gates and kernel evidence according to the RLVerify output contract.

When this skill calls `python3 -m harness` directly or through RLVerify CLI examples, pass `--backend codex` unless the user explicitly asks for another backend. Pass `--model <codex-model>` when a specific Codex model is under test; otherwise let the Codex CLI use its configured default.

---

<command-name>verify-falsify</command-name>

# /verify-falsify — numeric counterexample search for one claim

> A standalone component of **/verify-full-process** (the "falsification gate" phase). Run
> it on a single inequality / claim WITHOUT decomposing a whole proof or
> starting a session. For the full verification flow, use `/verify-full-process`. This is
> additive — it calls `rlverify.falsify`, the same module the pipeline uses.

## Input

$ARGUMENTS

Provide the claim to test — ideally as an inequality with its hypotheses,
verbatim (e.g. "for any distribution p over K≤4 atoms and t≥1,
‖p̂_t − p‖₁ ≤ sqrt(2 ln(2K/δ)/t) with prob ≥ 1−δ"). If only prose is given,
restate the exact inequality and its hypotheses before searching.

## What this does

Formalization is the most expensive way to discover a claim is false. This
component does the cheap thing first: sample hypothesis-satisfying instances
and look for a violation. **A found-and-re-verified violation is an audit
finding until a trusted deterministic checker, independent of the sampler
author, validates the serialized witness.**

It does **not** prove the claim. A PASS means "no counterexample in N
instances" — never "numerically verified".

## Standalone usage

Write an ad-hoc sampler for the claim (typically `/tmp/falsify_<name>.py`),
then wrap the outcome in the `rlverify.falsify` contract — that contract is
what keeps the result honest (it forces VACUOUS when the sampler never
exercised the claim, and forces REFUTED to carry a reproducible candidate
witness). Independent validation is a separate trusted step.

```python
import numpy as np
from rlverify.falsify import FalsifyReport, reverify

rng = np.random.default_rng(0)
N, TOL = 200_000, 1e-9
sampled = satisfied = violations = 0; worst = None; max_gap = 0.0
for _ in range(N):
    # sample an instance: Dirichlet for distributions, log-uniform grids up to
    # 1e9 for scale params (T, K, d), uniform [a,b] for bounded reals,
    # n ≤ 4 states/atoms; EXACT enumeration for probability claims
    inst = ...
    sampled += 1
    if not hypotheses(inst):            # skip instances that violate the claim's hyps
        continue
    satisfied += 1
    gap = lhs(inst) - rhs(inst)         # claim: lhs ≤ rhs
    if gap > TOL * max(1.0, abs(rhs(inst))):
        violations += 1
        if worst is None or gap > max_gap:
            worst, max_gap = inst, gap

# If a violation was found, cross-check it by a second pure-Python path. This
# permits the component OUTCOME REFUTED, but remains audit-only until a trusted
# deterministic checker independently validates the serialized witness:
if worst is not None:
    ok = reverify(worst, lhs_fn=lambda c: lhs(c), rhs_fn=lambda c: rhs(c),
                  exact=True)            # exact=True only for rational arithmetic
    report = FalsifyReport(block="<name>", verdict="REFUTED",
                           claim="<the inequality, verbatim>",
                           instances=sampled, hyp_satisfied=satisfied,
                           violations=violations, max_violation=max_gap,
                           certificate=worst, executed_by="agent")
else:
    report = FalsifyReport(block="<name>", verdict="PASSED",
                           claim="<the inequality, verbatim>",
                           instances=sampled, hyp_satisfied=satisfied,
                           executed_by="harness")
print(report.summary())
```

`FalsifyReport.__post_init__` enforces the contract: a REFUTED with no
certificate, or a PASSED with fewer than `MIN_SATISFIED` (1000)
hypothesis-satisfying instances, is rejected / downgraded. `executed_by`
must be `"harness"` only when the harness actually executed the search —
`"agent"` means the numbers are merely attested, not trustworthy.

### High-probability claims (don't reflexively SKIP)

A claim of the form `P(∃ arm i, ∃ t ≤ m : |prefix-mean − μ_i| > r(t)) ≤ δ`
with bounded rewards is **exactly computable** — Bernoulli is a valid
[0,1]-reward refutation instance:

```python
from fractions import Fraction
from rlverify.falsify import bernoulli_prefix_deviation, exp_series_exceeds
# per-arm exact P(∃ t ≤ m : violating(t, S_t)); arms multiply by independence.
# Restrict to the m = ⌊T/K⌋ phases completed deterministically so the
# finitized event is a SUBSET of the claimed bad event — STATE why the subset
# relation holds (the one step the DP cannot check). Certify an irrational
# threshold ln(2K/δ) via a rational upper bound with exp_series_exceeds.
```

## The four outcomes

- **REFUTED** — a violation found AND `reverify()` confirmed it by independent
  substitution. The claim is **UNVERIFIED/WRONG**; the certificate is the
  evidence.
- **PASSED** — no violation in ≥1000 hypothesis-satisfying instances. **Zero
  verification weight** — report as "no counterexample in N instances".
- **VACUOUS** — sampling rarely/never satisfied the hypotheses. Investigate
  satisfiability (the hypotheses may be contradictory).
- **SKIPPED** — not numerically checkable: ∃-statements; asymptotic / big-O /
  limit claims; measure-theoretic or topological claims (gate their finite
  corollaries instead); unsampleable hypotheses. Constant/log-factor errors
  may only show at astronomical scale — always put growing params on
  log-scale grids; if a finite-DP passes only at practical `m`, record
  SKIPPED-after-DP-pass with the `m` reached, not PASSED-as-evidence.

## Output (standard result card)

End with the standard result card (`verify-output-contract.md`). Always print
the sampling counts (they justify the verdict) and, for `REFUTED`, the
certificate as labelled `key=value` pairs tagged as the load-bearing evidence;
record whether `reverify` ran `exact` (rational) or float-tolerance.

Real example (mutated UCB1, Step 4):
```
/verify-falsify · mutated_step4_contradiction
OUTCOME      REFUTED
EVIDENCE     certificate   (reverify: float-tolerance, independent path)
WEIGHT       load-bearing
EXECUTED_BY  harness       (never "agent" on a load-bearing REFUTED)
DETAIL       gap 0.414 → (√2−1)·Δ at s = ceil(4 ln t / Δ^2); claim 2√(2 ln t/s) ≤ Δ
SAMPLING     instances 200000 · hyp_satisfied 55012 · violations 3
CERTIFICATE  Δ=0.99987  t=931623  s=55
NEXT         —   (block is UNVERIFIED/WRONG; skip its dependents)
```
- `PASSED`/`VACUOUS` print `EVIDENCE none · WEIGHT zero-weight · CERTIFICATE —`;
  a PASS is "no counterexample in N instances", never proof.
- `SKIPPED` prints `WEIGHT prioritization-only`; SKIPPED-after-DP-pass adds
  `DP_m <m reached>` so the partial check is visible but not counted as PASSED.

`SKIPPED` example (SA a.s.-convergence claim — not numerically checkable):
```
/verify-falsify · sa_main_as_convergence
OUTCOME       SKIPPED
EVIDENCE      none
WEIGHT        prioritization-only
REASON        "θ_n → θ* a.s." is a tail event over whole sample paths;
              any finite trajectory fits both convergence and divergence
GATE-INSTEAD  gate a finite corollary that IS sampleable, e.g. E||θ_k − θ*||^2 ≤ C·a_k
SAMPLING      instances 0 · hyp_satisfied 0 · violations 0   (not checkable)
NEXT          —   (falsification cannot decide this block)
```

## Optional: attach to a live /verify-full-process session

```python
from rlverify.driver import VerifyDriver
d = VerifyDriver(); d.resume("fixture_name")     # only if a session exists
d.record_falsification(report)                   # lands in runs/<fixture>.json
```

Standalone, just keep the `report.summary()` output — no driver needed.
