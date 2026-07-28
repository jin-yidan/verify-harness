# Ground Truth: UCB1 with Hoeffding at a Random Count

One planted flaw. The theorem itself is true (it is Auer–Cesa-Bianchi–Fischer
2002, Theorem 1, up to constants); the PROOF is flawed.

## Flaw — Step 3: fixed-n Hoeffding applied at the sample-dependent count N_{t-1}(a)

**Location.** Step 3: "Applying Hoeffding's inequality with $n = N_{t-1}(a)$
samples and deviation $\varepsilon = \sqrt{2\ln t / N_{t-1}(a)}$".

**What is wrong.** Hoeffding's inequality bounds deviations of the average of
a FIXED, deterministic number $n$ of independent samples. $N_{t-1}(a)$ is a
random variable, and it is not independent of the samples: UCB1 pulls arm $a$
again precisely when its empirical mean (of the samples so far) is high, so
the count and the sample values are strongly dependent. Conditioning on
$N_{t-1}(a) = n$ biases the sample distribution, and the fixed-n bound does
not apply.

**Correct fix** (Auer et al. 2002): union-bound over all possible values of
the count: $\mathbb{P}(\exists s \le t: \hat\mu_{a,s} \ge \mu_a +
\sqrt{2\ln t/s}) \le \sum_{s=1}^t t^{-4} = t^{-3}$, where $\hat\mu_{a,s}$ is
the (deterministic-index) mean of the FIRST $s$ samples. This changes the
tail sum in Step 4 from $\sum 2t^{-4}$ to $\sum 2t^{-3}$ — still summable, so
the theorem survives with the same form; only the proof step is invalid.

**Expected verdict**: UNVERIFIED/HYPOTHESIS_VIOLATION — the cited lemma
(fixed-n Hoeffding; in the library, `prefix_arm_mean_concentration` with
deterministic n) is correct; the application at the random count violates its
hypothesis. Distinct from WRONG (no false statement is asserted as the
theorem is true) and from INCOMPLETE (no step is missing — a step is applied
to the wrong object).

## Fully correct components

- Step 1 (regret decomposition): exact identity, in the library as
  `pseudoRegret_eq_sum_gap_mul_pullCount`.
- Step 2 (three-way split): correct; in the library as
  `ucb_index_three_way_split`.
- Step 4 (tail sum): $\sum 2t^{-4} < \infty$ is correct (instantiation of a
  p-series result), though it inherits Step 3's invalid bound.
- Steps 5–6: correct counting and algebra GIVEN the (unjustified) Step 3.

## Provenance

This fixture reconstructs the input of the original ucb1 verification run
(`runs/ucb1_logT_regret_hypothesis_violation_20260610_104609.json`), whose
hypothesis-violation finding is documented in PIPELINE.md and the A/B/P
comparison report.
