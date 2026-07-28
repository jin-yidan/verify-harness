# Ground Truth: UCB1 Regret, Mutated (mechanical single-edit)

**Source**: `benchmarks/ucb_regret_clean/statement.md` (Auer et al. 2002,
Theorem 1) with ONE mechanical mutation: the threshold constant **8 → 4** in
the theorem bound, Step 2's threshold $\ell$, and Step 7's combine line
(lines 13, 28, 61–62 of the clean fixture). The attribution header is
removed because the mutated text is NOT the published theorem. Everything
else is byte-identical to the clean control.

## The flaw (exact by construction)

With $\ell = \lceil 4 \ln n / \Delta_i^2 \rceil$, the case $s \ge \ell$ in
Step 4 no longer yields the contradiction: Step 4 (left intact) requires
$2\sqrt{2 \ln t / s} \le \Delta_i$, i.e. $s \ge 8 \ln t / \Delta_i^2$ — but
$s \ge 4\ln n/\Delta_i^2$ does not imply $s \ge 8\ln t/\Delta_i^2$ (take
$t = n$ and $s$ between the two thresholds). Concretely: at
$s = \lceil 4\ln n/\Delta_i^2 \rceil$ and $t = n$,
$2\sqrt{2\ln n/s} \approx \sqrt{2}\,\Delta_i > \Delta_i$.

Numeric instance: $\ln n = 1$, $\Delta_i = 1/2$ → $\ell = 16$; at
$s = 16, t = n$: $2\sqrt{2/16} = 1/\sqrt{2} \approx 0.707 > 0.5 = \Delta_i$.
Exact in ℚ via squares: claim needs $8\ln t / s \le \Delta_i^2$, i.e.
$8/16 = 1/2 \le 1/4$ — false.

This is the same factor-2 error class as the SE fixture's Step 4, but
mechanically derived rather than Claude-authored: ground truth is exact by
construction, and the falsification gate should REFUTE the threshold claim
numerically with an exact certificate.

**Expected verdict**: UNVERIFIED/WRONG (Step 4's contradiction fails for the
mutated threshold; the stated theorem bound with constant 4 is unjustified —
the provable constant is 8).

## Fully correct components

Steps 1 (regret decomposition), 3 (index condition), 5 (Hoeffding at fixed
(t,s) — correctly applied), 6 (tail sum) are untouched and correct. Step 2's
structure and Step 7's algebra are correct GIVEN their (mutated, wrong)
threshold.
