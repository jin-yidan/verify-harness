/-
# Confidence Sequences and Time-Uniform Bounds

Defines confidence sequence widths for anytime-valid inference.

Key difference from fixed-time confidence intervals:
- Fixed: P(|M_n - μ| > β(n, δ)) ≤ δ for a single fixed n
- Uniform: P(∃ n: |M_n - μ| > β(n, δ)) ≤ δ for ALL n simultaneously

Time-uniform bounds are essential for:
- Anytime algorithms, reward-free exploration, best-arm identification

## Main Results

* `fixedHoeffdingWidth` — fixed-time Hoeffding width: b·√(2·log(1/δ)/n)
* `tuHoeffdingWidth` — time-uniform Hoeffding width (with log-log cost)
* `tuHoeffding_wider` — time-uniform ≥ fixed (uniformity has a cost)
* `tuFreedmanWidth` — time-uniform Freedman width
* `doubling_epoch_weight_lt_one` — 6/(π²k²) < 1 for all k ≥ 1

## References

* [Howard et al., "Time-uniform confidence sequences", Ann. Stat. 2021]
* [Waudby-Smith and Ramdas, "Estimating Means by Betting", JRSS-B 2024]
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Pi.Bounds
import RLGeneralization.Concentration.Freedman

open Real

noncomputable section

/-! ### Fixed-Time Hoeffding Width (Baseline) -/

/-- **Fixed-time Hoeffding width**: b · √(2 · log(1/δ) / n). -/
def fixedHoeffdingWidth (b : ℝ) (n : ℕ) (δ : ℝ) : ℝ :=
  b * √(2 * Real.log (1 / δ) / ↑n)

/-- The fixed-time Hoeffding width is nonneg for b ≥ 0. -/
theorem fixedHoeffdingWidth_nonneg (b : ℝ) (n : ℕ) (δ : ℝ) (hb : 0 ≤ b) :
    0 ≤ fixedHoeffdingWidth b n δ := by
  unfold fixedHoeffdingWidth
  exact mul_nonneg hb (sqrt_nonneg _)

/-! ### Time-Uniform Hoeffding Width -/

/-- **Time-uniform Hoeffding confidence width** at time n.
    Uses the stitching/peeling method with a log-log factor. -/
def tuHoeffdingWidth (b : ℝ) (n : ℕ) (δ : ℝ) : ℝ :=
  let log_log_term := Real.log (max 1 (Real.log (2 * ↑n)))
  let α := log_log_term + Real.log (1 / δ) + Real.log (π ^ 2 / 3)
  b * √(2 * α / ↑n)

/-- The time-uniform width is nonneg for b ≥ 0. -/
theorem tuHoeffdingWidth_nonneg (b : ℝ) (n : ℕ) (δ : ℝ) (hb : 0 ≤ b) :
    0 ≤ tuHoeffdingWidth b n δ := by
  unfold tuHoeffdingWidth
  exact mul_nonneg hb (sqrt_nonneg _)

/-- **Time-uniform width ≥ fixed-time width** when the peeling cost is nonneg.

    Uniformity has a cost: the log-log factor makes the width strictly
    larger than the fixed-time Hoeffding width. -/
theorem tuHoeffding_wider (b : ℝ) (n : ℕ) (δ : ℝ)
    (hb : 0 ≤ b)
    (h_peeling : 0 ≤ Real.log (max 1 (Real.log (2 * ↑n))) +
      Real.log (π ^ 2 / 3)) :
    fixedHoeffdingWidth b n δ ≤ tuHoeffdingWidth b n δ := by
  unfold fixedHoeffdingWidth tuHoeffdingWidth
  simp only
  apply mul_le_mul_of_nonneg_left _ hb
  apply sqrt_le_sqrt
  apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ ↑n)
  nlinarith

/-! ### Doubling Epoch Weight -/

/-- **Doubling epoch weight bound**: 6/(π²·k²) < 1 for all k ≥ 1.

    In the doubling trick, epoch k gets level δ_k = δ · 6/(π²k²).
    The Basel sum ∑ 1/k² = π²/6 ensures ∑ δ_k = δ. -/
theorem doubling_epoch_weight_lt_one (k : ℕ) (hk : 0 < k) :
    6 / (π ^ 2 * (↑k) ^ 2) < 1 := by
  have hπ2 : (6 : ℝ) < π ^ 2 := by nlinarith [pi_gt_three]
  have hk_pos : (0 : ℝ) < ↑k := Nat.cast_pos.mpr hk
  have hk_sq : (1 : ℝ) ≤ (↑k) ^ 2 := by
    have : (1 : ℝ) ≤ ↑k := by exact_mod_cast hk
    nlinarith
  rw [div_lt_one (by positivity)]
  nlinarith

/-! ### Time-Uniform Freedman Width -/

/-- **Time-uniform Freedman width**: variance-adaptive confidence sequence.

    For bounded martingale differences with cumulative variance v and
    bound b, the width extends the fixed-time Freedman bound to all
    stopping times simultaneously.

    Ref: Howard et al. (2021), Theorem 4. -/
def tuFreedmanWidth (v b δ : ℝ) : ℝ :=
  let α := Real.log (max 1 (Real.log (max (exp 1) (2 * v / b ^ 2)))) +
    Real.log (1 / δ) + Real.log (π ^ 2 / 3)
  √(2 * v * α) + b * α / 3

end
