/-
# Exponential Quadratic Upper Bound

Second-order Taylor upper bound: exp(x) ≤ 1 + x + x²/2 for x ≤ 0.

## Main Results

* `exp_neg_le_quadratic` — exp(-y) ≤ 1 - y + y²/2 for y ≥ 0
* `exp_le_quadratic_of_nonpos` — exp(x) ≤ 1 + x + x²/2 for x ≤ 0

## References

* Complements Mathlib's `quadratic_le_exp_of_nonneg` (lower bound for x ≥ 0)
* Key building block for Hoeffding's lemma, sub-Gaussian bounds, multiplicative weights
-/
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

open Real

/-- **Exp quadratic upper bound (negative form)**: exp(-y) ≤ 1 - y + y²/2 for y ≥ 0.

    Proof: from (1-y+y²/2)(1+y+y²/2) = 1+y⁴/4 ≥ 1 and the Mathlib lower bound
    1+y+y²/2 ≤ exp(y), derive (1-y+y²/2)·exp(y) ≥ 1. -/
theorem exp_neg_le_quadratic {y : ℝ} (hy : 0 ≤ y) :
    Real.exp (-y) ≤ 1 - y + y ^ 2 / 2 := by
  have h_pos : (0 : ℝ) < 1 - y + y ^ 2 / 2 := by nlinarith [sq_nonneg (y - 1)]
  have h_exp : 1 + y + y ^ 2 / 2 ≤ Real.exp y := quadratic_le_exp_of_nonneg hy
  have h_ge_one : 1 ≤ (1 - y + y ^ 2 / 2) * Real.exp y := by
    have h4 : (0 : ℝ) ≤ y ^ 4 / 4 := by positivity
    calc (1 : ℝ) ≤ 1 + y ^ 4 / 4 := by linarith
      _ = (1 - y + y ^ 2 / 2) * (1 + y + y ^ 2 / 2) := by ring
      _ ≤ (1 - y + y ^ 2 / 2) * Real.exp y :=
          mul_le_mul_of_nonneg_left h_exp (le_of_lt h_pos)
  have h_div : 1 / Real.exp y ≤ 1 - y + y ^ 2 / 2 :=
    (div_le_iff₀ (Real.exp_pos y)).mpr h_ge_one
  rwa [one_div, ← Real.exp_neg] at h_div

/-- **Exp quadratic upper bound (standard form)**: exp(x) ≤ 1 + x + x²/2 for x ≤ 0.

    Immediate from `exp_neg_le_quadratic` with y = -x. -/
theorem exp_le_quadratic_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    Real.exp x ≤ 1 + x + x ^ 2 / 2 := by
  have h := exp_neg_le_quadratic (show 0 ≤ -x by linarith)
  linarith [show Real.exp x = Real.exp (- -x) by ring_nf]
