/-
# Log-Linear Sandwich Bounds

Tight two-sided bounds relating log to linear functions:
  x/(1+x) ≤ log(1+x) ≤ x   and   x ≤ -log(1-x) ≤ x/(1-x)

## Main Results

* `log_one_add_ge_div` — log(1+x) ≥ x/(1+x) for x > -1
* `neg_log_one_sub_ge` — -log(1-x) ≥ x for x < 1
* `neg_log_one_sub_le_div` — -log(1-x) ≤ x/(1-x) for 0 ≤ x < 1

## References

* Standard analysis; complements `log_one_plus_le` (log(1+x) ≤ x)
* Used in KL divergence, mixing time, information geometry, Bennett/Bernstein
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

open Real

/-- **Log lower bound**: log(1+x) ≥ x/(1+x) for x > -1.

    Together with `log_one_plus_le` (log(1+x) ≤ x for x ≥ 0), this gives
    the sandwich: x/(1+x) ≤ log(1+x) ≤ x. -/
theorem log_one_add_ge_div (x : ℝ) (hx : -1 < x) :
    x / (1 + x) ≤ Real.log (1 + x) := by
  have h1x : (0 : ℝ) < 1 + x := by linarith
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr h1x)
  rw [Real.log_inv] at h
  have h2 : 1 - (1 + x)⁻¹ = x / (1 + x) := by field_simp; ring
  linarith

/-- **Neg-log lower bound**: -log(1-x) ≥ x for x < 1.

    Equivalently, log(1-x) ≤ -x. Together with `neg_log_one_sub_le_div`,
    this gives: x ≤ -log(1-x) ≤ x/(1-x). -/
theorem neg_log_one_sub_ge (x : ℝ) (hx : x < 1) :
    x ≤ -Real.log (1 - x) := by
  have h1 : (0 : ℝ) < 1 - x := by linarith
  linarith [Real.log_le_sub_one_of_pos h1]

/-- **Neg-log upper bound**: -log(1-x) ≤ x/(1-x) for 0 ≤ x < 1.

    The tightest linear-rational upper bound on -log(1-x).
    Together with `neg_log_one_sub_ge`: x ≤ -log(1-x) ≤ x/(1-x). -/
theorem neg_log_one_sub_le_div {x : ℝ} (hx_nn : 0 ≤ x) (hx_lt : x < 1) :
    -Real.log (1 - x) ≤ x / (1 - x) := by
  have h1 : (0 : ℝ) < 1 - x := by linarith
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr h1)
  rw [Real.log_inv] at h
  have h2 : (1 - x)⁻¹ - 1 = x / (1 - x) := by field_simp; ring
  linarith
