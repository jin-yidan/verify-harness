/-
# Log-Sqrt Bound

Upper bound on log by square root: log(x) ≤ 2(√x - 1) for x > 0.

## Main Results

* `log_le_two_sqrt_sub_two` — log(x) ≤ 2(√x - 1) for x > 0

## References

* Standard "log grows slower than any power" bound
* Used in PAC-Bayes, sample complexity, mixing time bounds
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-- **Log-sqrt bound**: log(x) ≤ 2(√x - 1) for x > 0.

    Proof: write log(x) = 2 log(√x), then apply log(t) ≤ t - 1. -/
theorem log_le_two_sqrt_sub_two {x : ℝ} (hx : 0 < x) :
    Real.log x ≤ 2 * (Real.sqrt x - 1) := by
  have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h1 := Real.log_le_sub_one_of_pos hsqrt_pos
  have h2 : Real.log x = 2 * Real.log (Real.sqrt x) := by
    conv_lhs => rw [← Real.sq_sqrt (le_of_lt hx)]
    rw [Real.log_pow]; push_cast; ring
  linarith
