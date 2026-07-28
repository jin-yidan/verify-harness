import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Real

/-- **Hoeffding exponent for the UCB bonus**: at a fixed sample count `n ≥ 1`
    and confidence width `√(2·log t / n)`, the Hoeffding exponent evaluates to
    exactly `t⁻⁴`: `exp(−2n·(√(2 log t / n))²) = (t⁴)⁻¹` for `t ≥ 1`. -/
theorem hoeffding_exponent_ucb_bonus (n : ℕ) (hn : 1 ≤ n) (t : ℝ) (ht : 1 ≤ t) :
    Real.exp (-(2 * ↑n * Real.sqrt (2 * Real.log t / ↑n) ^ 2)) = ((t ^ 4)⁻¹ : ℝ) := by
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
  have hlog : 0 ≤ Real.log t := Real.log_nonneg ht
  have hn0 : (0 : ℝ) < ↑n := Nat.cast_pos.mpr (by omega)
  rw [Real.sq_sqrt (by positivity)]
  have harg : 2 * ↑n * (2 * Real.log t / ↑n) = (4 : ℕ) * Real.log t := by
    field_simp
    ring
  rw [harg, Real.exp_neg, Real.exp_nat_mul, Real.exp_log ht0]

