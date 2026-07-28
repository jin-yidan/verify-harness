/-
# Softplus Bounds

The softplus function `t ↦ log(1 + exp(t))` is the smooth approximation to
the ReLU function `max(0, t)`. These bounds quantify the approximation:

    max(0, t) ≤ log(1 + exp(t)) ≤ max(0, t) + log 2

## Main Results

* `softplus_ge_self` — log(1 + exp t) ≥ t
* `softplus_nonneg` — log(1 + exp t) ≥ 0
* `softplus_le_add_log2` — log(1 + exp t) ≤ max 0 t + log 2

## References

* Dugas et al. (2000), "Incorporating Second-Order Functional Knowledge"
* Used in logistic regression, neural networks, entropy-regularized RL
-/
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

open Real

/-- **Softplus lower bound (identity)**: log(1 + exp t) ≥ t.

    Proof: exp t ≤ 1 + exp t, so t = log(exp t) ≤ log(1 + exp t). -/
theorem softplus_ge_self (t : ℝ) : t ≤ Real.log (1 + Real.exp t) := by
  have h_le : Real.exp t ≤ 1 + Real.exp t := le_add_of_nonneg_left one_pos.le
  calc t = Real.log (Real.exp t) := (Real.log_exp t).symm
    _ ≤ Real.log (1 + Real.exp t) := by
        apply Real.log_le_log (Real.exp_pos t) h_le

/-- **Softplus nonnegativity**: log(1 + exp t) ≥ 0.

    Proof: 1 + exp t ≥ 1, so log(1 + exp t) ≥ log 1 = 0. -/
theorem softplus_nonneg (t : ℝ) : 0 ≤ Real.log (1 + Real.exp t) :=
  Real.log_nonneg (by linarith [Real.exp_pos t])

/-- **Softplus–ReLU gap**: log(1 + exp t) ≤ max(0, t) + log 2.

    The softplus function approximates ReLU to within log 2.
    Proof: case split — for t ≥ 0, use 1 ≤ exp t so 1 + exp t ≤ 2·exp t;
    for t < 0, use exp t ≤ 1 so 1 + exp t ≤ 2. -/
theorem softplus_le_add_log2 (t : ℝ) :
    Real.log (1 + Real.exp t) ≤ max 0 t + Real.log 2 := by
  rcases le_or_gt 0 t with ht | ht
  · rw [max_eq_right ht]
    have h1 : (1 : ℝ) ≤ Real.exp t := Real.one_le_exp ht
    have h_le : 1 + Real.exp t ≤ 2 * Real.exp t := by linarith
    calc Real.log (1 + Real.exp t)
        ≤ Real.log (2 * Real.exp t) := by
          apply Real.log_le_log (by linarith [Real.exp_pos t]) h_le
      _ = Real.log 2 + Real.log (Real.exp t) :=
          Real.log_mul (by norm_num) (ne_of_gt (Real.exp_pos t))
      _ = Real.log 2 + t := by rw [Real.log_exp]
      _ = t + Real.log 2 := by ring
  · rw [max_eq_left (le_of_lt ht)]
    have h_exp : Real.exp t ≤ Real.exp 0 := Real.exp_le_exp.mpr (le_of_lt ht)
    rw [Real.exp_zero] at h_exp
    calc Real.log (1 + Real.exp t)
        ≤ Real.log 2 := by
          apply Real.log_le_log (by linarith [Real.exp_pos t])
          linarith
      _ = 0 + Real.log 2 := by ring
