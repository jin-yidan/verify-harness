/-
# Reciprocal Approximation Bounds

Upper bounds on 1/(1-x) for small x ∈ [0, 1/2]:
  1/(1-x) ≤ 1+2x   and   1/(1-x) ≤ exp(2x)

## Main Results

* `inv_one_sub_le_one_add_two_mul` — 1/(1-x) ≤ 1+2x for 0 ≤ x ≤ 1/2
* `inv_one_sub_le_exp_two` — 1/(1-x) ≤ exp(2x) for 0 ≤ x ≤ 1/2

## References

* Standard analysis; used for discount factor approximation in MDPs,
  learning rate analysis, and perturbation bounds
-/
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-- **Linear reciprocal bound**: 1/(1-x) ≤ 1+2x for 0 ≤ x ≤ 1/2.

    Proof: clear denominators and check (1+2x)(1-x) = 1+x-2x² ≥ 1
    using x(1-2x) ≥ 0. -/
theorem inv_one_sub_le_one_add_two_mul {x : ℝ} (hx_nn : 0 ≤ x) (hx_le : x ≤ 1 / 2) :
    1 / (1 - x) ≤ 1 + 2 * x := by
  have h1 : (0 : ℝ) < 1 - x := by linarith
  rw [div_le_iff₀ h1]
  nlinarith

/-- **Exponential reciprocal bound**: 1/(1-x) ≤ exp(2x) for 0 ≤ x ≤ 1/2.

    Combines the linear bound with exp(t) ≥ 1+t. -/
theorem inv_one_sub_le_exp_two {x : ℝ} (hx_nn : 0 ≤ x) (hx_le : x ≤ 1 / 2) :
    1 / (1 - x) ≤ Real.exp (2 * x) := by
  have h1 : (0 : ℝ) < 1 - x := by linarith
  have h_lin : 1 / (1 - x) ≤ 1 + 2 * x := by
    rw [div_le_iff₀ h1]; nlinarith
  linarith [Real.add_one_le_exp (2 * x)]
