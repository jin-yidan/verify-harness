import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Bias-Variance Decomposition (MSE Decomposition)

The fundamental identity decomposing weighted mean squared error into
variance plus squared bias:

  E_P[(f - c)²] = Var_P(f) + (E_P[f] - c)²

This is the master identity for estimation theory in RL:
- Policy evaluation: MSE of value estimate = variance + bias²
- TD learning: approximation error decomposition
- Sample complexity: optimal bias-variance tradeoff
- Regression / function approximation error analysis
- Concentration inequality proofs via second-moment method

## Main Results

* `weighted_mse_decomposition` — E_P[(f-c)²] = Var_P(f) + (E_P[f]-c)²
-/

open Finset BigOperators

/-- **Bias-variance decomposition** (MSE = variance + bias²).

    For any probability distribution P on a finite type, function f,
    and target value c:

      ∑ P(x)·(f(x) - c)² = (∑ P(x)·f(x)² - (∑ P(x)·f(x))²) + (∑ P(x)·f(x) - c)²

    The first term is Var_P(f) and the second is (E_P[f] - c)² = bias².

    Proof: both sides equal ∑ P(x)·f(x)² - 2c·E[f] + c². The RHS
    is purely algebraic; the LHS uses ∑ P(x) = 1 to simplify. -/
theorem weighted_mse_decomposition {S : Type*} [Fintype S]
    (P : S → ℝ) (f : S → ℝ) (c : ℝ)
    (hP_sum : ∑ x, P x = 1) :
    ∑ x, P x * (f x - c) ^ 2 =
    (∑ x, P x * f x ^ 2 - (∑ x, P x * f x) ^ 2) +
    (∑ x, P x * f x - c) ^ 2 := by
  set μ := ∑ x, P x * f x
  -- Both sides equal ∑ P(x)·f(x)² - 2cμ + c²; RHS by ring
  suffices h : ∑ x, P x * (f x - c) ^ 2 =
      ∑ x, P x * f x ^ 2 - 2 * c * μ + c ^ 2 by
    rw [h]; ring
  -- Expand the summand algebraically
  have h_expand : ∀ x, P x * (f x - c) ^ 2 =
      P x * f x ^ 2 - 2 * c * (P x * f x) + c ^ 2 * P x := by
    intro x; ring
  simp_rw [h_expand]
  -- Distribute the three terms across the sum
  have h_const : ∑ x : S, c ^ 2 * P x = c ^ 2 := by
    rw [← Finset.mul_sum]; simp [hP_sum]
  have h_linear : ∑ x : S, 2 * c * (P x * f x) = 2 * c * μ := by
    rw [← Finset.mul_sum]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, h_const, h_linear]
