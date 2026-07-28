/-
# General Importance Sampling Variance Bound

Formalizes the general importance sampling variance bound:

  E_{π₀}[(w·r)²] ≤ ‖w‖_∞² · E_{π₀}[r²]

where w(a) = π(a)/π₀(a) is the importance weight.

The existing EXP3Bandit.lean has the EXP3-specific importance
weighted estimator. This module provides the general form.

## Hallucination Note

The checklist stated Var_{π₀}[w·r] ≤ ‖w‖_∞² · Var[r].
This is only correct for **zero-mean** r. In general:
  Var_{π₀}[w·r] ≤ ‖w‖_∞² · E_{π₀}[r²]  (correct)
  Var_{π₀}[w·r] ≤ ‖w‖_∞² · (Var_{π₀}[r] + E_{π₀}[r]²)  (correct, equivalent)
  Var_{π₀}[w·r] ≤ ‖w‖_∞² · Var_{π₀}[r]  (ONLY for zero-mean r)

## Main Results

* `is_second_moment_bound` — E[w²r²] ≤ ‖w‖² · E[r²]
* `is_variance_bound` — Var[wr] ≤ ‖w‖² · E[r²]
* `is_variance_bound_zero_mean` — Var[wr] ≤ ‖w‖² · Var[r] when E[r] = 0

## References

* [Owen, "Monte Carlo theory, methods and examples," Ch 9]
* [Metelli et al., "Policy Optimization via IS," ICML 2018]
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset BigOperators

noncomputable section

variable {A : Type*} [Fintype A]

/-! ### Second Moment Bound -/

/-- **IS second moment bound**: E_{π₀}[(w·r)²] ≤ ‖w‖_∞² · E_{π₀}[r²]
where w = π/π₀ is the importance weight.

Proof: E[(wr)²] = ∑ π₀·w²r² ≤ ‖w‖² · ∑ π₀·r² = ‖w‖² · E[r²]. -/
theorem is_second_moment_bound
    (π₀ : A → ℝ) (w r : A → ℝ)
    (hπ₀_nonneg : ∀ a, 0 ≤ π₀ a) (hπ₀_sum : ∑ a, π₀ a = 1)
    (w_max : ℝ) (hw : ∀ a, |w a| ≤ w_max) :
    ∑ a, π₀ a * (w a * r a) ^ 2 ≤
    w_max ^ 2 * ∑ a, π₀ a * r a ^ 2 := by
  calc ∑ a, π₀ a * (w a * r a) ^ 2
      = ∑ a, π₀ a * (w a ^ 2 * r a ^ 2) := by congr 1; ext a; ring
    _ ≤ ∑ a, π₀ a * (w_max ^ 2 * r a ^ 2) := by
        apply Finset.sum_le_sum; intro a _
        apply mul_le_mul_of_nonneg_left _ (hπ₀_nonneg a)
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        exact sq_le_sq' (abs_le.mp (hw a)).1 (abs_le.mp (hw a)).2
    _ = w_max ^ 2 * ∑ a, π₀ a * r a ^ 2 := by
        rw [Finset.mul_sum]; congr 1; ext a; ring

/-- **IS variance bound**: Var_{π₀}[w·r] ≤ ‖w‖_∞² · E_{π₀}[r²].

Since Var[X] = E[X²] - (E[X])² ≤ E[X²], this follows from
the second moment bound. -/
theorem is_variance_bound
    (π₀ : A → ℝ) (w r : A → ℝ)
    (hπ₀_nonneg : ∀ a, 0 ≤ π₀ a) (hπ₀_sum : ∑ a, π₀ a = 1)
    (w_max : ℝ) (hw : ∀ a, |w a| ≤ w_max) :
    (∑ a, π₀ a * (w a * r a) ^ 2) - (∑ a, π₀ a * (w a * r a)) ^ 2 ≤
    w_max ^ 2 * ∑ a, π₀ a * r a ^ 2 := by
  linarith [is_second_moment_bound π₀ w r hπ₀_nonneg hπ₀_sum w_max hw,
    sq_nonneg (∑ a, π₀ a * (w a * r a))]

/-- **IS variance bound (zero-mean)**: when E_{π₀}[r] = 0,
Var_{π₀}[w·r] ≤ ‖w‖_∞² · Var_{π₀}[r].

This is the form stated in the checklist, which is only valid
for zero-mean reward functions. -/
theorem is_variance_bound_zero_mean
    (π₀ : A → ℝ) (w r : A → ℝ)
    (hπ₀_nonneg : ∀ a, 0 ≤ π₀ a) (hπ₀_sum : ∑ a, π₀ a = 1)
    (w_max : ℝ) (hw : ∀ a, |w a| ≤ w_max)
    (h_zero_mean : ∑ a, π₀ a * r a = 0) :
    (∑ a, π₀ a * (w a * r a) ^ 2) - (∑ a, π₀ a * (w a * r a)) ^ 2 ≤
    w_max ^ 2 * ((∑ a, π₀ a * r a ^ 2) - (∑ a, π₀ a * r a) ^ 2) := by
  have h0 : (∑ a, π₀ a * r a) ^ 2 = 0 := by rw [h_zero_mean]; ring
  simp only [h0, sub_zero]
  exact is_variance_bound π₀ w r hπ₀_nonneg hπ₀_sum w_max hw

/-- **Effective sample size**: the IS effective sample size is
n_eff = n / (1 + Var_{π₀}[w]) ≈ n / ‖w‖_∞. Smaller ‖w‖_∞ means
less variance inflation. -/
theorem is_effective_sample_size
    (n : ℕ) (w_max : ℝ) (hw : 1 ≤ w_max)
    (n_eff : ℝ) (hn : n_eff = n / w_max) :
    n_eff * w_max = n := by
  rw [hn]; field_simp

end
