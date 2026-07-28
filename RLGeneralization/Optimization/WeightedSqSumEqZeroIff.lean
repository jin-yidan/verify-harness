import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open Finset BigOperators

/-- Weighted sum of squares with strictly positive weights is zero iff every term is zero.

For w_i > 0: ∑ w_i · x_i² = 0 ↔ ∀ i, x_i = 0.

This characterizes the zero set of weighted squared norms and is used
to prove uniqueness of minimizers for squared-residual objectives. -/
theorem weighted_sq_sum_eq_zero_iff {ι : Type*} [Fintype ι]
    (w x : ι → ℝ) (hw : ∀ i, 0 < w i) :
    ∑ i, w i * x i ^ 2 = 0 ↔ ∀ i, x i = 0 := by
  constructor
  · intro hsum i
    have h_nonneg : ∀ j, 0 ≤ w j * x j ^ 2 := fun j => mul_nonneg (le_of_lt (hw j)) (sq_nonneg _)
    have h_zero := Finset.sum_eq_zero_iff_of_nonneg (fun j _ => h_nonneg j) |>.mp hsum
    have hi := h_zero i (Finset.mem_univ i)
    rcases mul_eq_zero.mp hi with hw_zero | hx_sq_zero
    · exact absurd hw_zero (ne_of_gt (hw i))
    · exact pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp hx_sq_zero
  · intro h
    apply Finset.sum_eq_zero
    intro i _
    simp [h i]
