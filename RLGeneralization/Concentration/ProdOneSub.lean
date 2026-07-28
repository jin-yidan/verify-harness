/-
# Product of (1 - xᵢ) Bounds

Sandwich bounds for products of (1 - xₖ):
  1 - ∑ xₖ ≤ ∏ (1 - xₖ) ≤ exp(-∑ xₖ)

## Main Results

* `prod_one_sub_ge_one_sub_sum` — ∏_{k<n} (1-xₖ) ≥ 1 - ∑_{k<n} xₖ for 0 ≤ xₖ ≤ 1
* `prod_one_sub_le_exp_neg_sum` — ∏_{k<n} (1-xₖ) ≤ exp(-∑_{k<n} xₖ) for xₖ ≤ 1

## References

* Mathlib: `Real.one_sub_le_exp_neg`
* Used in stochastic approximation convergence, Q-learning, product-of-failures bounds
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

open Finset BigOperators Real

/-- **Product lower bound (Bonferroni)**: ∏_{k<n} (1-xₖ) ≥ 1 - ∑_{k<n} xₖ for 0 ≤ xₖ ≤ 1.

    The product of survival probabilities is at least 1 minus the sum of
    failure probabilities. Together with `prod_one_sub_le_exp_neg_sum`:

      1 - ∑ xₖ  ≤  ∏ (1 - xₖ)  ≤  exp(-∑ xₖ) -/
theorem prod_one_sub_ge_one_sub_sum (n : ℕ) (x : ℕ → ℝ)
    (hx_nn : ∀ k, k < n → 0 ≤ x k)
    (hx_le : ∀ k, k < n → x k ≤ 1) :
    1 - ∑ k ∈ range n, x k ≤ ∏ k ∈ range n, (1 - x k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [prod_range_succ, sum_range_succ]
    have ih' := ih (fun k hk => hx_nn k (Nat.lt_succ_of_lt hk))
                   (fun k hk => hx_le k (Nat.lt_succ_of_lt hk))
    have hx_n_nn := hx_nn n (Nat.lt_succ_iff.mpr le_rfl)
    have hx_n_le := hx_le n (Nat.lt_succ_iff.mpr le_rfl)
    have h_sum_nn : 0 ≤ ∑ k ∈ range n, x k :=
      Finset.sum_nonneg (fun k hk => hx_nn k (Nat.lt_succ_of_lt (Finset.mem_range.mp hk)))
    calc 1 - (∑ k ∈ range n, x k + x n)
        = (1 - ∑ k ∈ range n, x k) - x n := by ring
      _ ≤ (1 - ∑ k ∈ range n, x k) * (1 - x n) := by
          nlinarith [mul_nonneg hx_n_nn h_sum_nn]
      _ ≤ (∏ k ∈ range n, (1 - x k)) * (1 - x n) := by
          apply mul_le_mul_of_nonneg_right ih'
          linarith

/-- **Product of (1-xₖ) bound**: ∏_{k<n} (1-xₖ) ≤ exp(-∑_{k<n} xₖ) for xₖ ≤ 1. -/
theorem prod_one_sub_le_exp_neg_sum (n : ℕ) (x : ℕ → ℝ)
    (hx_le1 : ∀ k, k < n → x k ≤ 1) :
    ∏ k ∈ range n, (1 - x k) ≤ exp (-∑ k ∈ range n, x k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [prod_range_succ, sum_range_succ, neg_add, exp_add]
    apply mul_le_mul
    · exact ih (fun k hk => hx_le1 k (Nat.lt_succ_of_lt hk))
    · exact one_sub_le_exp_neg (x n)
    · linarith [hx_le1 n (Nat.lt_succ_iff.mpr le_rfl)]
    · exact exp_nonneg _
