/-
# Product of (1 + aₖ) Bounds

Sandwich bounds for products of (1 + aₖ):
  1 + ∑ aₖ ≤ ∏ (1 + aₖ) ≤ exp(∑ aₖ)

## Main Results

* `prod_one_add_ge_one_add_sum` — ∏_{k<n} (1 + aₖ) ≥ 1 + ∑_{k<n} aₖ for aₖ ≥ 0
* `prod_one_add_le_exp_sum` — ∏_{k<n} (1 + aₖ) ≤ exp(∑_{k<n} aₖ) for aₖ ≥ 0

## References

* Weierstrass, K. (classical inequality)
* Cesa-Bianchi & Lugosi, "Prediction, Learning, and Games" (2006)
* Complements `prod_one_sub_le_exp_neg_sum` in ProdOneSub.lean
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

open Finset BigOperators

/-- **Weierstrass product inequality**: ∏_{k<n} (1 + aₖ) ≥ 1 + ∑_{k<n} aₖ for aₖ ≥ 0.
    The product of terms (1 + aₖ) dominates 1 plus their sum. -/
theorem prod_one_add_ge_one_add_sum (n : ℕ) (a : ℕ → ℝ)
    (ha : ∀ k, k < n → 0 ≤ a k) :
    1 + ∑ k ∈ range n, a k ≤ ∏ k ∈ range n, (1 + a k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [prod_range_succ, sum_range_succ]
    have h_ih := ih (fun k hk => ha k (Nat.lt_succ_of_lt hk))
    have h_an : 0 ≤ a n := ha n (Nat.lt_succ_iff.mpr le_rfl)
    have h_sum_nn : 0 ≤ ∑ k ∈ range n, a k :=
      Finset.sum_nonneg (fun k hk => ha k (Nat.lt_succ_of_lt (Finset.mem_range.mp hk)))
    calc 1 + (∑ k ∈ range n, a k + a n)
        = (1 + ∑ k ∈ range n, a k) + a n := by ring
      _ ≤ (1 + ∑ k ∈ range n, a k) * (1 + a n) := by nlinarith [mul_nonneg h_sum_nn h_an]
      _ ≤ (∏ k ∈ range n, (1 + a k)) * (1 + a n) := by
          apply mul_le_mul_of_nonneg_right h_ih; linarith

open Real

/-- **Product-exp upper bound**: ∏_{k<n} (1 + aₖ) ≤ exp(∑_{k<n} aₖ) for aₖ ≥ 0.

    Each factor satisfies 1 + aₖ ≤ exp(aₖ), and multiplying preserves
    the inequality since all factors are nonneg. Together with
    `prod_one_add_ge_one_add_sum`, this gives the sandwich:

      1 + ∑ aₖ  ≤  ∏ (1 + aₖ)  ≤  exp(∑ aₖ) -/
theorem prod_one_add_le_exp_sum (n : ℕ) (a : ℕ → ℝ)
    (ha : ∀ k, k < n → 0 ≤ a k) :
    ∏ k ∈ range n, (1 + a k) ≤ exp (∑ k ∈ range n, a k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [prod_range_succ, sum_range_succ, exp_add]
    have ih' := ih (fun k hk => ha k (Nat.lt_succ_of_lt hk))
    have ha_n := ha n (Nat.lt_succ_iff.mpr le_rfl)
    have h_le : 1 + a n ≤ exp (a n) := by linarith [add_one_le_exp (a n)]
    exact mul_le_mul ih' h_le (by linarith) (exp_nonneg _)
