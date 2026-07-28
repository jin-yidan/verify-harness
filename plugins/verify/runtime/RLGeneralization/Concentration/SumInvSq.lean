/-
# Partial Sum of Inverse Squares

Upper bound for partial sums of 1/k²: ∑_{k=1}^{n} 1/k² ≤ 2 - 1/n ≤ 2.

## Main Results

* `sum_inv_sq_le` — ∑_{k<n} 1/(k+1)² ≤ 2 - 1/n for n ≥ 1
* `sum_inv_sq_le_two` — ∑_{k<n} 1/(k+1)² ≤ 2

## References

* Euler (1734), Basel problem (∑ 1/k² = π²/6)
* Used in Robbins-Monro step-size conditions (∑ αₖ² < ∞),
  UCB confidence widths, convergence rate analysis
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

open Finset BigOperators

private lemma inv_sq_le_inv_sub_inv (k : ℕ) (hk : 0 < k) :
    1 / ((k : ℝ) + 1) ^ 2 ≤ 1 / ↑k - 1 / (↑k + 1) := by
  have hk_pos : (0 : ℝ) < ↑k := Nat.cast_pos.mpr hk
  have hk1_pos : (0 : ℝ) < ↑k + 1 := by linarith
  have hk_ne : (↑k : ℝ) ≠ 0 := ne_of_gt hk_pos
  have hk1_ne : (↑k : ℝ) + 1 ≠ 0 := ne_of_gt hk1_pos
  rw [div_sub_div _ _ hk_ne hk1_ne, show (1 : ℝ) * (↑k + 1) - ↑k * 1 = 1 from by ring]
  have h_denom_le : (↑k : ℝ) * (↑k + 1) ≤ (↑k + 1) ^ 2 := by nlinarith
  exact div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ 1) (by positivity) h_denom_le

/-- **Partial sum of inverse squares (tight)**: ∑_{k<n} 1/(k+1)² ≤ 2 - 1/n for n ≥ 1.
    Uses telescoping comparison: 1/(k+1)² ≤ 1/k - 1/(k+1) for k ≥ 1. -/
theorem sum_inv_sq_le (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ range n, (1 / ((k : ℝ) + 1) ^ 2) ≤ 2 - 1 / (n : ℝ) := by
  induction n with
  | zero => omega
  | succ m ih =>
    by_cases hm : m = 0
    · subst hm; norm_num [sum_range_one]
    · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
      have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
      have hm_r_pos : (0 : ℝ) < ↑m := Nat.cast_pos.mpr hm_pos
      rw [sum_range_succ]
      have h_ih := ih hm1
      have h_key := inv_sq_le_inv_sub_inv m hm_pos
      have h_cast_eq : (1 : ℝ) / ((m : ℝ) + 1) = 1 / (↑(m + 1) : ℝ) := by
        push_cast; ring
      linarith

/-- **Partial sum of inverse squares**: ∑_{k<n} 1/(k+1)² ≤ 2 for all n.
    Corollary of the tight bound `sum_inv_sq_le`. -/
theorem sum_inv_sq_le_two (n : ℕ) :
    ∑ k ∈ range n, (1 / ((k : ℝ) + 1) ^ 2) ≤ 2 := by
  by_cases hn : n = 0
  · subst hn; simp
  · have h1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have h_tight := sum_inv_sq_le n h1
    have h_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    linarith [div_pos one_pos h_pos]
