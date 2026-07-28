/-
# Discrete Gronwall Inequality

Explicit finite-time bound for linear recurrences: if u_{n+1} ≤ a·u_n + b,
then u_n ≤ a^n·u_0 + b·∑_{k<n} a^k.

## Main Results

* `discrete_gronwall` — u_n ≤ a^n·u_0 + b·∑_{k<n} a^k

## References

* Gronwall, T.H. (1919), "Note on the derivatives …"
* Atkinson, K. (1989), "An Introduction to Numerical Analysis"
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

open Finset BigOperators

private lemma geom_sum_step (a : ℝ) (n : ℕ) :
    ∑ k ∈ range (n + 1), a ^ k = 1 + a * ∑ k ∈ range n, a ^ k := by
  rw [sum_range_succ', pow_zero]
  simp_rw [pow_succ']
  rw [← Finset.mul_sum]
  ring

/-- **Discrete Gronwall inequality**: If u_{n+1} ≤ a·u_n + b for 0 ≤ a,
    then u_n ≤ a^n · u_0 + b · ∑_{k<n} a^k. -/
theorem discrete_gronwall (n : ℕ) (u : ℕ → ℝ) (a b : ℝ)
    (ha : 0 ≤ a)
    (hrec : ∀ k, k < n → u (k + 1) ≤ a * u k + b) :
    u n ≤ a ^ n * u 0 + b * ∑ k ∈ range n, a ^ k := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h_ih := ih (fun k hk => hrec k (Nat.lt_succ_of_lt hk))
    have h_step := hrec n (Nat.lt_succ_iff.mpr le_rfl)
    have h_gs := geom_sum_step a n
    calc u (n + 1)
        ≤ a * u n + b := h_step
      _ ≤ a * (a ^ n * u 0 + b * ∑ k ∈ range n, a ^ k) + b := by nlinarith
      _ = a ^ (n + 1) * u 0 + b * ∑ k ∈ range (n + 1), a ^ k := by
          rw [h_gs]; ring

private lemma gronwall_sum_step (m : ℕ) (a : ℝ) (b : ℕ → ℝ) :
    a * (∑ k ∈ range m, a ^ (m - 1 - k) * b k) + b m =
    ∑ k ∈ range (m + 1), a ^ (m - k) * b k := by
  rw [sum_range_succ, mul_sum]
  congr 1
  · apply sum_congr rfl
    intro k hk
    have hk_lt : k < m := mem_range.mp hk
    have hexp : m - 1 - k + 1 = m - k := by omega
    rw [← mul_assoc, ← pow_succ', hexp]
  · simp

/-- **Discrete Gronwall with varying perturbation**: If u_{k+1} ≤ a·u_k + b_k
    for 0 ≤ a, then u_n ≤ a^n·u_0 + ∑_{k<n} a^{n-1-k}·b_k.
    Generalizes `discrete_gronwall` to time-varying perturbations b_k. -/
theorem discrete_gronwall_varying (n : ℕ) (u b : ℕ → ℝ) (a : ℝ)
    (ha : 0 ≤ a)
    (hrec : ∀ k, k < n → u (k + 1) ≤ a * u k + b k) :
    u n ≤ a ^ n * u 0 + ∑ k ∈ range n, a ^ (n - 1 - k) * b k := by
  induction n with
  | zero => simp
  | succ m ih =>
    have h_ih := ih (fun k hk => hrec k (Nat.lt_succ_of_lt hk))
    have h_step := hrec m (Nat.lt_succ_iff.mpr le_rfl)
    change u (m + 1) ≤ a ^ (m + 1) * u 0 + ∑ k ∈ range (m + 1), a ^ (m - k) * b k
    rw [← gronwall_sum_step]
    have h_expand : a * (a ^ m * u 0 + ∑ k ∈ range m, a ^ (m - 1 - k) * b k) =
        a ^ (m + 1) * u 0 + a * ∑ k ∈ range m, a ^ (m - 1 - k) * b k := by
      rw [mul_add, ← mul_assoc, ← pow_succ']
    linarith [mul_le_mul_of_nonneg_left h_ih ha]
