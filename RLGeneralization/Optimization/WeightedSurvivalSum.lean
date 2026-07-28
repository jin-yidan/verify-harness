import Mathlib

open Finset BigOperators

/-- Survival-weight telescoping identity: for any real sequence `a` and any `n`,
`∑_{i=1}^n a i * ∏_{j=i+1}^n (1 - a j) = 1 - ∏_{j=1}^n (1 - a j)`. Holds for
arbitrary reals (no nonnegativity or boundedness needed). -/
theorem weighted_survival_sum (a : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.Icc 1 n, a i * ∏ j ∈ Finset.Ioc i n, (1 - a j)
      = 1 - ∏ j ∈ Finset.Icc 1 n, (1 - a j) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1)]
    have htop : ∏ j ∈ Finset.Ioc (m+1) (m+1), (1 - a j) = 1 := by simp
    have hsplit : ∀ i ∈ Finset.Icc 1 m, a i * ∏ j ∈ Finset.Ioc i (m+1), (1 - a j)
        = (1 - a (m+1)) * (a i * ∏ j ∈ Finset.Ioc i m, (1 - a j)) := by
      intro i hi
      simp only [Finset.mem_Icc] at hi
      rw [Finset.prod_Ioc_succ_top (by omega : i ≤ m)]
      ring
    rw [Finset.sum_congr rfl hsplit, ← Finset.mul_sum, ih, htop,
        Finset.prod_Icc_succ_top (by omega : 1 ≤ m + 1)]
    ring

