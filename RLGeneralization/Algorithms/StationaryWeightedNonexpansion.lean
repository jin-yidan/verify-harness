import Mathlib
open Finset

/-- **Stationary-weighted non-expansion.** For a row-stochastic, entrywise
nonnegative transition matrix `P` on a finite type with stationary measure
`d` (i.e. `dᵀP = dᵀ`), the operator `v ↦ Pv` does not increase the
`d`-weighted squared `L²` norm: `∑ d s (Pv s)² ≤ ∑ d s (v s)²`. Proof is
Jensen on `x ↦ x²` per row, then stationarity collapses the weighted sum. -/
theorem stationary_weighted_nonexpansion {S : Type*} [Fintype S]
    (d : S → ℝ) (P : S → S → ℝ) (v : S → ℝ)
    (hd : ∀ s, 0 ≤ d s) (hP : ∀ s s', 0 ≤ P s s')
    (hrow : ∀ s, ∑ s', P s s' = 1) (hstat : ∀ s', ∑ s, d s * P s s' = d s') :
    ∑ s, d s * (∑ s', P s s' * v s') ^ 2 ≤ ∑ s, d s * v s ^ 2 := by
  have hjensen : ∀ s, (∑ s', P s s' * v s') ^ 2 ≤ ∑ s', P s s' * v s' ^ 2 := by
    intro s
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq univ
      (fun s' => Real.sqrt (P s s')) (fun s' => Real.sqrt (P s s') * v s')
    have e1 : ∀ s', Real.sqrt (P s s') * (Real.sqrt (P s s') * v s') = P s s' * v s' := by
      intro s'; rw [← mul_assoc, Real.mul_self_sqrt (hP s s')]
    have e2 : ∀ s', Real.sqrt (P s s') ^ 2 = P s s' := by
      intro s'; rw [Real.sq_sqrt (hP s s')]
    have e3 : ∀ s', (Real.sqrt (P s s') * v s') ^ 2 = P s s' * v s' ^ 2 := by
      intro s'; rw [mul_pow, Real.sq_sqrt (hP s s')]
    simp only [e1, e2, e3] at hcs
    rw [hrow s, one_mul] at hcs; exact hcs
  calc ∑ s, d s * (∑ s', P s s' * v s') ^ 2
      ≤ ∑ s, d s * (∑ s', P s s' * v s' ^ 2) := by
        apply Finset.sum_le_sum; intro s _
        exact mul_le_mul_of_nonneg_left (hjensen s) (hd s)
    _ = ∑ s, ∑ s', d s * (P s s' * v s' ^ 2) := by
        apply Finset.sum_congr rfl; intro s _; rw [Finset.mul_sum]
    _ = ∑ s', ∑ s, d s * (P s s' * v s' ^ 2) := Finset.sum_comm
    _ = ∑ s', (∑ s, d s * P s s') * v s' ^ 2 := by
        apply Finset.sum_congr rfl; intro s' _
        rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro s _; ring
    _ = ∑ s', d s' * v s' ^ 2 := by
        apply Finset.sum_congr rfl; intro s' _; rw [hstat s']

