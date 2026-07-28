import Mathlib
open Finset

/-- **Weighted per-row Jensen for squares.** For ANY nonnegative weights `μ`
(no stationarity required) and a row-stochastic, entrywise-nonnegative
kernel `P`, the weighted sum of squared row-averages is at most the weighted
sum of row-averaged squares: `∑ s, μ s · (Pv s)² ≤ ∑ s, μ s · ∑ s', P s s' · (v s')²`.
This is the always-true half of the stationary non-expansion bound — the
stationarity of `μ` is needed only to collapse the right-hand side. -/
theorem weighted_row_sq_jensen {S : Type*} [Fintype S]
    (μ : S → ℝ) (P : S → S → ℝ) (v : S → ℝ)
    (hμ : ∀ s, 0 ≤ μ s) (hP : ∀ s s', 0 ≤ P s s')
    (hrow : ∀ s, ∑ s', P s s' = 1) :
    ∑ s, μ s * (∑ s', P s s' * v s') ^ 2 ≤
      ∑ s, μ s * ∑ s', P s s' * v s' ^ 2 := by
  apply Finset.sum_le_sum
  intro s _
  apply mul_le_mul_of_nonneg_left _ (hμ s)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq univ
    (fun s' => Real.sqrt (P s s')) (fun s' => Real.sqrt (P s s') * v s')
  have e1 : ∀ s', Real.sqrt (P s s') * (Real.sqrt (P s s') * v s') = P s s' * v s' := by
    intro s'; rw [← mul_assoc, Real.mul_self_sqrt (hP s s')]
  have e2 : ∀ s', Real.sqrt (P s s') ^ 2 = P s s' := by
    intro s'; rw [Real.sq_sqrt (hP s s')]
  have e3 : ∀ s', (Real.sqrt (P s s') * v s') ^ 2 = P s s' * v s' ^ 2 := by
    intro s'; rw [mul_pow, Real.sq_sqrt (hP s s')]
  simp only [e1, e2, e3] at hcs
  rw [hrow s, one_mul] at hcs
  exact hcs

