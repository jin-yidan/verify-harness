import Mathlib
import RLGeneralization.Algorithms.StationaryWeightedNonexpansion
open Finset

/-- **TD Dirichlet-form lower bound / coercivity of `I − γP`.** With `P`
row-stochastic and entrywise nonnegative, `d` a stationary measure (`dᵀP = dᵀ`),
and `γ ≥ 0`, the `d`-weighted bilinear form of `I − γP` is bounded below by
`(1 − γ)` times the `d`-weighted squared norm of `v`:
`(1 − γ) ∑ d s (v s)² ≤ ∑ d s · v s · (v s − γ (Pv) s)`. This is the
positive-definiteness engine behind the TD(0) fixed point. Proof: stationary
non-expansion gives `‖Pv‖_d ≤ ‖v‖_d`, then Cauchy–Schwarz in the `d`-inner
product gives `⟨v, Pv⟩_d ≤ ‖v‖_d²`. -/
theorem td_weighted_dirichlet_lower_bound {S : Type*} [Fintype S]
    (d : S → ℝ) (P : S → S → ℝ) (v : S → ℝ)
    (hd : ∀ s, 0 ≤ d s) (hP : ∀ s s', 0 ≤ P s s')
    (hrow : ∀ s, ∑ s', P s s' = 1) (hstat : ∀ s', ∑ s, d s * P s s' = d s')
    (γ : ℝ) (hγ0 : 0 ≤ γ) :
    (1 - γ) * (∑ s, d s * v s ^ 2) ≤
      ∑ s, d s * (v s * (v s - γ * ∑ s', P s s' * v s')) := by
  set b : ℝ := ∑ s, d s * v s ^ 2 with hb_def
  set c : ℝ := ∑ s, d s * (∑ s', P s s' * v s') ^ 2 with hc_def
  set a : ℝ := ∑ s, d s * (v s * ∑ s', P s s' * v s') with ha_def
  have hb_nonneg : 0 ≤ b := by
    apply Finset.sum_nonneg; intro s _; exact mul_nonneg (hd s) (sq_nonneg _)
  have hc_le_b : c ≤ b := stationary_weighted_nonexpansion d P v hd hP hrow hstat
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq univ
    (fun s => Real.sqrt (d s) * v s) (fun s => Real.sqrt (d s) * (∑ s', P s s' * v s'))
  have ef : ∀ s, (Real.sqrt (d s) * v s) * (Real.sqrt (d s) * (∑ s', P s s' * v s'))
      = d s * (v s * ∑ s', P s s' * v s') := by
    intro s; rw [show Real.sqrt (d s) * v s * (Real.sqrt (d s) * (∑ s', P s s' * v s'))
      = (Real.sqrt (d s) * Real.sqrt (d s)) * (v s * (∑ s', P s s' * v s')) by ring,
      Real.mul_self_sqrt (hd s)]
  have eg1 : ∀ s, (Real.sqrt (d s) * v s) ^ 2 = d s * v s ^ 2 := by
    intro s; rw [mul_pow, Real.sq_sqrt (hd s)]
  have eg2 : ∀ s, (Real.sqrt (d s) * (∑ s', P s s' * v s')) ^ 2
      = d s * (∑ s', P s s' * v s') ^ 2 := by
    intro s; rw [mul_pow, Real.sq_sqrt (hd s)]
  simp only [ef, eg1, eg2] at hcs
  have hbc : b * c ≤ b * b := mul_le_mul_of_nonneg_left hc_le_b hb_nonneg
  have ha2 : a ^ 2 ≤ b ^ 2 := by have := le_trans hcs hbc; nlinarith [this]
  have ha_le_b : a ≤ b := by
    have habs : |a| ≤ b := by
      rw [← Real.sqrt_sq hb_nonneg, ← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt ha2
    exact le_trans (le_abs_self a) habs
  have hsplit : ∑ s, d s * (v s * (v s - γ * ∑ s', P s s' * v s')) = b - γ * a := by
    rw [hb_def, ha_def, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro s _; ring
  rw [hsplit]
  nlinarith [ha_le_b, hγ0, mul_nonneg hγ0 (sub_nonneg.mpr ha_le_b)]

