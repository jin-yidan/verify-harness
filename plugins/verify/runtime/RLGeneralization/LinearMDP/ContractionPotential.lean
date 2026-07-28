/-
# Contraction Potential Composition

Compose per-step contraction cost bounds with the elliptical potential lemma
to obtain total contraction regret bounds for linear MDP algorithms.

## Main Results

* `contraction_regret_from_potential` — total contraction cost from potential bound
* `contraction_regret_with_sqrt` — specialized for H·K episode structure
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

set_option linter.unusedVariables false

open Finset BigOperators

noncomputable section

theorem contraction_regret_from_potential
    (d : ℕ) (hd : 0 < d) (T : ℕ) (K_real : ℝ) (hK : 1 ≤ K_real)
    (beta : ℝ) (hbeta : 0 < beta)
    (phi_norms : Fin T → ℝ) (h_nn : ∀ t, 0 ≤ phi_norms t)
    (h_ell : ∑ t, phi_norms t ≤ 2 * ↑d * Real.log (1 + ↑T / ↑d))
    (costs : Fin T → ℝ)
    (h_per_step : ∀ t, costs t ≤ 2 * (beta ^ 2 * phi_norms t + K_real⁻¹)) :
    ∑ t, costs t ≤
      4 * beta ^ 2 * ↑d * Real.log (1 + ↑T / ↑d) + 2 * ↑T * K_real⁻¹ := by
  have h_expand : ∀ t, costs t ≤ 2 * beta ^ 2 * phi_norms t + 2 * K_real⁻¹ := by
    intro t; have := h_per_step t; nlinarith
  have h1 : ∑ t, costs t ≤ ∑ t, (2 * beta ^ 2 * phi_norms t + 2 * K_real⁻¹) :=
    Finset.sum_le_sum fun t _ => h_expand t
  have h2 : ∑ t, (2 * beta ^ 2 * phi_norms t + 2 * K_real⁻¹) =
      2 * beta ^ 2 * ∑ t, phi_norms t + ↑T * (2 * K_real⁻¹) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  nlinarith

theorem contraction_regret_with_sqrt
    (d : ℕ) (hd : 0 < d) (H K : ℕ) (hK : 0 < K)
    (beta : ℝ) (hbeta : 0 < beta)
    (phi_norms : Fin (H * K) → ℝ) (h_nn : ∀ t, 0 ≤ phi_norms t)
    (h_ell : ∑ t, phi_norms t ≤ 2 * ↑d * Real.log (1 + ↑(H * K) / ↑d))
    (costs : Fin (H * K) → ℝ)
    (h_per_step : ∀ t, costs t ≤ 2 * (beta ^ 2 * phi_norms t + (K : ℝ)⁻¹)) :
    ∑ t, costs t ≤
      4 * beta ^ 2 * ↑d * Real.log (1 + ↑(H * K) / ↑d)
        + 2 * ↑H := by
  have hKr : (1 : ℝ) ≤ (K : ℝ) := Nat.one_le_cast.mpr hK
  have h := contraction_regret_from_potential d hd (H * K) (K : ℝ) hKr
    beta hbeta phi_norms h_nn h_ell costs h_per_step
  have hKinv : ↑(H * K) * (K : ℝ)⁻¹ = ↑H := by
    rw [Nat.cast_mul]; field_simp
  linarith

end
