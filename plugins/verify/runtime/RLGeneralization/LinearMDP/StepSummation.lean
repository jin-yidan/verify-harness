/-
# Per-Step to Total Bound Summation

Generic infrastructure for composing per-step bounds into total bounds
via `Finset.sum_le_sum`. Key application: summing per-step contraction
costs in CFPO and similar algorithms.

## Main Results

* `total_from_per_step_affine` — if cost_i ≤ α·x_i + β, then ∑ cost ≤ α·∑x + n·β
* `total_contraction_from_per_step` — specialization to contraction cost structure
* `total_contraction_with_potential` — compose with elliptical potential bound
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

open Finset BigOperators

noncomputable section

theorem sum_const_real {n : ℕ} (c : ℝ) :
    ∑ _ : Fin n, c = ↑n * c := by
  rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]

theorem total_from_per_step_affine {n : ℕ}
    (alpha beta : ℝ) (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta)
    (phi_norms : Fin n → ℝ) (h_nn : ∀ i, 0 ≤ phi_norms i)
    (costs : Fin n → ℝ)
    (h_per_step : ∀ i, costs i ≤ alpha * phi_norms i + beta) :
    ∑ i, costs i ≤ alpha * ∑ i, phi_norms i + ↑n * beta := by
  calc ∑ i, costs i
      ≤ ∑ i, (alpha * phi_norms i + beta) :=
        Finset.sum_le_sum fun i _ => h_per_step i
    _ = ∑ i, (alpha * phi_norms i) + ∑ i : Fin n, beta := Finset.sum_add_distrib
    _ = alpha * ∑ i, phi_norms i + ↑n * beta := by
        rw [← Finset.mul_sum, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]

theorem total_contraction_from_per_step {H : ℕ}
    (K : ℝ) (hK : 1 ≤ K) (beta : ℝ) (hbeta : 0 < beta)
    (phi_norms : Fin H → ℝ) (h_nn : ∀ h, 0 ≤ phi_norms h)
    (costs : Fin H → ℝ)
    (h_per_step : ∀ h, costs h ≤ 2 * (beta ^ 2 * phi_norms h + K⁻¹)) :
    ∑ h, costs h ≤ 2 * beta ^ 2 * ∑ h, phi_norms h + 2 * ↑H * K⁻¹ := by
  have h_expand : ∀ h, costs h ≤ 2 * beta ^ 2 * phi_norms h + 2 * K⁻¹ := by
    intro h; have := h_per_step h; nlinarith
  calc ∑ h, costs h
      ≤ ∑ h, (2 * beta ^ 2 * phi_norms h + 2 * K⁻¹) :=
        Finset.sum_le_sum fun h _ => h_expand h
    _ = ∑ h, (2 * beta ^ 2 * phi_norms h) + ∑ _ : Fin H, (2 * K⁻¹) :=
        Finset.sum_add_distrib
    _ = 2 * beta ^ 2 * ∑ h, phi_norms h + ↑H * (2 * K⁻¹) := by
        rw [← Finset.mul_sum, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    _ = 2 * beta ^ 2 * ∑ h, phi_norms h + 2 * ↑H * K⁻¹ := by ring

theorem total_contraction_with_potential {H : ℕ}
    (K : ℝ) (hK : 1 ≤ K) (beta : ℝ) (hbeta : 0 < beta)
    (d : ℕ) (hd : 0 < d)
    (phi_norms : Fin H → ℝ) (h_nn : ∀ h, 0 ≤ phi_norms h)
    (h_ell : ∑ h, phi_norms h ≤ 2 * ↑d * Real.log (1 + ↑H / ↑d))
    (costs : Fin H → ℝ)
    (h_per_step : ∀ h, costs h ≤ 2 * (beta ^ 2 * phi_norms h + K⁻¹)) :
    ∑ h, costs h ≤
      4 * beta ^ 2 * ↑d * Real.log (1 + ↑H / ↑d) + 2 * ↑H * K⁻¹ := by
  have h_total := total_contraction_from_per_step K hK beta hbeta phi_norms h_nn costs h_per_step
  nlinarith

end
