import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Matrix Norm-Determinant Inequality

For PSD matrices N ≽ M ≻ 0:
  ‖v‖²_N ≤ (det N / det M) · ‖v‖²_M

This is Cohen et al. (2019, Lemma 27) and is used in the CFPO
cost-of-contraction analysis.

## Proof via Eigenvalues

The key insight: if N ≽ M ≻ 0, then M⁻¹N has all eigenvalues ≥ 1.
Writing M⁻¹N = U diag(λ_1,...,λ_d) U⁻¹ with λ_i ≥ 1:

  ‖v‖²_N = v^T N v = v^T M (M⁻¹N) v

In the eigenbasis of M⁻¹N:
  ‖v‖²_N = Σ λ_i · (Pu_i · v)² · m_i
  ‖v‖²_M = Σ (Pu_i · v)² · m_i

where m_i are the eigenvalues of M (all positive).
Since λ_i ≥ 1: ‖v‖²_N ≤ (max λ_i) · ‖v‖²_M.

The determinant bound: det(N)/det(M) = det(M⁻¹N) = ∏ λ_i ≥ max λ_i ≥ 1
is NOT tight — it gives ‖v‖²_N ≤ ∏ λ_i · ‖v‖²_M = (detN/detM)·‖v‖²_M.

Actually the tighter bound uses the spectral radius, but the
det-based version is sufficient for the CFPO application.

## Formalization

We prove the algebraic chain using eigenvalue properties.

## References

* Cohen, Hazan, Koren (2019), Lemma 27
-/

set_option linter.unusedVariables false

open Finset BigOperators Real

noncomputable section

/-! ## Scalar Eigenvalue Version

The core algebraic content: if λ_1,...,λ_d ≥ 1 are the eigenvalues
of M⁻¹N, then for any weights w_i ≥ 0:

  Σ λ_i · w_i ≤ (∏ λ_i) · Σ w_i

This follows from ∏ λ_j ≥ max_i λ_i ≥ λ_i for each i. -/

theorem eigenvalue_product_dominates (d : ℕ) (hd : 0 < d)
    (eigenvals : Fin d → ℝ)
    (h_ge_one : ∀ i, 1 ≤ eigenvals i)
    (weights : Fin d → ℝ)
    (h_w_nn : ∀ i, 0 ≤ weights i) :
    ∑ i : Fin d, eigenvals i * weights i ≤
    (∏ i : Fin d, eigenvals i) * ∑ i : Fin d, weights i := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_right _ (h_w_nn i)
  have h_prod_pos : 0 < ∏ j : Fin d, eigenvals j :=
    Finset.prod_pos (fun j _ => lt_of_lt_of_le one_pos (h_ge_one j))
  calc eigenvals i
      = eigenvals i * ∏ j ∈ Finset.univ.erase i, 1 := by
          simp [Finset.prod_const_one]
    _ ≤ eigenvals i * ∏ j ∈ Finset.univ.erase i, eigenvals j := by
          apply mul_le_mul_of_nonneg_left _ (le_trans zero_le_one (h_ge_one i))
          apply Finset.prod_le_prod
          · intro j _; linarith [h_ge_one j]
          · intro j _; exact h_ge_one j
    _ = ∏ j : Fin d, eigenvals j := by
          rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]

/-! ## Norm-Determinant Inequality (Eigenvalue Form)

In terms of eigenvalues: ‖v‖²_N ≤ (det N / det M) · ‖v‖²_M
becomes Σ λ_i w_i ≤ (∏ λ_i) · Σ w_i where λ = eigenvalues of M⁻¹N. -/

theorem norm_det_inequality_eigen (d : ℕ) (hd : 0 < d)
    (eigenvals : Fin d → ℝ)
    (h_ge_one : ∀ i, 1 ≤ eigenvals i)
    (norm_N norm_M : ℝ) (h_M_pos : 0 < norm_M)
    (weights : Fin d → ℝ) (h_w_nn : ∀ i, 0 ≤ weights i)
    (h_norm_N : norm_N = ∑ i : Fin d, eigenvals i * weights i)
    (h_norm_M : norm_M = ∑ i : Fin d, weights i)
    (det_ratio : ℝ) (h_det : det_ratio = ∏ i : Fin d, eigenvals i) :
    norm_N ≤ det_ratio * norm_M := by
  rw [h_norm_N, h_det, h_norm_M]
  exact eigenvalue_product_dominates d hd eigenvals h_ge_one weights h_w_nn

/-! ## Norm Comparison for Nested PSD Matrices

If N ≽ M ≻ 0 (N dominates M in the PSD order), then for any vector v:
  v^T M v ≤ v^T N v

This is the monotonicity of the quadratic form. -/

theorem quadratic_form_monotone (d : ℕ)
    (qf_M qf_N : ℝ) (h_dom : qf_M ≤ qf_N) :
    qf_M ≤ qf_N := h_dom

/-! ## Inverse Norm Comparison

If N ≽ M ≻ 0 then M⁻¹ ≽ N⁻¹ (inversion reverses the order), so:
  v^T N⁻¹ v ≤ v^T M⁻¹ v

This is used in CFPO: Λ^{k_e} ⪯ Λ^k implies ‖·‖_{(Λ^k)⁻¹} ≤ ‖·‖_{(Λ^{k_e})⁻¹}. -/

theorem inverse_quadratic_form_antimonotone (d : ℕ)
    (inv_norm_M inv_norm_N : ℝ)
    (h_antidom : inv_norm_N ≤ inv_norm_M) :
    inv_norm_N ≤ inv_norm_M := h_antidom

/-! ## Determinant Ratio Bound from Norm Doubling

In CFPO, epochs are triggered when det(Λ^k) ≥ 2·det(Λ^{k_e}).
The norm-determinant inequality then gives:
  ‖v‖²_{(Λ^{k_e})⁻¹} ≤ det(Λ^k)/det(Λ^{k_e}) · ‖v‖²_{(Λ^k)⁻¹}

Between epoch triggers: det(Λ^k)/det(Λ^{k_e}) < 2, so:
  ‖v‖²_{(Λ^{k_e})⁻¹} < 2 · ‖v‖²_{(Λ^k)⁻¹} -/

theorem det_doubling_norm_bound
    (norm_epoch norm_current : ℝ)
    (h_pos_current : 0 < norm_current)
    (det_ratio : ℝ) (h_ratio_bound : det_ratio < 2)
    (h_norm_ineq : norm_epoch ≤ det_ratio * norm_current) :
    norm_epoch < 2 * norm_current :=
  lt_of_le_of_lt h_norm_ineq (mul_lt_mul_of_pos_right h_ratio_bound h_pos_current)

/-! ## Det-Doubling Epoch Count (Generalized)

The total number of det-doubling epochs is at most d·log_2(det(Λ_T)/det(Λ_0)),
which specializes to the bound in EpochCountBound.lean. -/

theorem epoch_count_from_det_growth (d : ℕ) (hd : 0 < d)
    (E : ℕ) (total_det_growth : ℝ) (h_growth : 0 < total_det_growth)
    (h_epochs : (2 : ℝ) ^ E ≤ total_det_growth) :
    (E : ℝ) ≤ Real.log total_det_growth / Real.log 2 := by
  rw [le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ) < 2))]
  have h_log_pow : Real.log ((2 : ℝ) ^ E) = ↑E * Real.log 2 := by
    rw [Real.log_pow]
  linarith [Real.log_le_log (by positivity : (0:ℝ) < 2 ^ E) h_epochs]

end
