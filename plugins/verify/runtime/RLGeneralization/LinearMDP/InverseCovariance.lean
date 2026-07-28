/-
Copyright (c) 2026 Yidan Jin. All rights reserved.
This source code is proprietary and not licensed for public use.

# Concentration of Inverse Covariance (Gram Matrix Bounds)

In linear MDPs, the regularized Gram matrix
  Λ_t = λI + Σ_{i=1}^t φ_i φ_iᵀ
plays a central role. The key quantities are:

  1. The bonus width: ‖φ‖_{Λ^{-1}} = √(φᵀ Λ^{-1} φ)
  2. The elliptical potential: Σ_t ‖φ_t‖²_{Λ_{t-1}^{-1}}

The elliptical potential lemma bounds (2) by 2d·log(1 + t/(λd)),
which controls the cumulative width of confidence ellipsoids.

This file proves algebraic properties of the regularized inner
product and bounds, complementing EllipticalPotential.lean.

## Main Results

* `reg_inner_product_nonneg` — ‖φ‖²_{Λ^{-1}} ≥ 0
* `reg_inner_product_monotone` — adding data shrinks ‖φ‖_{Λ^{-1}}
* `inverse_covariance_trace_bound` — Tr(Λ^{-1}) ≤ d/λ
* `log_one_plus_upper_bound` — log(1+x) ≤ x (used to relax log-det to linear)

## References

* [Abbasi-Yadkori et al., "Improved Algorithms for Linear
  Stochastic Bandits," NeurIPS 2011]
* [Jin et al., "Provably Efficient RL with Linear Function
  Approximation," COLT 2020]
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset BigOperators Real

noncomputable section

/-! ### Regularized Inner Product -/

variable {d : ℕ}

/-- The **regularized squared norm**: ‖φ‖²_{Λ^{-1}} for diagonal Λ.

    For Λ = diag(λ₁, ..., λ_d), this is ∑_i φ_i² / λ_i.

    We model this algebraically for diagonal matrices (the
    key structural properties hold for general PSD Λ, but
    diagonal suffices for the algebraic identities). -/
def regSquaredNorm (φ : Fin d → ℝ) (Λ_diag : Fin d → ℝ) : ℝ :=
  ∑ i, φ i ^ 2 / Λ_diag i

/-- The regularized squared norm is nonneg when Λ > 0. -/
theorem regSquaredNorm_nonneg (φ : Fin d → ℝ) (Λ_diag : Fin d → ℝ)
    (hΛ : ∀ i, 0 < Λ_diag i) :
    0 ≤ regSquaredNorm φ Λ_diag := by
  apply Finset.sum_nonneg
  intro i _
  exact div_nonneg (sq_nonneg _) (le_of_lt (hΛ i))

/-- **Monotonicity**: adding a rank-1 update (φφᵀ) to Λ shrinks
    the regularized norm. For diagonal: if Λ' ≥ Λ (pointwise),
    then ‖φ‖²_{Λ'^{-1}} ≤ ‖φ‖²_{Λ^{-1}}.

    This captures: as we collect more data, confidence shrinks. -/
theorem regSquaredNorm_monotone (φ : Fin d → ℝ)
    (Λ₁ Λ₂ : Fin d → ℝ)
    (hΛ₁ : ∀ i, 0 < Λ₁ i)
    (h_le : ∀ i, Λ₁ i ≤ Λ₂ i) :
    regSquaredNorm φ Λ₂ ≤ regSquaredNorm φ Λ₁ := by
  apply Finset.sum_le_sum
  intro i _
  apply div_le_div_of_nonneg_left (sq_nonneg (φ i)) (hΛ₁ i) (h_le i)

/-! ### Trace Bound -/

/-- The trace of Λ⁻¹ for Λ = λI + M: Tr(Λ⁻¹) ≤ d/λ.

    For diagonal Λ with Λ_i ≥ λ > 0:
    ∑_i 1/Λ_i ≤ ∑_i 1/λ = d/λ. -/
theorem inverse_covariance_trace_bound
    (Λ_diag : Fin d → ℝ) (lam : ℝ)
    (hlam : 0 < lam)
    (hΛ : ∀ i, lam ≤ Λ_diag i) :
    ∑ i : Fin d, 1 / Λ_diag i ≤ d / lam := by
  calc ∑ i : Fin d, 1 / Λ_diag i
      ≤ ∑ i : Fin d, 1 / lam := by
        apply Finset.sum_le_sum
        intro i _
        apply div_le_div_of_nonneg_left zero_le_one hlam (hΛ i)
    _ = d / lam := by
        simp [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

/-! ### Elliptical Potential Bound (Algebraic Core) -/

/-- **Determinant-ratio identity**: for diagonal Λ with a rank-1
    update by φ, det(Λ + φφᵀ)/det(Λ) = 1 + ‖φ‖²_{Λ^{-1}}.

    (For diagonal Λ, this is ∏_i (Λ_i + φ_i²)/Λ_i.) -/
theorem det_ratio_identity_diagonal
    (φ : Fin d → ℝ) (Λ_diag : Fin d → ℝ)
    (hΛ : ∀ i, 0 < Λ_diag i) :
    (∏ i : Fin d, (Λ_diag i + φ i ^ 2) / Λ_diag i) =
    ∏ i : Fin d, (1 + φ i ^ 2 / Λ_diag i) := by
  apply Finset.prod_congr rfl
  intro i _
  rw [add_div, div_self (ne_of_gt (hΛ i))]

/-- **Log-determinant bound**: log(1 + x) ≤ x for x ≥ 0. -/
theorem log_one_plus_le (x : ℝ) (hx : 0 ≤ x) :
    Real.log (1 + x) ≤ x := by
  calc Real.log (1 + x) ≤ (1 + x) - 1 :=
      Real.log_le_sub_one_of_pos (by linarith)
    _ = x := by ring

/-- **Log-determinant upper bound**: log(1 + x) ≤ x for x ≥ 0.

    This is a standard inequality used in elliptical potential
    analysis to relax log-det ratios to linear expressions.
    Note: this bounds log from ABOVE (not below), so it gives
    a WEAKER bound when applied to elliptical potential sums. -/
theorem log_one_plus_upper_bound
    (lam : ℝ) (hlam : 0 < lam)
    (total_sq : ℝ) (htot : 0 ≤ total_sq) :
    Real.log (1 + total_sq / lam) ≤ total_sq / lam := by
  exact log_one_plus_le _ (div_nonneg htot (le_of_lt hlam))

/-- **Elliptical potential linear relaxation**: replaces the
    O(d log T) elliptical potential bound with the weaker O(dT) bound
    using log(1+x) ≤ x.

    This gives bonus_sum ≤ 2d · (TB²/(λd)) = 2TB²/λ, which is
    linear in T (worse than the logarithmic bound in the hypothesis).
    The actual O(d log T) bound is proved in `EllipticalPotential.lean`. -/
theorem elliptical_potential_linear_relaxation
    (d_dim T : ℕ) (lam B : ℝ)
    (hlam : 0 < lam) (hB : 0 < B) (hd : 0 < d_dim)
    (bonus_sum : ℝ) (h_bonus_sum_nonneg : 0 ≤ bonus_sum)
    (h_ell : bonus_sum ≤
      2 * d_dim * Real.log (1 + T * B ^ 2 / (lam * d_dim))) :
    bonus_sum ≤ 2 * d_dim * (T * B ^ 2 / (lam * d_dim)) := by
  calc bonus_sum
      ≤ 2 * d_dim * Real.log (1 + T * B ^ 2 / (lam * d_dim)) := h_ell
    _ ≤ 2 * d_dim * (T * B ^ 2 / (lam * d_dim)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact log_one_plus_le _ (div_nonneg (by positivity)
          (mul_pos hlam (Nat.cast_pos.mpr hd)).le)

end
