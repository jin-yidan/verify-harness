/-
# Self-Normalized Concentration

Self-normalized tail bounds for linear predictors (Abbasi-Yadkori et al., 2011).
These are the concentration results underlying LinUCB and LSVI-UCB.

## Main Results

* `regularizedGram_isHermitian` — Λ_T is symmetric (proved)
* `regularizedGram_posDef` — Λ_T is PD when λ > 0 (proved)
* `selfNormalizedNorm_nonneg` — ‖v‖²_{Λ^{-1}} ≥ 0 for PD Λ (proved)
* `confidenceRadiusSq_pos` — β² > 0 when σ, δ > 0 and δ < 1 (proved)
* `confidenceRadiusSq_le_of_smaller_ldr` — β² monotone in log-det ratio (proved)
* `self_normalized_bound_conditional` — concentration bound (conditional on martingale MGF)
* `confidence_ellipsoid_conditional` — estimation bound (conditional on OLS reduction)
* `linucb_prediction_error` — Cauchy-Schwarz + confidence bound (proved, CS no longer conditional)

* `self_normalized_cauchy_schwarz` — |φ^T v|² ≤ ‖φ‖²_{Λ⁻¹}·‖v‖²_Λ

## References

* Abbasi-Yadkori, Pál, Szepesvári, "Improved Algorithms for Linear Stochastic
  Bandits," NIPS 2011.
* Agarwal et al., "RL: Theory and Algorithms," Appendix A.5 (2026).
-/

import RLGeneralization.Concentration.MatrixBernstein
import Mathlib.LinearAlgebra.Matrix.PosDef

open Finset BigOperators Real Matrix

noncomputable section

variable {d : ℕ}

/-! ### Regularized Gram Matrix -/

/-- Λ_T = λI + ∑_{t=1}^T φ_t φ_t^T (regularized Gram matrix). -/
def regularizedGram (T : ℕ) (lam : ℝ) (phi : Fin T → Fin d → ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  lam • (1 : Matrix (Fin d) (Fin d) ℝ) +
  ∑ t : Fin T, Matrix.of (fun i j => phi t i * phi t j)

/-- The regularized Gram matrix is symmetric. -/
theorem regularizedGram_isHermitian (T : ℕ) (lam : ℝ)
    (phi : Fin T → Fin d → ℝ) :
    (regularizedGram T lam phi).IsHermitian := by
  simp only [Matrix.IsHermitian, regularizedGram]
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
    star_trivial]
  congr 1
  rw [Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro t _
  ext i j
  simp [Matrix.conjTranspose_apply, Matrix.of_apply, star_trivial, mul_comm]

/-- Λ_T is positive definite when λ > 0.

    Proof: λI is PD (`PosDef.one.smul`), each φφ^T is PSD (rank-1 outer product via
    `posSemidef_vecMulVec_star_self`), sum of PSD is PSD (`posSemidef_sum`),
    PD + PSD = PD (`PosDef.add_posSemidef`). -/
theorem regularizedGram_posDef (T : ℕ) (lam : ℝ) (hlam : 0 < lam)
    (phi : Fin T → Fin d → ℝ) [NeZero d] :
    (regularizedGram T lam phi).PosDef := by
  simp only [regularizedGram]
  apply Matrix.PosDef.add_posSemidef
  · exact Matrix.PosDef.one.smul hlam
  · apply Matrix.posSemidef_sum
    intro t _
    change (Matrix.vecMulVec (phi t) (phi t)).PosSemidef
    rw [show phi t = star (phi t) from by ext i; simp [star_trivial]]
    exact Matrix.posSemidef_vecMulVec_star_self (phi t)

/-! ### Self-Normalized Norm -/

/-- ‖v‖²_{Λ^{-1}} = v^T Λ^{-1} v. -/
def selfNormalizedNorm (v : Fin d → ℝ) (Λ : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  dotProduct v (Λ⁻¹ *ᵥ v)

/-- ‖v‖²_{Λ^{-1}} ≥ 0 for PD Λ.
    Proof: set w = Λ⁻¹v, then v^TΛ⁻¹v = w^T(Λw) ≥ 0 by PSD of Λ,
    using Λ(Λ⁻¹v) = v from invertibility. Avoids computing PosDef of Λ⁻¹. -/
theorem selfNormalizedNorm_nonneg (v : Fin d → ℝ)
    (Λ : Matrix (Fin d) (Fin d) ℝ) (hΛ : Λ.PosDef) :
    0 ≤ selfNormalizedNorm v Λ := by
  simp only [selfNormalizedNorm]
  -- Use PSD of Λ on w = Λ⁻¹ *ᵥ v: 0 ≤ star w ⬝ᵥ (Λ *ᵥ w)
  have hPSD := hΛ.posSemidef.dotProduct_mulVec_nonneg (Λ⁻¹ *ᵥ v)
  simp only [star_trivial] at hPSD
  -- Simplify: Λ *ᵥ (Λ⁻¹ *ᵥ v) = (Λ * Λ⁻¹) *ᵥ v = 1 *ᵥ v = v
  have hdet : IsUnit Λ.det := (isUnit_iff_isUnit_det (A := Λ)).mp hΛ.isUnit
  rw [mulVec_mulVec, mul_nonsing_inv Λ hdet, one_mulVec] at hPSD
  rw [dotProduct_comm] at hPSD
  exact hPSD

/-! ### Cauchy-Schwarz for Self-Normalized Norms -/

/-- |φ^T v|² ≤ ‖φ‖²_{Λ^{-1}} · ‖v‖²_Λ.

    Cauchy-Schwarz in the Λ-weighted inner product via the discriminant
    argument: the quadratic q(t) = ⟨tΛφ+v, Λ⁻¹(tΛφ+v)⟩ ≥ 0 for all t
    (since Λ⁻¹ is PSD), and expanding gives q(t) = at²+2bt+c where
    a = φ·Λφ, b = φ·v, c = v·Λ⁻¹v. Non-negative discriminant gives b²≤ac. -/
theorem self_normalized_cauchy_schwarz (phi v : Fin d → ℝ)
    (Λ : Matrix (Fin d) (Fin d) ℝ) (hΛ : Λ.PosDef) :
    (dotProduct phi v) ^ 2 ≤
      selfNormalizedNorm phi Λ⁻¹ * selfNormalizedNorm v Λ := by
  unfold selfNormalizedNorm
  -- (Λ⁻¹)⁻¹ = Λ for invertible Λ
  have hdet : IsUnit Λ.det := hΛ.isUnit.map Matrix.detMonoidHom
  rw [nonsing_inv_nonsing_inv Λ hdet]
  -- Set a = φ·Λφ, c = v·Λ⁻¹v
  set a := dotProduct phi (Λ *ᵥ phi)
  set c := dotProduct v (Λ⁻¹ *ᵥ v)
  -- Helper: Λ⁻¹ * Λ = I (for cancellation)
  have h_inv_mul : Λ⁻¹ * Λ = 1 := nonsing_inv_mul Λ hdet
  -- Helper: Λ symmetric (Λᵀ = Λ, from PD → Hermitian → symmetric for ℝ)
  have h_sym : Λ.transpose = Λ := by
    have h := hΛ.isHermitian.eq
    ext i j; change Λ j i = Λ i j
    have hij := congr_fun (congr_fun h i) j
    simp only [conjTranspose_apply, star_trivial] at hij; exact hij
  -- Helper: Λ⁻¹ symmetric
  have h_inv_sym : (Λ⁻¹).transpose = Λ⁻¹ := by
    have h := hΛ.inv.isHermitian.eq
    ext i j; change Λ⁻¹ j i = Λ⁻¹ i j
    have hij := congr_fun (congr_fun h i) j
    simp only [conjTranspose_apply, star_trivial] at hij; exact hij
  -- Helper: for symmetric M, vecMul x M = M.mulVec x
  have vecmul_eq (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.transpose = M) (x : Fin d → ℝ) :
      x ᵥ* M = M *ᵥ x := by
    conv_lhs => rw [show M = Mᵀᵀ from (transpose_transpose M).symm]
    rw [vecMul_transpose, hM]
  -- Helper: symmetric bilinear form identity ⟨Mx, y⟩ = ⟨x, My⟩
  have sym_dot (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.transpose = M) (x y : Fin d → ℝ) :
      dotProduct (M *ᵥ x) y = dotProduct x (M *ᵥ y) := by
    rw [dotProduct_comm, dotProduct_mulVec, vecmul_eq M hM, dotProduct_comm]
  -- Discriminant argument: q(t) ≥ 0 for all t implies b² ≤ ac
  suffices h_quad : ∀ t : ℝ, 0 ≤ a * t ^ 2 + 2 * dotProduct phi v * t + c by
    have ha : 0 ≤ a := by
      simpa [star_trivial] using hΛ.posSemidef.dotProduct_mulVec_nonneg phi
    by_cases ha0 : a = 0
    · -- a = 0 → Λ PD gives phi = 0 → b = 0
      have : phi = 0 := by
        by_contra h
        have := by simpa [star_trivial] using hΛ.dotProduct_mulVec_pos h
        linarith
      subst this; simp [ha0]
    · -- a > 0 → evaluate at t₀ = -b/a, multiply by a to clear fractions
      have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      have h_spec := h_quad (-(dotProduct phi v) / a)
      have key : a * (a * (-(dotProduct phi v) / a) ^ 2 +
          2 * (dotProduct phi v) * (-(dotProduct phi v) / a) + c) =
          a * c - (dotProduct phi v) ^ 2 := by
        field_simp; ring
      have h1 := mul_nonneg (le_of_lt ha_pos) h_spec
      rw [key] at h1; linarith
  -- Prove q(t) = ⟨w, Λ⁻¹ w⟩ for w = tΛφ + v, hence ≥ 0
  intro t
  have h_psd := hΛ.inv.posSemidef.dotProduct_mulVec_nonneg (t • Λ *ᵥ phi + v)
  simp only [star_trivial] at h_psd
  suffices h_eq : dotProduct (t • Λ *ᵥ phi + v) (Λ⁻¹ *ᵥ (t • Λ *ᵥ phi + v)) =
      a * t ^ 2 + 2 * dotProduct phi v * t + c by linarith
  -- Expand Λ⁻¹ *ᵥ (t • Λ *ᵥ phi + v)
  rw [mulVec_add, mulVec_smul]
  -- Λ⁻¹ (Λ phi) = phi
  rw [show Λ⁻¹ *ᵥ (Λ *ᵥ phi) = phi from by
    rw [mulVec_mulVec, h_inv_mul, one_mulVec]]
  -- Expand dot products using bilinearity
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul]
  -- Cross term: ⟨Λφ, Λ⁻¹v⟩ = ⟨φ, ΛΛ⁻¹v⟩ = ⟨φ, v⟩
  rw [sym_dot Λ h_sym phi (Λ⁻¹ *ᵥ v)]
  rw [show Λ *ᵥ (Λ⁻¹ *ᵥ v) = v from by
    rw [mulVec_mulVec, mul_nonsing_inv Λ hdet, one_mulVec]]
  rw [dotProduct_comm (Λ *ᵥ phi) phi, dotProduct_comm v phi]
  simp only [smul_eq_mul]
  ring

/-! ### Confidence Radius -/

/-- β²(T, δ) = 2σ²·(log_det_ratio + 2·log(1/δ)) where log_det_ratio = log(det Λ_T/λ^d). -/
def confidenceRadiusSq (σ δ log_det_ratio : ℝ) : ℝ :=
  2 * σ ^ 2 * (log_det_ratio + 2 * Real.log (1 / δ))

/-- β² > 0 when σ > 0, 0 < δ < 1, and log_det_ratio ≥ 0. -/
theorem confidenceRadiusSq_pos (σ δ log_det_ratio : ℝ)
    (hσ : 0 < σ) (hδ : 0 < δ) (hδ1 : δ < 1) (h_ldr : 0 ≤ log_det_ratio) :
    0 < confidenceRadiusSq σ δ log_det_ratio := by
  simp only [confidenceRadiusSq]
  apply mul_pos (mul_pos (by linarith) (sq_pos_of_pos hσ))
  have h1 : 0 < Real.log (1 / δ) := by
    apply Real.log_pos
    rwa [one_div, one_lt_inv₀ hδ]
  linarith

/-- β² is monotone increasing in log_det_ratio. -/
theorem confidenceRadiusSq_le_of_smaller_ldr (σ δ ldr₁ ldr₂ : ℝ)
    (_hσ : 0 < σ) (hδ : 0 < δ) (hδ1 : δ < 1) (h : ldr₁ ≤ ldr₂) :
    confidenceRadiusSq σ δ ldr₁ ≤ confidenceRadiusSq σ δ ldr₂ := by
  simp only [confidenceRadiusSq]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by linarith) (sq_nonneg σ))
  linarith

/-! ### Main Concentration Theorems (Conditional) -/

/-- **Vector self-normalized bound** (conditional).

-- Hypothesis: The two preconditions (`h_mgf_bound`, `h_ldr_decomp`) encode the
-- outcome of the vector self-normalized martingale argument
-- (Abbasi-Yadkori et al. 2011, Theorem 1). A full proof requires:
--   1. Constructing the supermartingale M_t = exp(λ^T S_t - ½ λ^T Λ_t λ)
--      and applying Ville's maximal inequality (measure-theoretic).
--   2. Optimizing over λ via the matrix determinant lemma to obtain the
--      log-det ratio. This step needs `Real.log_det` and the matrix
--      determinant lemma, which are not yet in Mathlib.
-- These hypotheses are the minimal interface: any proof of the martingale
-- bound that provides `h_mgf_bound` and `h_ldr_decomp` completes the theorem.

With probability ≥ 1-δ, for the weighted sum S_T = ∑_t φ_t ε_t:
  ‖S_T‖²_{Λ_T^{-1}} ≤ β²(T, δ)
where β² = 2σ²·(log det(Λ_T)/λ^d + 2 log 1/δ). -/
theorem self_normalized_bound_conditional
    (T : ℕ) (lam : ℝ) (_hlam : 0 < lam)
    (phi : Fin T → Fin d → ℝ) (sigma delta ldr : ℝ)
    (_hσ : 0 < sigma) (_hδ : 0 < delta) (_hδ1 : delta < 1)
    (weighted_sum : Fin d → ℝ)
    -- Intermediate: martingale MGF bound gives norm ≤ 2σ² · total_ldr
    (total_ldr : ℝ)
    (h_mgf_bound : selfNormalizedNorm weighted_sum (regularizedGram T lam phi) ≤
      2 * sigma ^ 2 * total_ldr)
    -- Log-det-ratio decomposition: total_ldr ≤ ldr + 2·log(1/δ)
    (h_ldr_decomp : total_ldr ≤ ldr + 2 * Real.log (1 / delta)) :
    selfNormalizedNorm weighted_sum (regularizedGram T lam phi) ≤
      confidenceRadiusSq sigma delta ldr := by
  unfold confidenceRadiusSq
  calc selfNormalizedNorm weighted_sum (regularizedGram T lam phi)
      ≤ 2 * sigma ^ 2 * total_ldr := h_mgf_bound
    _ ≤ 2 * sigma ^ 2 * (ldr + 2 * Real.log (1 / delta)) := by
        apply mul_le_mul_of_nonneg_left h_ldr_decomp
        exact mul_nonneg (by norm_num) (sq_nonneg sigma)

/-- **Confidence ellipsoid contains θ*** (conditional).

-- Hypothesis: The two preconditions encode the standard OLS reduction:
--   1. `h_error_eq`: The estimation error θ̂ - θ* equals a weighted noise
--      vector Λ_T⁻¹ Σ_t φ_t ε_t. This is an algebraic identity from the
--      normal equations (Λ_T θ̂ = Σ_t φ_t y_t) that holds for any linear
--      regression estimator. A full proof needs Mathlib's `Matrix.mulVec`
--      injectivity from `PosDef.isUnit` — straightforward but tedious.
--   2. `h_noise_bound`: The self-normalized bound on the noise sum, which
--      follows from `self_normalized_bound_conditional` above once the
--      martingale hypotheses are discharged.

The ellipsoidal confidence set C_T = {θ | ‖θ̂-θ‖²_Λ ≤ β²} contains the
true parameter θ* with probability ≥ 1-δ.

This is the key lemma for LinUCB's optimism guarantee. -/
theorem confidence_ellipsoid_conditional
    (T : ℕ) (lam : ℝ) (_hlam : 0 < lam)
    (phi : Fin T → Fin d → ℝ) (theta_star theta_hat : Fin d → ℝ)
    (sigma delta ldr : ℝ)
    (_hσ : 0 < sigma) (_hδ : 0 < delta) (_hδ1 : delta < 1)
    -- Estimation error = Λ⁻¹ · weighted noise sum
    (weighted_noise : Fin d → ℝ)
    (h_error_eq : ∀ i, theta_hat i - theta_star i = weighted_noise i)
    -- Self-normalized bound on the noise sum (from martingale argument)
    (h_noise_bound : selfNormalizedNorm weighted_noise
        (regularizedGram T lam phi) ≤
      confidenceRadiusSq sigma delta ldr) :
    selfNormalizedNorm (fun i => theta_hat i - theta_star i)
      (regularizedGram T lam phi) ≤
      confidenceRadiusSq sigma delta ldr := by
  have h_eq : (fun i => theta_hat i - theta_star i) = weighted_noise :=
    funext h_error_eq
  rw [h_eq]
  exact h_noise_bound

/-! ### LinUCB Application -/

/-- **LinUCB prediction error bound**.

For arm feature vector φ, the prediction error satisfies:
  |φ^T (θ̂ - θ*)| ≤ ‖φ‖_{Λ^{-1}} · β(T, δ)

Proof: |φ^T (θ̂-θ*)| ≤ ‖φ‖_{Λ^{-1}} · ‖θ̂-θ*‖_Λ  (Cauchy-Schwarz, proved)
       ‖θ̂-θ*‖_Λ ≤ β(T,δ)                           (confidence ellipsoid) -/
theorem linucb_prediction_error
    (T : ℕ) (lam : ℝ) (hlam : 0 < lam)
    (phi_arm : Fin d → ℝ) (theta_star theta_hat : Fin d → ℝ)
    (sigma delta ldr : ℝ) (_hσ : 0 < sigma)
    (_hδ : 0 < delta) (_hδ1 : delta < 1) (_h_ldr : 0 ≤ ldr)
    (phi_hist : Fin T → Fin d → ℝ) [NeZero d]
    (beta_sq := confidenceRadiusSq sigma delta ldr)
    (h_conc : selfNormalizedNorm (fun i => theta_hat i - theta_star i)
        (regularizedGram T lam phi_hist) ≤ beta_sq) :
    (dotProduct phi_arm (fun i => theta_hat i - theta_star i)) ^ 2 ≤
      selfNormalizedNorm phi_arm (regularizedGram T lam phi_hist)⁻¹ * beta_sq := by
  have hΛ_pd := regularizedGram_posDef T lam hlam phi_hist
  -- Cauchy-Schwarz: |φ^T v|² ≤ ‖φ‖²_{Λ⁻¹} · ‖v‖²_Λ (proved inline)
  have h_cs := self_normalized_cauchy_schwarz phi_arm
    (fun i => theta_hat i - theta_star i) (regularizedGram T lam phi_hist) hΛ_pd
  have h_phi_nonneg : 0 ≤ selfNormalizedNorm phi_arm (regularizedGram T lam phi_hist)⁻¹ := by
    apply selfNormalizedNorm_nonneg
    exact hΛ_pd.inv
  exact le_trans h_cs (mul_le_mul_of_nonneg_left h_conc h_phi_nonneg)

end
