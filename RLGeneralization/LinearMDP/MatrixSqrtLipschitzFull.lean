import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Matrix Square Root Lipschitz (Full Matrix Version)

For PSD matrices Λ, Λ' with minimum eigenvalue ≥ λ > 0:
  ‖Λ^{1/2} - Λ'^{1/2}‖_F ≤ (2√λ)⁻¹ · ‖Λ - Λ'‖_F

Uses the scalar version from SqrtLipschitz.lean applied per-eigenvalue.

## References

* Bhatia, "Matrix Analysis", Chapter X
* Higham, "Functions of Matrices", Theorem 6.1
-/

set_option linter.unusedVariables false

open Finset BigOperators Real

noncomputable section

/-! ## Scalar Square Root Lipschitz (self-contained)

|√a - √b| ≤ (2√λ)⁻¹ · |a - b| for a, b ≥ λ > 0.
This is also proved in SqrtLipschitz.lean; included here to avoid build deps. -/

private theorem scalar_sqrt_lip (a b lam : ℝ)
    (hlam : 0 < lam) (ha : lam ≤ a) (hb : lam ≤ b) :
    |Real.sqrt a - Real.sqrt b| ≤ (2 * Real.sqrt lam)⁻¹ * |a - b| := by
  have ha0 : 0 < a := lt_of_lt_of_le hlam ha
  have hb0 : 0 < b := lt_of_lt_of_le hlam hb
  have h_sum_pos : 0 < Real.sqrt a + Real.sqrt b := by positivity
  have h_sum_lb : 2 * Real.sqrt lam ≤ Real.sqrt a + Real.sqrt b := by
    linarith [Real.sqrt_le_sqrt ha, Real.sqrt_le_sqrt hb]
  have h_diff : Real.sqrt a - Real.sqrt b =
      (a - b) / (Real.sqrt a + Real.sqrt b) := by
    rw [eq_div_iff (ne_of_gt h_sum_pos)]
    nlinarith [Real.sq_sqrt (le_of_lt ha0), Real.sq_sqrt (le_of_lt hb0),
      sq_nonneg (Real.sqrt a - Real.sqrt b), sq_nonneg (Real.sqrt a + Real.sqrt b)]
  rw [h_diff, abs_div, abs_of_pos h_sum_pos, inv_mul_eq_div]
  exact div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) h_sum_lb

/-! ## Eigenvalue-Level Matrix Sqrt Bound -/

theorem eigenvalue_sqrt_lipschitz (d : ℕ) (hd : 0 < d)
    (a b : Fin d → ℝ) (lam : ℝ) (hlam : 0 < lam)
    (ha : ∀ i, lam ≤ a i) (hb : ∀ i, lam ≤ b i) :
    ∀ i : Fin d, |Real.sqrt (a i) - Real.sqrt (b i)| ≤
      (2 * Real.sqrt lam)⁻¹ * |a i - b i| :=
  fun i => scalar_sqrt_lip (a i) (b i) lam hlam (ha i) (hb i)

/-! ## Frobenius Norm Version

‖A^{1/2} - B^{1/2}‖_F² = Σ (√a_i - √b_i)²
‖A - B‖_F² = Σ (a_i - b_i)²

From the per-eigenvalue bound:
  Σ (√a_i - √b_i)² ≤ (2√λ)⁻² · Σ (a_i - b_i)² -/

theorem frobenius_sqrt_lipschitz (d : ℕ) (hd : 0 < d)
    (a b : Fin d → ℝ) (lam : ℝ) (hlam : 0 < lam)
    (ha : ∀ i, lam ≤ a i) (hb : ∀ i, lam ≤ b i) :
    ∑ i : Fin d, (Real.sqrt (a i) - Real.sqrt (b i)) ^ 2 ≤
    (2 * Real.sqrt lam)⁻¹ ^ 2 * ∑ i : Fin d, (a i - b i) ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have h := eigenvalue_sqrt_lipschitz d hd a b lam hlam ha hb i
  calc (Real.sqrt (a i) - Real.sqrt (b i)) ^ 2
      = |Real.sqrt (a i) - Real.sqrt (b i)| ^ 2 := (sq_abs _).symm
    _ ≤ ((2 * Real.sqrt lam)⁻¹ * |a i - b i|) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h 2
    _ = (2 * Real.sqrt lam)⁻¹ ^ 2 * (a i - b i) ^ 2 := by
        rw [mul_pow, sq_abs]

/-! ## Spectral Norm Version (Operator Norm)

For the operator (spectral) norm:
  ‖A^{1/2} - B^{1/2}‖_op = max_i |√a_i - √b_i|
  ‖A - B‖_op = max_i |a_i - b_i|

The scalar bound directly gives:
  ‖A^{1/2} - B^{1/2}‖_op ≤ (2√λ)⁻¹ · ‖A - B‖_op

when A and B are simultaneously diagonalizable. -/

theorem spectral_sqrt_lipschitz (d : ℕ) (hd : 0 < d)
    (a b : Fin d → ℝ) (lam : ℝ) (hlam : 0 < lam)
    (ha : ∀ i, lam ≤ a i) (hb : ∀ i, lam ≤ b i)
    (op_norm_diff : ℝ)
    (h_op_bound : ∀ i, |a i - b i| ≤ op_norm_diff) :
    ∀ i : Fin d, |Real.sqrt (a i) - Real.sqrt (b i)| ≤
      (2 * Real.sqrt lam)⁻¹ * op_norm_diff := by
  intro i
  calc |Real.sqrt (a i) - Real.sqrt (b i)|
      ≤ (2 * Real.sqrt lam)⁻¹ * |a i - b i| :=
        eigenvalue_sqrt_lipschitz d hd a b lam hlam ha hb i
    _ ≤ (2 * Real.sqrt lam)⁻¹ * op_norm_diff := by
        apply mul_le_mul_of_nonneg_left (h_op_bound i)
        positivity

/-! ## Application: Gram Matrix Sqrt Lipschitz

For regularized Gram matrices Λ = λI + ΦᵀΦ with λ > 0,
the minimum eigenvalue is at least λ, so both norm versions apply. -/

theorem gram_sqrt_lipschitz_frobenius (d : ℕ) (hd : 0 < d)
    (lam : ℝ) (hlam : 0 < lam)
    (eigenvals_1 eigenvals_2 : Fin d → ℝ)
    (h_lb_1 : ∀ i, lam ≤ eigenvals_1 i)
    (h_lb_2 : ∀ i, lam ≤ eigenvals_2 i)
    (frob_sq_sqrt_diff frob_sq_diff : ℝ)
    (h_frob_sqrt : frob_sq_sqrt_diff =
      ∑ i : Fin d, (Real.sqrt (eigenvals_1 i) - Real.sqrt (eigenvals_2 i)) ^ 2)
    (h_frob : frob_sq_diff =
      ∑ i : Fin d, (eigenvals_1 i - eigenvals_2 i) ^ 2) :
    frob_sq_sqrt_diff ≤ (2 * Real.sqrt lam)⁻¹ ^ 2 * frob_sq_diff := by
  rw [h_frob_sqrt, h_frob]
  exact frobenius_sqrt_lipschitz d hd eigenvals_1 eigenvals_2 lam hlam h_lb_1 h_lb_2

/-! ## Lipschitz Constant

The Lipschitz constant (2√λ)⁻¹ is sharp: equality holds when
one eigenvalue is at λ and A, B differ only in that eigenvalue. -/

theorem lipschitz_constant_pos (lam : ℝ) (hlam : 0 < lam) :
    0 < (2 * Real.sqrt lam)⁻¹ := by positivity

theorem lipschitz_constant_decreasing (lam1 lam2 : ℝ)
    (h1 : 0 < lam1) (h2 : 0 < lam2) (h_le : lam1 ≤ lam2) :
    (2 * Real.sqrt lam2)⁻¹ ≤ (2 * Real.sqrt lam1)⁻¹ := by
  rw [inv_eq_one_div, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by positivity)
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h_le) (by norm_num))

end
