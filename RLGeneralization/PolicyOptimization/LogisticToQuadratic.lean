import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic
import RLGeneralization.PolicyOptimization.LogisticToLinear

open Finset BigOperators

open Real

-- σ and σ_le_one come from LogisticToLinear

theorem logistic_to_quadratic (K : ℝ) (hK : 1 ≤ K) (z : ℝ) (hz : 0 ≤ z) :
    σ (z - Real.log K) ≤ 2 * (z ^ 2 + K⁻¹) := by
  have hK_pos : (0 : ℝ) < K := by linarith
  by_cases hcase : 1 ≤ z
  · have h1 := σ_le_one (z - Real.log K)
    have h2 : (0 : ℝ) ≤ K⁻¹ := by positivity
    nlinarith [sq_nonneg z]
  · push_neg at hcase
    unfold σ
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 1 + exp (-(z - Real.log K)))]
    have hrew : exp (-(z - Real.log K)) = K * exp (-z) := by
      rw [show -(z - Real.log K) = Real.log K + (-z) from by ring, exp_add, exp_log hK_pos]
    rw [hrew]
    have hexpand : 2 * (z ^ 2 + K⁻¹) * (1 + K * exp (-z))
      = 2 * z ^ 2 + 2 * K * z ^ 2 * exp (-z) + 2 * K⁻¹ + 2 * exp (-z) := by
      field_simp; ring
    rw [hexpand]
    have hexp : 1 - z ≤ exp (-z) := by linarith [add_one_le_exp (-z)]
    have hKz : 0 ≤ 2 * K * z ^ 2 * exp (-z) := by positivity
    have hKinv : 0 ≤ 2 * K⁻¹ := by positivity
    nlinarith [sq_nonneg (z - 1/2)]
