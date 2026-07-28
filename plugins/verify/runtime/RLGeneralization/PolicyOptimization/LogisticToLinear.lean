import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

open Finset BigOperators

open Real

noncomputable def σ (t : ℝ) : ℝ := 1 / (1 + exp (-t))

theorem σ_le_one (t : ℝ) : σ t ≤ 1 := by
  unfold σ; rw [div_le_one (by positivity)]; linarith [exp_pos (-t)]

theorem σ_nonneg (t : ℝ) : 0 ≤ σ t := by
  unfold σ; positivity

theorem logistic_to_linear (K : ℝ) (hK : 1 ≤ Real.log K) (β : ℝ) (hβ : 0 < β)
    (y : ℝ) (hy : 0 ≤ y) :
    y * σ (-β * y + Real.log K) ≤ 2 * Real.log K / β := by
  have hlog_pos : 0 < Real.log K := by linarith
  by_cases hcase : y ≤ 2 * Real.log K / β
  · nlinarith [σ_le_one (-β * y + Real.log K), σ_nonneg (-β * y + Real.log K)]
  · push_neg at hcase
    have hy_pos : 0 < y :=
      lt_of_le_of_lt (div_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (le_of_lt hlog_pos)) (le_of_lt hβ)) hcase
    have hby_pos : 0 < β * y := by positivity
    unfold σ
    have h_neg : -(- β * y + Real.log K) = β * y - Real.log K := by ring
    rw [h_neg, mul_one_div]
    have h_2logK_lt : 2 * Real.log K < β * y := by
      have := (div_lt_iff₀ hβ).mp hcase; nlinarith
    have hexp_lower : β * y - Real.log K + 1 ≤ exp (β * y - Real.log K) := add_one_le_exp _
    have hden : β * y / 2 ≤ 1 + exp (β * y - Real.log K) := by nlinarith
    have hby2_pos : 0 < β * y / 2 := by positivity
    have h1 : y / (1 + exp (β * y - Real.log K)) ≤ y / (β * y / 2) :=
      div_le_div_of_nonneg_left (le_of_lt hy_pos) hby2_pos hden
    have h2 : y / (β * y / 2) = 2 / β := by
      have : β ≠ 0 := ne_of_gt hβ
      have : y ≠ 0 := ne_of_gt hy_pos
      field_simp
    linarith [show (2:ℝ) / β ≤ 2 * Real.log K / β from by
      rw [div_le_div_iff₀ hβ hβ]; nlinarith]
