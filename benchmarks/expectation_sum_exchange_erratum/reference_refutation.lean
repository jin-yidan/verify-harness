import Mathlib

open MeasureTheory Filter Set

namespace ErratumVerify

/-- Escaping-mass counterexample to the limit-exchange inference of the
proposition's proof ("Sₙ → X pointwise ⟹ E[Sₙ] → E[X]"): on (0,1] with
Lebesgue measure, Z n = n·1_{(0,1/n]} tends to 0 at every point of (0,1],
yet ∫ Z n = 1 for every n ≥ 1. Taking X₁ = Z 1, Xᵢ = Z i − Z (i−1) gives
partial sums Sₙ = Z n with every E[Xᵢ] defined, X = Σᵢ Xᵢ = 0 pointwise,
but E[Sₙ] = 1 ↛ 0 = E[X]. -/
theorem limit_exchange_counterexample :
    ∃ Z : ℕ → ℝ → ℝ,
      (∀ x ∈ Set.Ioc (0:ℝ) 1,
        Tendsto (fun n => Z n x) atTop (nhds 0)) ∧
      (∀ n : ℕ, 1 ≤ n → ∫ x in Set.Ioc (0:ℝ) 1, Z n x = 1) := by
  refine ⟨fun n x => Set.indicator (Set.Ioc (0:ℝ) (1 / (n:ℝ)))
            (fun _ => (n : ℝ)) x, ?_, ?_⟩
  · intro x hx
    apply tendsto_atTop_of_eventually_const (i₀ := ⌈1 / x⌉₊ + 1)
    intro n hn
    have hx0 : 0 < x := hx.1
    have h1n : 1 / (n : ℝ) < x := by
      have hceil : (1 / x) ≤ (⌈1 / x⌉₊ : ℝ) := Nat.le_ceil _
      have hnn : (⌈1 / x⌉₊ : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn
      have hnpos : (0:ℝ) < n := lt_of_lt_of_le (by positivity) hnn
      rw [div_lt_iff₀ hnpos]
      have h1x : 1 / x < (n : ℝ) := lt_of_le_of_lt hceil (by linarith)
      calc (1:ℝ) = x * (1 / x) := by field_simp
        _ < x * n := mul_lt_mul_of_pos_left h1x hx0
    exact Set.indicator_of_notMem (fun hmem => absurd hmem.2 (not_le.mpr h1n)) _
  · intro n hn
    have hnR : (0:ℝ) < n := by exact_mod_cast hn
    rw [setIntegral_indicator measurableSet_Ioc]
    have hinter : Set.Ioc (0:ℝ) 1 ∩ Set.Ioc (0:ℝ) (1 / (n:ℝ)) =
        Set.Ioc (0:ℝ) (1 / (n:ℝ)) := by
      apply Set.inter_eq_self_of_subset_right
      apply Set.Ioc_subset_Ioc_right
      rw [div_le_one hnR]
      exact_mod_cast hn
    have h0 : (0:ℝ) ≤ 1 / (n:ℝ) - 0 := by rw [sub_zero]; positivity
    rw [hinter, setIntegral_const, measureReal_def, Real.volume_Ioc,
        ENNReal.toReal_ofReal h0, smul_eq_mul, sub_zero]
    field_simp

end ErratumVerify

#print axioms ErratumVerify.limit_exchange_counterexample
