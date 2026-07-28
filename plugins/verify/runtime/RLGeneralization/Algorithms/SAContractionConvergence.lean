import Mathlib.Tactic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# SA Contraction Convergence

Deterministic contraction convergence for stochastic approximation:
if e(t+1) ≤ (1 - c·α_t)·e(t) with divergent step sizes, then e(t) → 0.
-/

open Finset BigOperators

theorem sa_contraction_convergence
    (e : ℕ → ℝ) (α : ℕ → ℝ) (c : ℝ)
    (hc_pos : 0 < c)
    (hα_nn : ∀ t, 0 ≤ α t)
    (hcα_le1 : ∀ t, c * α t ≤ 1)
    (he_nn : ∀ t, 0 ≤ e t)
    (he_rec : ∀ t, e (t + 1) ≤ (1 - c * α t) * e t)
    (hα_div : ∀ B : ℝ, ∃ N, B ≤ ∑ k ∈ Finset.range N, α k) :
    Filter.Tendsto e Filter.atTop (nhds 0) := by
  set a := fun k => c * α k with ha_def
  have ha_nn : ∀ k, 0 ≤ a k := fun k => mul_nonneg (le_of_lt hc_pos) (hα_nn k)
  have ha_le1 : ∀ k, a k ≤ 1 := hcα_le1
  have error_le_prod : ∀ t, e t ≤ e 0 * ∏ k ∈ Finset.range t, (1 - a k) := by
    intro t; induction t with
    | zero => simp
    | succ n ih =>
      calc e (n + 1) ≤ (1 - a n) * e n := he_rec n
        _ ≤ (1 - a n) * (e 0 * ∏ k ∈ Finset.range n, (1 - a k)) :=
            mul_le_mul_of_nonneg_left ih (by linarith [ha_le1 n])
        _ = e 0 * ((∏ k ∈ Finset.range n, (1 - a k)) * (1 - a n)) := by ring
        _ = e 0 * ∏ k ∈ Finset.range (n + 1), (1 - a k) := by rw [Finset.prod_range_succ]
  have prod_le_exp : ∀ n, ∏ k ∈ Finset.range n, (1 - a k) ≤ Real.exp (- ∑ k ∈ Finset.range n, a k) := by
    intro n; induction n with
    | zero => simp
    | succ m ih =>
      rw [Finset.prod_range_succ, Finset.sum_range_succ, neg_add]
      calc (∏ k ∈ Finset.range m, (1 - a k)) * (1 - a m)
          ≤ Real.exp (- ∑ k ∈ Finset.range m, a k) * (1 - a m) :=
            mul_le_mul_of_nonneg_right ih (by linarith [ha_le1 m])
        _ ≤ Real.exp (- ∑ k ∈ Finset.range m, a k) * Real.exp (-(a m)) := by
            apply mul_le_mul_of_nonneg_left _ (le_of_lt (Real.exp_pos _))
            linarith [Real.add_one_le_exp (-(a m))]
        _ = Real.exp (- ∑ k ∈ Finset.range m, a k + -(a m)) := by rw [← Real.exp_add]
  have h_upper : ∀ n, e n ≤ e 0 * Real.exp (-∑ k ∈ Finset.range n, a k) := by
    intro n
    calc e n ≤ e 0 * ∏ k ∈ Finset.range n, (1 - a k) := error_le_prod n
      _ ≤ e 0 * Real.exp (-∑ k ∈ Finset.range n, a k) :=
          mul_le_mul_of_nonneg_left (prod_le_exp n) (he_nn 0)
  have h_sum_div : Filter.Tendsto (fun n => ∑ k ∈ Finset.range n, a k) Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    obtain ⟨N, hN⟩ := hα_div (b / c)
    use N; intro n hn
    have hsub : ∑ k ∈ Finset.range N, α k ≤ ∑ k ∈ Finset.range n, α k :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hn) (fun i _ _ => hα_nn i)
    calc b = c * (b / c) := by field_simp
      _ ≤ c * ∑ k ∈ Finset.range N, α k := mul_le_mul_of_nonneg_left hN (le_of_lt hc_pos)
      _ ≤ c * ∑ k ∈ Finset.range n, α k := mul_le_mul_of_nonneg_left hsub (le_of_lt hc_pos)
      _ = ∑ k ∈ Finset.range n, a k := by rw [ha_def, ← Finset.mul_sum]
  have h_bound_zero : Filter.Tendsto (fun n => e 0 * Real.exp (-∑ k ∈ Finset.range n, a k)) Filter.atTop (nhds 0) := by
    have h_exp : Filter.Tendsto (fun n => Real.exp (-∑ k ∈ Finset.range n, a k)) Filter.atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp (Filter.tendsto_neg_atTop_atBot.comp h_sum_div)
    have h_mul := h_exp.const_mul (e 0)
    simp at h_mul; exact h_mul
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_bound_zero he_nn h_upper
