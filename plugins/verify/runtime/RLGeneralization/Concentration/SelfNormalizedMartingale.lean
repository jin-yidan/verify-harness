/-
# Self-Normalized Martingale Infrastructure

Discharges the conditional hypotheses in `self_normalized_bound_conditional`
from SelfNormalized.lean. Provides the probability-event machinery:
Ville's inequality for finitary supermartingales, sub-Gaussian MGF
to tail bound conversion, and the self-normalized concentration theorem.

## Main Results

* `ville_inequality_finitary` — P(M ≥ c) ≤ 1/c for supermartingale M
* `subgaussian_mgf_to_concentration` — MGF bound → sub-Gaussian tail
* `self_normalized_concentration` — ‖S_T‖²_{Λ⁻¹} concentration from supermartingale
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Finset BigOperators Real

noncomputable section

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

def eventProb' (P : Ω → ℝ) (pred : Ω → Prop) [DecidablePred pred] : ℝ :=
  ∑ ω ∈ Finset.univ.filter pred, P ω

theorem ville_inequality_finitary
    (P : Ω → ℝ) (hP : ∀ ω, 0 ≤ P ω) (hsum : ∑ ω : Ω, P ω = 1)
    (M : Ω → ℝ) (hM_nn : ∀ ω, 0 ≤ M ω)
    (h_supermtg : ∑ ω : Ω, P ω * M ω ≤ 1)
    (c : ℝ) (hc : 0 < c) :
    eventProb' P (fun ω => c ≤ M ω) ≤ 1 / c := by
  rw [le_div_iff₀ hc]
  unfold eventProb'
  calc (∑ ω ∈ Finset.univ.filter (fun ω => c ≤ M ω), P ω) * c
      ≤ ∑ ω ∈ Finset.univ.filter (fun ω => c ≤ M ω), P ω * M ω := by
        rw [Finset.sum_mul]
        apply Finset.sum_le_sum; intro ω hω
        have hmem := (Finset.mem_filter.mp hω).2
        exact mul_le_mul_of_nonneg_left hmem (hP ω)
    _ ≤ ∑ ω : Ω, P ω * M ω :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun ω _ _ => mul_nonneg (hP ω) (hM_nn ω))
    _ ≤ 1 := h_supermtg

theorem subgaussian_mgf_to_concentration
    (P : Ω → ℝ) (hP : ∀ ω, 0 ≤ P ω) (hsum : ∑ ω : Ω, P ω = 1)
    (X : Ω → ℝ) (sigma : ℝ) (hsigma : 0 < sigma)
    (h_mgf : ∀ lam : ℝ, 0 < lam →
      ∑ ω : Ω, P ω * Real.exp (lam * X ω - lam ^ 2 * sigma ^ 2 / 2) ≤ 1)
    (t : ℝ) (ht : 0 < t) :
    eventProb' P (fun ω => t ≤ X ω) ≤ Real.exp (- t ^ 2 / (2 * sigma ^ 2)) := by
  set lam_opt := t / sigma ^ 2 with hlam_def
  have hlam_pos : 0 < lam_opt := div_pos ht (by positivity)
  have h_spec := h_mgf lam_opt hlam_pos
  have h_ville := ville_inequality_finitary P hP hsum
    (fun ω => Real.exp (lam_opt * X ω - lam_opt ^ 2 * sigma ^ 2 / 2))
    (fun ω => le_of_lt (Real.exp_pos _))
    h_spec
    (Real.exp (lam_opt * t - lam_opt ^ 2 * sigma ^ 2 / 2))
    (Real.exp_pos _)
  have h_mono : eventProb' P (fun ω => t ≤ X ω) ≤
      eventProb' P (fun ω => Real.exp (lam_opt * t - lam_opt ^ 2 * sigma ^ 2 / 2) ≤
        Real.exp (lam_opt * X ω - lam_opt ^ 2 * sigma ^ 2 / 2)) := by
    unfold eventProb'
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro ω hω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
      apply Real.exp_le_exp.mpr
      linarith [mul_le_mul_of_nonneg_left hω (le_of_lt hlam_pos)]
    · intro ω _ _; exact hP ω
  calc eventProb' P (fun ω => t ≤ X ω)
      ≤ eventProb' P _ := h_mono
    _ ≤ 1 / Real.exp (lam_opt * t - lam_opt ^ 2 * sigma ^ 2 / 2) := h_ville
    _ = Real.exp (-(lam_opt * t - lam_opt ^ 2 * sigma ^ 2 / 2)) := by
        rw [one_div, Real.exp_neg]
    _ = Real.exp (- t ^ 2 / (2 * sigma ^ 2)) := by
        congr 1; rw [hlam_def]; field_simp; ring

theorem self_normalized_concentration
    (P : Ω → ℝ) (hP : ∀ ω, 0 ≤ P ω) (hsum : ∑ ω : Ω, P ω = 1)
    (self_norm_sq : Ω → ℝ) (h_nn : ∀ ω, 0 ≤ self_norm_sq ω)
    (sigma : ℝ) (hsigma : 0 < sigma)
    (log_det_ratio : ℝ) (hldr : 0 ≤ log_det_ratio)
    (h_supermtg : ∑ ω : Ω, P ω *
      Real.exp (self_norm_sq ω / (2 * sigma ^ 2) - log_det_ratio / 2) ≤ 1)
    (delta : ℝ) (hdelta : 0 < delta) :
    eventProb' P (fun ω =>
      sigma ^ 2 * log_det_ratio + 2 * sigma ^ 2 * Real.log (1 / delta)
        < self_norm_sq ω) ≤ delta := by
  set threshold := sigma ^ 2 * log_det_ratio + 2 * sigma ^ 2 * Real.log (1 / delta)
  set M := fun ω => Real.exp (self_norm_sq ω / (2 * sigma ^ 2) - log_det_ratio / 2)
  have hM_nn : ∀ ω, 0 ≤ M ω := fun ω => le_of_lt (Real.exp_pos _)
  set c_val := 1 / delta
  have hc_pos : 0 < c_val := by positivity
  have h_ville := ville_inequality_finitary P hP hsum M hM_nn h_supermtg c_val hc_pos
  have h_mono : eventProb' P (fun ω => threshold < self_norm_sq ω) ≤
      eventProb' P (fun ω => c_val ≤ M ω) := by
    unfold eventProb'
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro ω hω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
      rw [show c_val = Real.exp (Real.log c_val) from (Real.exp_log hc_pos).symm]
      apply Real.exp_le_exp.mpr
      show Real.log (1 / delta) ≤ self_norm_sq ω / (2 * sigma ^ 2) - log_det_ratio / 2
      have hsig2 : (0 : ℝ) < 2 * sigma ^ 2 := by positivity
      rw [le_sub_iff_add_le, le_div_iff₀ hsig2]
      nlinarith
    · intro ω _ _; exact hP ω
  calc eventProb' P (fun ω => threshold < self_norm_sq ω)
      ≤ eventProb' P (fun ω => c_val ≤ M ω) := h_mono
    _ ≤ 1 / c_val := h_ville
    _ = delta := by
        show 1 / (1 / delta) = delta
        rw [one_div_one_div]

end
