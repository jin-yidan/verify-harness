/-
# Probability Event Framework

Finitary probability event API for high-probability statements and union bounds.
Works over finite sample spaces with explicit probability mass functions.

## Main Results

* `eventProb_nonneg` — event probability is nonneg
* `eventProb_le_one` — event probability is at most 1
* `complement_split` — P(A) + P(¬A) = 1
* `complementProb_le` — if P(¬good) ≤ δ then P(good) ≥ 1-δ
* `markov_bound` — P(X ≥ t) ≤ E[X]/t
* `eventProb_mono` — monotonicity of event probability
* `union_bound_two` — P(A ∨ B) ≤ P(A) + P(B)
* `good_event_intersection` — P(A ∧ B) ≥ 1 - (δ₁ + δ₂) from individual failure bounds
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Finset BigOperators

noncomputable section

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

def eventProb (P : Ω → ℝ) (pred : Ω → Prop) [DecidablePred pred] : ℝ :=
  ∑ ω ∈ Finset.univ.filter pred, P ω

theorem eventProb_nonneg (P : Ω → ℝ) (hP : ∀ ω, 0 ≤ P ω)
    (pred : Ω → Prop) [DecidablePred pred] :
    0 ≤ eventProb P pred :=
  Finset.sum_nonneg fun ω _ => hP ω

theorem eventProb_le_one (P : Ω → ℝ) (hP : ∀ ω, 0 ≤ P ω)
    (hsum : ∑ ω : Ω, P ω = 1)
    (pred : Ω → Prop) [DecidablePred pred] :
    eventProb P pred ≤ 1 := by
  unfold eventProb
  calc ∑ ω ∈ Finset.univ.filter pred, P ω
      ≤ ∑ ω : Ω, P ω :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun ω _ _ => hP ω)
    _ = 1 := hsum

theorem complement_split (P : Ω → ℝ)
    (hsum : ∑ ω : Ω, P ω = 1)
    (pred : Ω → Prop) [DecidablePred pred] :
    eventProb P pred + eventProb P (fun ω => ¬ pred ω) = 1 := by
  unfold eventProb
  rw [← hsum, ← Finset.sum_filter_add_sum_filter_not Finset.univ pred]

theorem complementProb_le (P : Ω → ℝ) (hP : ∀ ω, 0 ≤ P ω)
    (hsum : ∑ ω : Ω, P ω = 1)
    (good : Ω → Prop) [DecidablePred good] (δ : ℝ)
    (h_fail : eventProb P (fun ω => ¬ good ω) ≤ δ) :
    eventProb P good ≥ 1 - δ := by
  have h_split := complement_split P hsum good
  linarith

theorem markov_bound (P : Ω → ℝ) (hP : ∀ ω, 0 ≤ P ω)
    (X : Ω → ℝ) (hX : ∀ ω, 0 ≤ X ω)
    (t : ℝ) (ht : 0 < t)
    (mean : ℝ) (hmean : ∑ ω : Ω, P ω * X ω = mean) :
    eventProb P (fun ω => t ≤ X ω) ≤ mean / t := by
  rw [le_div_iff₀ ht]
  unfold eventProb
  calc (∑ ω ∈ Finset.univ.filter (fun ω => t ≤ X ω), P ω) * t
      ≤ ∑ ω ∈ Finset.univ.filter (fun ω => t ≤ X ω), P ω * X ω := by
        rw [Finset.sum_mul]
        apply Finset.sum_le_sum; intro ω hω
        have hmem := (Finset.mem_filter.mp hω).2
        exact mul_le_mul_of_nonneg_left hmem (hP ω)
    _ ≤ ∑ ω : Ω, P ω * X ω :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun ω _ _ => mul_nonneg (hP ω) (hX ω))
    _ = mean := hmean

theorem eventProb_mono (P : Ω → ℝ) (hP : ∀ ω, 0 ≤ P ω)
    (p q : Ω → Prop) [DecidablePred p] [DecidablePred q]
    (h : ∀ ω, p ω → q ω) :
    eventProb P p ≤ eventProb P q := by
  unfold eventProb
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    exact h ω hω
  · intro ω _ _; exact hP ω

theorem union_bound_two (P : Ω → ℝ) (hP : ∀ ω, 0 ≤ P ω)
    (A B : Ω → Prop) [DecidablePred A] [DecidablePred B]
    (δ₁ δ₂ : ℝ) (hA : eventProb P A ≤ δ₁) (hB : eventProb P B ≤ δ₂) :
    eventProb P (fun ω => A ω ∨ B ω) ≤ δ₁ + δ₂ := by
  unfold eventProb at *
  calc ∑ ω ∈ Finset.univ.filter (fun ω => A ω ∨ B ω), P ω
      ≤ ∑ ω ∈ Finset.univ.filter A ∪ Finset.univ.filter B, P ω := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro ω hω
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hω ⊢
          exact hω
        · intro ω _ _; exact hP ω
    _ ≤ ∑ ω ∈ Finset.univ.filter A, P ω + ∑ ω ∈ Finset.univ.filter B, P ω := by
        rw [← Finset.sum_union_inter]
        linarith [Finset.sum_nonneg (fun ω (_ : ω ∈ Finset.univ.filter A ∩ Finset.univ.filter B) => hP ω)]
    _ ≤ δ₁ + δ₂ := add_le_add hA hB

theorem good_event_intersection (P : Ω → ℝ) (hP : ∀ ω, 0 ≤ P ω)
    (hsum : ∑ ω : Ω, P ω = 1)
    (A B : Ω → Prop) [DecidablePred A] [DecidablePred B]
    (δ₁ δ₂ : ℝ)
    (hA : eventProb P (fun ω => ¬ A ω) ≤ δ₁)
    (hB : eventProb P (fun ω => ¬ B ω) ≤ δ₂) :
    eventProb P (fun ω => A ω ∧ B ω) ≥ 1 - (δ₁ + δ₂) := by
  apply complementProb_le P hP hsum
  have hmono : eventProb P (fun ω => ¬ (A ω ∧ B ω)) ≤
      eventProb P (fun ω => ¬ A ω ∨ ¬ B ω) := by
    apply eventProb_mono P hP
    intro ω h; exact not_and_or.mp h
  calc eventProb P (fun ω => ¬ (A ω ∧ B ω))
      ≤ eventProb P (fun ω => ¬ A ω ∨ ¬ B ω) := hmono
    _ ≤ δ₁ + δ₂ := union_bound_two P hP _ _ δ₁ δ₂ hA hB

end
