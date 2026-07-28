/-
# Online-to-Batch Conversion

Converts cumulative bounds to per-round guarantees: if the total is ≤ R,
then some round achieves ≤ R/T (minimum ≤ average).

## Main Results

* `exists_le_div_of_sum_le` — ∑ aₖ ≤ R ⟹ ∃ t < T, aₜ ≤ R/T

## References

* Shalev-Shwartz, "Online Learning and Online Convex Optimization" (2012)
* Hazan, "Introduction to Online Convex Optimization" (2016)
* Cesa-Bianchi & Lugosi, "Prediction, Learning, and Games" (2006)
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

open Finset BigOperators

/-- **Online-to-batch conversion**: if the sum of losses over T rounds is ≤ R,
    then some round t has loss ≤ R/T. Equivalently: minimum ≤ average. -/
theorem exists_le_div_of_sum_le (T : ℕ) (hT : 0 < T) (a : ℕ → ℝ) (R : ℝ)
    (hR : ∑ k ∈ range T, a k ≤ R) :
    ∃ t, t < T ∧ a t ≤ R / ↑T := by
  have hne : (range T).Nonempty := nonempty_range_iff.mpr (by omega)
  have h_sum_const : ∑ _ ∈ range T, R / (↑T : ℝ) = R := by
    rw [sum_const, card_range, nsmul_eq_mul]
    field_simp
  have h_sum_le : ∑ k ∈ range T, a k ≤ ∑ _ ∈ range T, R / (↑T : ℝ) := by linarith
  obtain ⟨t, ht_mem, ht_le⟩ := exists_le_of_sum_le hne h_sum_le
  exact ⟨t, mem_range.mp ht_mem, ht_le⟩
