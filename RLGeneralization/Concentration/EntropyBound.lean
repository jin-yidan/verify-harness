/-
# Entropy Upper Bound

Shannon entropy of a finite distribution is at most log(n).

## Main Results

* `entropy_le_log_card` — -∑ pᵢ log pᵢ ≤ log(n) for probability distributions

## References

* Maximum entropy principle (Shannon 1948)
* Used in bandit information ratios, PAC-Bayes, MaxEnt IRL
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open Finset BigOperators Real

/-- **Entropy upper bound**: H(p) = -∑ pᵢ log pᵢ ≤ log n.

    Proof: KL(p‖uniform) ≥ 0 via log(y) ≤ y - 1, then expand
    to get ∑ pᵢ log(n·pᵢ) ≥ 0. -/
theorem entropy_le_log_card {ι : Type*} [Fintype ι] [Nonempty ι]
    (p : ι → ℝ) (hp_pos : ∀ i, 0 < p i) (hp_sum : ∑ i, p i = 1) :
    -(∑ i, p i * Real.log (p i)) ≤ Real.log (Fintype.card ι) := by
  have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  suffices h : 0 ≤ ∑ i, p i * Real.log (↑(Fintype.card ι) * p i) by
    have h1 : ∀ i, p i * Real.log (↑(Fintype.card ι) * p i) =
        p i * Real.log ↑(Fintype.card ι) + p i * Real.log (p i) := by
      intro i
      rw [Real.log_mul (ne_of_gt hn) (ne_of_gt (hp_pos i)), mul_add]
    simp_rw [h1] at h
    rw [Finset.sum_add_distrib] at h
    have h2 : ∑ i : ι, p i * Real.log ↑(Fintype.card ι) =
        Real.log ↑(Fintype.card ι) := by
      simp_rw [mul_comm (p _) (Real.log _)]
      rw [← Finset.mul_sum, hp_sum, mul_one]
    linarith
  have key : ∀ i ∈ Finset.univ, p i * Real.log (↑(Fintype.card ι) * p i) ≥
      p i - 1 / ↑(Fintype.card ι) := by
    intro i _
    have hpi := hp_pos i
    have hnpi : 0 < ↑(Fintype.card ι) * p i := mul_pos hn hpi
    have h_log := Real.log_le_sub_one_of_pos (inv_pos.mpr hnpi)
    rw [Real.log_inv] at h_log
    have h_ge : Real.log (↑(Fintype.card ι) * p i) ≥ 1 - (↑(Fintype.card ι) * p i)⁻¹ := by
      linarith
    have h_mul : p i * Real.log (↑(Fintype.card ι) * p i) ≥
        p i * (1 - (↑(Fintype.card ι) * p i)⁻¹) :=
      mul_le_mul_of_nonneg_left h_ge.le (le_of_lt hpi)
    have h_simp : p i * (1 - (↑(Fintype.card ι) * p i)⁻¹) =
        p i - 1 / ↑(Fintype.card ι) := by
      rw [mul_inv, mul_comm (↑(Fintype.card ι))⁻¹ (p i)⁻¹]
      field_simp
    linarith
  have h_sum := Finset.sum_le_sum (fun i hi => (key i hi).le)
  have h_zero : ∑ i : ι, (p i - 1 / ↑(Fintype.card ι)) = 0 := by
    rw [Finset.sum_sub_distrib, hp_sum]
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  linarith
