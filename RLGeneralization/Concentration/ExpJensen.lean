/-
# Jensen's Inequality for Exp

The exponential function is convex: exp of a weighted average ≤ weighted
average of exp.

## Main Results

* `exp_jensen` — exp(∑ wᵢxᵢ) ≤ ∑ wᵢ exp(xᵢ) for probability weights

## References

* Standard convex analysis / probability theory
* Key building block for Hoeffding's lemma, sub-Gaussian analysis, MGF bounds
-/
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open Finset BigOperators

/-- **Jensen's inequality for exp**: exp(∑ wᵢxᵢ) ≤ ∑ wᵢ exp(xᵢ).

    Proof: from exp(y) ≥ 1+y, derive ∑ wᵢ exp(xᵢ−μ) ≥ 1 where μ = ∑ wᵢxᵢ,
    then factor out exp(−μ) and multiply by exp(μ). -/
theorem exp_jensen {ι : Type*} [Fintype ι]
    (w x : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hw_sum : ∑ i, w i = 1) :
    Real.exp (∑ i, w i * x i) ≤ ∑ i, w i * Real.exp (x i) := by
  set μ := ∑ i, w i * x i with hμ_def
  have h1 : (1 : ℝ) ≤ ∑ i, w i * Real.exp (x i - μ) := by
    have h_eq : ∑ i, w i * (1 + (x i - μ)) = 1 := by
      simp_rw [mul_add, mul_one, mul_sub]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hw_sum]
      simp_rw [mul_comm (w _) μ]
      rw [← Finset.mul_sum, hw_sum, mul_one]; ring
    linarith [Finset.sum_le_sum (show ∀ i ∈ Finset.univ,
        w i * (1 + (x i - μ)) ≤ w i * Real.exp (x i - μ) from
      fun i _ => mul_le_mul_of_nonneg_left
        (by linarith [Real.add_one_le_exp (x i - μ)]) (hw i))]
  have h2 : ∑ i, w i * Real.exp (x i - μ) =
      Real.exp (-μ) * ∑ i, w i * Real.exp (x i) := by
    rw [Finset.mul_sum]; congr 1; ext i
    rw [show x i - μ = x i + (-μ) from sub_eq_add_neg _ _, Real.exp_add]; ring
  rw [h2] at h1
  have h3 : Real.exp μ * Real.exp (-μ) = 1 := by
    rw [← Real.exp_add, show μ + (-μ) = (0 : ℝ) by ring, Real.exp_zero]
  have h4 := mul_le_mul_of_nonneg_left h1 (le_of_lt (Real.exp_pos μ))
  rw [mul_one, ← mul_assoc, h3, one_mul] at h4
  exact h4
