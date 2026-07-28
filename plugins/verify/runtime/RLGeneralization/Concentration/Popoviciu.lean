/-
# Popoviciu's Variance Inequality

Variance of a bounded random variable: Var(X) ≤ (b-a)²/4 when X ∈ [a,b].

## Main Results

* `popoviciu` — E[X²] - (E[X])² ≤ (b-a)²/4

## References

* Popoviciu (1935), Sur les équations algébriques
* Key building block for Hoeffding's lemma and sub-Gaussian analysis
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open Finset BigOperators

/-- **Popoviciu's variance inequality**: Var(X) ≤ (b-a)²/4 for X ∈ [a,b].

    Proof: from (xᵢ-a)(b-xᵢ) ≥ 0, bound E[X²], then apply AM-GM
    to get (μ-a)(b-μ) ≤ ((b-a)/2)². -/
theorem popoviciu {ι : Type*} [Fintype ι]
    (p x : ι → ℝ) {a b : ℝ}
    (hp : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (hxa : ∀ i, a ≤ x i) (hxb : ∀ i, x i ≤ b) :
    ∑ i, p i * x i ^ 2 - (∑ i, p i * x i) ^ 2 ≤ (b - a) ^ 2 / 4 := by
  set μ := ∑ i, p i * x i with hμ_def
  have h1 : ∀ i, x i ^ 2 ≤ (a + b) * x i - a * b := by
    intro i; nlinarith [mul_nonneg (sub_nonneg.mpr (hxa i)) (sub_nonneg.mpr (hxb i))]
  have h2 : ∑ i, p i * x i ^ 2 ≤ (a + b) * μ - a * b := by
    have h_le : ∀ i ∈ Finset.univ, p i * x i ^ 2 ≤ p i * ((a + b) * x i - a * b) :=
      fun i _ => mul_le_mul_of_nonneg_left (h1 i) (hp i)
    have h_eq : ∑ i, p i * ((a + b) * x i - a * b) = (a + b) * μ - a * b := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib]
      congr 1
      · simp_rw [← mul_assoc, mul_comm (p _) (a + b), mul_assoc]
        rw [← Finset.mul_sum]
      · simp_rw [mul_comm (p _) (a * b)]
        rw [← Finset.mul_sum, hp_sum, mul_one]
    linarith [Finset.sum_le_sum h_le]
  nlinarith [sq_nonneg (2 * μ - a - b)]
