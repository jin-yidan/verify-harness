/-
# Convexity of Squaring

Convex combination bound for x²: (ta + (1-t)b)² ≤ ta² + (1-t)b².

## Main Results

* `sq_convex_combination` — (ta + (1-t)b)² ≤ ta² + (1-t)b² for t ∈ [0,1]
* `sum_sq_convex_combination` — vector version: ∑(taᵢ+(1-t)bᵢ)² ≤ t·∑aᵢ²+(1-t)·∑bᵢ²

## References

* Jensen's inequality applied to f(x) = x² (convex)
* Used in bias-variance analysis, PAC-Bayes, optimization convergence
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open Finset BigOperators

/-- **Convexity of squaring**: (ta + (1-t)b)² ≤ ta² + (1-t)b² for t ∈ [0,1].

    The gap is t(1-t)(a-b)² ≥ 0. -/
theorem sq_convex_combination {a b t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (t * a + (1 - t) * b) ^ 2 ≤ t * a ^ 2 + (1 - t) * b ^ 2 := by
  have h1 : 0 ≤ 1 - t := by linarith
  nlinarith [sq_nonneg (a - b), mul_nonneg ht0 h1]

/-- **Convexity of ℓ² norm**: ‖ta + (1-t)b‖² ≤ t·‖a‖² + (1-t)·‖b‖² for t ∈ [0,1]. -/
theorem sum_sq_convex_combination {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∑ i, (t * a i + (1 - t) * b i) ^ 2 ≤
    t * ∑ i, a i ^ 2 + (1 - t) * ∑ i, b i ^ 2 := by
  have h : ∀ i ∈ Finset.univ, (t * a i + (1 - t) * b i) ^ 2 ≤
      t * (a i) ^ 2 + (1 - t) * (b i) ^ 2 :=
    fun i _ => sq_convex_combination ht0 ht1
  calc ∑ i, (t * a i + (1 - t) * b i) ^ 2
      ≤ ∑ i, (t * a i ^ 2 + (1 - t) * b i ^ 2) :=
        Finset.sum_le_sum h
    _ = ∑ i, t * a i ^ 2 + ∑ i, (1 - t) * b i ^ 2 := Finset.sum_add_distrib
    _ = t * ∑ i, a i ^ 2 + (1 - t) * ∑ i, b i ^ 2 := by
        congr 1 <;> exact (Finset.mul_sum Finset.univ _ _).symm
