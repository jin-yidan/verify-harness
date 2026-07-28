/-
# Squared Difference Bounds

Bounds on squared differences in terms of squared norms:
  (a-b)² ≤ 2(a²+b²)

## Main Results

* `sq_sub_le_two_mul_sq` — (a-b)² ≤ 2(a²+b²)
* `sum_sq_sub_le_two_mul_sum_sq` — ∑(aᵢ-bᵢ)² ≤ 2(∑aᵢ² + ∑bᵢ²)

## References

* Parallelogram law consequence
* Used in stability, perturbation, and approximation bounds
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open Finset BigOperators

/-- **Squared difference bound**: (a-b)² ≤ 2(a²+b²).

    Proof: 2(a²+b²) - (a-b)² = (a+b)² ≥ 0. -/
theorem sq_sub_le_two_mul_sq (a b : ℝ) :
    (a - b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  nlinarith [sq_nonneg (a + b)]

/-- **Sum of squared differences**: ∑(aᵢ-bᵢ)² ≤ 2(∑aᵢ² + ∑bᵢ²). -/
theorem sum_sq_sub_le_two_mul_sum_sq {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) :
    ∑ i, (a i - b i) ^ 2 ≤ 2 * (∑ i, a i ^ 2 + ∑ i, b i ^ 2) := by
  calc ∑ i, (a i - b i) ^ 2
      ≤ ∑ i, (2 * (a i ^ 2 + b i ^ 2)) :=
        Finset.sum_le_sum (fun i _ => sq_sub_le_two_mul_sq (a i) (b i))
    _ = 2 * ∑ i, (a i ^ 2 + b i ^ 2) := by rw [← Finset.mul_sum]
    _ = 2 * (∑ i, a i ^ 2 + ∑ i, b i ^ 2) := by
        congr 1; exact Finset.sum_add_distrib
