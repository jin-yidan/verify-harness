/-
# Weighted Cauchy-Schwarz Inequality

The weighted Cauchy-Schwarz inequality for finite sums:
  (∑ wᵢaᵢ)² ≤ (∑ wᵢ)(∑ wᵢaᵢ²)

## Main Results

* `weighted_cauchy_schwarz` — (∑ wᵢaᵢ)² ≤ (∑ wᵢ)(∑ wᵢaᵢ²) for wᵢ ≥ 0

## References

* Generalizes E[X]² ≤ E[X²] (Jensen's inequality for x²)
* Used in variance bounds, importance sampling, policy gradient variance
-/
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

open Finset BigOperators

/-- **Weighted Cauchy-Schwarz**: (∑ wᵢaᵢ)² ≤ (∑ wᵢ)(∑ wᵢaᵢ²).

    Proved by substituting f = √w, g = √w·a into the unweighted
    Cauchy-Schwarz `sum_mul_sq_le_sq_mul_sq`. -/
theorem weighted_cauchy_schwarz {ι : Type*} [Fintype ι]
    (w a : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    (∑ i, w i * a i) ^ 2 ≤ (∑ i, w i) * ∑ i, w i * a i ^ 2 := by
  have h1 : ∀ i, w i * a i = Real.sqrt (w i) * (Real.sqrt (w i) * a i) := by
    intro i; rw [← mul_assoc, Real.mul_self_sqrt (hw i)]
  have h2 : ∀ i, w i = Real.sqrt (w i) ^ 2 := by
    intro i; exact (Real.sq_sqrt (hw i)).symm
  have h3 : ∀ i, w i * a i ^ 2 = (Real.sqrt (w i) * a i) ^ 2 := by
    intro i; rw [mul_pow, Real.sq_sqrt (hw i)]
  calc (∑ i, w i * a i) ^ 2
      = (∑ i, Real.sqrt (w i) * (Real.sqrt (w i) * a i)) ^ 2 := by
        congr 1; exact Finset.sum_congr rfl (fun i _ => h1 i)
    _ ≤ (∑ i, Real.sqrt (w i) ^ 2) * ∑ i, (Real.sqrt (w i) * a i) ^ 2 :=
        sum_mul_sq_le_sq_mul_sq Finset.univ _ _
    _ = (∑ i, w i) * ∑ i, w i * a i ^ 2 := by
        congr 1
        · exact Finset.sum_congr rfl (fun i _ => (h2 i).symm)
        · exact Finset.sum_congr rfl (fun i _ => (h3 i).symm)
