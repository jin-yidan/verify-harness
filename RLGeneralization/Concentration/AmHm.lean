/-
# AM-HM Inequality

Arithmetic mean ≥ harmonic mean: n² ≤ (∑ xᵢ)(∑ 1/xᵢ) for positive reals.

## Main Results

* `am_hm_inequality` — n² ≤ (∑ xᵢ)(∑ 1/xᵢ)

## References

* Cauchy-Schwarz with f = √x, g = 1/√x
* Used in sample complexity lower bounds, importance sampling, optimal design
-/
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

open Finset BigOperators

/-- **AM-HM inequality**: n² ≤ (∑ xᵢ)(∑ 1/xᵢ) for positive reals.

    Equivalently: arithmetic mean ≥ harmonic mean.
    Proof: Cauchy-Schwarz with f(i) = √xᵢ, g(i) = 1/√xᵢ. -/
theorem am_hm_inequality {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (hx : ∀ i, 0 < x i) :
    (Fintype.card ι : ℝ) ^ 2 ≤ (∑ i, x i) * ∑ i, 1 / x i := by
  have h_sqrt_ne : ∀ i, Real.sqrt (x i) ≠ 0 :=
    fun i => ne_of_gt (Real.sqrt_pos.mpr (hx i))
  have key := sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => Real.sqrt (x i)) (fun i => 1 / Real.sqrt (x i))
  have h1 : ∑ i : ι, Real.sqrt (x i) * (1 / Real.sqrt (x i)) = (Fintype.card ι : ℝ) := by
    simp_rw [one_div, mul_inv_cancel₀ (h_sqrt_ne _)]
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h2 : ∑ i : ι, Real.sqrt (x i) ^ 2 = ∑ i, x i := by
    congr 1; ext i; exact Real.sq_sqrt (le_of_lt (hx i))
  have h3 : ∑ i : ι, (1 / Real.sqrt (x i)) ^ 2 = ∑ i, 1 / x i := by
    congr 1; ext i; rw [div_pow, one_pow, Real.sq_sqrt (le_of_lt (hx i))]
  rw [h1, h2, h3] at key
  exact key
