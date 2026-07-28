/-
# L1-L2 Norm Bound

The standard Cauchy-Schwarz consequence: ∑|aᵢ| ≤ √n · √(∑aᵢ²).

## Main Results

* `sum_abs_le_sqrt_card_mul` — ∑|aᵢ| ≤ √n · √(∑aᵢ²)

## References

* Cauchy-Schwarz inequality with constant vector
* Used in regret analysis, L²→L¹ conversion, linear bandits
-/
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

open Finset BigOperators

/-- **L1-L2 bound**: ∑|aᵢ| ≤ √n · √(∑aᵢ²).

    Cauchy-Schwarz with the constant-1 vector: (∑|aᵢ|·1)² ≤ (∑aᵢ²)(∑1) = n·∑aᵢ².
    Taking square roots gives the bound. -/
theorem sum_abs_le_sqrt_card_mul {ι : Type*} [Fintype ι]
    (a : ι → ℝ) :
    ∑ i, |a i| ≤ Real.sqrt (Fintype.card ι) * Real.sqrt (∑ i, a i ^ 2) := by
  have h_nn : (0 : ℝ) ≤ ∑ i, |a i| :=
    Finset.sum_nonneg (fun i _ => abs_nonneg _)
  rw [← Real.sqrt_sq h_nn, ← Real.sqrt_mul (Nat.cast_nonneg _)]
  apply Real.sqrt_le_sqrt
  have h_cs := sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => |a i|) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, sum_const, card_univ, nsmul_eq_mul, mul_one] at h_cs
  simp_rw [sq_abs] at h_cs
  linarith
