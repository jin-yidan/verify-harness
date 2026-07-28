import Mathlib

open Finset BigOperators

/-- If every term `f i` over a finite index set lies in `[0, M]`, then the sum of
the squares is bounded by `M` times the sum: `∑ (f i)^2 ≤ M * ∑ f i`. -/
theorem sq_sum_le_max_mul_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) (M : ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) (hM : ∀ i ∈ s, f i ≤ M) :
    ∑ i ∈ s, (f i) ^ 2 ≤ M * ∑ i ∈ s, f i := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have h0 := hf i hi
  have h1 := hM i hi
  nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)]

