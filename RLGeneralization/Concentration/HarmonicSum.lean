/-
# Harmonic Sum Bound

Upper bound for the harmonic sum: H_n = ∑_{k=1}^{n} 1/k ≤ 1 + log(n).

## Main Results

* `harmonic_sum_le_one_add_log` — ∑_{k<n} 1/(k+1) ≤ 1 + log(n)

## References

* Thin wrapper over Mathlib's `harmonic_le_one_add_log`
  (NumberTheory/Harmonic/Bounds.lean), restated as a real-valued finite sum —
  the form used directly in UCB regret analysis, Robbins-Monro step-size
  conditions, and coupon collector bounds. The original hand-rolled induction
  proof was replaced after the 2026-06-10 gate audit found the Mathlib
  duplicate (see rlverify/results/gate_ab_test.md).
-/
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

open Finset Real

/-- **Harmonic sum bound**: ∑_{k<n} 1/(k+1) ≤ 1 + log(n).

    Real-valued finite-sum form of Mathlib's `harmonic_le_one_add_log`. -/
theorem harmonic_sum_le_one_add_log (n : ℕ) :
    ∑ k ∈ range n, (1 / ((k : ℝ) + 1)) ≤ 1 + Real.log n := by
  have h := harmonic_le_one_add_log n
  have h_eq : ((harmonic n : ℚ) : ℝ) = ∑ k ∈ range n, (1 / ((k : ℝ) + 1)) := by
    unfold harmonic
    push_cast
    simp [one_div]
  linarith [h_eq ▸ h]
