/-
# Abel Summation (Summation by Parts)

The discrete analogue of integration by parts. Relates a weighted sum
to boundary terms minus a sum weighted by differences.

## Main Results

* `abel_summation` — ∑_{k<n} aₖ·Δbₖ = aₙbₙ - a₀b₀ - ∑_{k<n} Δaₖ·b_{k+1}
* `abel_summation_sym` — ∑_{k<n} Δaₖ·bₖ = aₙbₙ - a₀b₀ - ∑_{k<n} a_{k+1}·Δbₖ

## References

* Abel, N.H. (1826), "Untersuchungen über die Reihe …"
* Cesa-Bianchi & Lugosi, "Prediction, Learning, and Games" (2006), Lemma 2.1
* Apostol, "Mathematical Analysis" (1974), Theorem 12.4
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open Finset BigOperators

/-- **Abel summation (summation by parts)**:
    ∑_{k<n} aₖ (b_{k+1} - bₖ) = aₙ bₙ - a₀ b₀ - ∑_{k<n} (a_{k+1} - aₖ) b_{k+1}. -/
theorem abel_summation (n : ℕ) (a b : ℕ → ℝ) :
    ∑ k ∈ range n, a k * (b (k + 1) - b k) =
    a n * b n - a 0 * b 0 - ∑ k ∈ range n, (a (k + 1) - a k) * b (k + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, sum_range_succ, ih]
    ring

/-- **Abel summation, symmetric form**:
    ∑_{k<n} (a_{k+1} - aₖ) bₖ = aₙ bₙ - a₀ b₀ - ∑_{k<n} a_{k+1} (b_{k+1} - bₖ). -/
theorem abel_summation_sym (n : ℕ) (a b : ℕ → ℝ) :
    ∑ k ∈ range n, (a (k + 1) - a k) * b k =
    a n * b n - a 0 * b 0 - ∑ k ∈ range n, a (k + 1) * (b (k + 1) - b k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, sum_range_succ, ih]
    ring
