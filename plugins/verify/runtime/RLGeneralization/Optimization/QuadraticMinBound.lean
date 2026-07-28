/-
# Quadratic Lower Bound (Completing the Square)

The quadratic form L/2·t² + g·t is bounded below by -g²/(2L) for L > 0.
This is the algebraic core of the gradient descent sufficient decrease lemma.

## Main Results

* `quadratic_min_bound` — L/2·t² + g·t ≥ -g²/(2L) for L > 0

## References

* Nesterov, *Introductory Lectures on Convex Optimization* (2004), Theorem 2.1.14
* Bubeck, *Convex Optimization: Algorithms and Complexity* (2015)
* Used in SGD, gradient descent, mirror descent, policy gradient, LQR
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-- **Quadratic lower bound** (completing the square): for L > 0,
    L/2 · t² + g · t ≥ -g²/(2L).

    Proof: L/2·t² + g·t + g²/(2L) = (L·t + g)²/(2L) ≥ 0. -/
theorem quadratic_min_bound {L : ℝ} (hL : 0 < L) (g t : ℝ) :
    -(g ^ 2 / (2 * L)) ≤ L / 2 * t ^ 2 + g * t := by
  have key : 0 ≤ L / 2 * t ^ 2 + g * t + g ^ 2 / (2 * L) := by
    have : L / 2 * t ^ 2 + g * t + g ^ 2 / (2 * L) = (L * t + g) ^ 2 / (2 * L) := by
      field_simp
      ring
    rw [this]
    exact div_nonneg (sq_nonneg _) (by linarith)
  linarith
