/-
# Young's Inequality with Epsilon

The parametric form of Young's inequality: ab ≤ ε·a² + b²/(4ε).
Also known as the Peter-Paul inequality.

## Main Results

* `young_with_epsilon` — ab ≤ ε·a² + b²/(4ε) for ε > 0

## References

* Young, W.H. (1912), "On classes of summable functions"
* Used in optimization convergence proofs, Lyapunov analysis,
  absorbing cross-terms in learning rate derivations
-/
import Mathlib.Tactic

/-- **Young's inequality with ε**: ab ≤ ε·a² + b²/(4ε) for ε > 0.
    Allows trading off between a² and b² contributions via the parameter ε. -/
theorem young_with_epsilon (a b ε : ℝ) (hε : 0 < ε) :
    a * b ≤ ε * a ^ 2 + b ^ 2 / (4 * ε) := by
  have h : 0 ≤ ε * a ^ 2 - a * b + b ^ 2 / (4 * ε) := by
    rw [show ε * a ^ 2 - a * b + b ^ 2 / (4 * ε) =
        (2 * ε * a - b) ^ 2 / (4 * ε) from by field_simp; ring]
    positivity
  linarith
