import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-- Two estimates within radius `r` of true values preserve the true ordering
up to an additive `2r`: if `|a - x| <= r`, `|b - y| <= r` and `x <= y`, then
`a <= b + 2r`. Confidence-interval algebra used by elimination-style bandit
arguments (the optimal arm is never eliminated). -/
theorem est_le_est_add_two_radius (a b x y r : ℝ)
    (ha : |a - x| ≤ r) (hb : |b - y| ≤ r) (hxy : x ≤ y) :
    a ≤ b + 2 * r := by
  have h1 := abs_le.mp ha
  have h2 := abs_le.mp hb
  linarith [h1.1, h1.2, h2.1, h2.2]

