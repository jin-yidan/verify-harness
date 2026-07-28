import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-- A true gap larger than `4r` forces an observed gap larger than `2r` under
`r`-accurate estimates: if `|a - x| <= r`, `|b - y| <= r` and `x - y > 4r`,
then `a - b > 2r`. Confidence-interval algebra used by elimination-style
bandit arguments (suboptimal arms trigger the elimination criterion). -/
theorem est_gap_gt_of_true_gap_gt_four_radius (a b x y r : ℝ)
    (ha : |a - x| ≤ r) (hb : |b - y| ≤ r) (h : 4 * r < x - y) :
    2 * r < a - b := by
  have h1 := abs_le.mp ha
  have h2 := abs_le.mp hb
  linarith [h1.1, h1.2, h2.1, h2.2]

