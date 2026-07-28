import Mathlib.Tactic

/-- **Scalar geometric recursion-solve.** If `x ≤ c + γ·x` and `γ < 1`, then
`x ≤ c/(1-γ)`. This is the algebraic fixed-point step underlying contraction
error bounds (e.g. value-loss / approximate-DP amplification): collect the
`x` terms and divide by the positive quantity `1-γ`. Holds for any `γ < 1`
(`0 ≤ γ` is not needed). -/
theorem le_div_one_sub_of_le_add_mul (x c gamma : ℝ) (hgamma : gamma < 1)
    (h : x ≤ c + gamma * x) : x ≤ c / (1 - gamma) := by
  have h1g : (0:ℝ) < 1 - gamma := by linarith
  rw [le_div_iff₀ h1g]
  nlinarith

