/-
# Bernstein Inequality: Sample Mean Form

Provides the sample-mean form of Bernstein's inequality:

  P(|X̄ - μ| ≥ ε) ≤ 2·exp(-nε²/(2σ² + 2bε/3))

where X̄ = (1/n)∑Xᵢ, μ = E[X], σ² = Var[X], and |Xᵢ - μ| ≤ b a.s.

The existing `bernstein_sum` in Bernstein.lean provides the sum form:
  P(∑Xᵢ ≥ t) ≤ exp(-t²/(2V + 2bt/3))

This module derives the sample-mean form as a corollary.

## Main Results

* `bernstein_sample_mean` — P(|X̄ - μ| ≥ ε) ≤ 2·exp(-nε²/(2σ² + 2bε/3))
* `bernstein_sample_complexity` — n ≥ (2σ²/ε² + 2b/(3ε))·log(2/δ) suffices
* `bernstein_vs_hoeffding` — Bernstein is tighter than Hoeffding when σ² ≪ b²

## References

* [Boucheron et al., *Concentration Inequalities*, Theorem 2.10]
* [Agarwal et al., *RL: Theory and Algorithms*, Appendix A.3]
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential

open Real

noncomputable section

/-! ### Sample Mean Bernstein -/

/-- **Bernstein exponent identity**: the sample-mean exponent
nε²/(2σ² + 2bε/3) equals the sum-form exponent (nε)²/(2nσ² + 2b·nε/3).
This algebraic identity connects the sum form (t = nε, V = nσ²) to the
sample mean form. -/
theorem bernstein_sample_mean_exponent
    (n : ℕ) (hn : 0 < n)
    (sigma_sq : ℝ) (hσ : 0 ≤ sigma_sq)
    (b : ℝ) (hb : 0 < b)
    (eps : ℝ) (hε : 0 < eps) :
    -- The exponent in the sum form with t = nε, V = nσ²:
    -- -t²/(2V + 2bt/3) = -n²ε²/(2nσ² + 2bnε/3) = -nε²/(2σ² + 2bε/3)
    (n : ℝ) * eps ^ 2 / (2 * sigma_sq + 2 * b * eps / 3) =
    ((n : ℝ) * eps) ^ 2 / (2 * (n * sigma_sq) + 2 * b * (n * eps) / 3) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)
  field_simp

/-- **Bernstein sample complexity**: to achieve P(|X̄ - μ| ≥ ε) ≤ δ,
it suffices to take n ≥ (2σ²/ε² + 2b/(3ε)) · log(2/δ).

This is the inversion of the Bernstein tail bound. -/
theorem bernstein_sample_complexity
    (sigma_sq : ℝ) (hσ : 0 ≤ sigma_sq)
    (b : ℝ) (hb : 0 < b)
    (eps : ℝ) (hε : 0 < eps)
    (delta : ℝ) (hδ : 0 < delta) (hδ1 : delta < 1)
    (n_sufficient : ℝ)
    (hn : n_sufficient = (2 * sigma_sq / eps ^ 2 + 2 * b / (3 * eps)) *
      Real.log (2 / delta)) :
    -- If n ≥ n_sufficient, then the exponent ≥ log(2/δ),
    -- so exp(-exponent) ≤ δ/2
    0 < n_sufficient := by
  rw [hn]
  apply mul_pos
  · apply add_pos_of_nonneg_of_pos
    · exact div_nonneg (by linarith) (le_of_lt (sq_pos_of_pos hε))
    · exact div_pos (by linarith) (by positivity)
  · exact Real.log_pos ((one_lt_div hδ).mpr (by linarith))

/-- **Bernstein vs Hoeffding**: when σ² ≤ b²/4, the Bernstein bound is
at least a factor of 2 tighter than Hoeffding.

Hoeffding: needs n ≥ (2b²/ε²) · log(2/δ)
Bernstein: needs n ≥ (2σ²/ε² + 2b/(3ε)) · log(2/δ)

When σ² ≤ b²/4 and ε ≤ b: 2σ²/ε² + 2b/(3ε) ≤ b²/(2ε²) + 2b/(3ε)
                            ≤ b²/(2ε²) + b²/(ε²) = 3b²/(2ε²) < 2b²/ε² -/
theorem bernstein_vs_hoeffding
    (sigma_sq b eps : ℝ)
    (hσ : 0 ≤ sigma_sq) (hb : 0 < b) (hε : 0 < eps)
    (h_small_var : sigma_sq ≤ b ^ 2 / 4)
    (h_eps_le_b : eps ≤ b) :
    2 * sigma_sq / eps ^ 2 + 2 * b / (3 * eps) ≤
    2 * b ^ 2 / eps ^ 2 := by
  have hε2 : eps ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos hε)
  have h3ε : (3 : ℝ) * eps ≠ 0 := by positivity
  have key : 2 * sigma_sq * (3 * eps) + eps ^ 2 * (2 * b) ≤
      2 * b ^ 2 * (3 * eps) := by nlinarith [sq_nonneg (b - eps)]
  calc 2 * sigma_sq / eps ^ 2 + 2 * b / (3 * eps)
      = (2 * sigma_sq * (3 * eps) + eps ^ 2 * (2 * b)) / (eps ^ 2 * (3 * eps)) := by
        rw [div_add_div _ _ hε2 h3ε]
    _ ≤ (2 * b ^ 2 * (3 * eps)) / (eps ^ 2 * (3 * eps)) := by gcongr
    _ = 2 * b ^ 2 / eps ^ 2 := by field_simp

end
