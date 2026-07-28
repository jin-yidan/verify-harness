import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
# Exponential Inequalities

Standalone bounds on `Real.exp` used across online learning, bandit algorithms,
and concentration inequalities. The main result `exp_neg_le_one_sub_add_sq`
proves `exp(-x) ≤ 1 - x + x²` for `x ≥ 0`, resolving the `ExpIneq` axiom
used in EXP3 / Hedge analysis.

## Main Results

* `exp_neg_le_one_sub_add_sq` — exp(-x) ≤ 1 - x + x² for x ≥ 0
* `exp_neg_le_inv_one_add` — exp(-x) ≤ 1/(1+x) for x ≥ 0
-/

open Real

/-- **exp(-x) ≤ 1/(1+x)** for `x ≥ 0`.

    Equivalently, `(1+x) ≤ exp(x)` (Mathlib's `add_one_le_exp`),
    inverted. Used as a stepping stone for the quadratic bound. -/
theorem exp_neg_le_inv_one_add {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-x) ≤ (1 + x)⁻¹ := by
  have h1x_pos : (0 : ℝ) < 1 + x := by linarith
  rw [Real.exp_neg]
  exact inv_anti₀ h1x_pos (by linarith [add_one_le_exp x])

/-- **exp(-x) ≤ 1 - x + x²** for `x ≥ 0`.

    The key analytic fact for EXP3 / Hedge / multiplicative weights:
    the exponential weight update `exp(-η·ℓ)` is bounded by a quadratic
    in the loss, enabling the potential-function regret argument.

    Proof: `exp(-x) ≤ 1/(1+x) ≤ 1 - x + x²`. The first step inverts
    `1 + x ≤ exp(x)`. The second uses `(1+x)(1-x+x²) = 1 + x³ ≥ 1`. -/
theorem exp_neg_le_one_sub_add_sq {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-x) ≤ 1 - x + x ^ 2 := by
  have h1x_pos : (0 : ℝ) < 1 + x := by linarith
  calc Real.exp (-x)
      ≤ (1 + x)⁻¹ := exp_neg_le_inv_one_add hx
    _ ≤ 1 - x + x ^ 2 := by
        rw [inv_eq_one_div, div_le_iff₀ h1x_pos]
        have : (1 - x + x ^ 2) * (1 + x) = 1 + x ^ 3 := by ring
        rw [this]
        have : 0 ≤ x ^ 3 := by positivity
        linarith
