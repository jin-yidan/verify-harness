import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# sqrt_lipschitz_on_interval

The scalar square root Lipschitz bound: for a, b ≥ λ > 0,
  |√a - √b| ≤ (2√λ)⁻¹ · |a - b|

This is the scalar version of the matrix square root Lipschitz inequality
(Bhatia Ch. X, Higham Thm 6.1). The matrix version follows by applying
this bound to each eigenvalue via spectral decomposition.

Proof sketch:
  |√a - √b| = |a - b| / (√a + √b)   [difference of squares]
  √a + √b ≥ 2√λ                       [since a, b ≥ λ]
  ∴ |√a - √b| ≤ |a - b| / (2√λ)

-/

open Real

noncomputable section

/-- The scalar square root is Lipschitz on [λ, ∞) with constant (2√λ)⁻¹.
    For positive definite matrices, this gives ‖Λ^{1/2} - Λ'^{1/2}‖ ≤ (2√λ_min)⁻¹ · ‖Λ - Λ'‖
    by applying to each eigenvalue. -/
theorem sqrt_lipschitz_on_interval
    (a b lam : ℝ) (hlam : 0 < lam) (ha : lam ≤ a) (hb : lam ≤ b) :
    |Real.sqrt a - Real.sqrt b| ≤ (2 * Real.sqrt lam)⁻¹ * |a - b| := by
  have ha0 : (0 : ℝ) ≤ a := le_trans (le_of_lt hlam) ha
  have hb0 : (0 : ℝ) ≤ b := le_trans (le_of_lt hlam) hb
  have hsqa : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha0
  have hsqb : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb0
  have hsqa_ge : Real.sqrt lam ≤ Real.sqrt a := Real.sqrt_le_sqrt ha
  have hsqb_ge : Real.sqrt lam ≤ Real.sqrt b := Real.sqrt_le_sqrt hb
  have hsql_pos : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hsum_pos : 0 < Real.sqrt a + Real.sqrt b := by linarith
  have hsum_ge : 2 * Real.sqrt lam ≤ Real.sqrt a + Real.sqrt b := by linarith
  have h2sql_pos : 0 < 2 * Real.sqrt lam := by linarith
  -- Key identity: |√a - √b| · (√a + √b) = |a - b| via difference of squares
  have hident : |Real.sqrt a - Real.sqrt b| * (Real.sqrt a + Real.sqrt b) = |a - b| := by
    have h1 : (Real.sqrt a - Real.sqrt b) * (Real.sqrt a + Real.sqrt b) = a - b := by
      nlinarith [sq_nonneg (Real.sqrt a), sq_nonneg (Real.sqrt b)]
    rw [← h1, abs_mul, abs_of_pos hsum_pos]
  -- Therefore |√a - √b| = |a - b| / (√a + √b)
  have hdiv : |Real.sqrt a - Real.sqrt b| = |a - b| / (Real.sqrt a + Real.sqrt b) := by
    rw [eq_div_iff (ne_of_gt hsum_pos)]
    exact hident
  -- Rewrite RHS
  have hrhs : (2 * Real.sqrt lam)⁻¹ * |a - b| = |a - b| / (2 * Real.sqrt lam) := by
    ring
  rw [hdiv, hrhs]
  -- Conclude by monotonicity: √a + √b ≥ 2√λ implies division is smaller
  apply div_le_div_of_nonneg_left (abs_nonneg _) h2sql_pos hsum_ge
