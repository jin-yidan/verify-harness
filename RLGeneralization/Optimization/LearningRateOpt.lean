import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Optimal Learning Rate Bound

The algebraic core of learning rate optimization: for any bound of
the form `A/η + η·B`, the AM-GM inequality gives a lower bound
`2·√(A·B)`, achieved at `η = √(A/B)`.

This pattern appears in:
- EXP3 / Hedge regret bounds (η = √(log K / KT))
- Online mirror descent (η = √(2D₀ / TG²))
- SGD convergence rate (α = √(D² / σ²T))
- Natural policy gradient (η = √(log|A| / KH))
- UCB exploration-exploitation tradeoff

## Main Results

* `div_add_mul_ge_two_sqrt` — A/η + η·B ≥ 2·√(AB) for η > 0
* `opt_learning_rate_eq` — A/√(A/B) + √(A/B)·B = 2·√(AB)
-/

open Real

noncomputable section

/-- **Learning rate lower bound** (AM-GM for regret bounds).

    For `A, B > 0` and any `η > 0`:

      A / η + η * B ≥ 2 * √(A * B)

    This is the fundamental inequality for learning rate tuning:
    any choice of η gives at least `2·√(AB)` total cost.

    Proof: set `u = √(A/η)` and `v = √(η·B)`, then
    `(u - v)² ≥ 0` gives `u² + v² ≥ 2uv`, i.e.,
    `A/η + η·B ≥ 2·√(A·B)`. -/
theorem div_add_mul_ge_two_sqrt
    {A B η : ℝ} (hA : 0 < A) (hB : 0 < B) (hη : 0 < η) :
    2 * Real.sqrt (A * B) ≤ A / η + η * B := by
  have hAη : 0 < A / η := div_pos hA hη
  have hηB : 0 < η * B := mul_pos hη hB
  have h_sq : 0 ≤ (Real.sqrt (A / η) - Real.sqrt (η * B)) ^ 2 := sq_nonneg _
  have h_expand : (Real.sqrt (A / η) - Real.sqrt (η * B)) ^ 2 =
      A / η + η * B - 2 * Real.sqrt (A / η) * Real.sqrt (η * B) := by
    rw [sub_sq, sq_sqrt hAη.le, sq_sqrt hηB.le]
    ring
  have h_prod : Real.sqrt (A / η) * Real.sqrt (η * B) = Real.sqrt (A * B) := by
    rw [← Real.sqrt_mul hAη.le, show A / η * (η * B) = A * B by field_simp]
  linarith

/-- **Optimal learning rate identity**.

    At `η = √(A/B)`, the bound `A/η + η·B` achieves its minimum
    value `2·√(A·B)`.

    Combined with `div_add_mul_ge_two_sqrt`, this shows that `η = √(A/B)`
    is the optimal learning rate and `2·√(AB)` is the tight bound. -/
theorem opt_learning_rate_eq
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    A / Real.sqrt (A / B) + Real.sqrt (A / B) * B =
    2 * Real.sqrt (A * B) := by
  have hAB : 0 < A / B := div_pos hA hB
  have hη : 0 < Real.sqrt (A / B) := Real.sqrt_pos.mpr hAB
  have hη_ne : Real.sqrt (A / B) ≠ 0 := hη.ne'
  have hη_sq : Real.sqrt (A / B) ^ 2 = A / B := sq_sqrt hAB.le
  suffices h : (A / Real.sqrt (A / B) + Real.sqrt (A / B) * B) *
      Real.sqrt (A / B) = 2 * Real.sqrt (A * B) * Real.sqrt (A / B) by
    exact mul_right_cancel₀ hη_ne h
  have lhs : (A / Real.sqrt (A / B) + Real.sqrt (A / B) * B) *
      Real.sqrt (A / B) = 2 * A := by
    rw [add_mul, div_mul_cancel₀ A hη_ne, mul_assoc,
        mul_comm B _, ← mul_assoc, ← sq, hη_sq, div_mul_cancel₀ A hB.ne']
    ring
  have rhs : 2 * Real.sqrt (A * B) * Real.sqrt (A / B) = 2 * A := by
    rw [mul_assoc, ← Real.sqrt_mul (mul_nonneg hA.le hB.le)]
    rw [show A * B * (A / B) = A * A by field_simp]
    rw [Real.sqrt_mul_self hA.le]
  rw [lhs, rhs]

end
