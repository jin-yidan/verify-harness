import Mathlib.Data.Real.Basic
import Mathlib.Tactic

theorem geometric_decay_from_one_step_contraction
    (f : ℕ → ℝ) (κ : ℝ)
    (hκ_lt : κ < 1)
    (h_step : ∀ t, f (t + 1) ≤ (1 - κ) * f t) :
    ∀ t, f t ≤ (1 - κ) ^ t * f 0 := by
  intro t
  induction t with
  | zero => simp
  | succ n ih =>
    calc f (n + 1) ≤ (1 - κ) * f n := h_step n
    _ ≤ (1 - κ) * ((1 - κ) ^ n * f 0) := by
        apply mul_le_mul_of_nonneg_left ih
        linarith
    _ = (1 - κ) ^ (n + 1) * f 0 := by ring
