/-
# Affine Contraction Bound

Bound on the affine recurrence V_{t+1} ≤ (1-α)V_t + β.

## Main Results

* `affine_contraction_bound` — V_T ≤ (1-α)^T · V_0 + β·(1-(1-α)^T)/α
* `affine_contraction_steady_state` — V_T ≤ (1-α)^T · V_0 + β/α

## References

* Standard result in optimization and RL convergence analysis
* Generalizes `geometric_decay_from_one_step_contraction` (β = 0 case)
* Used in: approximate value iteration, SGD with noise, TD learning, Markov chain mixing
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-- **Affine contraction bound**: if V_{t+1} ≤ (1-α)V_t + β with α ∈ (0,1],
    then V_T ≤ (1-α)^T · V_0 + β·(1-(1-α)^T)/α.

    Proof by induction on T, with algebra via field_simp + ring. -/
theorem affine_contraction_bound (V : ℕ → ℝ) (α β : ℝ)
    (hα_pos : 0 < α) (hα_le : α ≤ 1)
    (h_step : ∀ t, V (t + 1) ≤ (1 - α) * V t + β) (T : ℕ) :
    V T ≤ (1 - α) ^ T * V 0 + β * (1 - (1 - α) ^ T) / α := by
  induction T with
  | zero => simp
  | succ n ih =>
    have h_nn : 0 ≤ 1 - α := by linarith
    calc V (n + 1)
        ≤ (1 - α) * V n + β := h_step n
      _ ≤ (1 - α) * ((1 - α) ^ n * V 0 + β * (1 - (1 - α) ^ n) / α) + β := by
          linarith [mul_le_mul_of_nonneg_left ih h_nn]
      _ = (1 - α) ^ (n + 1) * V 0 + β * (1 - (1 - α) ^ (n + 1)) / α := by
          field_simp [ne_of_gt hα_pos]
          ring

/-- **Affine contraction steady-state**: V_T ≤ (1-α)^T · V_0 + β/α for β ≥ 0.

    Weaker but simpler form, discarding the transient decay factor on β. -/
theorem affine_contraction_steady_state (V : ℕ → ℝ) (α β : ℝ)
    (hα_pos : 0 < α) (hα_le : α ≤ 1) (hβ : 0 ≤ β)
    (h_step : ∀ t, V (t + 1) ≤ (1 - α) * V t + β) (T : ℕ) :
    V T ≤ (1 - α) ^ T * V 0 + β / α := by
  have h := affine_contraction_bound V α β hα_pos hα_le h_step T
  have h_nn : 0 ≤ 1 - α := by linarith
  have h_pow_le : (1 - α) ^ T ≤ 1 := pow_le_one₀ h_nn (by linarith)
  have h_factor : β * (1 - (1 - α) ^ T) / α ≤ β / α := by
    apply div_le_div_of_nonneg_right _ (le_of_lt hα_pos)
    nlinarith [pow_nonneg h_nn T]
  linarith
