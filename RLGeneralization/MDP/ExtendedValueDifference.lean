import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Extended Value Difference Lemma (Finite-Horizon)

The extended value difference lemma decomposes the gap between the true
value V^π and an approximate value V̂ as a sum of per-step Bellman
residuals along the trajectory induced by π:

  V^π_1(s) - V̂_1(s) = Σ_{h=1}^{H} E_{π,P}[r_h + P_h V^π_{h+1} - Q̂_h]

## References

* Shani, Efroni, Mannor (2020), Lemma 1
* Jiang & Li (2016), simulation lemma for finite-horizon MDPs
-/

set_option linter.unusedVariables false

open Finset BigOperators

noncomputable section

/-! ## Telescoping Sum Identity -/

private theorem telescoping_with_remainder (H : ℕ)
    (diff : ℕ → ℝ) (residual : ℕ → ℝ)
    (h_recursion : ∀ h, h < H → diff h = residual h + diff (h + 1)) :
    diff 0 = ∑ h ∈ Finset.range H, residual h + diff H := by
  induction H with
  | zero => simp
  | succ n ih =>
    have ih' := ih (fun h hlt => h_recursion h (by omega))
    rw [Finset.sum_range_succ, ih']
    linarith [h_recursion n (by omega)]

theorem telescoping_sum_identity (H : ℕ)
    (diff : ℕ → ℝ) (residual : ℕ → ℝ)
    (h_terminal : diff H = 0)
    (h_recursion : ∀ h, h < H → diff h = residual h + diff (h + 1)) :
    diff 0 = ∑ h ∈ Finset.range H, residual h := by
  have := telescoping_with_remainder H diff residual h_recursion
  linarith

/-! ## Extended Value Difference Lemma -/

theorem extended_value_difference (H : ℕ)
    (V_gap : ℕ → ℝ) (bellman_residual : ℕ → ℝ)
    (h_terminal : V_gap H = 0)
    (h_decomp : ∀ h, h < H → V_gap h = bellman_residual h + V_gap (h + 1)) :
    V_gap 0 = ∑ h ∈ Finset.range H, bellman_residual h :=
  telescoping_sum_identity H V_gap bellman_residual h_terminal h_decomp

/-! ## Regret via Value Difference -/

theorem regret_via_value_difference (K H : ℕ)
    (V_gap : Fin K → ℕ → ℝ)
    (residual : Fin K → ℕ → ℝ)
    (h_terminal : ∀ k, V_gap k H = 0)
    (h_decomp : ∀ k h, h < H → V_gap k h = residual k h + V_gap k (h + 1)) :
    ∑ k : Fin K, V_gap k 0 =
    ∑ k : Fin K, ∑ h ∈ Finset.range H, residual k h := by
  congr 1; ext k
  exact extended_value_difference H (V_gap k) (residual k) (h_terminal k) (h_decomp k)

/-! ## Signed Bellman Residual Bound -/

theorem value_difference_abs_bound (H : ℕ)
    (V_gap : ℕ → ℝ) (residual : ℕ → ℝ) (width : ℕ → ℝ)
    (h_terminal : V_gap H = 0)
    (h_decomp : ∀ h, h < H → V_gap h = residual h + V_gap (h + 1))
    (h_bound : ∀ h, h < H → |residual h| ≤ width h) :
    |V_gap 0| ≤ ∑ h ∈ Finset.range H, width h := by
  rw [extended_value_difference H V_gap residual h_terminal h_decomp]
  calc |∑ h ∈ Finset.range H, residual h|
      ≤ ∑ h ∈ Finset.range H, |residual h| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ h ∈ Finset.range H, width h :=
        Finset.sum_le_sum (fun h hm => h_bound h (Finset.mem_range.mp hm))

end
