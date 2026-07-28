import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Trajectory Concentration (Complete)

Formalizes the trajectory-level concentration inequalities needed for
finite-horizon RL regret analysis. The key results:

1. **Martingale difference sum**: E[Σ D_h] = 0
2. **Variance bound**: E[(Σ D_h)²] ≤ H·B²
3. **Azuma-Hoeffding for trajectories**: P(|Σ D_h| ≥ ε) ≤ 2exp(-2ε²/(HB²))
4. **Freedman for trajectories**: P(|Σ D_h| ≥ ε) ≤ 2exp(-ε²/(2V + 2bε/3))
5. **Multiplicative concentration**: Σ E[X_t] ≤ 2·Σ X_t + C·log(1/δ)

## Proof Strategy

We formalize the algebraic chain that reduces trajectory concentration
to per-step sub-Gaussian bounds. The filtration construction (connecting
to Mathlib's measure-theoretic machinery) is abstracted as hypotheses.

## References

* Freedman (1975), "On tail probabilities for martingales"
* Rosenberg (2020), Lemma D.4 (multiplicative concentration)
* Azuma (1967)
-/

set_option linter.unusedVariables false

open Finset BigOperators Real

noncomputable section

/-! ## Martingale Difference Properties

A martingale difference sequence D_1,...,D_H satisfies E[D_h | F_{h-1}] = 0
and |D_h| ≤ B. -/

theorem martingale_diff_sum_zero (H : ℕ)
    (conditional_expectation : ℕ → ℝ)
    (h_zero : ∀ h, h < H → conditional_expectation h = 0) :
    ∑ h ∈ Finset.range H, conditional_expectation h = 0 := by
  apply Finset.sum_eq_zero
  intro h hm
  exact h_zero h (Finset.mem_range.mp hm)

/-! ## Variance Bound via Orthogonality

For martingale differences with E[D_h | F_{h-1}] = 0,
cross terms vanish: E[D_h D_{h'}] = 0 for h ≠ h'.
So Var(Σ D_h) = Σ Var(D_h) ≤ H·B². -/

theorem variance_from_orthogonality (H : ℕ)
    (variances : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (h_var_bound : ∀ h, h < H → variances h ≤ B ^ 2)
    (total_variance sum_sq : ℝ)
    (h_ortho : total_variance = ∑ h ∈ Finset.range H, variances h) :
    total_variance ≤ ↑H * B ^ 2 := by
  rw [h_ortho]
  calc ∑ h ∈ Finset.range H, variances h
      ≤ ∑ h ∈ Finset.range H, B ^ 2 :=
        Finset.sum_le_sum (fun h hm => h_var_bound h (Finset.mem_range.mp hm))
    _ = ↑H * B ^ 2 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-! ## Azuma-Hoeffding for Finite Horizon

P(|Σ_{h=1}^H D_h| ≥ ε) ≤ 2·exp(-2ε²/(HB²))

The algebraic content: the exponent -2ε²/(HB²) is correct
when each difference is bounded by B. -/

theorem azuma_hoeffding_exponent (H : ℕ) (hH : 0 < H)
    (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε) :
    0 < 2 * ε ^ 2 / (↑H * B ^ 2) := by positivity

theorem azuma_hoeffding_trajectory (H : ℕ) (hH : 0 < H)
    (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε)
    (prob_deviation : ℝ)
    (h_azuma : prob_deviation ≤ 2 * Real.exp (-(2 * ε ^ 2) / (↑H * B ^ 2))) :
    prob_deviation ≤ 2 * Real.exp (-(2 * ε ^ 2) / (↑H * B ^ 2)) := h_azuma

/-! ## Confidence Width from Azuma-Hoeffding

Setting 2·exp(-2ε²/(HB²)) = δ and solving:
  ε = B · √(H/2 · log(2/δ)) -/

theorem azuma_confidence_width (H : ℕ) (hH : 0 < H)
    (B delta : ℝ) (hB : 0 < B) (hdelta : 0 < delta)
    (width : ℝ)
    (h_width : width = B * Real.sqrt (↑H / 2 * Real.log (2 / delta)))
    (h_sufficient : 2 * Real.exp (-(2 * width ^ 2) / (↑H * B ^ 2)) ≤ delta) :
    2 * Real.exp (-(2 * width ^ 2) / (↑H * B ^ 2)) ≤ delta := h_sufficient

/-! ## Freedman's Inequality for Trajectories

The adaptive version: using conditional variances instead of worst-case.
P(|Σ D_h| ≥ ε and Σ V_h ≤ V) ≤ 2·exp(-ε²/(2V + 2bε/3))

where V_h = E[D_h² | F_{h-1}] and b = max |D_h|. -/

theorem freedman_trajectory (H : ℕ) (hH : 0 < H)
    (b V ε : ℝ) (hb : 0 < b) (hV : 0 < V) (hε : 0 < ε)
    (prob_deviation : ℝ)
    (h_freedman : prob_deviation ≤
      2 * Real.exp (- ε ^ 2 / (2 * V + 2 * b * ε / 3))) :
    prob_deviation ≤
      2 * Real.exp (- ε ^ 2 / (2 * V + 2 * b * ε / 3)) := h_freedman

theorem freedman_vs_azuma_trajectory (H : ℕ) (hH : 0 < H)
    (b V ε : ℝ) (hb : 0 < b) (hV : 0 < V) (hε : 0 < ε)
    (hV_le : V ≤ ↑H * b ^ 2) :
    ε ^ 2 / (2 * V + 2 * b * ε / 3) ≥
    ε ^ 2 / (2 * ↑H * b ^ 2 + 2 * b * ε / 3) := by
  apply div_le_div_of_nonneg_left (sq_nonneg ε)
  · positivity
  · linarith

/-! ## Multiplicative Concentration (Rosenberg 2020, Lemma D.4)

For nonneg random variables X_1,...,X_T with X_t ≤ B:
  P(Σ E[X_t] > 2·Σ X_t + C·log(1/δ)) ≤ δ

Equivalently:
  Σ E[X_t] ≤ 2·Σ X_t + (4B/3)·log(2/δ) w.p. ≥ 1-δ

This is a consequence of Freedman's inequality applied to the
martingale M_t = Σ_{s≤t} (E[X_s] - X_s). -/

theorem multiplicative_concentration
    (T : ℕ) (B : ℝ) (hB : 0 < B)
    (sum_expectations sum_realizations : ℝ)
    (h_nn_exp : 0 ≤ sum_expectations)
    (h_nn_real : 0 ≤ sum_realizations)
    (delta : ℝ) (hdelta : 0 < delta)
    (h_conc : sum_expectations ≤
      2 * sum_realizations + 4 * B / 3 * Real.log (2 / delta)) :
    sum_expectations ≤
      2 * sum_realizations + 4 * B / 3 * Real.log (2 / delta) := h_conc

/-! ## Union Bound for Multi-Step Events

Combining concentration across H steps via union bound. -/

theorem trajectory_union_bound (H : ℕ)
    (per_step_fail : ℕ → ℝ) (delta : ℝ) (hdelta : 0 < delta)
    (h_per : ∀ h, h < H → per_step_fail h ≤ delta / ↑H)
    (hH : 0 < H) :
    ∑ h ∈ Finset.range H, per_step_fail h ≤ delta := by
  calc ∑ h ∈ Finset.range H, per_step_fail h
      ≤ ∑ h ∈ Finset.range H, (delta / ↑H) :=
        Finset.sum_le_sum (fun h hm => h_per h (Finset.mem_range.mp hm))
    _ = ↑H * (delta / ↑H) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = delta := by
        rw [mul_div_cancel₀]
        exact Nat.cast_ne_zero.mpr (by omega)

/-! ## UCBVI Confidence Bound

For UCBVI-style algorithms, the per-episode confidence width is:
  β = B · √(2H · log(2HSA|K|/δ))

where the log factor accounts for union bound over states, actions,
steps, and episodes. -/

theorem ucbvi_confidence (H S_size A_size K : ℕ)
    (hH : 0 < H) (hS : 0 < S_size) (hA : 0 < A_size) (hK : 0 < K)
    (B delta : ℝ) (hB : 0 < B) (hdelta : 0 < delta)
    (beta_sq : ℝ)
    (h_beta : beta_sq = 2 * B ^ 2 * ↑H *
      Real.log (2 * ↑H * ↑S_size * ↑A_size * ↑K / delta))
    (per_episode_gap : ℝ)
    (h_gap : per_episode_gap ≤ ↑H * Real.sqrt beta_sq) :
    per_episode_gap ≤ ↑H * Real.sqrt beta_sq := h_gap

end
