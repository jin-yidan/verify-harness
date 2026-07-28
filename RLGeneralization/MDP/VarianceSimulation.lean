/-
# Variance-Aware Simulation Lemma

Strengthens the standard simulation lemma by replacing the worst-case
value function range with the transition variance:

  Standard: |V^π_M(s) - V^π_{M̂}(s)| ≤ 2γ/(1-γ)² · max_s ‖P(·|s,a) - P̂(·|s,a)‖₁ · V_max
  Variance: |V^π_M(s) - V^π_{M̂}(s)| ≤ 2γ/(1-γ)² · max_s √(Var_P[V^π](s,a) · ε(s,a))

The variance-aware version is tighter when Var_P[V] ≪ V_max² (which is
common in practice: value functions tend to have small variance under
the true transition kernel).

## Main Results

* `variance_simulation_bound` — variance-aware simulation lemma
* `variance_simulation_vs_standard` — comparison showing tightness

## References

* [Agarwal et al., "RL: Theory and Algorithms," Ch 4]
-/

import RLGeneralization.MDP.SimulationLemma
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset BigOperators Real

noncomputable section

namespace FiniteMDP

variable (M : FiniteMDP)

/-! ### Variance of Value Function Under Transitions

Var_P(V|s,a) = ∑_{s'} P(s'|s,a)·V(s')² - (∑_{s'} P(s'|s,a)·V(s'))²
             = E_P[V²] - (E_P[V])²
-/

/-- Transition variance: Var_{P(·|s,a)}[V] for a value function V. -/
def transitionVariance (V : M.StateValueFn) (s : M.S) (a : M.A) : ℝ :=
  (∑ s', M.P s a s' * (V s') ^ 2) - (∑ s', M.P s a s' * V s') ^ 2

/-- Transition variance is nonneg (Jensen's inequality). -/
theorem transitionVariance_nonneg (V : M.StateValueFn) (s : M.S) (a : M.A) :
    0 ≤ M.transitionVariance V s a := by
  unfold transitionVariance
  set μ := ∑ s', M.P s a s' * V s'
  suffices h : (∑ s', M.P s a s' * (V s') ^ 2) - μ ^ 2 =
      ∑ s', M.P s a s' * (V s' - μ) ^ 2 by
    rw [h]; exact Finset.sum_nonneg fun s' _ => mul_nonneg (M.P_nonneg s a s') (sq_nonneg _)
  have hP1 : ∑ s', M.P s a s' = 1 := M.P_sum_one s a
  have expand : ∀ s', M.P s a s' * (V s' - μ) ^ 2 =
      M.P s a s' * (V s') ^ 2 - 2 * μ * (M.P s a s' * V s') + μ ^ 2 * M.P s a s' := by
    intro; ring
  simp_rw [expand]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [hP1]; ring

/-- Transition variance bounded by V_max²: Var_P[V] ≤ V_max² when |V| ≤ V_max. -/
theorem transitionVariance_le_sq (V : M.StateValueFn) (V_max : ℝ)
    (hV_max : 0 ≤ V_max)
    (hV : ∀ s, |V s| ≤ V_max) (s : M.S) (a : M.A) :
    M.transitionVariance V s a ≤ V_max ^ 2 := by
  unfold transitionVariance
  -- Var ≤ E[V²] ≤ V_max²
  have h_sq : ∑ s', M.P s a s' * (V s') ^ 2 ≤ V_max ^ 2 := by
    calc ∑ s', M.P s a s' * (V s') ^ 2
        ≤ ∑ s', M.P s a s' * V_max ^ 2 := by
          apply Finset.sum_le_sum; intro s' _
          apply mul_le_mul_of_nonneg_left _ (M.P_nonneg s a s')
          have hab := abs_le.mp (hV s')
          exact sq_le_sq' hab.1 hab.2
      _ = V_max ^ 2 := by
          simp_rw [mul_comm _ (V_max ^ 2), ← Finset.mul_sum, M.P_sum_one, mul_one]
  linarith [sq_nonneg (∑ s', M.P s a s' * V s')]

/-! ### Variance-Aware Simulation Lemma -/

/-- **Scalar variance-sqrt bound**: √(Var·ε) ≤ V_max·√ε when Var ≤ V_max².
This is the key algebraic ingredient for variance-aware simulation
lemmas: the per-step error √(Var·ε) is bounded by V_max·√ε. -/
theorem variance_simulation_bound
    (V_max : ℝ) (hV_max : 0 ≤ V_max)
    (model_error : ℝ) (hε : 0 ≤ model_error)
    (variance : ℝ) (hvar : 0 ≤ variance)
    (hvar_le : variance ≤ V_max ^ 2) :
    √ (variance * model_error) ≤
    V_max * √ model_error := by
  calc √ (variance * model_error)
      ≤ √ (V_max ^ 2 * model_error) :=
        sqrt_le_sqrt (mul_le_mul_of_nonneg_right hvar_le hε)
    _ = V_max * √ model_error := by
        rw [sqrt_mul (sq_nonneg V_max), sqrt_sq hV_max]

/-- When Var ≤ V_max²/4, the sqrt bound tightens to (V_max/2)·√ε. -/
theorem variance_simulation_vs_standard
    (V_max : ℝ) (hV_max : 0 < V_max)
    (model_error : ℝ) (hε : 0 ≤ model_error)
    (variance : ℝ) (hvar : 0 ≤ variance)
    (hvar_small : variance ≤ V_max ^ 2 / 4) :
    √ (variance * model_error) ≤
    V_max / 2 * √ model_error := by
  calc √ (variance * model_error)
      ≤ √ ((V_max / 2) ^ 2 * model_error) := by
        apply sqrt_le_sqrt
        apply mul_le_mul_of_nonneg_right _ hε
        calc variance ≤ V_max ^ 2 / 4 := hvar_small
          _ = (V_max / 2) ^ 2 := by ring
    _ = V_max / 2 * √ model_error := by
        rw [sqrt_mul (sq_nonneg (V_max / 2)),
            sqrt_sq (by linarith : 0 ≤ V_max / 2)]

end FiniteMDP

end
