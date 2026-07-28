/-
# UCBVI-Simulation Lemma Bridge

Connects the simulation lemma (model-error → value gap) with
the UCBVI regret analysis (bonus → regret), showing they share
the same algebraic structure.

## Main Results

* `value_error_from_transition` — per-episode regret bounded
    by H² times the transition model error, via the simulation pattern

* `simulation_regret_composition` — total regret from accumulated
    model errors across K episodes (uses `Finset.sum_le_sum`)

* `bonus_dominates_model_error` — bonus ≥ H·ε_T per episode →
    total bonus ≥ H · total ε_T (rearrangement identity)

* `simulation_total_regret` — chains `simulation_regret_composition`
    with a provided bound on ∑_k ε_T(k), giving total regret ≤ H²·Σε_T

* `simulation_ucbvi_regret_bridge` — the algebraic equivalence:
    if per-episode regret ≤ H²·ε(k) and ∑ε(k) ≤ C·√K, then
    total regret ≤ H²·C·√K

## Architecture

The simulation lemma says: |V^π_M - V^π_M̂| ≤ f(ε_R, ε_T).
UCBVI's regret analysis says: V*(s) - V^π(s) ≤ sum of bonuses.
The bridge shows: bonus ≥ model error → regret ≤ model error sum.
-/

import RLGeneralization.MDP.SimulationLemma
import RLGeneralization.Exploration.UCBVI
import RLGeneralization.Generalization.FiniteHorizonSampleComplexity

open Finset BigOperators Real

noncomputable section

namespace FiniteHorizonMDP

variable (M : FiniteHorizonMDP)

/-- Per-episode regret from model error: if the per-step transition
    L1 error is ε_T, then backward induction gives value error ≤ H² · ε_T.
    This is the finite-horizon analogue of the simulation lemma.

    Hypotheses: assumes per-step backward-induction errors are each
    bounded by H·ε_T, and that the total value error decomposes as
    a sum of per-step errors (standard backward-induction structure). -/
theorem value_error_from_transition
    (V_hat V_star : M.S → ℝ)
    (ε_T : ℝ)
    -- Per-step backward induction errors
    (per_step_err : Fin M.H → ℝ)
    (h_ps_bound : ∀ h, per_step_err h ≤ (M.H : ℝ) * ε_T)
    -- Value error ≤ sum of per-step errors (backward induction)
    (h_value_sum : ∀ s, |V_hat s - V_star s| ≤ ∑ h : Fin M.H, per_step_err h)
    (s : M.S) :
    |V_hat s - V_star s| ≤ M.H ^ 2 * ε_T := by
  calc |V_hat s - V_star s|
      ≤ ∑ h : Fin M.H, per_step_err h := h_value_sum s
    _ ≤ ∑ _h : Fin M.H, (M.H : ℝ) * ε_T :=
        Finset.sum_le_sum (fun h _ => h_ps_bound h)
    _ = (M.H : ℝ) * ((M.H : ℝ) * ε_T) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = M.H ^ 2 * ε_T := by ring

/-- Total regret composition: if per-episode model error is ε(k),
    then cumulative regret ≤ H² · ∑ ε(k).

    This is the bridge between the simulation lemma (which bounds
    per-episode value gap) and the UCBVI regret (which sums over
    K episodes). The factor H² comes from error propagation through
    H backward induction steps (proved in FiniteHorizonSampleComplexity). -/
theorem simulation_regret_composition
    (K : ℕ) (ε : Fin K → ℝ) (_hε : ∀ k, 0 ≤ ε k)
    (per_episode_gap : Fin K → ℝ)
    (h_gap : ∀ k, per_episode_gap k ≤ M.H ^ 2 * ε k) :
    ∑ k : Fin K, per_episode_gap k ≤ M.H ^ 2 * ∑ k : Fin K, ε k := by
  calc ∑ k : Fin K, per_episode_gap k
      ≤ ∑ k : Fin K, M.H ^ 2 * ε k :=
        Finset.sum_le_sum (fun k _ => h_gap k)
    _ = M.H ^ 2 * ∑ k : Fin K, ε k := by
        rw [← Finset.mul_sum]

/-- The simulation-UCBVI equivalence: UCBVI's bonus-based regret bound
    and the simulation lemma's error-based bound are algebraically
    equivalent up to the factor connecting bonus size to model error.

    Specifically: if bonus(s,a,h) ≥ H · ε_T(k), then the UCBVI regret
    bound (sum of bonuses) dominates the simulation bound (H · sum ε_T).

    This theorem packages the algebraic content: given a bonus that
    dominates the model error, regret is controlled. -/
theorem bonus_dominates_model_error
    (K : ℕ) (ε : Fin K → ℝ) (bonus_total : ℝ)
    (h_bonus_sum : ∑ k : Fin K, M.H * ε k ≤ bonus_total)
    (_hH : 0 < M.H) :
    M.H * ∑ k : Fin K, ε k ≤ bonus_total := by
  rwa [← Finset.mul_sum] at h_bonus_sum

/-- **Total regret from a sum-of-errors bound**.

    Chains `simulation_regret_composition` with a provided upper bound on
    the total model error ∑_k ε_T(k) ≤ total_eps.

    This is the key composition step: if we have a bound on cumulative
    model errors (e.g., from Azuma-Hoeffding concentration or a data-dependent
    argument), then simulation_regret_composition converts it to a regret bound.

    The `total_eps` in practice comes from:
    - Cauchy-Schwarz: ∑_k ε(k) ≤ √K · ‖ε‖_2
    - Concentration: ε(k) = O(1/√N_k) where N_k are episode visit counts -/
theorem simulation_total_regret
    (K : ℕ) (ε : Fin K → ℝ) (hε : ∀ k, 0 ≤ ε k)
    (total_eps : ℝ) (h_total : ∑ k : Fin K, ε k ≤ total_eps)
    (per_episode_gap : Fin K → ℝ)
    (h_sim : ∀ k, per_episode_gap k ≤ M.H ^ 2 * ε k) :
    ∑ k : Fin K, per_episode_gap k ≤ M.H ^ 2 * total_eps := by
  have h := M.simulation_regret_composition K ε hε per_episode_gap h_sim
  have hH2 : 0 ≤ (M.H : ℝ) ^ 2 := sq_nonneg _
  linarith [mul_le_mul_of_nonneg_left h_total hH2]

/-- **UCBVI-Simulation regret bridge in O(H²·C·√K) form**.

    If:
    - Per-episode value gap ≤ H²·ε(k) for each episode k (simulation)
    - ∑_k ε(k) ≤ C · √K (total error bound from concentration)
    Then: ∑_k (value gap k) ≤ H² · C · √K.

    This combines the simulation error propagation (H² factor from
    backward induction depth) with an √K concentration bound on the
    accumulated model errors, giving the characteristic UCBVI scaling. -/
theorem simulation_ucbvi_regret_bridge
    (K : ℕ) (ε : Fin K → ℝ) (hε : ∀ k, 0 ≤ ε k)
    (C : ℝ) (_hC : 0 ≤ C)
    (h_total : ∑ k : Fin K, ε k ≤ C * Real.sqrt K)
    (per_episode_gap : Fin K → ℝ)
    (h_sim : ∀ k, per_episode_gap k ≤ M.H ^ 2 * ε k) :
    ∑ k : Fin K, per_episode_gap k ≤ M.H ^ 2 * C * Real.sqrt K := by
  have h1 := M.simulation_total_regret K ε hε (C * Real.sqrt K) h_total
    per_episode_gap h_sim
  linarith

end FiniteHorizonMDP

end
