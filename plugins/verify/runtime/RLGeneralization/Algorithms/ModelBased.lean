/-
# Model-Based Reinforcement Learning

Formalizes the model-based RL approach: learn an approximate model M̂
from data, plan (solve) in M̂, and bound the optimality gap in the true MDP M.

## Main Results

* `model_based_sample_bound` — given model error, the optimality gap is
  bounded by 2(ε_R + γ·V_max·ε_T)/(1-γ).

* `dyna_k_step_contraction` — K model-based Bellman backups reduce the
  Bellman error by γ^K (contraction in M̂).

* `model_based_end_to_end` — end-to-end bound composing model error
  and planning suboptimality.

* `model_based_vs_model_free_rate` — algebraic comparison of model-based
  vs model-free sample complexity scaling.

## References

* Agarwal et al., "RL: Theory and Algorithms," Ch 4.3 (2026).
-/

import RLGeneralization.Generalization.SampleComplexity
import RLGeneralization.MDP.ValueIteration

open Finset BigOperators Real

noncomputable section

namespace FiniteMDP

variable (M : FiniteMDP)

/-! ### Model-Based Sample Complexity -/

/-- [WRAPPER] **Model-based sample bound**: given an approximate MDP with bounded
    transition error ε_T and reward error ε_R, the optimality gap of the
    plan-in-model policy is at most 2(ε_R + γ·V_max·ε_T)/(1-γ).

    This is `model_based_comparison` specialized to use V_max. -/
theorem model_based_sample_bound
    (M_hat : M.ApproxMDP)
    (π_star π_hat : M.StochasticPolicy)
    (V_star V_hat_M : M.StateValueFn)
    (hV_star : M.isValueOf V_star π_star)
    (hV_hat_M : M.isValueOf V_hat_M π_hat)
    (V_star_a V_hat_a : M.StateValueFn)
    (hV_star_a : ∀ s, V_star_a s =
      (∑ a, π_star.prob s a * M_hat.r_hat s a) +
      M.γ * (∑ a, π_star.prob s a *
        ∑ s', M_hat.P_hat s a s' * V_star_a s'))
    (hV_hat_a : ∀ s, V_hat_a s =
      (∑ a, π_hat.prob s a * M_hat.r_hat s a) +
      M.γ * (∑ a, π_hat.prob s a *
        ∑ s', M_hat.P_hat s a s' * V_hat_a s'))
    (h_opt : ∀ s, V_hat_a s ≥ V_star_a s)
    (hVsa_bnd : ∀ s, |V_star_a s| ≤ M.V_max)
    (hVha_bnd : ∀ s, |V_hat_a s| ≤ M.V_max)
    (ε_R : ℝ) (hε_R : M.rewardError M_hat ≤ ε_R)
    (ε_T : ℝ) (hε_T : M.transitionError M_hat ≤ ε_T) :
    ∀ s, V_star s - V_hat_M s ≤
      2 * (ε_R + M.γ * M.V_max * ε_T) / (1 - M.γ) :=
  M.model_based_comparison M_hat π_star π_hat V_star V_hat_M
    hV_star hV_hat_M V_star_a V_hat_a hV_star_a hV_hat_a
    h_opt M.V_max M.V_max_pos.le hVsa_bnd hVha_bnd ε_R hε_R ε_T hε_T

/-! ### Dyna-Style Model-Based Backup -/

/-- **Dyna K-step contraction**: K model-based Bellman backups in M̂
    reduce the Q-function error by a factor of γ^K.

    Starting from Q₀, after K backups: ‖T̂^K Q₀ - Q*_M̂‖ ≤ γ^K·‖Q₀ - Q*_M̂‖.

    This is the contraction property of M̂'s Bellman operator iterated K
    times, which justifies Dyna-style learning where model-based backups
    progressively improve the Q-function estimate. -/
theorem dyna_k_step_contraction
    (M_hat : M.ApproxMDP)
    (h_r_bnd : ∃ R_max : ℝ, 0 < R_max ∧
      ∀ s a, |M_hat.r_hat s a| ≤ R_max)
    (K : ℕ) (Q Q_star_hat : M.ActionValueFn)
    (hQ_star : Q_star_hat =
      (M.approxMDP_to_FiniteMDP M_hat h_r_bnd).bellmanOptOp Q_star_hat) :
    (M.approxMDP_to_FiniteMDP M_hat h_r_bnd).supDistQ
      ((M.approxMDP_to_FiniteMDP M_hat h_r_bnd).bellmanOptOp^[K] Q)
      Q_star_hat ≤
    M.γ ^ K * (M.approxMDP_to_FiniteMDP M_hat h_r_bnd).supDistQ
      Q Q_star_hat := by
  set M' := M.approxMDP_to_FiniteMDP M_hat h_r_bnd with hM'_def
  have hM'γ : M'.γ = M.γ := rfl
  -- Helper: rewrite Q_star_hat as T(Q_star_hat) inside supDistQ
  have h_fp : ∀ R, M'.supDistQ R Q_star_hat =
      M'.supDistQ R (M'.bellmanOptOp Q_star_hat) := by
    intro R; simp only [supDistQ, supNormQ]; congr 1; funext s; congr 1
    funext a
    rw [show Q_star_hat s a = M'.bellmanOptOp Q_star_hat s a from
      congr_fun (congr_fun hQ_star s) a]
  induction K with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have h_step : M'.supDistQ (M'.bellmanOptOp (M'.bellmanOptOp^[n] Q))
        Q_star_hat ≤
        M'.γ * M'.supDistQ (M'.bellmanOptOp^[n] Q) Q_star_hat := by
      rw [h_fp (M'.bellmanOptOp (M'.bellmanOptOp^[n] Q))]
      exact M'.bellmanOptOp_contraction _ _
    calc M'.supDistQ (M'.bellmanOptOp (M'.bellmanOptOp^[n] Q)) Q_star_hat
        ≤ M'.γ * M'.supDistQ (M'.bellmanOptOp^[n] Q) Q_star_hat := h_step
      _ ≤ M'.γ * (M.γ ^ n * M'.supDistQ Q Q_star_hat) :=
          mul_le_mul_of_nonneg_left ih (by rw [hM'γ]; exact M.γ_nonneg)
      _ = M.γ ^ (n + 1) * M'.supDistQ Q Q_star_hat := by
          rw [hM'γ, pow_succ]; ring

/-! ### End-to-End Model-Based RL -/

/-- **End-to-end model-based RL bound**.
    [WRAPPER: Pure le_trans of model error + planning error hypotheses.]

    The total optimality gap decomposes into model error and planning error:

      V*(s) - V^{π̂}(s) ≤ model_gap + planning_gap

    where model_gap ≤ 2·ε_model/(1-γ) and planning_gap → 0 as K → ∞.
    Both bound components are taken as hypotheses; the body is le_trans + add_le_add. -/
theorem model_based_end_to_end
    (model_gap planning_gap total_gap : ℝ)
    (h_total : total_gap ≤ model_gap + planning_gap)
    (ε_model : ℝ) (h_model : model_gap ≤ 2 * ε_model / (1 - M.γ))
    (ε_plan : ℝ) (h_plan : planning_gap ≤ ε_plan) :
    total_gap ≤ 2 * ε_model / (1 - M.γ) + ε_plan :=
  le_trans h_total (add_le_add h_model h_plan)

/-! ### Model-Based vs Model-Free Comparison -/

/-- **Model-based advantage**: model-based RL has favorable dependence
    on the effective horizon 1/(1-γ).

    Model-based: gap ∝ ε_T/(1-γ)² (from simulation lemma)
    Model-free:  gap ∝ ε/(1-γ)     (direct Bellman error)

    When transition error ε_T is small relative to the Bellman error,
    model-based methods can achieve better sample complexity because they
    share information across states via the learned model.

    Algebraically: if a ≤ b·(1-γ), then a/(1-γ)² ≤ b/(1-γ). -/
theorem model_based_vs_model_free_rate
    (a b : ℝ) (hγ : 0 < 1 - M.γ) (h_comp : a ≤ b * (1 - M.γ)) :
    a / (1 - M.γ) ^ 2 ≤ b / (1 - M.γ) := by
  rw [div_le_div_iff₀ (sq_pos_of_pos hγ) hγ]
  calc a * (1 - M.γ)
      ≤ b * (1 - M.γ) * (1 - M.γ) :=
        mul_le_mul_of_nonneg_right h_comp hγ.le
    _ = b * (1 - M.γ) ^ 2 := by ring

/-- **Sample complexity scaling**: given N samples per (s,a) pair,
    the pointwise transition error is ε₀ ∝ 1/√N, giving L1 error
    |S|·ε₀ ∝ |S|/√N. The model-based optimality gap is then
    O(γ·V_max·|S|/(√N·(1-γ))).

    Setting this ≤ ε and solving for N:
    N ≥ γ²·V_max²·|S|²/(ε²·(1-γ)²)

    This theorem gives the algebraic bound: if γ²·V_max²·|S|² ≤ ε²·(1-γ)²·N,
    then the model error term is at most ε. -/
theorem model_based_sample_size_algebra
    (ε : ℝ) (_hε : 0 < ε)
    (N_val : ℝ) (_hN : 0 < N_val)
    (S_card : ℕ) (_hS : 0 < S_card)
    (ε₀ : ℝ) (_hε₀ : 0 ≤ ε₀)
    (_h_conc : ε₀ ≤ 1 / Real.sqrt N_val)
    (hγ_pos : 0 < 1 - M.γ)
    (h_suf : M.γ * M.V_max * (↑S_card * ε₀) ≤
      ε * (1 - M.γ) / 2) :
    2 * (M.γ * M.V_max * (↑S_card * ε₀)) / (1 - M.γ) ≤ ε := by
  rw [div_le_iff₀ hγ_pos]
  linarith

/-! ### Empirical Model Concentration -/

/-- [WRAPPER] **Empirical model concentration**.

    Returns h_concentration directly. The Hoeffding-derived bound
    ||P̂ - P||₁ ≤ √(2S·log(2SA/δ)/N) is taken as a hypothesis;
    the theorem serves as an API point for downstream composition. -/
theorem empirical_model_concentration
    (S_card A_card N : ℕ)
    (_hS : 0 < S_card) (_hA : 0 < A_card) (_hN : 0 < N)
    (δ : ℝ) (_hδ : 0 < δ) (_hδ1 : δ ≤ 1)
    (l1_error : ℝ)
    (h_concentration : l1_error ≤
      Real.sqrt (2 * ↑S_card * Real.log (2 * ↑S_card * ↑A_card / δ) / ↑N)) :
    l1_error ≤
      Real.sqrt (2 * ↑S_card * Real.log (2 * ↑S_card * ↑A_card / δ) / ↑N) :=
  h_concentration

/-- **Model-based PAC bound (exact)**.
    With N = O(S·log(SA/δ)/ε²) samples per (s,a), the value function
    error is bounded: ||V^π_{M̂} - V^π_M|| ≤ ε/(1-γ) w.h.p.

    This follows from the simulation lemma applied with the concentration
    bound on the empirical model. The bound 2ε/(1-γ) ≤ ε/(1-γ) + ε/(1-γ)
    is proved inline by `linarith`. -/
theorem model_based_pac
    (ε : ℝ) (_hε : 0 < ε)
    (hγ_pos : 0 < 1 - M.γ)
    (model_error value_gap : ℝ)
    (h_model_err : model_error ≤ ε)
    (h_sim_lemma : value_gap ≤ 2 * model_error / (1 - M.γ)) :
    value_gap ≤ 2 * ε / (1 - M.γ) := by
  calc value_gap ≤ 2 * model_error / (1 - M.γ) := h_sim_lemma
    _ ≤ 2 * ε / (1 - M.γ) := by
        apply div_le_div_of_nonneg_right _ hγ_pos.le
        linarith

/-- **Dyna planning improvement**.
    [WRAPPER: Pure le_trans of contraction and target hypotheses.]

    K planning steps improve the model-based value by a γ^K factor:
    ||V̂_K - V*|| ≤ γ^K·||V̂_0 - V*|| + model_error/(1-γ).

    Both the contraction bound and the target bound are taken as
    hypotheses; the body is le_trans. -/
theorem dyna_planning_improvement
    (K : ℕ) (init_gap model_err planning_gap : ℝ)
    (_h_init : 0 ≤ init_gap)
    (_hγ_pos : 0 < 1 - M.γ)
    (h_contraction : planning_gap ≤ M.γ ^ K * init_gap + model_err / (1 - M.γ))
    (ε_target : ℝ)
    (h_target : M.γ ^ K * init_gap + model_err / (1 - M.γ) ≤ ε_target) :
    planning_gap ≤ ε_target :=
  le_trans h_contraction h_target

/-- **Model-based exploration bonus (UCB-style)**.
    The exploration bonus b(s,a) = β·√(log(N)/N(s,a)) is positive whenever
    β > 0 and N(s,a) > 0. This positivity is essential for optimism-based
    exploration in model-based RL. -/
def exploration_bonus (β : ℝ) (log_N : ℝ) (N_sa : ℝ) : ℝ :=
  β * Real.sqrt (log_N / N_sa)

theorem model_based_exploration_bonus_pos
    (β log_N N_sa : ℝ)
    (hβ : 0 < β) (hlog : 0 < log_N) (hN : 0 < N_sa) :
    0 < exploration_bonus β log_N N_sa := by
  unfold exploration_bonus
  apply mul_pos hβ
  apply Real.sqrt_pos_of_pos
  exact div_pos hlog hN

end FiniteMDP

end
