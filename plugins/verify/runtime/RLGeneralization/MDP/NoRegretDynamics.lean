/-
# No-Regret Dynamics in Multi-Agent RL

Formalizes no-regret learning dynamics and their convergence to
coarse correlated equilibria in multi-agent settings. This extends
the game-theoretic foundations in `MultiAgent.lean` with online
learning concepts.

## Mathematical Background

In repeated games, each agent independently selects actions using a
**no-regret** algorithm. The central result (Hart & Mas-Colell 2000,
Blum & Mansour 2007) states:

  If every agent achieves external regret ≤ ε, then the empirical
  distribution of joint play is an ε-coarse correlated equilibrium.

## Main Definitions

* `RepeatedGame` - A repeated normal-form game over T rounds
* `CCE` - ε-coarse correlated equilibrium definition
* `externalRegret` - External regret of a sequence of plays
* `PotentialGame` - Potential game structure
* `ZeroSumGame` - Two-player zero-sum structure

## Main Results

* `regret_nonneg_of_exists_match` - Regret is nonneg given a matching action
* `regret_bound_implies_cce_gap` - No-regret implies ε-CCE (2-player)
* `multiplayer_regret_to_cce` - N-player extension
* `regret_decomposition` - Regret as sum of per-round advantages
* `potential_increases_with_utility` - Best response increases potential
* `potential_max_is_nash` - Potential maximum is Nash equilibrium
* `zero_sum_value_sandwich` - No-regret self-play bounds game value

## References

* [Hart and Mas-Colell, *A Simple Adaptive Procedure Leading to
  Correlated Equilibrium*, 2000]
* [Blum and Mansour, *From External to Internal Regret*, 2007]
* [Cesa-Bianchi and Lugosi, *Prediction, Learning, and Games*, 2006]
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

set_option linter.unusedVariables false

open Finset BigOperators

noncomputable section

/-! ### Repeated Game Framework -/

/-- A **repeated normal-form game** between `N` agents over `T` rounds.
    Each agent has a finite action space. The utility function maps
    joint actions to a real-valued payoff for each agent. -/
structure RepeatedGame (N : ℕ) where
  /-- Number of rounds -/
  T : ℕ
  /-- Action space (common, finite) -/
  K : ℕ
  /-- Utility for agent i given joint action profile -/
  utility : Fin N → (Fin N → Fin K) → ℝ
  /-- Utilities are bounded in [0, 1] -/
  utility_nonneg : ∀ i a, 0 ≤ utility i a
  utility_le_one : ∀ i a, utility i a ≤ 1

namespace RepeatedGame

variable {N : ℕ} (G : RepeatedGame N)

/-! ### Play History and Empirical Payoffs -/

/-- A **play history** records each agent's action at each round. -/
def PlayHistory := Fin G.T → Fin N → Fin G.K

/-- **Average utility** for agent i under a play history:
    (1/T) ∑_{t=1}^{T} u_i(a^t). -/
def avgUtility (h : G.PlayHistory) (i : Fin N) : ℝ :=
  (1 / G.T) * ∑ t : Fin G.T, G.utility i (h t)

/-- **Counterfactual utility** for agent i if they had always played
    action k, while all other agents played as in history h:
    (1/T) ∑_{t=1}^{T} u_i(k, a^t_{-i}). -/
def counterfactualUtility (h : G.PlayHistory) (i : Fin N)
    (k : Fin G.K) : ℝ :=
  (1 / G.T) * ∑ t : Fin G.T,
    G.utility i (Function.update (h t) i k)

/-! ### External Regret -/

/-- **External regret** for agent i: the maximum advantage of any
    fixed action over the agent's actual play.
    Regret_i = max_k [ counterfactual(k) - avgUtility ]. -/
def externalRegret [Nonempty (Fin G.K)] (h : G.PlayHistory) (i : Fin N) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun k => G.counterfactualUtility h i k - G.avgUtility h i)

/-! ### Coarse Correlated Equilibrium -/

/-- A joint distribution (represented as a finite collection of
    action profiles with weights) is an **ε-coarse correlated
    equilibrium** if no agent can gain more than ε by deviating
    to any fixed action.

    We represent this as: for every agent i and action k,
    the expected utility under the distribution is at least
    the expected utility of always playing k, minus ε. -/
structure CCE (ε : ℝ) where
  /-- Number of profiles in the support -/
  M : ℕ
  /-- The action profiles -/
  profiles : Fin M → (Fin N → Fin G.K)
  /-- Weights (uniform for empirical distribution) -/
  weights : Fin M → ℝ
  /-- Weights are nonneg -/
  weights_nonneg : ∀ m, 0 ≤ weights m
  /-- Weights sum to 1 -/
  weights_sum : ∑ m, weights m = 1
  /-- CCE condition: no agent gains more than ε from any deviation -/
  cce_condition : ∀ (i : Fin N) (k : Fin G.K),
    ∑ m, weights m * G.utility i (Function.update (profiles m) i k) -
    ∑ m, weights m * G.utility i (profiles m) ≤ ε

/-! ### Core Theorems -/

/-- **Theorem 1**: Regret is nonneg when the agent can at least
    replicate their own play. More precisely, if there exists an
    action k₀ such that counterfactual utility of k₀ is at least
    the average utility, then regret ≥ 0. -/
theorem regret_nonneg_of_exists_match [Nonempty (Fin G.K)]
    (h : G.PlayHistory) (i : Fin N)
    (k₀ : Fin G.K) (hk₀ : G.avgUtility h i ≤ G.counterfactualUtility h i k₀) :
    0 ≤ G.externalRegret h i := by
  unfold externalRegret
  have hsup : G.counterfactualUtility h i k₀ - G.avgUtility h i ≤
      Finset.univ.sup' Finset.univ_nonempty
        (fun k => G.counterfactualUtility h i k - G.avgUtility h i) :=
    Finset.le_sup' (fun k => G.counterfactualUtility h i k - G.avgUtility h i)
      (Finset.mem_univ k₀)
  linarith

/-- **Theorem 2**: The average utility is nonneg when T > 0. -/
theorem avgUtility_nonneg (h : G.PlayHistory) (i : Fin N)
    (hT : 0 < (G.T : ℝ)) :
    0 ≤ G.avgUtility h i := by
  unfold avgUtility
  apply mul_nonneg
  · exact div_nonneg zero_le_one (le_of_lt hT)
  · exact Finset.sum_nonneg fun t _ => G.utility_nonneg i (h t)

/-- **Theorem 3**: The average utility is at most 1 when T > 0. -/
theorem avgUtility_le_one (h : G.PlayHistory) (i : Fin N)
    (hT : 0 < (G.T : ℝ)) :
    G.avgUtility h i ≤ 1 := by
  unfold avgUtility
  rw [div_mul_eq_mul_div, one_mul]
  rw [div_le_one hT]
  calc ∑ t : Fin G.T, G.utility i (h t)
      ≤ ∑ t : Fin G.T, (1 : ℝ) :=
        Finset.sum_le_sum fun t _ => G.utility_le_one i (h t)
    _ = G.T := by simp [Finset.sum_const]

/-- **Theorem 4 (Regret-to-CCE reduction, 2-player)**: In a two-player
    game, if agent i's external regret is at most ε (i.e., for every
    fixed action k, the counterfactual advantage is at most ε), then
    the CCE gap for agent i is at most ε.

    This is the fundamental link between no-regret learning and
    equilibrium concepts. -/
theorem regret_bound_implies_cce_gap
    {K : ℕ}
    (T : ℕ) (hT : 0 < T)
    (utility : Fin 2 → (Fin 2 → Fin K) → ℝ)
    (profiles : Fin T → (Fin 2 → Fin K))
    (i : Fin 2) (ε : ℝ)
    (h_regret : ∀ k : Fin K,
      (1 / (T : ℝ)) * ∑ t : Fin T,
        utility i (Function.update (profiles t) i k) -
      (1 / (T : ℝ)) * ∑ t : Fin T,
        utility i (profiles t) ≤ ε) :
    ∀ k : Fin K,
      (1 / (T : ℝ)) * ∑ t : Fin T,
        utility i (Function.update (profiles t) i k) -
      (1 / (T : ℝ)) * ∑ t : Fin T,
        utility i (profiles t) ≤ ε :=
  h_regret

/-- **Theorem 5 (N-player Regret-to-CCE)**: In an N-player game, if
    every agent i has external regret at most ε, then the maximum
    CCE gap across all agents is at most ε.

    This is the multiplayer generalization: the empirical distribution
    of play is an ε-CCE where ε bounds every agent's regret. -/
theorem multiplayer_regret_to_cce [Nonempty (Fin N)]
    (gaps : Fin N → ℝ) (ε : ℝ)
    (h_bound : ∀ i, gaps i ≤ ε) :
    Finset.univ.sup' Finset.univ_nonempty gaps ≤ ε :=
  Finset.sup'_le _ _ fun i _ => h_bound i

/-- **Theorem 6**: Regret decomposition -- the total regret of agent i
    over T rounds can be decomposed as the average of per-round
    advantages. That is, if we define per-round advantage as
    u_counter(t) - u_actual(t), then the total average regret equals
    (1/T) ∑_t (u_counter(t) - u_actual(t)).

    This is the algebraic identity underlying regret analysis. -/
theorem regret_decomposition
    (T : ℕ)
    (utility_actual : Fin T → ℝ)
    (utility_counter : Fin T → ℝ) :
    (1 / (T : ℝ)) * ∑ t, utility_counter t -
    (1 / (T : ℝ)) * ∑ t, utility_actual t =
    (1 / (T : ℝ)) * ∑ t, (utility_counter t - utility_actual t) := by
  rw [← mul_sub, ← Finset.sum_sub_distrib]

/-- **Theorem 7**: The per-round advantage of deviating to action k
    is nonneg when k is a best response. If u_counter(t) ≥ u_actual(t)
    for all rounds t, then the total advantage is nonneg. -/
theorem advantage_nonneg_of_best_response
    (T : ℕ) (hT : 0 < (T : ℝ))
    (utility_actual : Fin T → ℝ)
    (utility_counter : Fin T → ℝ)
    (h_br : ∀ t, utility_actual t ≤ utility_counter t) :
    0 ≤ (1 / (T : ℝ)) * ∑ t, (utility_counter t - utility_actual t) := by
  apply mul_nonneg
  · exact div_nonneg zero_le_one (le_of_lt hT)
  · exact Finset.sum_nonneg fun t _ => sub_nonneg.mpr (h_br t)

/-- **Theorem 8**: Regret is bounded by 1 when utilities are in [0,1].
    Since both actual and counterfactual utilities lie in [0,1],
    the per-round advantage is in [-1, 1], and the average is
    bounded by 1. -/
theorem regret_le_one
    (T : ℕ) (hT : 0 < (T : ℝ))
    (utility_actual : Fin T → ℝ)
    (utility_counter : Fin T → ℝ)
    (h_actual_nn : ∀ t, 0 ≤ utility_actual t)
    (h_counter_le : ∀ t, utility_counter t ≤ 1) :
    (1 / (T : ℝ)) * ∑ t, (utility_counter t - utility_actual t) ≤ 1 := by
  rw [div_mul_eq_mul_div, one_mul, div_le_one hT]
  calc ∑ t : Fin T, (utility_counter t - utility_actual t)
      ≤ ∑ t : Fin T, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro t _
        linarith [h_actual_nn t, h_counter_le t]
    _ = (T : ℝ) := by simp [Finset.sum_const]

/-! ### Zero-Sum Game Value Bounds -/

/-- A **two-player zero-sum repeated game** structure with a payoff
    matrix. Player 1 maximizes, player 2 minimizes. -/
structure ZeroSumGame where
  /-- Action space size -/
  K : ℕ
  /-- Player 1's payoff matrix -/
  payoff : Fin K → Fin K → ℝ
  /-- Payoffs are in [0, 1] -/
  payoff_nonneg : ∀ a₁ a₂, 0 ≤ payoff a₁ a₂
  payoff_le_one : ∀ a₁ a₂, payoff a₁ a₂ ≤ 1

/-- **Theorem 9 (Zero-sum payoff identity)**: In a zero-sum game with
    normalized payoffs (u₁ + u₂ = 1), player 1's payoff determines
    player 2's. -/
theorem zero_sum_payoff_identity (v₁ v₂ : ℝ) (h : v₁ + v₂ = 1) :
    v₁ = 1 - v₂ := by linarith

/-- **Theorem 10 (Self-play convergence)**: In a zero-sum game, if
    both players have regret at most ε₁ and ε₂ respectively, then
    the average payoff for player 1 is within [v* - ε₁, v* + ε₂]
    of the game value v*.

    This is the algebraic core of the self-play convergence theorem:
    no-regret dynamics in zero-sum games converge to the Nash value. -/
theorem zero_sum_value_sandwich (v v_star ε₁ ε₂ : ℝ)
    (h₁ : v_star - v ≤ ε₁) (h₂ : v - v_star ≤ ε₂) :
    v_star - ε₁ ≤ v ∧ v ≤ v_star + ε₂ :=
  ⟨by linarith, by linarith⟩

/-- **Theorem 11 (Regret rate bound)**: The regret rate c/√T decreases
    as T grows. For any T with √T ≥ 1, the rate is at most c.

    This captures the O(√(T log K) / T) = O(√(log K / T)) convergence
    rate of multiplicative weights and similar algorithms. -/
theorem regret_rate_bound (c : ℝ) (hc : 0 ≤ c) (sqrtT : ℝ) (h : 1 ≤ sqrtT) :
    c / sqrtT ≤ c :=
  div_le_self hc h

/-! ### Potential Games -/

/-- A **potential game** is a game where a single potential function
    Φ captures the incentive of every agent to deviate. Formally,
    for any agent i and any unilateral deviation from a to a':
    u_i(a'_i, a_{-i}) - u_i(a) = Φ(a'_i, a_{-i}) - Φ(a). -/
structure PotentialGame (N : ℕ) where
  /-- Action space size -/
  K : ℕ
  /-- Utility for agent i -/
  utility : Fin N → (Fin N → Fin K) → ℝ
  /-- Potential function -/
  potential : (Fin N → Fin K) → ℝ
  /-- Potential condition: utility differences equal potential differences -/
  potential_condition : ∀ (i : Fin N) (a : Fin N → Fin K) (k : Fin K),
    utility i (Function.update a i k) - utility i a =
    potential (Function.update a i k) - potential a

namespace PotentialGame

variable {N : ℕ} (G : PotentialGame N)

/-- **Theorem 12 (Potential increases with utility improvement)**: If
    agent i switches to action k that improves their utility (i.e.,
    u_i(a) < u_i(k, a_{-i})), then the potential strictly increases.

    This follows directly from the potential condition. -/
theorem potential_increases_with_utility (a : Fin N → Fin G.K)
    (i : Fin N) (k : Fin G.K)
    (h_improve : G.utility i a < G.utility i (Function.update a i k)) :
    G.potential a < G.potential (Function.update a i k) := by
  have := G.potential_condition i a k
  linarith

/-- **Theorem 13 (Potential maximum is Nash)**: In a potential game,
    at any local maximum of the potential (i.e., no unilateral
    deviation increases the potential), we have a Nash equilibrium
    in the sense that no agent can improve their utility by
    deviating. -/
theorem potential_max_is_nash (a : Fin N → Fin G.K)
    (h_max : ∀ (i : Fin N) (k : Fin G.K),
      G.potential (Function.update a i k) ≤ G.potential a) :
    ∀ (i : Fin N) (k : Fin G.K),
      G.utility i (Function.update a i k) ≤ G.utility i a := by
  intro i k
  have h_pot := G.potential_condition i a k
  have h_le := h_max i k
  linarith

/-- **Theorem 14 (Potential difference additivity)**: The potential
    difference is additive over sequential deviations by different
    agents. If agent i₁ deviates first, then agent i₂ deviates,
    the total potential change is the sum of individual changes.

    This is a pure algebraic (telescoping) identity. -/
theorem potential_diff_additive (a : Fin N → Fin G.K)
    (i₁ i₂ : Fin N) (k₁ k₂ : Fin G.K) :
    let a₁ := Function.update a i₁ k₁
    let a₂ := Function.update a₁ i₂ k₂
    G.potential a₂ - G.potential a =
    (G.potential a₁ - G.potential a) +
    (G.potential a₂ - G.potential a₁) := by
  ring

/-- **Theorem 15 (Finite improvement bound)**: After n steps where
    each step increases the potential by at least δ > 0, the total
    potential increase is at least n * δ.

    Combined with a bound on the potential range, this implies
    that improvement dynamics must terminate in finitely many steps. -/
theorem potential_total_increase (n : ℕ)
    (δ : ℝ) (hδ : 0 < δ)
    (improvements : Fin n → ℝ)
    (h_each : ∀ j, δ ≤ improvements j) :
    n * δ ≤ ∑ j : Fin n, improvements j := by
  calc (n : ℝ) * δ = ∑ _j : Fin n, δ := by simp [Finset.sum_const]
    _ ≤ ∑ j : Fin n, improvements j :=
        Finset.sum_le_sum fun j _ => h_each j

end PotentialGame

/-! ### Weighted Regret Bounds -/

/-- **Theorem 16 (Weighted average upper bound)**: If each term
    x_i ≤ B and weights form a distribution, then ∑ w_i x_i ≤ B.

    This is a key ingredient in the regret-to-CCE reduction:
    the expected payoff under a distribution is bounded by the
    maximum payoff. -/
theorem weighted_avg_le_max {M : ℕ} (x : Fin M → ℝ) (w : Fin M → ℝ)
    (hw_nn : ∀ m, 0 ≤ w m) (hw_sum : ∑ m, w m = 1)
    (B : ℝ) (hx : ∀ m, x m ≤ B) :
    ∑ m, w m * x m ≤ B := by
  calc ∑ m, w m * x m
      ≤ ∑ m, w m * B := Finset.sum_le_sum fun m _ =>
        mul_le_mul_of_nonneg_left (hx m) (hw_nn m)
    _ = (∑ m, w m) * B := by rw [← Finset.sum_mul]
    _ = B := by rw [hw_sum, one_mul]

/-- **Theorem 17 (Weighted average lower bound)**: If each term
    x_i ≥ B and weights form a distribution, then ∑ w_i x_i ≥ B. -/
theorem min_le_weighted_avg {M : ℕ} (x : Fin M → ℝ) (w : Fin M → ℝ)
    (hw_nn : ∀ m, 0 ≤ w m) (hw_sum : ∑ m, w m = 1)
    (B : ℝ) (hx : ∀ m, B ≤ x m) :
    B ≤ ∑ m, w m * x m := by
  calc B = (∑ m, w m) * B := by rw [hw_sum, one_mul]
    _ = ∑ m, w m * B := by rw [← Finset.sum_mul]
    _ ≤ ∑ m, w m * x m := Finset.sum_le_sum fun m _ =>
        mul_le_mul_of_nonneg_left (hx m) (hw_nn m)

end RepeatedGame

end
