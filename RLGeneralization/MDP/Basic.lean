/-
# Markov Decision Process: Basic Definitions

This file defines the core structure of a finite Markov Decision Process (MDP),
including states, actions, transition kernels, reward functions, policies,
and value functions.

## Main Definitions

* `FiniteMDP` - A finite MDP with states `S`, actions `A`, transition function,
  reward function, and discount factor.
* `Policy` - A (stationary, deterministic) policy mapping states to actions.
* `StochasticPolicy` - A stochastic policy mapping states to distributions over actions.
* `ValueFunction` - The state value function V^π.
* `ActionValueFunction` - The action value function Q^π.

## References

* [Puterman, *Markov Decision Processes*][puterman2014]
* [Sutton and Barto, *Reinforcement Learning: An Introduction*][sutton2018]
-/

import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset BigOperators

noncomputable section

/-! ### MDP Structure -/

/-- A finite Markov Decision Process. -/
structure FiniteMDP where
  /-- The state space (finite) -/
  S : Type
  /-- The action space (finite) -/
  A : Type
  [instFintypeS : Fintype S]
  [instFintypeA : Fintype A]
  [instDecEqS : DecidableEq S]
  [instDecEqA : DecidableEq A]
  [instNonemptyS : Nonempty S]
  [instNonemptyA : Nonempty A]
  /-- Transition probability: P(s'|s,a) -/
  P : S → A → S → ℝ
  /-- Reward function: r(s,a) -/
  r : S → A → ℝ
  /-- Discount factor γ ∈ [0,1) -/
  γ : ℝ
  /-- Transition probabilities are nonnegative -/
  P_nonneg : ∀ s a s', 0 ≤ P s a s'
  /-- Transition probabilities sum to 1 -/
  P_sum_one : ∀ s a, ∑ s', P s a s' = 1
  /-- Reward is bounded -/
  r_bound : ∃ R_max : ℝ, 0 < R_max ∧ ∀ s a, |r s a| ≤ R_max
  /-- Discount factor is in [0,1) -/
  γ_nonneg : 0 ≤ γ
  γ_lt_one : γ < 1

namespace FiniteMDP

variable (M : FiniteMDP)

-- Make the type class instances available
attribute [instance] FiniteMDP.instFintypeS FiniteMDP.instFintypeA
  FiniteMDP.instDecEqS FiniteMDP.instDecEqA
  FiniteMDP.instNonemptyS FiniteMDP.instNonemptyA

/-! ### Policies -/

/-- A deterministic stationary policy: maps states to actions. -/
def DetPolicy := M.S → M.A

/-- A stochastic stationary policy: maps (state, action) to probability of taking that action. -/
structure StochasticPolicy where
  /-- π(a|s): probability of action a in state s -/
  prob : M.S → M.A → ℝ
  /-- Probabilities are nonneg -/
  prob_nonneg : ∀ s a, 0 ≤ prob s a
  /-- Probabilities sum to 1 over actions -/
  prob_sum_one : ∀ s, ∑ a, prob s a = 1

/-! ### Value Functions -/

/-- The state value function V : S → ℝ -/
def StateValueFn := M.S → ℝ

/-- The action value function Q : S × A → ℝ -/
def ActionValueFn := M.S → M.A → ℝ

/-! ### Bellman Operators -/

/-- The expected next-state value under policy π from state s:
    ∑_a π(a|s) ∑_{s'} P(s'|s,a) V(s') -/
def expectedNextValue (π : M.StochasticPolicy) (V : M.StateValueFn) (s : M.S) : ℝ :=
  ∑ a, π.prob s a * ∑ s', M.P s a s' * V s'

/-- The expected immediate reward under policy π from state s:
    ∑_a π(a|s) r(s,a) -/
def expectedReward (π : M.StochasticPolicy) (s : M.S) : ℝ :=
  ∑ a, π.prob s a * M.r s a

/-- The Bellman evaluation operator T^π : V ↦ r^π + γ P^π V -/
def bellmanEvalOp (π : M.StochasticPolicy) (V : M.StateValueFn) : M.StateValueFn :=
  fun s => M.expectedReward π s + M.γ * M.expectedNextValue π V s

/-- The Bellman optimality operator T* : Q ↦ r + γ P max_a Q -/
def bellmanOptOp (Q : M.ActionValueFn) : M.ActionValueFn :=
  fun s a => M.r s a + M.γ * ∑ s', M.P s a s' *
    (Finset.univ.sup' Finset.univ_nonempty (fun a' => Q s' a'))

/-! ### Fixed Points and Optimal Values -/

/-- V is the value function of policy π if it satisfies the Bellman evaluation equation -/
def isValueOf (V : M.StateValueFn) (π : M.StochasticPolicy) : Prop :=
  ∀ s, V s = M.expectedReward π s + M.γ * M.expectedNextValue π V s

/-- Q is the action-value function of policy π if it satisfies the Bellman equation -/
def isActionValueOf (Q : M.ActionValueFn) (π : M.StochasticPolicy) : Prop :=
  ∀ s a, Q s a = M.r s a + M.γ * ∑ s', M.P s a s' * (∑ a', π.prob s' a' * Q s' a')

/-- Q* satisfies the Bellman optimality equation -/
def isBellmanOptimalQ (Q : M.ActionValueFn) : Prop :=
  ∀ s a, Q s a = M.r s a + M.γ * ∑ s', M.P s a s' *
    (Finset.univ.sup' Finset.univ_nonempty (fun a' => Q s' a'))

/-- V* satisfies the Bellman optimality equation -/
def isBellmanOptimalV (V : M.StateValueFn) : Prop :=
  ∀ s, V s = Finset.univ.sup' Finset.univ_nonempty
    (fun a => M.r s a + M.γ * ∑ s', M.P s a s' * V s')

/-! ### Maximum reward bound -/

/-- The maximum absolute reward -/
def R_max : ℝ := M.r_bound.choose

lemma R_max_pos : 0 < M.R_max := M.r_bound.choose_spec.1

lemma r_le_R_max (s : M.S) (a : M.A) : |M.r s a| ≤ M.R_max := M.r_bound.choose_spec.2 s a

/-- The maximum possible value: R_max / (1 - γ) -/
def V_max : ℝ := M.R_max / (1 - M.γ)

lemma V_max_pos : 0 < M.V_max := by
  unfold V_max
  apply div_pos M.R_max_pos
  linarith [M.γ_lt_one]

/-! ### Greedy Policy Construction -/

/-- The greedy action at state s w.r.t. Q-function Q:
    a*(s) = argmax_a Q(s,a).
    Uses `Finset.exists_max_image` for finite action spaces. -/
def greedyAction (Q : M.ActionValueFn) (s : M.S) : M.A :=
  (Finset.exists_max_image Finset.univ (Q s)
    Finset.univ_nonempty).choose

/-- The greedy action achieves the maximum Q-value. -/
theorem greedyAction_spec (Q : M.ActionValueFn) (s : M.S) :
    ∀ a, Q s a ≤ Q s (M.greedyAction Q s) := by
  intro a
  have := (Finset.exists_max_image Finset.univ (Q s)
    Finset.univ_nonempty).choose_spec
  exact this.2 a (Finset.mem_univ a)

/-- The greedy action's Q-value equals the sup. -/
theorem greedyAction_eq_sup (Q : M.ActionValueFn) (s : M.S) :
    Q s (M.greedyAction Q s) =
    Finset.univ.sup' Finset.univ_nonempty (Q s) := by
  apply le_antisymm
  · exact Finset.le_sup' (Q s) (Finset.mem_univ _)
  · exact Finset.sup'_le _ _ (fun a _ => M.greedyAction_spec Q s a)

end FiniteMDP

end
