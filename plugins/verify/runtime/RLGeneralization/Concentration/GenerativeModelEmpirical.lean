/-
# Generative Model: Empirical MDP Definitions

Defines the canonical empirical MDP, policy converters, and
greedy-side witnesses extracted from a generative-model sample point.

## Main Definitions

* `empiricalApproxMDPRV` — approximate MDP from a sample point
* `empiricalModelMDP` — full empirical MDP with sample transitions
* `toEmpiricalModelPolicy` / `ofEmpiricalModelPolicy` — policy converters
* `empiricalModelValueFromQ` — Q-to-V conversion on the empirical model
* `empiricalGreedyValue` — canonical true-model value of the empirical greedy policy

## References

* [Azar, Munos, Kappen, *Minimax PAC bounds on the sample complexity
  of RL with a generative model*][azar2013]
-/

import RLGeneralization.Concentration.GenerativeModelCore
import RLGeneralization.MDP.BanachFixedPoint
import RLGeneralization.MDP.PolicyIteration

open Finset BigOperators MeasureTheory ProbabilityTheory ENNReal

noncomputable section

namespace FiniteMDP

variable (M : FiniteMDP)

/-- The canonical empirical approximate MDP extracted from a generative-model
    sample point, using the empirical transition kernel and the true reward. -/
def empiricalApproxMDPRV {N : ℕ} (hN : 0 < N)
    (ω : M.SampleIndex N → M.S) : M.ApproxMDP where
  P_hat := M.empiricalTransitionRV hN ω
  r_hat := M.r
  P_hat_nonneg := M.empiricalTransitionRV_nonneg hN ω
  P_hat_sum_one := M.empiricalTransitionRV_sum_one hN ω

/-- The empirical sample point viewed as an actual finite MDP with the empirical
    transition kernel and the true reward function. -/
def empiricalModelMDP {N : ℕ} (hN : 0 < N)
    (ω : M.SampleIndex N → M.S) : FiniteMDP where
  S := M.S
  A := M.A
  P := M.empiricalTransitionRV hN ω
  r := M.r
  γ := M.γ
  P_nonneg := M.empiricalTransitionRV_nonneg hN ω
  P_sum_one := M.empiricalTransitionRV_sum_one hN ω
  r_bound := M.r_bound
  γ_nonneg := M.γ_nonneg
  γ_lt_one := M.γ_lt_one

/-- Reuse a policy on the true MDP as a policy on the empirical-model MDP
    extracted from a sample point. -/
def toEmpiricalModelPolicy {N : ℕ} (hN : 0 < N)
    (ω : M.SampleIndex N → M.S) (π : M.StochasticPolicy) :
    (M.empiricalModelMDP hN ω).StochasticPolicy where
  prob := π.prob
  prob_nonneg := π.prob_nonneg
  prob_sum_one := π.prob_sum_one

/-- Forget a policy on the empirical-model MDP back to the underlying policy on
    the true state-action space. -/
def ofEmpiricalModelPolicy {N : ℕ} (hN : 0 < N)
    (ω : M.SampleIndex N → M.S)
    (π : (M.empiricalModelMDP hN ω).StochasticPolicy) : M.StochasticPolicy where
  prob := π.prob
  prob_nonneg := π.prob_nonneg
  prob_sum_one := π.prob_sum_one

/-- The greedy policy induced by the canonical Bellman-optimal fixed point of
    the empirical model. -/
def empiricalOptimalPolicy {N : ℕ} (hN : 0 < N)
    (ω : M.SampleIndex N → M.S) :
    (M.empiricalModelMDP hN ω).StochasticPolicy :=
  (M.empiricalModelMDP hN ω).greedyStochasticPolicy
    ((M.empiricalModelMDP hN ω).optimalQFixedPoint)

/-- The empirical-model greedy policy viewed back on the original MDP state and
    action space. -/
def empiricalGreedyPolicy {N : ℕ} (hN : 0 < N)
    (ω : M.SampleIndex N → M.S) : M.StochasticPolicy :=
  M.ofEmpiricalModelPolicy hN ω (M.empiricalOptimalPolicy hN ω)

/-- The state-value function induced by an empirical-model action-value function
    under a fixed policy, expressed on the original state space. -/
def empiricalModelValueFromQ {N : ℕ} (hN : 0 < N)
    (ω : M.SampleIndex N → M.S)
    (π : M.StochasticPolicy)
    (Q : (M.empiricalModelMDP hN ω).ActionValueFn) : M.StateValueFn :=
  fun s => ∑ a, π.prob s a * Q s a

/-- If `Q` is an action-value fixed point for policy `π` in the empirical model,
    then the policy-weighted action values satisfy the empirical Bellman equation. -/
theorem empiricalModelValueFromQ_isValueOf {N : ℕ} (hN : 0 < N)
    (ω : M.SampleIndex N → M.S)
    (π : M.StochasticPolicy)
    (Q : (M.empiricalModelMDP hN ω).ActionValueFn)
    (hQ :
      (M.empiricalModelMDP hN ω).isActionValueOf Q
        (M.toEmpiricalModelPolicy hN ω π)) :
    (M.empiricalModelMDP hN ω).isValueOf
      (M.empiricalModelValueFromQ hN ω π Q)
      (M.toEmpiricalModelPolicy hN ω π) := by
  intro s
  dsimp [FiniteMDP.isValueOf, empiricalModelValueFromQ,
    FiniteMDP.expectedReward, FiniteMDP.expectedNextValue]
  calc
    ∑ a, π.prob s a * Q s a
      = ∑ a, π.prob s a *
          ((M.empiricalModelMDP hN ω).r s a +
            (M.empiricalModelMDP hN ω).γ * ∑ s',
              (M.empiricalModelMDP hN ω).P s a s' *
                (∑ a', (M.toEmpiricalModelPolicy hN ω π).prob s' a' * Q s' a')) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [hQ s a]
    _ = (∑ a, π.prob s a * (M.empiricalModelMDP hN ω).r s a) +
        (M.empiricalModelMDP hN ω).γ *
          (∑ a, π.prob s a *
            ∑ s', (M.empiricalModelMDP hN ω).P s a s' *
              (∑ a', (M.toEmpiricalModelPolicy hN ω π).prob s' a' * Q s' a')) := by
          simp_rw [mul_add, Finset.sum_add_distrib]
          congr 1
          have hγ :
              ∀ a, π.prob s a *
                ((M.empiricalModelMDP hN ω).γ *
                  ∑ s', (M.empiricalModelMDP hN ω).P s a s' *
                    (∑ a', (M.toEmpiricalModelPolicy hN ω π).prob s' a' * Q s' a')) =
                (M.empiricalModelMDP hN ω).γ *
                  (π.prob s a *
                    ∑ s', (M.empiricalModelMDP hN ω).P s a s' *
                      (∑ a', (M.toEmpiricalModelPolicy hN ω π).prob s' a' * Q s' a')) := by
            intro a
            ring
          simp_rw [hγ]
          exact (Finset.mul_sum _ _ _).symm
    _ = (∑ a, (M.toEmpiricalModelPolicy hN ω π).prob s a *
            (M.empiricalModelMDP hN ω).r s a) +
        (M.empiricalModelMDP hN ω).γ *
          (∑ a, (M.toEmpiricalModelPolicy hN ω π).prob s a *
            ∑ s', (M.empiricalModelMDP hN ω).P s a s' *
              (M.empiricalModelValueFromQ hN ω π Q) s') := by
          change
            (∑ a, π.prob s a * (M.empiricalModelMDP hN ω).r s a) +
              (M.empiricalModelMDP hN ω).γ *
                (∑ a, π.prob s a *
                  ∑ s', (M.empiricalModelMDP hN ω).P s a s' *
                    (∑ a', π.prob s' a' * Q s' a')) =
            (∑ a, π.prob s a * (M.empiricalModelMDP hN ω).r s a) +
              (M.empiricalModelMDP hN ω).γ *
                (∑ a, π.prob s a *
                  ∑ s', (M.empiricalModelMDP hN ω).P s a s' *
                    (∑ a', π.prob s' a' * Q s' a'))
          rfl

/-- The canonical true-model value function of the empirical greedy policy,
    obtained by Banach policy evaluation on the original MDP. -/
def empiricalGreedyValue {N : ℕ} (hN : 0 < N)
    (ω : M.SampleIndex N → M.S) : M.StateValueFn :=
  M.valueFromQ (M.empiricalGreedyPolicy hN ω)
    (M.actionValueFixedPoint (M.empiricalGreedyPolicy hN ω))

/-- The canonical true-model value associated with the empirical greedy policy
    satisfies the Bellman evaluation equation on the original MDP. -/
theorem empiricalGreedyValue_isValueOf {N : ℕ} (hN : 0 < N)
    (ω : M.SampleIndex N → M.S) :
    M.isValueOf (M.empiricalGreedyValue hN ω) (M.empiricalGreedyPolicy hN ω) := by
  exact M.valueFromQ_isValueOf (M.empiricalGreedyPolicy hN ω)
    (M.actionValueFixedPoint (M.empiricalGreedyPolicy hN ω))
    (M.actionValueFixedPoint_isActionValueOf (M.empiricalGreedyPolicy hN ω))

end FiniteMDP

end
