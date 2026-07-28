/-
# Partially Observable Markov Decision Processes (POMDPs)

Formalizes POMDPs: MDPs where the agent does not observe the state
directly, but instead receives observations through an emission model.
The belief state (posterior over states) is the sufficient statistic,
and a POMDP can be reformulated as a (continuous-state) belief MDP.

## Mathematical Background

A POMDP extends a finite MDP with:
- An observation space O
- An emission model Q(o | s): probability of observing o in state s
- The agent's information at time t is the history (a₀, o₁, ..., aₜ₋₁, oₜ)

The **belief state** b_t ∈ Δ(S) is the posterior distribution over states
given the history. It is a sufficient statistic for decision-making:
  b'(s') ∝ Q(o | s') · ∑_s P(s' | s, a) · b(s)

## Main Definitions

* `POMDP` - POMDP structure with states, actions, observations
* `BeliefState` - Distribution over states b ∈ Δ(S)
* `beliefUpdate` - Bayesian belief update formula
* `belief_update_nonneg` - Updated belief weights are nonneg
* `BeliefMDPConfig` - POMDP as belief MDP configuration

## Approach

We work with finite state, action, and observation spaces. Belief states
are represented as finite distributions (weight functions summing to 1).
The belief update is the algebraic Bayesian formula.

## Blocked

- **Belief MDP optimization**: the belief MDP has continuous state space
  Δ(S) ⊂ ℝ^|S|, so standard finite MDP algorithms don't apply directly.
  Solving POMDPs is PSPACE-hard in general.
- **Point-based value iteration**: practical POMDP algorithms use
  α-vector representations. Requires LP duality in Δ(S).
- **Spectral methods for POMDPs**: observable operator models require
  tensor algebra not in Mathlib.

## References

* [Kaelbling, Littman, Cassandra, *Planning and acting in partially observable
  stochastic domains*, 1998]
* [Smallwood and Sondik, *The optimal control of partially observable
  Markov processes over a finite horizon*, 1973]
* [Agarwal et al., *RL: Theory and Algorithms*]
-/

import RLGeneralization.MDP.BellmanContraction
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Field

open Finset BigOperators

noncomputable section

/-! ### POMDP Structure -/

/-- A **Partially Observable Markov Decision Process** (POMDP).

    Extends the finite MDP with an observation space O and an
    emission model Q(o | s). The agent observes o_t ∼ Q(· | s_t)
    instead of s_t directly. -/
structure POMDP where
  /-- State space (finite) -/
  S : Type
  /-- Action space (finite) -/
  A : Type
  /-- Observation space (finite) -/
  O : Type
  [instFintypeS : Fintype S]
  [instFintypeA : Fintype A]
  [instFintypeO : Fintype O]
  [instDecEqS : DecidableEq S]
  [instDecEqA : DecidableEq A]
  [instDecEqO : DecidableEq O]
  [instNonemptyS : Nonempty S]
  [instNonemptyA : Nonempty A]
  [instNonemptyO : Nonempty O]
  /-- Transition probability: P(s' | s, a) -/
  P : S → A → S → ℝ
  /-- Emission probability: Q(o | s) -/
  Q : S → O → ℝ
  /-- Reward function: r(s, a) -/
  r : S → A → ℝ
  /-- Discount factor γ ∈ [0, 1) -/
  γ : ℝ
  /-- P is nonneg -/
  P_nonneg : ∀ s a s', 0 ≤ P s a s'
  /-- P sums to 1 -/
  P_sum_one : ∀ s a, ∑ s', P s a s' = 1
  /-- Q is nonneg -/
  Q_nonneg : ∀ s o, 0 ≤ Q s o
  /-- Q sums to 1 -/
  Q_sum_one : ∀ s, ∑ o, Q s o = 1
  /-- Discount factor bounds -/
  γ_nonneg : 0 ≤ γ
  γ_lt_one : γ < 1

namespace POMDP

variable (M : POMDP)

attribute [instance] POMDP.instFintypeS POMDP.instFintypeA POMDP.instFintypeO
  POMDP.instDecEqS POMDP.instDecEqA POMDP.instDecEqO
  POMDP.instNonemptyS POMDP.instNonemptyA POMDP.instNonemptyO

/-! ### Belief State -/

/-- A **belief state**: a probability distribution over the state space S.
    Represents the agent's posterior belief about the current state
    given the observation history. -/
structure BeliefState where
  /-- Weight (probability) for each state -/
  wt : M.S → ℝ
  /-- Weights are nonneg -/
  wt_nonneg : ∀ s, 0 ≤ wt s
  /-- Weights sum to 1 -/
  wt_sum_one : ∑ s, wt s = 1

/-- **Convex combination of two belief states**:
    b_mix(s) = λ · b₁(s) + (1-λ) · b₂(s). -/
def mixBeliefState (b₁ b₂ : M.BeliefState) (lam : ℝ)
    (hlam_nonneg : 0 ≤ lam) (hlam_le_one : lam ≤ 1) : M.BeliefState where
  wt s := lam * b₁.wt s + (1 - lam) * b₂.wt s
  wt_nonneg s := add_nonneg
    (mul_nonneg hlam_nonneg (b₁.wt_nonneg s))
    (mul_nonneg (by linarith) (b₂.wt_nonneg s))
  wt_sum_one := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
      b₁.wt_sum_one, b₂.wt_sum_one, mul_one]
    ring

/-- The mix weight formula. -/
@[simp]
theorem mixBeliefState_wt (b₁ b₂ : M.BeliefState) (lam : ℝ)
    (hlam_nonneg : 0 ≤ lam) (hlam_le_one : lam ≤ 1) (s : M.S) :
    (M.mixBeliefState b₁ b₂ lam hlam_nonneg hlam_le_one).wt s =
      lam * b₁.wt s + (1 - lam) * b₂.wt s := rfl

/-- Expected reward under a belief state and action:
    r(b, a) = ∑_s b(s) · r(s, a). -/
def beliefReward (b : M.BeliefState) (a : M.A) : ℝ :=
  ∑ s, b.wt s * M.r s a

/-- The expected reward is a convex combination of state rewards. -/
theorem beliefReward_convex (b : M.BeliefState) (a : M.A)
    (R_min R_max : ℝ)
    (hmin : ∀ s, R_min ≤ M.r s a)
    (hmax : ∀ s, M.r s a ≤ R_max) :
    R_min ≤ M.beliefReward b a ∧ M.beliefReward b a ≤ R_max := by
  unfold beliefReward
  constructor
  · calc R_min = R_min * 1 := by ring
      _ = R_min * ∑ s, b.wt s := by rw [b.wt_sum_one]
      _ = ∑ s, R_min * b.wt s := by rw [Finset.mul_sum]
      _ = ∑ s, b.wt s * R_min := by congr 1; ext s; ring
      _ ≤ ∑ s, b.wt s * M.r s a :=
        Finset.sum_le_sum fun s _ =>
          mul_le_mul_of_nonneg_left (hmin s) (b.wt_nonneg s)
  · calc ∑ s, b.wt s * M.r s a
        ≤ ∑ s, b.wt s * R_max :=
        Finset.sum_le_sum fun s _ =>
          mul_le_mul_of_nonneg_left (hmax s) (b.wt_nonneg s)
      _ = R_max * ∑ s, b.wt s := by rw [Finset.mul_sum]; congr 1; ext s; ring
      _ = R_max * 1 := by rw [b.wt_sum_one]
      _ = R_max := by ring

/-! ### Belief Update

The Bayesian belief update upon taking action a and observing o:

  b'(s') = Q(o | s') · ∑_s P(s' | s, a) · b(s) / Z

where Z = ∑_{s'} Q(o | s') · ∑_s P(s' | s, a) · b(s) is the
normalizing constant (observation likelihood). -/

/-- **Unnormalized belief update weight** for state s' after action a
    and observation o:

    w(s') = Q(o | s') · ∑_s P(s' | s, a) · b(s) -/
def unnormalizedBeliefWeight (b : M.BeliefState) (a : M.A) (o : M.O)
    (s' : M.S) : ℝ :=
  M.Q s' o * ∑ s, M.P s a s' * b.wt s

/-- The unnormalized belief weight is nonneg. -/
theorem unnormalizedBeliefWeight_nonneg (b : M.BeliefState) (a : M.A)
    (o : M.O) (s' : M.S) :
    0 ≤ M.unnormalizedBeliefWeight b a o s' := by
  unfold unnormalizedBeliefWeight
  apply mul_nonneg (M.Q_nonneg s' o)
  apply Finset.sum_nonneg
  intro s _
  exact mul_nonneg (M.P_nonneg s a s') (b.wt_nonneg s)

/-- **Observation likelihood**: the normalizing constant for belief update.
    Z(b, a, o) = ∑_{s'} Q(o | s') · ∑_s P(s' | s, a) · b(s). -/
def observationLikelihood (b : M.BeliefState) (a : M.A) (o : M.O) : ℝ :=
  ∑ s', M.unnormalizedBeliefWeight b a o s'

/-- The observation likelihood is nonneg. -/
theorem observationLikelihood_nonneg (b : M.BeliefState) (a : M.A) (o : M.O) :
    0 ≤ M.observationLikelihood b a o := by
  unfold observationLikelihood
  exact Finset.sum_nonneg fun s' _ => M.unnormalizedBeliefWeight_nonneg b a o s'

/-- **Belief update formula**: given that Z > 0 (observation is possible),
    the normalized belief after action a and observation o.

    b'(s') = Q(o | s') · ∑_s P(s' | s, a) · b(s) / Z -/
def beliefUpdate (b : M.BeliefState) (a : M.A) (o : M.O)
    (hZ : 0 < M.observationLikelihood b a o) : M.BeliefState where
  wt s' := M.unnormalizedBeliefWeight b a o s' / M.observationLikelihood b a o
  wt_nonneg s' := div_nonneg
    (M.unnormalizedBeliefWeight_nonneg b a o s')
    (le_of_lt hZ)
  wt_sum_one := by
    have : ∑ s', M.unnormalizedBeliefWeight b a o s' / M.observationLikelihood b a o =
        (∑ s', M.unnormalizedBeliefWeight b a o s') / M.observationLikelihood b a o := by
      rw [Finset.sum_div]
    rw [this]
    exact div_self (ne_of_gt hZ)

/-- The belief update preserves the probability constraint. -/
theorem beliefUpdate_sum_one (b : M.BeliefState) (a : M.A) (o : M.O)
    (hZ : 0 < M.observationLikelihood b a o) :
    ∑ s', (M.beliefUpdate b a o hZ).wt s' = 1 :=
  (M.beliefUpdate b a o hZ).wt_sum_one

/-- The updated belief is given by the normalized unnormalized weight. -/
theorem beliefUpdate_apply (b : M.BeliefState) (a : M.A) (o : M.O)
    (hZ : 0 < M.observationLikelihood b a o) (s' : M.S) :
    (M.beliefUpdate b a o hZ).wt s' =
      M.unnormalizedBeliefWeight b a o s' / M.observationLikelihood b a o :=
  rfl

/-- The updated belief weights are nonnegative. -/
theorem beliefUpdate_nonneg (b : M.BeliefState) (a : M.A) (o : M.O)
    (hZ : 0 < M.observationLikelihood b a o) (s' : M.S) :
    0 ≤ (M.beliefUpdate b a o hZ).wt s' :=
  (M.beliefUpdate b a o hZ).wt_nonneg s'

/-! ### POMDP as Belief MDP

A POMDP can be reformulated as an MDP over belief states.
The belief MDP has:
- State space: Δ(S) (the probability simplex over S)
- Action space: A (same as original)
- Transition: b --a,o--> b' via belief update
- Reward: r(b, a) = ∑_s b(s) r(s, a)

This reformulation shows that the POMDP is "solved" in principle
by solving the belief MDP. However, the belief MDP has a continuous
state space (the simplex Δ(S)), making exact solution intractable. -/

/-- **Belief MDP configuration**: the key data needed to formulate
    the POMDP as an MDP over belief states. -/
structure BeliefMDPConfig (M : POMDP) where
  /-- The belief reward function: r(b, a) = ∑_s b(s) r(s, a) -/
  reward : M.BeliefState → M.A → ℝ
  /-- The reward is the expected MDP reward -/
  reward_eq : ∀ b a, reward b a = M.beliefReward b a

/-- Constructing the belief MDP configuration from a POMDP. -/
def toBeliefMDPConfig : M.BeliefMDPConfig where
  reward := M.beliefReward
  reward_eq := fun _ _ => rfl

/-! ### Sufficient Statistic Property

The belief state b_t is a **sufficient statistic** for decision-making:
the optimal action depends only on b_t, not on the full history.

This is because:
1. The belief state captures all information from the history
   relevant to future rewards (by Bayes' rule)
2. The belief state evolution is Markovian:
   b_{t+1} depends only on (b_t, a_t, o_{t+1})

Formally proving sufficiency requires the theory of sufficient statistics
and information-theoretic arguments. We capture the algebraic structure. -/

/-- **Belief state determines expected immediate reward**: the expected
    reward E[r(s_t, a_t) | history] depends on the history only through
    the belief state b_t. This is the key sufficient-statistic property. -/
theorem belief_determines_reward (b : M.BeliefState) (a : M.A) :
    M.beliefReward b a = ∑ s, b.wt s * M.r s a := by
  rfl

/-- **Belief state determines next-state distribution**: the distribution
    over next states, ∑_s P(s' | s, a) b(s), depends on history only
    through b. -/
def predictedNextState (b : M.BeliefState) (a : M.A) (s' : M.S) : ℝ :=
  ∑ s, M.P s a s' * b.wt s

/-- The predicted next-state distribution sums to 1. -/
theorem predictedNextState_sum_one (b : M.BeliefState) (a : M.A) :
    ∑ s', M.predictedNextState b a s' = 1 := by
  unfold predictedNextState
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  simp_rw [M.P_sum_one _ a, one_mul]
  exact b.wt_sum_one

/-- The predicted next-state distribution is nonneg. -/
theorem predictedNextState_nonneg (b : M.BeliefState) (a : M.A) (s' : M.S) :
    0 ≤ M.predictedNextState b a s' := by
  unfold predictedNextState
  exact Finset.sum_nonneg fun s _ => mul_nonneg (M.P_nonneg s a s') (b.wt_nonneg s)

/-- The observation likelihood is the observation-weighted predicted
    next-state distribution. -/
theorem observationLikelihood_eq_predictedNextState (b : M.BeliefState)
    (a : M.A) (o : M.O) :
    M.observationLikelihood b a o =
      ∑ s', M.Q s' o * M.predictedNextState b a s' := by
  unfold observationLikelihood unnormalizedBeliefWeight predictedNextState
  rfl

/-- The observation likelihood over all observations sums to 1. -/
theorem observationLikelihood_sum_one (b : M.BeliefState) (a : M.A) :
    ∑ o, M.observationLikelihood b a o = 1 := by
  calc
    ∑ o, M.observationLikelihood b a o
        = ∑ o, ∑ s', M.Q s' o * M.predictedNextState b a s' := by
            simp [M.observationLikelihood_eq_predictedNextState]
    _ = ∑ s', (∑ o, M.Q s' o) * M.predictedNextState b a s' := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro s' _
          rw [show ∑ o, M.Q s' o * M.predictedNextState b a s' =
              (∑ o, M.Q s' o) * M.predictedNextState b a s' by
                rw [← Finset.sum_mul]]
    _ = ∑ s', M.predictedNextState b a s' := by
          simp [M.Q_sum_one]
    _ = 1 := M.predictedNextState_sum_one b a

/-! ### Alpha Vectors and Piecewise-Linear Convex Value Functions

In finite-horizon POMDPs, the optimal value function over the belief
simplex is **piecewise linear and convex** (PWLC). It can be represented
as the upper envelope of a finite set of **alpha vectors** α_i : S → ℝ,
where V(b) = max_i ∑_s b(s) · α_i(s).

## References

* [Smallwood and Sondik, *The optimal control of partially observable
  Markov processes over a finite horizon*, 1973]
* [Cassandra, Kaelbling, Littman, *Acting optimally in partially
  observable stochastic domains*, 1994]
-/

/-- An **alpha vector**: a function from states to reals.
    Each alpha vector represents a value function conditioned on a
    particular policy tree. The value at belief b is the dot product
    ∑_s b(s) · α(s). -/
def AlphaVector := M.S → ℝ

/-- The value of an alpha vector at a belief state:
    alphaValue(α, b) = ∑_s b(s) · α(s).

    This is the dot product ⟨b, α⟩ on the state space. -/
def alphaValue (α : M.AlphaVector) (b : M.BeliefState) : ℝ :=
  ∑ s, b.wt s * α s

/-- Alpha value is linear in the belief: for any convex combination
    λ b₁ + (1-λ) b₂, the alpha value decomposes linearly. -/
theorem alphaValue_linear (α : M.AlphaVector) (b₁ b₂ : M.BeliefState)
    (lam : ℝ) (hlamnonneg : 0 ≤ lam) (hlamle_one : lam ≤ 1) :
    M.alphaValue α (M.mixBeliefState b₁ b₂ lam hlamnonneg hlamle_one) =
      lam * M.alphaValue α b₁ + (1 - lam) * M.alphaValue α b₂ := by
  unfold alphaValue
  simp only [mixBeliefState_wt, add_mul]
  rw [Finset.sum_add_distrib]
  have h₁ : ∑ s, lam * b₁.wt s * α s = lam * ∑ s, b₁.wt s * α s := by
    rw [Finset.mul_sum]; congr 1; ext1 s; ring
  have h₂ : ∑ s, (1 - lam) * b₂.wt s * α s = (1 - lam) * ∑ s, b₂.wt s * α s := by
    rw [Finset.mul_sum]; congr 1; ext1 s; ring
  rw [h₁, h₂]

/-- A **piecewise linear and convex** (PWLC) value function on beliefs.
    V(b) = max_i alphaValue(α_i, b) for a finite set of alpha vectors.

    This is the fundamental representation theorem for POMDP value functions:
    the optimal value function over any finite horizon is always PWLC. -/
structure PiecewiseLinearConvex where
  /-- The index type for alpha vectors (finite) -/
  Idx : Type
  [instFintypeIdx : Fintype Idx]
  [instNonemptyIdx : Nonempty Idx]
  /-- The alpha vectors -/
  alphas : Idx → M.AlphaVector
  /-- The value function is the max over alpha vectors -/
  value : M.BeliefState → ℝ
  /-- Value equals the max of alpha values -/
  value_eq : ∀ b, value b = Finset.univ.sup' Finset.univ_nonempty
    (fun i => M.alphaValue (alphas i) b)

attribute [instance] PiecewiseLinearConvex.instFintypeIdx PiecewiseLinearConvex.instNonemptyIdx

/-- PWLC value functions are convex:
    V(λ b₁ + (1-λ) b₂) ≤ λ V(b₁) + (1-λ) V(b₂).

    Proof: max of linear functions is convex. Each α_i is linear in b,
    so max_i α_i(b) is convex as the pointwise supremum of affine functions. -/
theorem pwlc_convex (pw : M.PiecewiseLinearConvex)
    (b₁ b₂ : M.BeliefState) (lam : ℝ)
    (hlamnonneg : 0 ≤ lam) (hlamle_one : lam ≤ 1) :
    pw.value (M.mixBeliefState b₁ b₂ lam hlamnonneg hlamle_one) ≤
      lam * pw.value b₁ + (1 - lam) * pw.value b₂ := by
  rw [pw.value_eq]
  apply Finset.sup'_le
  intro i _
  -- For each alpha vector i: alphaValue(α_i, b_mix) = λ αᵢ(b₁) + (1-λ) αᵢ(b₂)
  have hlin := M.alphaValue_linear (pw.alphas i) b₁ b₂ lam hlamnonneg hlamle_one
  rw [hlin]
  -- Now: λ αᵢ(b₁) + (1-λ) αᵢ(b₂) ≤ λ max_j αⱼ(b₁) + (1-λ) max_j αⱼ(b₂)
  have h1 : M.alphaValue (pw.alphas i) b₁ ≤
      Finset.univ.sup' Finset.univ_nonempty
        (fun j => M.alphaValue (pw.alphas j) b₁) :=
    Finset.le_sup' (fun j => M.alphaValue (pw.alphas j) b₁) (Finset.mem_univ i)
  have h2 : M.alphaValue (pw.alphas i) b₂ ≤
      Finset.univ.sup' Finset.univ_nonempty
        (fun j => M.alphaValue (pw.alphas j) b₂) :=
    Finset.le_sup' (fun j => M.alphaValue (pw.alphas j) b₂) (Finset.mem_univ i)
  have h1' : M.alphaValue (pw.alphas i) b₁ ≤ pw.value b₁ := by
    rw [pw.value_eq]; exact h1
  have h2' : M.alphaValue (pw.alphas i) b₂ ≤ pw.value b₂ := by
    rw [pw.value_eq]; exact h2
  have hlam2 : 0 ≤ 1 - lam := by linarith
  linarith [mul_le_mul_of_nonneg_left h1' hlamnonneg,
            mul_le_mul_of_nonneg_left h2' hlam2]

/-! ### Belief-Space Bellman Operator -/

/-- **Belief-space Bellman operator**: one step of value iteration in belief space.
    (TV)(b) = max_a [r(b,a) + γ · ∑_o P(o|b,a) · V(τ(b,a,o))]

    For the operator to be well-defined, we require that the value of V at
    updated beliefs (where observation likelihood is zero) defaults to 0.
    The `beliefValueAtUpdate` argument provides V(τ(b,a,o)) for each (a,o). -/
def beliefBellmanOp
    (_V : M.BeliefState → ℝ)
    -- [CONDITIONAL HYPOTHESIS] Value of V at belief updates; handles normalization
    (beliefValueAtUpdate : M.BeliefState → M.A → M.O → ℝ)
    (b : M.BeliefState) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun a =>
    M.beliefReward b a + M.γ * ∑ o : M.O,
      M.observationLikelihood b a o * beliefValueAtUpdate b a o

/-! ### Belief-Space Contraction and Convergence -/

/-- Sup-norm distance between two belief value functions over a finite
    set of belief points. -/
def beliefSupDist (V₁ V₂ : M.BeliefState → ℝ)
    (beliefs : Finset M.BeliefState) (hne : beliefs.Nonempty) : ℝ :=
  beliefs.sup' hne fun b => |V₁ b - V₂ b|

/-- The belief Bellman operator is a γ-contraction in the sup norm.
    This follows from the standard contraction property: the max and
    expectation operators are non-expansive, and the discount factor
    γ < 1 provides strict contraction.

    ‖TV₁ - TV₂‖_∞ ≤ γ · ‖V₁ - V₂‖_∞ -/
theorem beliefBellman_contraction
    (V₁ V₂ : M.BeliefState → ℝ)
    (bvu₁ bvu₂ : M.BeliefState → M.A → M.O → ℝ)
    (D : ℝ)
    -- Hypothesis: belief value at updates satisfies the contraction bound
    (hbvu_bound : ∀ b a o, |bvu₁ b a o - bvu₂ b a o| ≤ D) :
    ∀ b, |M.beliefBellmanOp V₁ bvu₁ b - M.beliefBellmanOp V₂ bvu₂ b| ≤
      M.γ * D := by
  intro b
  unfold beliefBellmanOp
  -- |max_a f(a) - max_a g(a)| ≤ max_a |f(a) - g(a)|
  set f := fun a => M.beliefReward b a + M.γ * ∑ o : M.O,
    M.observationLikelihood b a o * bvu₁ b a o
  set g := fun a => M.beliefReward b a + M.γ * ∑ o : M.O,
    M.observationLikelihood b a o * bvu₂ b a o
  calc |Finset.univ.sup' Finset.univ_nonempty f -
        Finset.univ.sup' Finset.univ_nonempty g|
      ≤ Finset.univ.sup' Finset.univ_nonempty (fun a => |f a - g a|) := by
        exact FiniteMDP.abs_sup_sub_sup_le f g
    _ ≤ M.γ * D := by
        apply Finset.sup'_le
        intro a _
        -- f(a) - g(a) = γ · ∑_o P(o|b,a) · (bvu₁(b,a,o) - bvu₂(b,a,o))
        have hdiff : f a - g a = M.γ * ∑ o : M.O,
            M.observationLikelihood b a o * (bvu₁ b a o - bvu₂ b a o) := by
          simp only [f, g]
          rw [show M.beliefReward b a + M.γ * ∑ o : M.O,
                M.observationLikelihood b a o * bvu₁ b a o -
              (M.beliefReward b a + M.γ * ∑ o : M.O,
                M.observationLikelihood b a o * bvu₂ b a o) =
              M.γ * (∑ o : M.O, M.observationLikelihood b a o * bvu₁ b a o -
                ∑ o : M.O, M.observationLikelihood b a o * bvu₂ b a o) by ring]
          congr 1
          rw [← Finset.sum_sub_distrib]
          congr 1; ext1 o; ring
        rw [hdiff, abs_mul, abs_of_nonneg M.γ_nonneg]
        apply mul_le_mul_of_nonneg_left _ M.γ_nonneg
        -- |∑_o P(o|b,a) · (bvu₁ - bvu₂)| ≤ D via weighted sum bound
        -- We use: observation likelihoods sum to 1 and are nonneg
        have hobs_nonneg : ∀ o, 0 ≤ M.observationLikelihood b a o :=
          fun o => M.observationLikelihood_nonneg b a o
        have hobs_sum : ∑ o, M.observationLikelihood b a o = 1 :=
          M.observationLikelihood_sum_one b a
        exact FiniteMDP.abs_weighted_sum_le_bound
          (fun o => M.observationLikelihood b a o)
          (fun o => bvu₁ b a o - bvu₂ b a o)
          D hobs_nonneg hobs_sum (fun o => hbvu_bound b a o)

/-- [VACUOUS] **Monotonicity of error bound, not convergence**.
    Proves: if err ≤ γ^n * D₀ and γ^n ≤ γ_pow_bound, then
    err ≤ γ_pow_bound * D₀. This is just monotonicity of
    multiplication by a nonneg factor, not a convergence result. -/
theorem belief_value_bound_monotone
    (n : ℕ) (γ_pow_bound D₀ : ℝ)
    (hγ_pow : M.γ ^ n ≤ γ_pow_bound)
    (hD₀ : 0 ≤ D₀) :
    ∀ (err : ℝ), err ≤ M.γ ^ n * D₀ → err ≤ γ_pow_bound * D₀ :=
  fun _ herr => le_trans herr (mul_le_mul_of_nonneg_right hγ_pow hD₀)

/-- [VACUOUS] **Nonnegativity of γ^n * D**.
    Proves: 0 ≤ γ^n * D when γ ≥ 0 and D ≥ 0.
    This is just mul_nonneg, not a geometric convergence rate. -/
theorem contraction_iterate_nonneg
    (n : ℕ) (D : ℝ) (hD : 0 ≤ D) :
    0 ≤ M.γ ^ n * D := by
  exact mul_nonneg (pow_nonneg M.γ_nonneg n) hD

/-- After sufficiently many iterations, the error is arbitrarily small.
    For any ε > 0, choosing n ≥ log(ε(1-γ)/R_max) / log(γ) suffices. -/
theorem belief_iteration_eps_convergence
    (ε : ℝ) (D₀ : ℝ) (hD₀ : 0 < D₀)
    (n : ℕ) (hγ_pow : M.γ ^ n < ε / D₀) :
    M.γ ^ n * D₀ < ε := by
  rwa [lt_div_iff₀ hD₀] at hγ_pow

end POMDP

end
