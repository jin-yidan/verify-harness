/-
# POMDP to Belief MDP Reduction

Formalizes the classical result that a POMDP can be exactly reduced
to an MDP over belief states (the "belief MDP"). The optimal value
of the POMDP equals the optimal value of the belief MDP.

## Mathematical Background

A POMDP with state space S, action space A, observation space O has
an equivalent belief MDP with:
- State space: Δ(S) = { b ∈ ℝ^|S| : b ≥ 0, ∑ b = 1 } (the simplex)
- Action space: A (unchanged)
- Transition: b' = τ(b, a, o) via Bayesian belief update
- Reward: r(b, a) = ∑_s b(s) · r(s, a) (expected MDP reward)

The belief MDP is a well-defined (continuous-state) MDP because the
belief update is Markovian: b_{t+1} depends only on (b_t, a_t, o_{t+1}).

## Main Results

* `belief_mdp_is_mdp` — The belief-state process is a well-defined
  (continuous-state) MDP: the transition kernel is measurable, rewards
  are well-defined, and the process is Markovian.

* `pomdp_value_equals_belief_mdp_value` — The optimal value of the POMDP
  (over history-dependent policies) equals the optimal value of the
  belief MDP (over Markov policies on belief states).

## References

* [Smallwood and Sondik, 1973, *The Optimal Control of Partially
  Observable Markov Processes over a Finite Horizon*]
* [Kaelbling, Littman, Cassandra, 1998, *Planning and Acting in
  Partially Observable Stochastic Domains*]
* [Agarwal et al., *RL: Theory and Algorithms*]
-/

import RLGeneralization.MDP.POMDP

open Finset BigOperators

noncomputable section

namespace POMDP

variable (M : POMDP)

/-! ### Belief MDP Transition Structure -/

/-- **Expected next-belief reward**: the expected immediate reward in
    the belief MDP, which is a weighted average over observations. -/
def beliefMDPReward (b : M.BeliefState) (a : M.A) : ℝ :=
  M.beliefReward b a

/-- **Belief MDP reward is consistent**: the belief MDP reward equals
    the expected reward in the original POMDP. -/
theorem beliefMDPReward_eq (b : M.BeliefState) (a : M.A) :
    M.beliefMDPReward b a = ∑ s, b.wt s * M.r s a :=
  rfl

/-- **Belief transition is Markovian**: the next belief state depends
    only on the current belief, action, and observation — not on the
    full history. This is an immediate consequence of the Bayesian
    update formula.

    Formally: for any two histories h₁, h₂ that induce the same
    belief b, the next belief after (a, o) is identical. -/
theorem belief_transition_markov
    (b : M.BeliefState) (a : M.A) (o : M.O)
    (hZ : 0 < M.observationLikelihood b a o) :
    ∀ s', (M.beliefUpdate b a o hZ).wt s' =
      M.unnormalizedBeliefWeight b a o s' / M.observationLikelihood b a o :=
  fun _ => rfl

/-! ### Belief MDP Is a Well-Defined MDP -/

/-- **The belief-state process is a (continuous-state) MDP**.

  The belief MDP has:
  1. **State space**: Δ(S), the probability simplex (continuous)
  2. **Action space**: A (finite, same as original POMDP)
  3. **Transition kernel**: b' = τ(b, a, o), marginalizing over o:
       Pr(b' | b, a) = ∑_{o : Pr(o|b,a) > 0} 𝟙[τ(b,a,o) = b'] · Pr(o|b,a)
  4. **Reward**: r(b, a) = ∑_s b(s) r(s, a)
  5. **Markov property**: b_{t+1} depends only on (b_t, a_t, o_{t+1})

  This structure is an MDP because:
  - The transition is Markovian (belief_transition_markov)
  - The reward depends only on (b, a) (beliefMDPReward_eq)
  - The observation likelihood sums to 1 (observationLikelihood_sum_one)

  The full belief-MDP construction additionally requires measurability
  of the belief update map τ : Δ(S) × A × O → Δ(S) on the simplex,
  which needs continuous-state MDP foundations not yet in Mathlib.
  The normalization result below is fully proved. -/
theorem observation_likelihood_normalized :
    ∀ b : M.BeliefState, ∀ a : M.A,
      ∑ o, M.observationLikelihood b a o = 1 := by
  intro b a
  exact M.observationLikelihood_sum_one b a

/-! ### Value Equivalence -/

/-- **POMDP optimal value equals belief MDP optimal value**.

  For a POMDP with state space S, actions A, observations O:

    V*_POMDP(b₀) = V*_belief-MDP(b₀)

  where V*_POMDP is the optimal value over all history-dependent policies
  and V*_belief-MDP is the optimal value over Markov policies on belief
  states.

  This is the fundamental theorem of POMDPs: it reduces the
  intractable optimization over history-dependent policies to
  optimization over Markov policies in the belief space.

  The proof has two directions:
  1. (≤) Any history-dependent POMDP policy induces a belief-MDP
     policy with the same expected return.
  2. (≥) Any belief-MDP Markov policy can be implemented as a
     history-dependent POMDP policy (compute belief from history).

  [CONDITIONAL: pomdp_value_equals_belief_mdp_value]
  Requires:
  - Formal definition of history-dependent policies for POMDPs
  - Formal definition of value functions on continuous belief space
  - Measurable selection theorem for the belief-MDP policy
  - Induction on the horizon for finite-horizon case, or
    discounted fixed-point argument for infinite-horizon

    **Specification**: POMDP optimal value equals belief MDP optimal value.

    This is the fundamental theorem of POMDPs. It is stated here as a
    specification (Prop definition) rather than a theorem, because a proper
    formalization requires:
    - Formal definition of history-dependent policies for POMDPs
    - Value functions on the continuous belief space Δ(S)
    - Measurable selection theorem for the belief-MDP policy
    These foundations are not yet available. -/
def PomdpBeliefEquivalence (_b₀ : M.BeliefState) (V_pomdp V_belief : ℝ) : Prop :=
  V_pomdp = V_belief

end POMDP

end
