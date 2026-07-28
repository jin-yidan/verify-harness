/-
# Certified Value Iteration

Defines a concrete finite MDP structure with explicit state/action types
(`Fin n`, `Fin m`) and arrays for transition probabilities and rewards.
Provides certified value iteration: given a concrete MDP and K steps,
produces a value function together with a proof of its approximation bound.

## Main Definitions

* `ConcreteFiniteMDP` - A finite MDP with `Fin n` states and `Fin m` actions,
  with transition probabilities and rewards stored as functions on `Fin`.
* `concreteToFiniteMDP` - Lifts a `ConcreteFiniteMDP` to a `FiniteMDP`.
* `certifiedValueIteration` - Returns a Sigma type `Σ' Q, proof_of_bound`:
  the Q-function after K iterations together with a proof that
  ‖Q_K - Q*‖_∞ ≤ γ^K · ‖Q_0 - Q*‖_∞.

## References

* [Puterman, *Markov Decision Processes*][puterman2014]
* [Bertsekas, *Dynamic Programming and Optimal Control*][bertsekas2012]
-/

import RLGeneralization.MDP.ValueIteration

open Finset BigOperators

noncomputable section

/-! ### Concrete MDP with Fin types -/

/-- A concrete finite MDP with `Fin n` states and `Fin m` actions.
    Transition probabilities and rewards are given as functions on finite types,
    making them suitable for concrete computation. -/
structure ConcreteFiniteMDP (n m : ℕ) (hn : 0 < n) (hm : 0 < m) where
  /-- Transition probability: P(s'|s,a) -/
  P : Fin n → Fin m → Fin n → ℝ
  /-- Reward function: r(s,a) -/
  r : Fin n → Fin m → ℝ
  /-- Discount factor γ ∈ [0,1) -/
  γ : ℝ
  /-- Transition probabilities are nonnegative -/
  P_nonneg : ∀ s a s', 0 ≤ P s a s'
  /-- Transition probabilities sum to 1 -/
  P_sum_one : ∀ s a, ∑ s' : Fin n, P s a s' = 1
  /-- Reward is bounded -/
  r_bound : ∃ R_max : ℝ, 0 < R_max ∧ ∀ s a, |r s a| ≤ R_max
  /-- Discount factor is in [0,1) -/
  γ_nonneg : 0 ≤ γ
  γ_lt_one : γ < 1

namespace ConcreteFiniteMDP

variable {n m : ℕ} {hn : 0 < n} {hm : 0 < m}


/-- Lift a `ConcreteFiniteMDP` to the abstract `FiniteMDP` structure.
    This allows us to apply all theorems from the MDP library
    (contraction, value iteration convergence, etc.) to concrete instances. -/
def toFiniteMDP (C : ConcreteFiniteMDP n m hn hm) : FiniteMDP where
  S := Fin n
  A := Fin m
  instNonemptyS := ⟨⟨0, hn⟩⟩
  instNonemptyA := ⟨⟨0, hm⟩⟩
  P := C.P
  r := C.r
  γ := C.γ
  P_nonneg := C.P_nonneg
  P_sum_one := C.P_sum_one
  r_bound := C.r_bound
  γ_nonneg := C.γ_nonneg
  γ_lt_one := C.γ_lt_one

/-! ### Certified Value Iteration -/

/-- **Certified value iteration** (exact).

  Given a concrete MDP and a number of iterations K, produces
  a Sigma type containing:
  1. The Q-function `Q_K` obtained by K steps of value iteration.
  2. A proof that ‖Q_K - Q*‖_∞ ≤ γ^K · ‖Q_0 - Q*‖_∞ for any
     fixed point Q* of the Bellman optimality operator.

  The certificate leverages `value_iteration_geometric_error` from the
  abstract MDP library. Concrete evaluation of the bound requires
  instantiating Q* (e.g., via a solver or oracle). -/
def certifiedValueIteration (C : ConcreteFiniteMDP n m hn hm) (K : ℕ)
    (Q_star : C.toFiniteMDP.ActionValueFn)
    (hQ_star : Q_star = C.toFiniteMDP.bellmanOptOp Q_star) :
    Σ' (Q_K : C.toFiniteMDP.ActionValueFn),
      C.toFiniteMDP.supDistQ Q_K Q_star ≤
        C.toFiniteMDP.γ ^ K * C.toFiniteMDP.supDistQ (C.toFiniteMDP.valueIterationQ 0) Q_star :=
  ⟨C.toFiniteMDP.valueIterationQ K,
   C.toFiniteMDP.value_iteration_geometric_error Q_star hQ_star K⟩

/-- **Certified value iteration with explicit error bound** (exact).

  Given a concrete MDP, a number of iterations K, and an initial error
  bound C₀ ≥ ‖Q_0 - Q*‖_∞, produces:
  1. The Q-function Q_K.
  2. A proof that ‖Q_K - Q*‖_∞ ≤ γ^K · C₀.

  This is the form most useful for producing numerical certificates:
  the user supplies C₀ (e.g., R_max / (1-γ)) and the output bound
  is a concrete expression in γ, K, and C₀. -/
def certifiedValueIterationBound (C : ConcreteFiniteMDP n m hn hm) (K : ℕ)
    (Q_star : C.toFiniteMDP.ActionValueFn)
    (hQ_star : Q_star = C.toFiniteMDP.bellmanOptOp Q_star)
    (C₀ : ℝ) (_hC₀ : 0 < C₀)
    (hC₀_bound : C.toFiniteMDP.supDistQ (C.toFiniteMDP.valueIterationQ 0) Q_star ≤ C₀) :
    Σ' (Q_K : C.toFiniteMDP.ActionValueFn),
      C.toFiniteMDP.supDistQ Q_K Q_star ≤ C.toFiniteMDP.γ ^ K * C₀ :=
  ⟨C.toFiniteMDP.valueIterationQ K,
   calc C.toFiniteMDP.supDistQ (C.toFiniteMDP.valueIterationQ K) Q_star
       ≤ C.toFiniteMDP.γ ^ K * C.toFiniteMDP.supDistQ (C.toFiniteMDP.valueIterationQ 0) Q_star :=
         C.toFiniteMDP.value_iteration_geometric_error Q_star hQ_star K
     _ ≤ C.toFiniteMDP.γ ^ K * C₀ :=
         mul_le_mul_of_nonneg_left hC₀_bound (pow_nonneg C.γ_nonneg K)⟩

/-- **Certified greedy policy with suboptimality bound** (exact).

  Given a concrete MDP and K iterations of value iteration, produces:
  1. A greedy action selector (the policy).
  2. A proof that for any V_greedy satisfying the Bellman equation
     of the greedy policy, the suboptimality gap satisfies
     V*(s) - V_greedy(s) ≤ 2 · γ^K · ‖Q_0 - Q*‖_∞ / (1 - γ).

  This combines `value_iteration_geometric_error` with
  `q_error_amplification` to provide an end-to-end policy certificate. -/
def certifiedGreedyPolicy (C : ConcreteFiniteMDP n m hn hm) (K : ℕ)
    (Q_star : C.toFiniteMDP.ActionValueFn)
    (hQ_star_fp : Q_star = C.toFiniteMDP.bellmanOptOp Q_star)
    (V_star : C.toFiniteMDP.StateValueFn)
    (hV_star : ∀ s, V_star s =
      Finset.univ.sup' Finset.univ_nonempty (Q_star s))
    (hQ_star_bellman : ∀ s a, Q_star s a =
      C.toFiniteMDP.r s a + C.γ * ∑ s', C.toFiniteMDP.P s a s' * V_star s') :
    Σ' (a_gr : Fin n → Fin m),
      ∀ (V_greedy : C.toFiniteMDP.StateValueFn),
        (∀ s, V_greedy s =
          C.toFiniteMDP.r s (a_gr s) +
          C.γ * ∑ s', C.toFiniteMDP.P s (a_gr s) s' * V_greedy s') →
        ∀ s, V_star s - V_greedy s ≤
          2 * (C.toFiniteMDP.γ ^ K *
            C.toFiniteMDP.supDistQ (C.toFiniteMDP.valueIterationQ 0) Q_star) /
            (1 - C.γ) :=
  ⟨C.toFiniteMDP.greedyAction (C.toFiniteMDP.valueIterationQ K),
   fun V_greedy hV_greedy =>
     C.toFiniteMDP.value_iteration_with_greedy
       Q_star hQ_star_fp V_star hV_star hQ_star_bellman K V_greedy hV_greedy⟩

end ConcreteFiniteMDP

/-! ### Instantiation Sanity Checks -/

/-- The concrete MDP lifts to a valid FiniteMDP with correct discount factor. -/
theorem ConcreteFiniteMDP.toFiniteMDP_γ {n m : ℕ} {hn : 0 < n} {hm : 0 < m}
    (C : ConcreteFiniteMDP n m hn hm) :
    C.toFiniteMDP.γ = C.γ := rfl

/-- Value iteration at step 0 is the zero function for a concrete MDP. -/
theorem ConcreteFiniteMDP.valueIterationQ_zero {n m : ℕ} {hn : 0 < n} {hm : 0 < m}
    (C : ConcreteFiniteMDP n m hn hm) (s : Fin n) (a : Fin m) :
    C.toFiniteMDP.valueIterationQ 0 s a = 0 := by
  simp [FiniteMDP.valueIterationQ, Function.iterate_zero]

end
