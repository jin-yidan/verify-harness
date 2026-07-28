/-
# Tabular Planner for Small MDPs

Defines a tabular planner for small MDPs (|S| <= 20, |A| <= 5),
outputting a policy together with a certified suboptimality bound.
Uses value iteration and the Bellman contraction property to
produce the bound.

## Main Definitions

* `SmallMDP` - A concrete MDP with bounded state/action spaces,
  parameterized by `Fin n` and `Fin m` with `n ≤ 20` and `m ≤ 5`.
* `plannerOutput` - The output of the tabular planner: a greedy
  policy (action selector) together with a suboptimality certificate.
* `tabularPlan` - The main planner: runs K steps of value iteration
  and returns a certified policy.

## References

* [Puterman, *Markov Decision Processes*][puterman2014]
* [Agarwal et al., *RL: Theory and Algorithms*][agarwal2026]
-/

import RLGeneralization.MDP.ValueIteration

open Finset BigOperators

noncomputable section

/-! ### Small MDP Definition -/

/-- A **small MDP** suitable for tabular planning (exact).

  This is a concrete MDP with `Fin n` states and `Fin m` actions,
  where n <= 20 and m <= 5. The size bounds ensure that brute-force
  value iteration is tractable (at most 20 * 5 = 100 state-action pairs
  per iteration). -/
structure SmallMDP (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (hn_small : n ≤ 20) (hm_small : m ≤ 5) where
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

namespace SmallMDP

variable {n m : ℕ} {hn : 0 < n} {hm : 0 < m}
  {hn_small : n ≤ 20} {hm_small : m ≤ 5}

/-- Lift a `SmallMDP` to the abstract `FiniteMDP` structure. -/
def toFiniteMDP (S : SmallMDP n m hn hm hn_small hm_small) : FiniteMDP where
  S := Fin n
  A := Fin m
  instNonemptyS := ⟨⟨0, hn⟩⟩
  instNonemptyA := ⟨⟨0, hm⟩⟩
  P := S.P
  r := S.r
  γ := S.γ
  P_nonneg := S.P_nonneg
  P_sum_one := S.P_sum_one
  r_bound := S.r_bound
  γ_nonneg := S.γ_nonneg
  γ_lt_one := S.γ_lt_one

/-! ### Planner Output -/

/-- The output of the tabular planner: a greedy policy (action selector)
  together with an exact certified suboptimality bound.

  The bound states that for any V_greedy satisfying the Bellman equation
  of the greedy policy, the gap V*(s) - V_greedy(s) is controlled by
  the iteration count K. -/
structure PlannerOutput (S : SmallMDP n m hn hm hn_small hm_small)
    (K : ℕ)
    (Q_star : S.toFiniteMDP.ActionValueFn)
    (V_star : S.toFiniteMDP.StateValueFn) where
  /-- The greedy action selector (the policy) -/
  policy : Fin n → Fin m
  /-- The policy achieves the maximum Q-value at each state -/
  policy_greedy : ∀ s a,
    S.toFiniteMDP.valueIterationQ K s a ≤
    S.toFiniteMDP.valueIterationQ K s (policy s)
  /-- Suboptimality certificate: for any V satisfying the Bellman equation
      of the policy, the gap is bounded -/
  suboptimality_bound :
    ∀ (V_greedy : S.toFiniteMDP.StateValueFn),
      (∀ s, V_greedy s =
        S.toFiniteMDP.r s (policy s) +
        S.toFiniteMDP.γ * ∑ s', S.toFiniteMDP.P s (policy s) s' * V_greedy s') →
      ∀ s, V_star s - V_greedy s ≤
        2 * (S.toFiniteMDP.γ ^ K *
          S.toFiniteMDP.supDistQ (S.toFiniteMDP.valueIterationQ 0) Q_star) /
          (1 - S.toFiniteMDP.γ)

/-! ### Tabular Planner -/

/-- **Tabular planner** (exact).

  Given a small MDP and a number of iterations K, runs value iteration
  and returns a `PlannerOutput` consisting of:
  1. A greedy policy (action selector) w.r.t. Q_K.
  2. A proof that the policy maximizes Q_K at each state.
  3. An exact certified suboptimality bound.

  The planner uses `greedyAction` from the MDP library to extract
  the policy, and `value_iteration_with_greedy` for the bound. -/
def tabularPlan (S : SmallMDP n m hn hm hn_small hm_small) (K : ℕ)
    (Q_star : S.toFiniteMDP.ActionValueFn)
    (hQ_star_fp : Q_star = S.toFiniteMDP.bellmanOptOp Q_star)
    (V_star : S.toFiniteMDP.StateValueFn)
    (hV_star : ∀ s, V_star s =
      Finset.univ.sup' Finset.univ_nonempty (Q_star s))
    (hQ_star_bellman : ∀ s a, Q_star s a =
      S.toFiniteMDP.r s a + S.toFiniteMDP.γ * ∑ s', S.toFiniteMDP.P s a s' * V_star s') :
    PlannerOutput S K Q_star V_star where
  policy := S.toFiniteMDP.greedyAction (S.toFiniteMDP.valueIterationQ K)
  policy_greedy := fun s a =>
    S.toFiniteMDP.greedyAction_spec (S.toFiniteMDP.valueIterationQ K) s a
  suboptimality_bound := fun V_greedy hV_greedy =>
    S.toFiniteMDP.value_iteration_with_greedy
      Q_star hQ_star_fp V_star hV_star hQ_star_bellman K V_greedy hV_greedy

/-! ### Iteration Count Sufficient for ε-Optimality -/

/-- **ε-optimal tabular planner** (exact).

  Given a small MDP, ε > 0, and K ≥ log(C/ε)/(1-γ) iterations,
  the greedy policy w.r.t. Q_K is 2ε/(1-γ)-suboptimal.

  This combines `value_iteration_epsilon_optimal` with the greedy
  policy construction. The user supplies the iteration budget K
  and the theorem certifies the approximation quality. -/
theorem tabularPlan_epsilon_optimal
    (S : SmallMDP n m hn hm hn_small hm_small)
    (Q_star : S.toFiniteMDP.ActionValueFn)
    (hQ_star_fp : Q_star = S.toFiniteMDP.bellmanOptOp Q_star)
    (V_star : S.toFiniteMDP.StateValueFn)
    (hV_star : ∀ s, V_star s =
      Finset.univ.sup' Finset.univ_nonempty (Q_star s))
    (hQ_star_bellman : ∀ s a, Q_star s a =
      S.toFiniteMDP.r s a + S.toFiniteMDP.γ * ∑ s', S.toFiniteMDP.P s a s' * V_star s')
    (ε : ℝ) (hε : 0 < ε)
    (C : ℝ) (hC : 0 < C)
    (hC_bound : S.toFiniteMDP.supDistQ (S.toFiniteMDP.valueIterationQ 0) Q_star ≤ C)
    (K : ℕ) (hK_pos : 0 < K)
    (hK : Real.log (C / ε) / (1 - S.toFiniteMDP.γ) ≤ K)
    (V_greedy : S.toFiniteMDP.StateValueFn)
    (hV_greedy : ∀ s, V_greedy s =
      S.toFiniteMDP.r s
        (S.toFiniteMDP.greedyAction (S.toFiniteMDP.valueIterationQ K) s) +
      S.toFiniteMDP.γ * ∑ s', S.toFiniteMDP.P s
        (S.toFiniteMDP.greedyAction (S.toFiniteMDP.valueIterationQ K) s) s' *
        V_greedy s') :
    ∀ s, V_star s - V_greedy s ≤ 2 * ε / (1 - S.toFiniteMDP.γ) :=
  S.toFiniteMDP.value_iteration_epsilon_optimal
    Q_star hQ_star_fp V_star hV_star hQ_star_bellman
    ε hε C hC hC_bound K hK_pos hK V_greedy hV_greedy

/-! ### Size-Aware Complexity Bound -/

/-- **Per-iteration work bound** for the tabular planner.

  Each iteration of value iteration on a small MDP touches at most
  n * m state-action pairs, each requiring a sum over n next-states.
  Total per-iteration work is O(n^2 * m).

  For a small MDP with n <= 20, m <= 5, this is at most
  20^2 * 5 = 2000 operations per iteration.

  This is a type-level statement (not a computational bound),
  capturing the structural complexity of the problem. -/
theorem perIterationStatePairs
    (_S : SmallMDP n m hn hm hn_small hm_small) :
    n * m ≤ 100 := by
  calc n * m ≤ 20 * 5 := Nat.mul_le_mul hn_small hm_small
    _ = 100 := by norm_num

/-- **Total work bound** for K iterations of the tabular planner.

  K iterations on a small MDP require at most K * n * m * n
  = K * n^2 * m arithmetic operations (each state-action pair
  requires summing over n next-states).

  For small MDPs: K * 20^2 * 5 = 2000 * K. -/
theorem totalWorkBound
    (_S : SmallMDP n m hn hm hn_small hm_small) (K : ℕ) :
    K * (n * m * n) ≤ K * 2000 := by
  apply Nat.mul_le_mul_left
  calc n * m * n ≤ 20 * 5 * 20 := by
        apply Nat.mul_le_mul
        · exact Nat.mul_le_mul hn_small hm_small
        · exact hn_small
    _ = 2000 := by norm_num

end SmallMDP

/-! ### Instantiation Tests -/

/-- The small MDP lifts to a valid FiniteMDP. -/
theorem SmallMDP.toFiniteMDP_well_formed
    {n m : ℕ} {hn : 0 < n} {hm : 0 < m}
    {hn_small : n ≤ 20} {hm_small : m ≤ 5}
    (S : SmallMDP n m hn hm hn_small hm_small) :
    S.toFiniteMDP.γ = S.γ := rfl

/-- Value iteration at step 0 is zero for a small MDP. -/
theorem SmallMDP.valueIterationQ_zero
    {n m : ℕ} {hn : 0 < n} {hm : 0 < m}
    {hn_small : n ≤ 20} {hm_small : m ≤ 5}
    (S : SmallMDP n m hn hm hn_small hm_small)
    (s : Fin n) (a : Fin m) :
    S.toFiniteMDP.valueIterationQ 0 s a = 0 := by
  simp [FiniteMDP.valueIterationQ, Function.iterate_zero]

/-- The tabular planner's greedy policy achieves the max Q-value. -/
example {n m : ℕ} {hn : 0 < n} {hm : 0 < m}
    {hn_small : n ≤ 20} {hm_small : m ≤ 5}
    (S : SmallMDP n m hn hm hn_small hm_small)
    (K : ℕ) (s : Fin n) (a : Fin m)
    (Q_star : S.toFiniteMDP.ActionValueFn)
    (hQ_star_fp : Q_star = S.toFiniteMDP.bellmanOptOp Q_star)
    (V_star : S.toFiniteMDP.StateValueFn)
    (hV_star : ∀ s, V_star s = Finset.univ.sup' Finset.univ_nonempty (Q_star s))
    (hQ_star_bellman : ∀ s a, Q_star s a =
      S.toFiniteMDP.r s a + S.toFiniteMDP.γ * ∑ s', S.toFiniteMDP.P s a s' * V_star s') :
    S.toFiniteMDP.valueIterationQ K s a ≤
      S.toFiniteMDP.valueIterationQ K s
        ((S.tabularPlan K Q_star hQ_star_fp V_star hV_star hQ_star_bellman).policy s) :=
  (S.tabularPlan K Q_star hQ_star_fp V_star hV_star hQ_star_bellman).policy_greedy s a

end
