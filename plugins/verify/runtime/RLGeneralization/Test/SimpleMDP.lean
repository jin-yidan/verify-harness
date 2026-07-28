/-
# Test: Library Instantiation

Verifies that the library definitions and theorems can be
instantiated and used with concrete MDP parameters.
-/

import RLGeneralization.MDP.ValueIteration
import RLGeneralization.MDP.FiniteHorizon

open Finset BigOperators

noncomputable section

/-- Test: value iteration Q-function is well-defined for
    any MDP with 0 iterations (returns the zero function). -/
example (M : FiniteMDP) (s : M.S) (a : M.A) :
    M.valueIterationQ 0 s a = 0 := by
  simp [FiniteMDP.valueIterationQ, Function.iterate_zero]

/-- Test: bellman contraction works compositionally. -/
example (M : FiniteMDP) (Q₁ Q₂ : M.ActionValueFn) :
    M.supDistQ (M.bellmanOptOp Q₁) (M.bellmanOptOp Q₂) ≤
    M.γ * M.supDistQ Q₁ Q₂ :=
  M.bellmanOptOp_contraction Q₁ Q₂

/-- Test: greedy action is well-defined and achieves max. -/
example (M : FiniteMDP) (Q : M.ActionValueFn) (s : M.S) (a : M.A) :
    Q s a ≤ Q s (M.greedyAction Q s) :=
  M.greedyAction_spec Q s a

/-- Test: finite-horizon backward induction value is nonneg. -/
example (M : FiniteHorizonMDP) (k : ℕ) (hk : k ≤ M.H)
    (s : M.S) (a : M.A) :
    0 ≤ M.backwardQ k hk s a :=
  M.backwardQ_nonneg k hk s a

/-- Test: backward induction value bounded by remaining steps. -/
example (M : FiniteHorizonMDP) (k : ℕ) (hk : k ≤ M.H)
    (s : M.S) (a : M.A) :
    M.backwardQ k hk s a ≤ k :=
  M.backwardQ_le k hk s a

end
