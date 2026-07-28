/-
# Banach Fixed-Point Bridge for Discounted Q-Operators

This file transports the Bellman Q-evaluation and Bellman optimality operators
to a complete `PiLp ∞` space over the finite state-action index set and applies
Mathlib's Banach fixed-point theorem.

## Main Results

* `actionValueFixedPoint_isActionValueOf` - constructs a Bellman-consistent
  policy action-value function from the contraction map.
* `exists_actionValue_fixedPoint` - policy evaluation has an action-value
  fixed point.
* `optimalQFixedPoint_isBellmanOptimalQ` - constructs a Bellman-optimal
  fixed point of the optimality operator.
* `tendsto_iterate_actionValueFixedPointQSpace` - iterates of the transported
  Bellman operator converge to the fixed point.

 ## References

 * [Agarwal et al., *RL: Theory and Algorithms*][agarwal2026]
 * Mathlib `Topology.MetricSpace.Contracting`
 -/

import RLGeneralization.MDP.Resolvent
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Data.Finset.Lattice.Prod

open Finset BigOperators

noncomputable section

namespace FiniteMDP

variable (M : FiniteMDP)

/-- The complete sup-norm model for Q-functions indexed by state-action pairs. -/
abbrev QSpace := PiLp (⊤ : ENNReal) (fun _ : M.S × M.A => ℝ)

/-- View an action-value function as an element of the complete `PiLp ∞` space. -/
def toQSpace (Q : M.ActionValueFn) : M.QSpace :=
  (WithLp.equiv (⊤ : ENNReal) _).symm (fun i : M.S × M.A => Q i.1 i.2)

/-- Forget a `PiLp ∞` point back to an action-value function on the MDP. -/
def ofQSpace (x : M.QSpace) : M.ActionValueFn :=
  fun s a => x (s, a)

@[simp] lemma ofQSpace_apply (x : M.QSpace) (s : M.S) (a : M.A) :
    M.ofQSpace x s a = x (s, a) := rfl

@[simp] lemma of_toQSpace (Q : M.ActionValueFn) :
    M.ofQSpace (M.toQSpace Q) = Q := by
  funext s a
  rfl

@[simp] lemma toQSpace_ofQSpace (x : M.QSpace) :
    M.toQSpace (M.ofQSpace x) = x := by
  ext i
  rfl

/-- The project sup norm on Q-functions agrees with the flat sup over the
state-action product. -/
lemma supNormQ_eq_supPair (Q : M.ActionValueFn) :
    M.supNormQ Q =
      ((Finset.univ : Finset M.S) ×ˢ (Finset.univ : Finset M.A)).sup'
        (Finset.univ_nonempty.product Finset.univ_nonempty)
        (fun i : M.S × M.A => |Q i.1 i.2|) := by
  unfold FiniteMDP.supNormQ
  symm
  exact Finset.sup'_product_left (s := (Finset.univ : Finset M.S))
    (t := (Finset.univ : Finset M.A))
    (h := Finset.univ_nonempty.product Finset.univ_nonempty)
    (f := fun i : M.S × M.A => |Q i.1 i.2|)

/-- The metric on the complete `PiLp ∞` model exactly matches the project's
`supDistQ` distance after transport back to action-value functions. -/
lemma qSpace_dist_eq_supDistQ (x y : M.QSpace) :
    dist x y = M.supDistQ (M.ofQSpace x) (M.ofQSpace y) := by
  rw [PiLp.dist_eq_iSup]
  rw [← Finset.sup'_univ_eq_ciSup (f := fun i : M.S × M.A => dist (x i) (y i))]
  have hpair :
      (Finset.univ : Finset (M.S × M.A)).sup' Finset.univ_nonempty
        (fun i : M.S × M.A => dist (x i) (y i)) =
      ((Finset.univ : Finset M.S) ×ˢ (Finset.univ : Finset M.A)).sup'
        (Finset.univ_nonempty.product Finset.univ_nonempty)
        (fun i : M.S × M.A => dist (x i) (y i)) := by
      simp
  rw [hpair]
  change ((Finset.univ : Finset M.S) ×ˢ (Finset.univ : Finset M.A)).sup'
      (Finset.univ_nonempty.product Finset.univ_nonempty)
      (fun i : M.S × M.A => |(M.ofQSpace x) i.1 i.2 - (M.ofQSpace y) i.1 i.2|) =
    M.supDistQ (M.ofQSpace x) (M.ofQSpace y)
  rw [← M.supNormQ_eq_supPair
    (Q := fun s a => (M.ofQSpace x) s a - (M.ofQSpace y) s a)]
  rfl

/-- The Bellman Q-evaluation operator transported to the complete `PiLp ∞`
space. -/
def bellmanEvalOpQSpace (π : M.StochasticPolicy) (x : M.QSpace) : M.QSpace :=
  M.toQSpace (M.bellmanEvalOpQ π (M.ofQSpace x))

/-- The transported Bellman Q-evaluation operator satisfies the metric
contraction bound inherited from `supDistQ`. -/
lemma bellmanEvalOpQSpace_dist_le (π : M.StochasticPolicy) (x y : M.QSpace) :
    dist (M.bellmanEvalOpQSpace π x) (M.bellmanEvalOpQSpace π y) ≤
      M.γ * dist x y := by
  rw [M.qSpace_dist_eq_supDistQ, M.qSpace_dist_eq_supDistQ]
  exact M.bellmanEvalOpQ_contraction π (M.ofQSpace x) (M.ofQSpace y)

/-- The transported Bellman Q-evaluation operator is Lipschitz with constant
`γ`. -/
lemma bellmanEvalOpQSpace_lipschitz (π : M.StochasticPolicy) :
    LipschitzWith ⟨M.γ, M.γ_nonneg⟩ (M.bellmanEvalOpQSpace π) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  simpa using M.bellmanEvalOpQSpace_dist_le π x y

/-- The transported Bellman Q-evaluation operator is a contracting map on the
complete `PiLp ∞` Q-space. -/
lemma bellmanEvalOpQSpace_contracting (π : M.StochasticPolicy) :
    ContractingWith ⟨M.γ, M.γ_nonneg⟩ (M.bellmanEvalOpQSpace π) := by
  refine ⟨?_, M.bellmanEvalOpQSpace_lipschitz π⟩
  change M.γ < 1
  exact M.γ_lt_one

/-- The Banach fixed point of the transported Bellman Q-evaluation operator. -/
noncomputable def actionValueFixedPointQSpace (π : M.StochasticPolicy) : M.QSpace :=
  ContractingWith.fixedPoint (M.bellmanEvalOpQSpace π)
    (M.bellmanEvalOpQSpace_contracting π)

/-- The Bellman-consistent action-value function obtained by transporting the
Banach fixed point back to the original Q-function space. -/
noncomputable def actionValueFixedPoint (π : M.StochasticPolicy) : M.ActionValueFn :=
  M.ofQSpace (M.actionValueFixedPointQSpace π)

/-- The transported Banach fixed point is genuinely fixed by the Bellman
Q-evaluation operator. -/
lemma actionValueFixedPointQSpace_isFixedPt (π : M.StochasticPolicy) :
    Function.IsFixedPt (M.bellmanEvalOpQSpace π)
      (M.actionValueFixedPointQSpace π) :=
  ContractingWith.fixedPoint_isFixedPt (f := M.bellmanEvalOpQSpace π)
    (hf := M.bellmanEvalOpQSpace_contracting π)

/-- The Banach fixed point is a Bellman-consistent action-value function for
the policy. -/
lemma actionValueFixedPoint_isActionValueOf (π : M.StochasticPolicy) :
    M.isActionValueOf (M.actionValueFixedPoint π) π := by
  rw [M.isActionValueOf_iff_fixedPoint π]
  intro s a
  have hfix := M.actionValueFixedPointQSpace_isFixedPt π
  have hcoord := congrArg (fun z : M.QSpace => z (s, a)) hfix.eq
  simpa [Function.IsFixedPt, actionValueFixedPoint,
    actionValueFixedPointQSpace, bellmanEvalOpQSpace] using hcoord.symm

/-- Policy evaluation has an action-value fixed point, obtained by applying
Banach's theorem to the transported Bellman operator. -/
lemma exists_actionValue_fixedPoint (π : M.StochasticPolicy) :
    ∃ Q, M.isActionValueOf Q π := by
  exact ⟨M.actionValueFixedPoint π, M.actionValueFixedPoint_isActionValueOf π⟩

/-- Iterates of the transported Bellman Q-evaluation operator converge to the
Banach fixed point. -/
lemma tendsto_iterate_actionValueFixedPointQSpace (π : M.StochasticPolicy)
    (x : M.QSpace) :
    Filter.Tendsto (fun n => (M.bellmanEvalOpQSpace π)^[n] x) Filter.atTop
      (nhds (M.actionValueFixedPointQSpace π)) := by
  simpa [actionValueFixedPointQSpace] using
    (ContractingWith.tendsto_iterate_fixedPoint
      (f := M.bellmanEvalOpQSpace π)
      (hf := M.bellmanEvalOpQSpace_contracting π)
      x)

/-- A priori geometric convergence bound for iterates of the transported
Bellman Q-evaluation operator. -/
lemma apriori_dist_iterate_actionValueFixedPointQSpace_le
    (π : M.StochasticPolicy) (x : M.QSpace) (n : ℕ) :
    dist ((M.bellmanEvalOpQSpace π)^[n] x) (M.actionValueFixedPointQSpace π) ≤
      dist x (M.bellmanEvalOpQSpace π x) * M.γ ^ n / (1 - M.γ) := by
  simpa [actionValueFixedPointQSpace] using
    (ContractingWith.apriori_dist_iterate_fixedPoint_le
      (f := M.bellmanEvalOpQSpace π)
      (hf := M.bellmanEvalOpQSpace_contracting π)
      x n)

/-! ### Bellman Optimality via Banach -/

/-- The Bellman optimality operator transported to the complete `PiLp ∞`
Q-space. -/
def bellmanOptOpQSpace (x : M.QSpace) : M.QSpace :=
  M.toQSpace (M.bellmanOptOp (M.ofQSpace x))

/-- The transported Bellman optimality operator satisfies the metric
contraction bound inherited from `supDistQ`. -/
lemma bellmanOptOpQSpace_dist_le (x y : M.QSpace) :
    dist (M.bellmanOptOpQSpace x) (M.bellmanOptOpQSpace y) ≤
      M.γ * dist x y := by
  rw [M.qSpace_dist_eq_supDistQ, M.qSpace_dist_eq_supDistQ]
  exact M.bellmanOptOp_contraction (M.ofQSpace x) (M.ofQSpace y)

/-- The transported Bellman optimality operator is Lipschitz with constant
`γ`. -/
lemma bellmanOptOpQSpace_lipschitz :
    LipschitzWith ⟨M.γ, M.γ_nonneg⟩ M.bellmanOptOpQSpace := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  simpa using M.bellmanOptOpQSpace_dist_le x y

/-- The transported Bellman optimality operator is a contracting map on the
complete `PiLp ∞` Q-space. -/
lemma bellmanOptOpQSpace_contracting :
    ContractingWith ⟨M.γ, M.γ_nonneg⟩ M.bellmanOptOpQSpace := by
  refine ⟨?_, M.bellmanOptOpQSpace_lipschitz⟩
  change M.γ < 1
  exact M.γ_lt_one

/-- The Banach fixed point of the transported Bellman optimality operator. -/
noncomputable def optimalQFixedPointQSpace : M.QSpace :=
  ContractingWith.fixedPoint M.bellmanOptOpQSpace M.bellmanOptOpQSpace_contracting

/-- The Bellman-optimal Q-function obtained by transporting the Banach fixed
point back to the original action-value function space. -/
noncomputable def optimalQFixedPoint : M.ActionValueFn :=
  M.ofQSpace M.optimalQFixedPointQSpace

/-- The transported Banach fixed point is genuinely fixed by the Bellman
optimality operator. -/
lemma optimalQFixedPointQSpace_isFixedPt :
    Function.IsFixedPt M.bellmanOptOpQSpace M.optimalQFixedPointQSpace :=
  ContractingWith.fixedPoint_isFixedPt (f := M.bellmanOptOpQSpace)
    (hf := M.bellmanOptOpQSpace_contracting)

/-- The Banach fixed point is Bellman optimal. -/
lemma optimalQFixedPoint_isBellmanOptimalQ :
    M.isBellmanOptimalQ M.optimalQFixedPoint := by
  intro s a
  have hfix := M.optimalQFixedPointQSpace_isFixedPt
  have hcoord := congrArg (fun z : M.QSpace => z (s, a)) hfix.eq
  simpa [Function.IsFixedPt, optimalQFixedPoint, optimalQFixedPointQSpace,
    bellmanOptOpQSpace] using hcoord.symm

/-- The Bellman optimality operator has a fixed point. -/
lemma exists_bellmanOptimalQ_fixedPoint :
    ∃ Q, M.isBellmanOptimalQ Q := by
  exact ⟨M.optimalQFixedPoint, M.optimalQFixedPoint_isBellmanOptimalQ⟩

/-- Iterates of the transported Bellman optimality operator converge to the
Banach optimal fixed point. -/
lemma tendsto_iterate_optimalQFixedPointQSpace (x : M.QSpace) :
    Filter.Tendsto (fun n => M.bellmanOptOpQSpace^[n] x) Filter.atTop
      (nhds M.optimalQFixedPointQSpace) := by
  simpa [optimalQFixedPointQSpace] using
    (ContractingWith.tendsto_iterate_fixedPoint
      (f := M.bellmanOptOpQSpace)
      (hf := M.bellmanOptOpQSpace_contracting)
      x)

/-- A priori geometric convergence bound for iterates of the transported
Bellman optimality operator. -/
lemma apriori_dist_iterate_optimalQFixedPointQSpace_le
    (x : M.QSpace) (n : ℕ) :
    dist (M.bellmanOptOpQSpace^[n] x) M.optimalQFixedPointQSpace ≤
      dist x (M.bellmanOptOpQSpace x) * M.γ ^ n / (1 - M.γ) := by
  simpa [optimalQFixedPointQSpace] using
    (ContractingWith.apriori_dist_iterate_fixedPoint_le
      (f := M.bellmanOptOpQSpace)
      (hf := M.bellmanOptOpQSpace_contracting)
      x n)

end FiniteMDP
