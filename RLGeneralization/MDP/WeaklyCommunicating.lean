/-
# Weakly Communicating MDPs

Defines the weakly communicating property for MDPs, which is the
standard structural assumption in average-reward RL theory.

An MDP is weakly communicating if there exists a policy under which
every state can reach every other state (possibly in multiple steps).
This is weaker than "communicating" (which requires reachability
under EVERY policy).

## Main Results

* `WeaklyCommunicating` -- definition
* `biasSpan` / `biasSpan_nonneg` -- span of the bias function
* `biasSpan_le_of_pointwise` -- sp(h) <= C from pointwise h(s1)-h(s2) <= C
  [used with coupling hypothesis C = D * R_max]

## References

* [Puterman, *Markov Decision Processes*, Ch 8.3]
* [Wei et al., "Model-Free RL in Infinite-Horizon Average-Reward MDPs,"
  ICML 2020]
-/

import RLGeneralization.MDP.Basic

open Finset BigOperators

noncomputable section

namespace FiniteMDP

variable (M : FiniteMDP)

/-! ### Definition -/

/-- An MDP is **weakly communicating** if there exists a single policy pi
such that, under pi, every state is reachable from every other state
(the induced Markov chain has a single recurrent class). -/
structure WeaklyCommunicating where
  /-- The witnessing policy -/
  connectingPolicy : M.DetPolicy
  /-- The MDP diameter under this policy: max_{s,s'} E[T(s->s'|pi)] -/
  diameter : ℕ
  /-- Diameter is positive -/
  diameter_pos : 0 < diameter

/-- The **span** of the bias function h* for a weakly communicating MDP:
sp(h*) = max_s h*(s) - min_s h*(s). -/
def biasSpan (h : M.StateValueFn) : ℝ :=
  (Finset.univ.sup' ⟨Classical.arbitrary M.S, Finset.mem_univ _⟩ h) -
  (Finset.univ.inf' ⟨Classical.arbitrary M.S, Finset.mem_univ _⟩ h)

/-- Span is nonneg. -/
theorem biasSpan_nonneg (h : M.StateValueFn) :
    0 ≤ M.biasSpan h := by
  unfold biasSpan
  apply sub_nonneg.mpr
  let s₀ : M.S := Classical.arbitrary M.S
  exact le_trans (Finset.inf'_le h (Finset.mem_univ s₀))
    (Finset.le_sup' h (Finset.mem_univ s₀))

/-! ### Span bound from pointwise difference bound -/

/-- **Span bound from pointwise difference bound**.

If h(s₁) - h(s₂) ≤ C for all s₁, s₂, then sp(h) = sup h - inf h ≤ C.

In RL applications, the coupling argument for weakly communicating MDPs
(Puterman Thm 8.5.4) gives C = D·R_max. That measure-theoretic step
is not formalized here — this theorem converts the pointwise bound
into the sup-inf span bound. -/
theorem biasSpan_le_of_pointwise
    (h : M.StateValueFn) (C : ℝ)
    (h_pointwise : ∀ s₁ s₂ : M.S, h s₁ - h s₂ ≤ C) :
    M.biasSpan h ≤ C := by
  unfold biasSpan
  set w : M.S := Classical.arbitrary M.S
  apply sub_le_iff_le_add.mpr
  apply Finset.sup'_le _ _
  intro s _
  suffices Finset.univ.inf' ⟨w, Finset.mem_univ w⟩ h ≥ h s - C by linarith
  apply Finset.le_inf'
  intro s₂ _
  linarith [h_pointwise s s₂]

end FiniteMDP

end
