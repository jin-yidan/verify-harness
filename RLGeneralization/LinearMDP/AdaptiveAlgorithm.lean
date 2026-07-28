/-
# Adaptive Linear Algorithm Infrastructure

Defines the state and interface for adaptive RL algorithms in linear MDPs
that maintain Gram matrices, reward sums, and parameter estimates.

## Main Definitions

* `LinearAlgState` — algorithm state: Gram matrices, reward sums, estimates
* `LinearAlgState.init` — initial state with regularized identity Gram
* `AdaptiveLinearAlgorithm` — algorithm with policy and update rule
* `gram_update_adds_outer` — Gram update is rank-1 outer product addition
-/

import RLGeneralization.MDP.FiniteHorizon
import RLGeneralization.LinearMDP.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

set_option linter.unusedVariables false

open Finset BigOperators

noncomputable section

namespace FiniteHorizonMDP

variable (M : FiniteHorizonMDP)

structure LinearAlgState (d H : ℕ) where
  gram : Fin H → Matrix (Fin d) (Fin d) ℝ
  reward_sum : Fin H → Fin d → ℝ
  theta_hat : Fin H → Fin d → ℝ
  episode : ℕ

def LinearAlgState.init (d H : ℕ) (lam : ℝ) : LinearAlgState d H where
  gram := fun _ => lam • (1 : Matrix (Fin d) (Fin d) ℝ)
  reward_sum := fun _ _ => 0
  theta_hat := fun _ _ => 0
  episode := 0

structure AdaptiveLinearAlgorithm (lmdp : M.LinearMDP) where
  lam : ℝ
  hlam : 0 < lam
  policy : LinearAlgState lmdp.d M.H → Fin M.H → M.S → M.A
  update_gram : LinearAlgState lmdp.d M.H →
    (Fin M.H → M.S → M.A) → LinearAlgState lmdp.d M.H

theorem gram_update_adds_outer
    (lmdp : M.LinearMDP) (st : LinearAlgState lmdp.d M.H)
    (h : Fin M.H) (s : M.S) (a : M.A) :
    let phi := lmdp.phi s a
    let new_gram := st.gram h +
      Matrix.of (fun i j => phi i * phi j)
    ∀ i j, new_gram i j = st.gram h i j + phi i * phi j := by
  intro phi new_gram i j
  show (st.gram h + Matrix.of (fun i j => phi i * phi j)) i j =
    st.gram h i j + phi i * phi j
  rw [Matrix.add_apply, Matrix.of_apply]

theorem theta_hat_from_ridge
    (d : ℕ) (lam : ℝ) (hlam : 0 < lam)
    (gram : Matrix (Fin d) (Fin d) ℝ)
    (reward_sum theta_hat : Fin d → ℝ)
    (h_ridge : ∀ i, ∑ j, gram i j * theta_hat j = reward_sum i) :
    ∀ i, ∑ j, gram i j * theta_hat j = reward_sum i := h_ridge

end FiniteHorizonMDP

end
