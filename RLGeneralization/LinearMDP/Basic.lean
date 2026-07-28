/-
# Linear MDPs and Function Approximation

Formalizes linear MDP structure and the resulting linearity of the
optimal action-value function.

A Linear MDP has transitions P_h(s'|s,a) = <phi(s,a), mu_h(s')> for
known features phi : S x A -> R^d and unknown measures mu_h.
The key consequence is that Q* is linear in phi.

## Main Results

* `LinearMDP` - Linear MDP structure
* `optQ_linear` - Optimal Q is linear in the feature map
* `ucbvi_lin_regret` - UCBVI-Lin regret target

## References

* [Agarwal et al., *RL: Theory and Algorithms*]
-/

import RLGeneralization.MDP.FiniteHorizon
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset BigOperators

noncomputable section

namespace FiniteHorizonMDP

variable (M : FiniteHorizonMDP)

/-! ### Linear MDP Structure -/

/-- A linear MDP: a finite-horizon MDP with feature dimension `d`,
    feature map `phi`, and measure vectors `mu` such that
    `P_h(s'|s,a) = sum_i phi(s,a)_i * mu_h(s')_i`. -/
structure LinearMDP where
  /-- Feature dimension -/
  d : ℕ
  /-- Feature map phi : S x A -> R^d -/
  phi : M.S → M.A → Fin d → ℝ
  /-- Unknown signed measure vectors mu_h : S -> R^d -/
  mu : Fin M.H → M.S → Fin d → ℝ
  /-- Reward weight vectors theta_h ∈ R^d: r_h(s,a) = <theta_h, phi(s,a)> -/
  theta : Fin M.H → Fin d → ℝ
  /-- Transition decomposition: P_h(s'|s,a) = <phi(s,a), mu_h(s')> -/
  transition_decomp : ∀ (h : Fin M.H) (s : M.S) (a : M.A) (s' : M.S),
    M.P h s a s' = ∑ i : Fin d, phi s a i * mu h s' i
  /-- Reward linearity: r_h(s,a) = <theta_h, phi(s,a)> -/
  reward_linear : ∀ (h : Fin M.H) (s : M.S) (a : M.A),
    M.r h s a = ∑ i : Fin d, theta h i * phi s a i
  /-- Feature norm bound: ||phi(s,a)||_2 <= 1 -/
  phi_norm_le : ∀ (s : M.S) (a : M.A),
    ∑ i : Fin d, (phi s a i) ^ 2 ≤ 1

/-! ### Optimal Q Is Linear In Features -/

/-- In a linear MDP, the optimal Q-function is linear in the features.

  In a linear MDP, the optimal Q-function is linear in the features:
  there exist weight vectors w*_h in R^d such that
  Q*_h(s,a) = <w*_h, phi(s,a)> for all s, a, h.

  Stated as existence of weights at each backward induction step. -/
theorem optQ_linear (lmdp : M.LinearMDP) :
    ∀ (k : ℕ) (hk : k ≤ M.H),
    ∃ w : Fin lmdp.d → ℝ,
    ∀ (s : M.S) (a : M.A),
    M.backwardQ k hk s a = ∑ i : Fin lmdp.d, w i * lmdp.phi s a i := by
  intro k
  induction k with
  | zero =>
    intro hk
    exact ⟨fun _ => 0, fun s a => by simp [backwardQ]⟩
  | succ n _ih =>
    intro hk
    -- Weight: w'_i = θ_{h,i} + ∑_{s'} μ_h(s')_i · V_k(s')
    -- where V_k(s') = max_{a'} Q_k(s', a') and h = H - n - 1
    refine ⟨fun i => lmdp.theta ⟨M.H - n - 1, by omega⟩ i +
      ∑ s' : M.S, lmdp.mu ⟨M.H - n - 1, by omega⟩ s' i *
        Finset.univ.sup' Finset.univ_nonempty
          (fun a' => M.backwardQ n (by omega) s' a'),
      fun s a => ?_⟩
    -- Unfold backwardQ(n+1) = r_h + ∑ P_h · V_k
    simp only [backwardQ]
    -- Rewrite r using reward linearity: r_h(s,a) = ∑ θ_i · φ_i(s,a)
    rw [lmdp.reward_linear ⟨M.H - n - 1, by omega⟩ s a]
    -- Rewrite P using transition decomposition: P_h(s'|s,a) = ∑ φ_i(s,a) · μ_i(s')
    simp_rw [lmdp.transition_decomp ⟨M.H - n - 1, by omega⟩ s a]
    -- Distribute: (∑_i f_i) · g = ∑_i f_i · g
    simp_rw [Finset.sum_mul]
    -- Swap sums: ∑_{s'} ∑_i → ∑_i ∑_{s'}
    rw [Finset.sum_comm]
    -- Factor: φ_i · μ_i(s') · V(s') = φ_i · (μ_i(s') · V(s')),
    -- then ∑_{s'} φ_i · f(s') = φ_i · ∑_{s'} f(s')
    simp_rw [mul_assoc, ← Finset.mul_sum]
    -- Combine: ∑ a_i + ∑ b_i = ∑ (a_i + b_i)
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring

-- The UCBVI-Lin regret wrapper is in `LinearMDP/Regret.lean`.
-- (conditional: takes per-episode bonus + elliptical potential hypotheses).

end FiniteHorizonMDP

end
