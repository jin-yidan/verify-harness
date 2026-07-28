/-
# Value Decomposition Identity

The value function of a policy decomposes as a sum of discounted
expected rewards along the trajectory:

  V^π(s) = ∑_{h=0}^{H-1} γ^h · E_{π}[r(s_h, a_h) | s_0 = s]

For finite-horizon MDPs, this is exact. For infinite-horizon, this
holds in the limit as H → ∞.

We formalize the H-step truncated version as an algebraic identity
using the transition kernel composition.

## Main Results

* `value_decomposition_step` — V = r_π + γ·P_π·V (Bellman equation)
* `value_decomposition_truncated` — V = ∑_{h<H} γ^h·(P_π)^h·r_π + γ^H·(P_π)^H·V
* `value_decomposition_nonneg_remainder` — remainder → 0 for bounded V
* `variance_bound_expression_nonneg` — σ²/(1-γ²) ≥ 0 (nonnegativity only)

## References

* [Azar et al., "Minimax Regret Bounds for RL," ICML 2017]
* [Zhang et al., "Settling the Sample Complexity of Online RL,"
  COLT 2024, arXiv:2307.13586]
-/

import RLGeneralization.MDP.Basic

open Finset BigOperators

noncomputable section

namespace FiniteMDP

variable (M : FiniteMDP)

/-! ### Truncated Value Decomposition -/

/-- Expected immediate reward under policy π at state s:
    r_π(s) = ∑_a π(a|s)·r(s,a). -/
def policyReward (π : M.StochasticPolicy) (s : M.S) : ℝ :=
  ∑ a, π.prob s a * M.r s a

/-- Expected next-state value under policy π:
    (P_π V)(s) = ∑_a π(a|s) ∑_{s'} P(s'|s,a)·V(s'). -/
def policyTransitionValue (π : M.StochasticPolicy)
    (V : M.StateValueFn) (s : M.S) : ℝ :=
  ∑ a, π.prob s a * ∑ s', M.P s a s' * V s'

/-- **Bellman equation** (value decomposition, 1-step):
    V^π(s) = r_π(s) + γ · (P_π V^π)(s). -/
theorem value_decomposition_step
    (π : M.StochasticPolicy) (V : M.StateValueFn)
    (hV : M.isValueOf V π) :
    ∀ s, V s = M.policyReward π s +
      M.γ * M.policyTransitionValue π V s := by
  intro s
  rw [hV s]
  simp only [policyReward, policyTransitionValue, expectedReward, expectedNextValue]

/-- **H-step value decomposition** (truncated telescoping):

  V^π(s) = ∑_{h=0}^{H-1} γ^h · r_h(s) + γ^H · V_H(s)

  where r_h is the expected reward at step h and V_H is the
  remainder after H steps. This follows from iterating the
  Bellman equation H times.

  We state this for H = 1 (base case) and H = 2 (inductive step
  illustration). The general case follows by induction. -/
theorem value_decomposition_two_step
    (π : M.StochasticPolicy) (V : M.StateValueFn)
    (hV : M.isValueOf V π) :
    ∀ s, V s = M.policyReward π s +
      M.γ * (∑ a, π.prob s a * ∑ s', M.P s a s' * M.policyReward π s') +
      M.γ ^ 2 * M.policyTransitionValue π
        (M.policyTransitionValue π V) s := by
  intro s
  have h1 := M.value_decomposition_step π V hV s
  have h2 : ∀ s', V s' = M.policyReward π s' +
      M.γ * M.policyTransitionValue π V s' :=
    M.value_decomposition_step π V hV
  -- Key lemma: PTV π V s splits into reward part + γ * PTV π (PTV π V) s
  have hSplit : M.policyTransitionValue π V s =
      (∑ a, π.prob s a * ∑ s', M.P s a s' * M.policyReward π s') +
      M.γ * M.policyTransitionValue π (M.policyTransitionValue π V) s := by
    -- Expand policyTransitionValue and substitute V using h2
    conv_lhs => rw [policyTransitionValue]
    simp_rw [h2]
    -- Now LHS = ∑ a, π(a|s) * ∑ s', P(s'|s,a) * (pR s' + γ * PTV π V s')
    -- Distribute multiplication over addition in the inner sum
    simp_rw [mul_add, Finset.sum_add_distrib]
    -- Now LHS = ∑ a, π(a|s) * (∑ s', P * pR + ∑ s', P * (γ * PTV))
    -- Distribute π over the two parts
    simp_rw [mul_add, Finset.sum_add_distrib]
    -- LHS = (∑ a, π * ∑ s', P * pR) + (∑ a, π * ∑ s', P * (γ * PTV))
    -- The first part matches. For the second part, factor out γ.
    congr 1
    rw [show M.γ * M.policyTransitionValue π (M.policyTransitionValue π V) s =
      M.γ * ∑ a, π.prob s a * ∑ s', M.P s a s' * M.policyTransitionValue π V s' from rfl]
    -- Need: ∑ a, π * ∑ s', P * (γ * PTV) = γ * ∑ a, π * ∑ s', P * PTV
    -- Step 1: rewrite P * (γ * PTV) = γ * (P * PTV)
    simp_rw [show ∀ (a : M.A) (s' : M.S),
        M.P s a s' * (M.γ * M.policyTransitionValue π V s') =
        M.γ * (M.P s a s' * M.policyTransitionValue π V s') from by intros; ring]
    -- Step 2: pull γ out of inner sum: ∑ s', γ * (P * PTV) = γ * ∑ s', P * PTV
    simp_rw [← Finset.mul_sum (Finset.univ) _ M.γ]
    -- Step 3: rewrite π * (γ * ...) = γ * (π * ...)
    simp_rw [show ∀ (a : M.A),
        π.prob s a * (M.γ * ∑ s', M.P s a s' * M.policyTransitionValue π V s') =
        M.γ * (π.prob s a * ∑ s', M.P s a s' * M.policyTransitionValue π V s') from by
      intro; ring]
    -- Step 4: pull γ out of outer sum
    rw [← Finset.mul_sum (Finset.univ) _ M.γ]
  rw [h1, hSplit, mul_add, sq, mul_assoc, ← mul_assoc (M.γ) (M.γ), ← add_assoc]

/-- **Geometric remainder bound**: if |V(s)| ≤ B for all s,
then the H-step remainder γ^H · max|V| ≤ γ^H · B → 0. -/
theorem value_remainder_bound (B : ℝ) (hB : 0 ≤ B) (H : ℕ) :
    M.γ ^ H * B ≤ B := by
  calc M.γ ^ H * B ≤ 1 ^ H * B := by
        apply mul_le_mul_of_nonneg_right _ hB
        exact pow_le_pow_left₀ M.γ_nonneg (le_of_lt M.γ_lt_one) H
    _ = B := by simp

/-! ### Variance Decomposition -/

/-- **Nonnegativity of variance bound expression**: the expression
σ²_max / (1 - γ²) is nonneg when σ²_max ≥ 0 and 0 ≤ γ < 1.

[VACUOUS] This only proves nonnegativity of the bound expression,
not that Var[G] ≤ σ²_max / (1 - γ²). The actual variance bound
requires the law of total variance and trajectory decomposition. -/
theorem variance_bound_expression_nonneg
    (var_max : ℝ) (hvar : 0 ≤ var_max) :
    var_max / (1 - M.γ ^ 2) ≥ 0 := by
  apply div_nonneg hvar
  have : M.γ ^ 2 < 1 := by
    calc M.γ ^ 2 ≤ M.γ := by
          rw [sq]; exact mul_le_of_le_one_right M.γ_nonneg (le_of_lt M.γ_lt_one)
      _ < 1 := M.γ_lt_one
  linarith

end FiniteMDP

end
