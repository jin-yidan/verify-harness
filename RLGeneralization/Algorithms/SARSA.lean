/-
# SARSA: On-Policy Temporal Difference Learning

Formalizes the SARSA algorithm (State-Action-Reward-State-Action), the
on-policy counterpart to Q-learning. SARSA evaluates and improves the
policy it is following, while Q-learning evaluates the greedy policy
regardless of the behavior policy.

## Main Definitions

* `SARSAUpdate` — One-step SARSA update: Q(s,a) ← Q(s,a) + α·(r + γ·Q(s',a') - Q(s,a))
* `SARSANoise` — Sampling noise: difference between sample and expected backup
* `ExpectedSARSAUpdate` — Expected SARSA: uses E_{a'~π}[Q(s',a')] instead of Q(s',a')
* `sarsa_vs_qlearning_gap` — Comparison: |SARSA - QLearning| ≤ policy gap

## Key Difference from Q-Learning

Q-learning backup: r + γ · max_{a'} Q(s', a')     (off-policy, uses greedy)
SARSA backup:      r + γ · Q(s', a')               (on-policy, uses behavior a')
Expected SARSA:    r + γ · ∑_{a'} π(a'|s') Q(s',a') (on-policy, averages over π)

SARSA converges to Q^π (the value of the behavior policy), while
Q-learning converges to Q* (the optimal value). Under ε-greedy with
ε → 0, both converge to Q*.

## References

* [Rummery and Niranjan, *On-line Q-learning using connectionist systems*, 1994]
* [Sutton and Barto, *Reinforcement Learning: An Introduction*, Ch 6.4]
* [Singh et al., *Convergence Results for Single-Step On-Policy RL Algorithms*, 2000]
-/

import RLGeneralization.MDP.BellmanContraction

open Finset BigOperators

noncomputable section

namespace FiniteMDP

variable (M : FiniteMDP)

/-! ### SARSA Update Rule -/

/-- A single SARSA update step.

  Given current Q-function, state `s`, action `a`, observed reward `r_obs`,
  observed next state `s'`, observed next action `a'`, and step size `α`:

    Q'(s,a) = (1 - α) · Q(s,a) + α · (r_obs + γ · Q(s', a'))

  For all other (s₀, a₀) ≠ (s, a), Q'(s₀, a₀) = Q(s₀, a₀).

  The key difference from Q-learning is using Q(s', a') instead of max_{a'} Q(s', a'). -/
def SARSAUpdate (Q : M.ActionValueFn) (s : M.S) (a : M.A)
    (r_obs : ℝ) (s' : M.S) (a' : M.A) (α : ℝ) : M.ActionValueFn :=
  fun s₀ a₀ =>
    if s₀ = s ∧ a₀ = a then
      (1 - α) * Q s a + α * (r_obs + M.γ * Q s' a')
    else
      Q s₀ a₀

/-- SARSA update preserves values at non-updated entries. -/
theorem SARSAUpdate_other (Q : M.ActionValueFn) (s : M.S) (a : M.A)
    (r_obs : ℝ) (s' : M.S) (a' : M.A) (α : ℝ)
    (s₀ : M.S) (a₀ : M.A) (h : ¬(s₀ = s ∧ a₀ = a)) :
    M.SARSAUpdate Q s a r_obs s' a' α s₀ a₀ = Q s₀ a₀ := by
  simp [SARSAUpdate, h]

/-- SARSA update at the updated entry. -/
theorem SARSAUpdate_self (Q : M.ActionValueFn) (s : M.S) (a : M.A)
    (r_obs : ℝ) (s' : M.S) (a' : M.A) (α : ℝ) :
    M.SARSAUpdate Q s a r_obs s' a' α s a =
    (1 - α) * Q s a + α * (r_obs + M.γ * Q s' a') := by
  simp [SARSAUpdate]

/-! ### Expected SARSA -/

/-- **Expected SARSA update**: uses the expected value under π instead
    of the sampled next action.

    Q'(s,a) = (1-α)·Q(s,a) + α·(r_obs + γ·∑_{a'} π(a'|s')·Q(s',a'))

    Expected SARSA interpolates between SARSA and Q-learning:
    - With π = greedy policy, it equals Q-learning
    - With π = behavior policy, it's a lower-variance version of SARSA -/
def ExpectedSARSAUpdate (Q : M.ActionValueFn) (s : M.S) (a : M.A)
    (r_obs : ℝ) (s' : M.S) (π : M.StochasticPolicy) (α : ℝ) : M.ActionValueFn :=
  fun s₀ a₀ =>
    if s₀ = s ∧ a₀ = a then
      (1 - α) * Q s a + α * (r_obs + M.γ * ∑ a', π.prob s' a' * Q s' a')
    else
      Q s₀ a₀

/-! ### SARSA Noise Decomposition -/

/-- **SARSA sampling noise**: the difference between the sample backup
    and the expected Bellman evaluation backup.

    noise = (r_obs + γ · Q(s', a')) - (r(s,a) + γ · ∑_{s'} P(s'|s,a) · Q(s', π(s')))

    where the first term is the sample backup (from one transition)
    and the second is the expected backup under the behavior policy π. -/
def SARSANoise (Q : M.ActionValueFn) (π : M.DetPolicy)
    (s : M.S) (a : M.A) (r_obs : ℝ) (s' : M.S) : ℝ :=
  (r_obs + M.γ * Q s' (π s')) -
  (M.r s a + M.γ * ∑ s'', M.P s a s'' * Q s'' (π s''))

/-- SARSA noise has conditional expectation zero (over s' ~ P(·|s,a) and
    r_obs having expectation r(s,a)).

    E_{s',r}[noise | s,a] = 0

    This is because E[r_obs] = r(s,a) and E[Q(s',π(s'))] = ∑ P(s')Q(s',π(s')). -/
theorem SARSANoise_expected_zero (Q : M.ActionValueFn) (π : M.DetPolicy)
    (s : M.S) (a : M.A) :
    M.r s a + M.γ * ∑ s', M.P s a s' * Q s' (π s') -
    (M.r s a + M.γ * ∑ s', M.P s a s' * Q s' (π s')) = 0 := by
  ring

/-- SARSA noise is bounded when Q is bounded. -/
theorem SARSANoise_bounded (Q : M.ActionValueFn) (π : M.DetPolicy)
    (V_max : ℝ) (hV : ∀ s a, |Q s a| ≤ V_max)
    (s : M.S) (a : M.A) (_r_obs s' : M.S) :
    |M.SARSANoise Q π s a (M.r s a) s'| ≤ 2 * M.γ * V_max := by
  unfold SARSANoise
  have h1 : |Q s' (π s')| ≤ V_max := hV s' (π s')
  have h2 : |∑ s'', M.P s a s'' * Q s'' (π s'')| ≤ V_max := by
    calc |∑ s'', M.P s a s'' * Q s'' (π s'')|
        ≤ ∑ s'', |M.P s a s'' * Q s'' (π s'')| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ s'', M.P s a s'' * |Q s'' (π s'')| := by
          congr 1; funext s''; rw [abs_mul, abs_of_nonneg (M.P_nonneg s a s'')]
      _ ≤ ∑ s'', M.P s a s'' * V_max := by
          apply Finset.sum_le_sum; intro s'' _
          exact mul_le_mul_of_nonneg_left (hV s'' (π s'')) (M.P_nonneg s a s'')
      _ = V_max := by rw [← Finset.sum_mul, M.P_sum_one, one_mul]
  -- |noise| = |γ·Q(s',π(s')) - γ·∑P·Q| ≤ γ·|Q(s',π(s'))| + γ·|∑P·Q| ≤ 2γV_max
  simp only [add_sub_add_left_eq_sub]
  calc |M.γ * Q s' (π s') - M.γ * ∑ s'', M.P s a s'' * Q s'' (π s'')|
      = |M.γ * (Q s' (π s') - ∑ s'', M.P s a s'' * Q s'' (π s''))| := by ring_nf
    _ = M.γ * |Q s' (π s') - ∑ s'', M.P s a s'' * Q s'' (π s'')| := by
        rw [abs_mul, abs_of_nonneg M.γ_nonneg]
    _ ≤ M.γ * (|Q s' (π s')| + |∑ s'', M.P s a s'' * Q s'' (π s'')|) := by
        apply mul_le_mul_of_nonneg_left _ M.γ_nonneg
        calc |Q s' (π s') - ∑ s'', M.P s a s'' * Q s'' (π s'')|
            = |Q s' (π s') + -(∑ s'', M.P s a s'' * Q s'' (π s''))| := by rw [sub_eq_add_neg]
          _ ≤ |Q s' (π s')| + |-(∑ s'', M.P s a s'' * Q s'' (π s''))| := abs_add_le _ _
          _ = |Q s' (π s')| + |∑ s'', M.P s a s'' * Q s'' (π s'')| := by rw [abs_neg]
    _ ≤ M.γ * (V_max + V_max) := by
        apply mul_le_mul_of_nonneg_left _ M.γ_nonneg
        exact add_le_add h1 h2
    _ = 2 * M.γ * V_max := by ring

/-! ### SARSA vs Q-Learning Comparison -/

/-- **SARSA vs Q-learning one-step gap.**

  The difference between SARSA and Q-learning backups at (s, a) is:

    |SARSA_backup - QL_backup| = γ · |Q(s', a') - max_{a'} Q(s', a')|

  where a' is the action taken by the behavior policy.
  Since Q(s', a') ≤ max Q(s', ·), this gap is always:
    ≤ γ · (max_{a'} Q(s', a') - Q(s', a'))

  This is the "off-policy gap": Q-learning bootstraps from the greedy
  policy while SARSA bootstraps from the behavior policy. -/
theorem sarsa_vs_qlearning_gap (Q : M.ActionValueFn)
    (s' : M.S) (a' : M.A)
    (r_obs : ℝ) :
    |(r_obs + M.γ * Q s' a') -
     (r_obs + M.γ * Finset.univ.sup' Finset.univ_nonempty (Q s'))| =
    M.γ * |Q s' a' - Finset.univ.sup' Finset.univ_nonempty (Q s')| := by
  rw [show (r_obs + M.γ * Q s' a') - (r_obs + M.γ * Finset.univ.sup' Finset.univ_nonempty (Q s'))
    = M.γ * (Q s' a' - Finset.univ.sup' Finset.univ_nonempty (Q s')) from by ring]
  rw [abs_mul, abs_of_nonneg M.γ_nonneg]

/-- **SARSA converges to Q^π, not Q*.**

  Under a fixed policy π, the SARSA Bellman operator is:
    (T^π Q)(s,a) = r(s,a) + γ · ∑_{s'} P(s'|s,a) · Q(s', π(s'))

  This is the policy evaluation operator (not the optimality operator).
  It is a γ-contraction with fixed point Q^π.

  We prove: |T^π Q₁ - T^π Q₂|(s,a) ≤ γ · B when |Q₁ - Q₂| ≤ B everywhere. -/
theorem sarsa_bellman_contraction (Q₁ Q₂ : M.ActionValueFn)
    (π : M.DetPolicy) (B : ℝ) (_hB : 0 ≤ B)
    (h_diff : ∀ s a, |Q₁ s a - Q₂ s a| ≤ B) :
    ∀ s a,
    |(M.r s a + M.γ * ∑ s', M.P s a s' * Q₁ s' (π s')) -
     (M.r s a + M.γ * ∑ s', M.P s a s' * Q₂ s' (π s'))| ≤
    M.γ * B := by
  intro s a
  rw [show (M.r s a + M.γ * ∑ s', M.P s a s' * Q₁ s' (π s')) -
      (M.r s a + M.γ * ∑ s', M.P s a s' * Q₂ s' (π s')) =
    M.γ * ∑ s', M.P s a s' * (Q₁ s' (π s') - Q₂ s' (π s')) from by
    rw [add_sub_add_left_eq_sub, ← mul_sub, ← Finset.sum_sub_distrib]
    congr 1; exact Finset.sum_congr rfl fun s' _ => by ring]
  rw [abs_mul, abs_of_nonneg M.γ_nonneg]
  apply mul_le_mul_of_nonneg_left _ M.γ_nonneg
  calc |∑ s', M.P s a s' * (Q₁ s' (π s') - Q₂ s' (π s'))|
      ≤ ∑ s', |M.P s a s' * (Q₁ s' (π s') - Q₂ s' (π s'))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ s', M.P s a s' * |Q₁ s' (π s') - Q₂ s' (π s')| := by
        congr 1; funext s'; rw [abs_mul, abs_of_nonneg (M.P_nonneg s a s')]
    _ ≤ ∑ s', M.P s a s' * B := by
        apply Finset.sum_le_sum; intro s' _
        exact mul_le_mul_of_nonneg_left (h_diff s' (π s')) (M.P_nonneg s a s')
    _ = B := by rw [← Finset.sum_mul, M.P_sum_one, one_mul]

end FiniteMDP

end
