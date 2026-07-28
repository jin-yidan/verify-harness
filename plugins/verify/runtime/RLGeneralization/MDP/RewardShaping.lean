/-
# Reward Shaping: Potential-Based Shaping Theory

Formalizes the theory of potential-based reward shaping
(Ng, Hazan, Russell 1999), which shows that adding a potential-based
shaping term to the reward preserves optimal policies.

Given a potential function Φ : S → ℝ, the shaped reward is:
  r'(s, a, s') = r(s, a) + γ · Φ(s') - Φ(s)

The key result is that the shaped value function satisfies
  V'(s) = V(s) - Φ(s)
so optimal policies are invariant under potential-based shaping.

## Main Results

* `PotentialFunction` — type alias for potential functions Φ : S → ℝ
* `shapedReward` — the shaped reward r'(s, a, s') = r(s,a) + γΦ(s') - Φ(s)
* `shapedExpReward` — expected shaped reward from (s, a)
* `shaped_bellman_shift` — if V satisfies Bellman, then V - Φ satisfies
  Bellman for the shaped reward (the main theorem)
* `shaped_optimal_policy_invariant` — optimal policy is preserved
* `shaping_preserves_advantage` — advantage function is invariant
* `shaped_reward_bounded` — shaped reward boundedness

## References

* [Ng, Hazan, Russell, "Policy Invariance Under Reward Transformations:
  Theory and Application to Reward Shaping," ICML 1999]
* [Agarwal et al., *RL: Theory and Algorithms*][agarwal2026]
-/

import RLGeneralization.MDP.BellmanContraction

open Finset BigOperators

noncomputable section

namespace FiniteMDP

variable (M : FiniteMDP)

/-! ### Potential Functions -/

/-- A potential function Φ : S → ℝ used for reward shaping. -/
def PotentialFunction := M.S → ℝ

/-! ### Shaped Reward -/

/-- The shaped reward for a single transition (s, a, s'):
    r'(s, a, s') = r(s, a) + γ · Φ(s') - Φ(s). -/
def shapedReward (Φ : M.PotentialFunction) (s : M.S) (a : M.A) (s' : M.S) : ℝ :=
  M.r s a + M.γ * Φ s' - Φ s

/-- The expected shaped immediate reward from (s, a), integrating over next states:
    ∑_{s'} P(s'|s,a) · r'(s, a, s')
  = r(s, a) + γ · ∑_{s'} P(s'|s,a) · Φ(s') - Φ(s). -/
def shapedExpReward (Φ : M.PotentialFunction) (s : M.S) (a : M.A) : ℝ :=
  M.r s a + M.γ * ∑ s', M.P s a s' * Φ s' - Φ s

/-- The expected shaped reward equals the sum of shaped transition rewards
    weighted by transition probabilities. -/
theorem shapedExpReward_eq_sum (Φ : M.PotentialFunction) (s : M.S) (a : M.A) :
    M.shapedExpReward Φ s a =
    ∑ s', M.P s a s' * M.shapedReward Φ s a s' := by
  simp only [shapedExpReward, shapedReward]
  -- Both sides equal r(s,a) + γ·∑P·Φ' - Φ(s)
  -- Rewrite RHS: ∑ P·(r + γΦ' - Φ) into separated sums
  have h_expand : ∀ s', M.P s a s' * (M.r s a + M.γ * Φ s' - Φ s) =
      M.P s a s' * M.r s a + M.γ * (M.P s a s' * Φ s') -
        M.P s a s' * Φ s := by
    intro s'; ring
  simp_rw [h_expand, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hsum_r : ∑ s', M.P s a s' * M.r s a = M.r s a := by
    rw [← Finset.sum_mul, M.P_sum_one, one_mul]
  have hsum_Φ : ∑ s', M.P s a s' * Φ s = Φ s := by
    rw [← Finset.sum_mul, M.P_sum_one, one_mul]
  have hsum_γ : ∑ s', M.γ * (M.P s a s' * Φ s') =
      M.γ * ∑ s', M.P s a s' * Φ s' :=
    (Finset.mul_sum _ _ _).symm
  rw [hsum_r, hsum_γ, hsum_Φ]

/-! ### Deterministic Bellman Equation -/

/-- V satisfies the Bellman equation for deterministic policy π:
    V(s) = r(s, π(s)) + γ · ∑_{s'} P(s'|s, π(s)) · V(s'). -/
def isDetValueOf (V : M.StateValueFn) (π : M.DetPolicy) : Prop :=
  ∀ s, V s = M.r s (π s) + M.γ * ∑ s', M.P s (π s) s' * V s'

/-- V satisfies the Bellman equation for a deterministic policy π
    under the shaped reward:
    V(s) = shapedExpReward(s, π(s)) + γ · ∑_{s'} P(s'|s, π(s)) · V(s'). -/
def isDetShapedValueOf (Φ : M.PotentialFunction) (V : M.StateValueFn)
    (π : M.DetPolicy) : Prop :=
  ∀ s, V s = M.shapedExpReward Φ s (π s) +
    M.γ * ∑ s', M.P s (π s) s' * V s'

/-! ### Main Theorem: Shaped Bellman Shift -/

/-- **Shaped Bellman shift** (Ng, Hazan, Russell 1999).

  If V satisfies the Bellman equation for policy π under the original
  reward, then V' := V - Φ satisfies the Bellman equation for the
  same policy π under the shaped reward.

  This is the core algebraic identity behind reward shaping:
    shapedExpReward(s,a) + γ · ∑ P(s'|s,a) · V'(s')
  = [r(s,a) + γ·∑P·Φ(s') - Φ(s)] + γ · ∑ P(s'|s,a) · [V(s') - Φ(s')]
  = r(s,a) + γ·∑P·V(s') - Φ(s)
  = V(s) - Φ(s)
  = V'(s). -/
theorem shaped_bellman_shift (Φ : M.PotentialFunction)
    (V : M.StateValueFn) (π : M.DetPolicy)
    (hV : M.isDetValueOf V π) :
    M.isDetShapedValueOf Φ (fun s => V s - Φ s) π := by
  intro s
  simp only [shapedExpReward]
  -- LHS = V s - Φ s
  -- RHS = (r(s,π(s)) + γ·∑P·Φ(s') - Φ(s)) + γ·∑P·(V(s') - Φ(s'))
  -- Show RHS = r(s,π(s)) + γ·∑P·V(s') - Φ(s) = V(s) - Φ(s) = LHS
  have hbell := hV s
  -- Rewrite the next-value sum: ∑ P·(V - Φ) = ∑ P·V - ∑ P·Φ
  have hsum_split : ∑ s', M.P s (π s) s' * (V s' - Φ s') =
      (∑ s', M.P s (π s) s' * V s') -
      (∑ s', M.P s (π s) s' * Φ s') := by
    rw [← Finset.sum_sub_distrib]
    congr 1; ext s'; ring
  rw [hsum_split]
  linarith

/-! ### Optimal Policy Invariance -/

/-- **Optimal policy invariance under potential-based shaping**.

  If action a* maximizes r(s,a) + γ·∑P(s'|s,a)·V(s') over actions,
  then a* also maximizes the shaped version
  shapedExpReward(s,a) + γ·∑P(s'|s,a)·V'(s') over actions,
  because both expressions differ by the constant -Φ(s) which
  does not depend on the action.

  More precisely: the Q-value under shaped rewards equals the
  original Q-value minus Φ(s), so the argmax over actions is the same. -/
theorem shaped_optimal_policy_invariant (Φ : M.PotentialFunction)
    (V : M.StateValueFn) (s : M.S) (a : M.A) :
    M.shapedExpReward Φ s a + M.γ * ∑ s', M.P s a s' * (V s' - Φ s') =
    (M.r s a + M.γ * ∑ s', M.P s a s' * V s') - Φ s := by
  simp only [shapedExpReward]
  have hsum_split : ∑ s', M.P s a s' * (V s' - Φ s') =
      (∑ s', M.P s a s' * V s') -
      (∑ s', M.P s a s' * Φ s') := by
    rw [← Finset.sum_sub_distrib]
    congr 1; ext s'; ring
  rw [hsum_split]
  ring

/-- The action that maximizes the original Q-value also maximizes the
    shaped Q-value, since both differ by the constant -Φ(s).

    Formally: for all actions a,
      Q_original(s, a*) ≥ Q_original(s, a)
    implies
      Q_shaped(s, a*) ≥ Q_shaped(s, a). -/
theorem shaped_greedy_preserved (Φ : M.PotentialFunction)
    (V : M.StateValueFn) (s : M.S) (a_star a : M.A)
    (h_greedy : M.r s a_star + M.γ * ∑ s', M.P s a_star s' * V s' ≥
                M.r s a + M.γ * ∑ s', M.P s a s' * V s') :
    M.shapedExpReward Φ s a_star +
      M.γ * ∑ s', M.P s a_star s' * (V s' - Φ s') ≥
    M.shapedExpReward Φ s a +
      M.γ * ∑ s', M.P s a s' * (V s' - Φ s') := by
  rw [M.shaped_optimal_policy_invariant Φ V s a_star,
      M.shaped_optimal_policy_invariant Φ V s a]
  linarith

/-! ### Advantage Invariance -/

/-- The one-step Q-value under shaped rewards for a deterministic policy:
    Q'(s, a) = shapedExpReward(s, a) + γ · ∑ P(s'|s,a) · V'(s'). -/
def shapedQValue (Φ : M.PotentialFunction) (V : M.StateValueFn)
    (s : M.S) (a : M.A) : ℝ :=
  M.shapedExpReward Φ s a + M.γ * ∑ s', M.P s a s' * (V s' - Φ s')

/-- The original one-step Q-value:
    Q(s, a) = r(s, a) + γ · ∑ P(s'|s,a) · V(s'). -/
def originalQValue (V : M.StateValueFn) (s : M.S) (a : M.A) : ℝ :=
  M.r s a + M.γ * ∑ s', M.P s a s' * V s'

/-- The shaped Q-value equals the original Q-value minus Φ(s). -/
theorem shapedQ_eq_originalQ_sub (Φ : M.PotentialFunction)
    (V : M.StateValueFn) (s : M.S) (a : M.A) :
    M.shapedQValue Φ V s a = M.originalQValue V s a - Φ s := by
  simp only [shapedQValue, originalQValue]
  exact M.shaped_optimal_policy_invariant Φ V s a

/-- **Advantage invariance under potential-based shaping**.

  The advantage A(s,a) = Q(s,a) - V(s) is invariant under
  potential-based reward shaping:
    A'(s,a) = Q'(s,a) - V'(s) = (Q(s,a) - Φ(s)) - (V(s) - Φ(s)) = A(s,a).

  This means shaping does not distort the relative preference
  among actions; it only shifts value functions by a state-dependent
  constant. -/
theorem shaping_preserves_advantage (Φ : M.PotentialFunction)
    (V : M.StateValueFn) (s : M.S) (a : M.A) :
    M.shapedQValue Φ V s a - (V s - Φ s) =
    M.originalQValue V s a - V s := by
  rw [M.shapedQ_eq_originalQ_sub]
  ring

/-! ### Shaped Reward Boundedness -/

/-- **Shaped reward boundedness**.

  If the original reward satisfies |r(s,a)| ≤ R_max and the potential
  function satisfies |Φ(s)| ≤ B for all states, then the shaped
  expected reward satisfies:
    |shapedExpReward(s, a)| ≤ R_max + (1 + γ) · B.

  This is useful for bounding value functions under shaped rewards. -/
theorem shaped_reward_bounded (Φ : M.PotentialFunction) (B : ℝ)
    (hΦ : ∀ s, |Φ s| ≤ B) (s : M.S) (a : M.A) :
    |M.shapedExpReward Φ s a| ≤ M.R_max + (1 + M.γ) * B := by
  simp only [shapedExpReward]
  -- |r(s,a) + γ·∑P·Φ(s') - Φ(s)| ≤ |r(s,a)| + γ·|∑P·Φ(s')| + |Φ(s)|
  -- ≤ R_max + γ·B + B = R_max + (1+γ)·B
  have hr := M.r_le_R_max s a
  have hΦs := hΦ s
  -- Bound |∑ P·Φ(s')| ≤ B using weighted sum bound
  have hPΦ : |∑ s', M.P s a s' * Φ s'| ≤ B :=
    abs_weighted_sum_le_bound _ _ B (M.P_nonneg s a) (M.P_sum_one s a) hΦ
  -- Now combine using triangle inequality
  calc |M.r s a + M.γ * ∑ s', M.P s a s' * Φ s' - Φ s|
      ≤ |M.r s a| + |M.γ * ∑ s', M.P s a s' * Φ s'| + |Φ s| := by
        calc |M.r s a + M.γ * ∑ s', M.P s a s' * Φ s' - Φ s|
            = |(M.r s a + M.γ * ∑ s', M.P s a s' * Φ s') + (-Φ s)| := by ring_nf
          _ ≤ |M.r s a + M.γ * ∑ s', M.P s a s' * Φ s'| + |-(Φ s)| :=
              abs_add_le _ _
          _ = |M.r s a + M.γ * ∑ s', M.P s a s' * Φ s'| + |Φ s| := by
              rw [abs_neg]
          _ ≤ (|M.r s a| + |M.γ * ∑ s', M.P s a s' * Φ s'|) + |Φ s| := by
              linarith [abs_add_le (M.r s a) (M.γ * ∑ s', M.P s a s' * Φ s')]
    _ ≤ M.R_max + M.γ * B + B := by
        have hγ_term : |M.γ * ∑ s', M.P s a s' * Φ s'| ≤ M.γ * B := by
          rw [abs_mul, abs_of_nonneg M.γ_nonneg]
          exact mul_le_mul_of_nonneg_left hPΦ M.γ_nonneg
        linarith [hΦs]
    _ = M.R_max + (1 + M.γ) * B := by ring

/-- Shaped reward boundedness for single transitions.
    If |r(s,a)| ≤ R_max and |Φ(s)| ≤ B, then
    |r'(s,a,s')| ≤ R_max + (1 + γ) · B. -/
theorem shaped_transition_reward_bounded (Φ : M.PotentialFunction) (B : ℝ)
    (hΦ : ∀ s, |Φ s| ≤ B) (s : M.S) (a : M.A) (s' : M.S) :
    |M.shapedReward Φ s a s'| ≤ M.R_max + (1 + M.γ) * B := by
  simp only [shapedReward]
  have hr := M.r_le_R_max s a
  have hΦs := hΦ s
  have hΦs' := hΦ s'
  calc |M.r s a + M.γ * Φ s' - Φ s|
      ≤ |M.r s a| + |M.γ * Φ s'| + |Φ s| := by
        calc |M.r s a + M.γ * Φ s' - Φ s|
            = |(M.r s a + M.γ * Φ s') + (-Φ s)| := by ring_nf
          _ ≤ |M.r s a + M.γ * Φ s'| + |-(Φ s)| := abs_add_le _ _
          _ = |M.r s a + M.γ * Φ s'| + |Φ s| := by rw [abs_neg]
          _ ≤ (|M.r s a| + |M.γ * Φ s'|) + |Φ s| := by
              linarith [abs_add_le (M.r s a) (M.γ * Φ s')]
    _ ≤ M.R_max + M.γ * B + B := by
        have : |M.γ * Φ s'| ≤ M.γ * B := by
          rw [abs_mul, abs_of_nonneg M.γ_nonneg]
          exact mul_le_mul_of_nonneg_left hΦs' M.γ_nonneg
        linarith
    _ = M.R_max + (1 + M.γ) * B := by ring

end FiniteMDP

end
