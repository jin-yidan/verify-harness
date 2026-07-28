/-
# Component-Wise Value Bounds

Formalizes a component-wise comparison between optimal values in the
true and approximate models using resolvent identities.

## Main Results

* `value_gap_upper` - Upper bound direction for the component-wise comparison:
    V*(s) - V̂*(s) ≤ resolvent of γ(P-P̂)V*
    (using π* as the comparison policy)

## Key Idea

The simulation inequality (SimulationLemma.lean) gives an
absolute value bound: |V^π_M - V^π_{M̂}| ≤ bound.
The one-sided resolvent comparison gives a component-wise bound that is
tighter because it uses the resolvent's sign-preserving property.

## References

* [Agarwal et al., *RL: Theory and Algorithms*]
-/

import RLGeneralization.MDP.Resolvent
import RLGeneralization.MDP.BanachFixedPoint

open Finset BigOperators

noncomputable section

namespace FiniteMDP

variable (M : FiniteMDP)

/-! ### Upper Bound Direction -/

/-- **Fixed-policy resolvent bound**.

  For a fixed policy pi evaluated in both M and M̂ (with same
  rewards), the value gap satisfies the resolvent equation:

    V^pi_M(s) - V^pi_{M̂}(s)
      = gamma * sum_a pi(a|s) sum_{s'} (P - P̂)(s'|s,a) V^pi_M(s')
        + gamma * sum_a pi(a|s) sum_{s'} P̂(s'|s,a) (V^pi_M(s') - V^pi_{M̂}(s'))

  This is the fixed-point identity underlying the component-wise
  comparison. The one-sided resolvent bound then gives
  V^pi_M - V^pi_{M̂} <= epsilon_trans/(1-gamma).

  **Caveat**: This proves the fixed-policy resolvent equation only.
  The full optimal-value comparison additionally uses optimality in M̂ (V̂* >= V̂^{pi*})
  to compare optimal values; that step is in `optimal_value_gap_upper_bound`. -/
theorem value_gap_resolvent (M_hat : M.ApproxMDP)
    (π : M.StochasticPolicy)
    (V_M V_Mhat : M.StateValueFn)
    (hV_M : M.isValueOf V_M π)
    (hV_Mhat : ∀ s, V_Mhat s =
      (∑ a, π.prob s a * M_hat.r_hat s a) +
      M.γ * (∑ a, π.prob s a *
        ∑ s', M_hat.P_hat s a s' * V_Mhat s'))
    -- Same rewards (standard tabular setup assumes deterministic rewards)
    (h_same_r : ∀ s a, M.r s a = M_hat.r_hat s a) :
    ∀ s, V_M s - V_Mhat s =
      (∑ a, π.prob s a * M.γ *
        ∑ s', (M.P s a s' - M_hat.P_hat s a s') * V_M s') +
      M.γ * (∑ a, π.prob s a *
        ∑ s', M_hat.P_hat s a s' * (V_M s' - V_Mhat s')) := by
  intro s
  rw [hV_M s, hV_Mhat s]
  unfold expectedReward expectedNextValue
  -- After expanding, rewards cancel (h_same_r), leaving
  -- γ(P-P̂)V_M + γP̂(V_M - V_Mhat)
  simp_rw [h_same_r]
  -- After h_same_r: reward terms are identical, so they cancel.
  -- Remains: γ(∑π∑PV_M) - γ(∑π∑P̂V_Mhat)
  -- = γ∑π∑(P-P̂)V_M + γ∑π∑P̂(V_M-V_Mhat)
  -- Split each P·V_M - P̂·V_Mhat = (P-P̂)V_M + P̂(V_M-V_Mhat)
  have hsplit : ∀ (a : M.A) (s' : M.S),
      M.P s a s' * V_M s' - M_hat.P_hat s a s' * V_Mhat s' =
      (M.P s a s' - M_hat.P_hat s a s') * V_M s' +
      M_hat.P_hat s a s' * (V_M s' - V_Mhat s') :=
    fun _ _ => by ring
  -- The inner sums distribute
  have hinner : ∀ a,
      ∑ s', M.P s a s' * V_M s' -
      ∑ s', M_hat.P_hat s a s' * V_Mhat s' =
      ∑ s', (M.P s a s' - M_hat.P_hat s a s') * V_M s' +
      ∑ s', M_hat.P_hat s a s' * (V_M s' - V_Mhat s') := by
    intro a
    rw [← Finset.sum_sub_distrib]
    simp_rw [hsplit, Finset.sum_add_distrib]
  -- The outer sum distributes
  have houter :
      ∑ a, π.prob s a * (∑ s', M.P s a s' * V_M s') -
      ∑ a, π.prob s a * (∑ s', M_hat.P_hat s a s' * V_Mhat s') =
      ∑ a, π.prob s a *
        ∑ s', (M.P s a s' - M_hat.P_hat s a s') * V_M s' +
      ∑ a, π.prob s a *
        ∑ s', M_hat.P_hat s a s' * (V_M s' - V_Mhat s') := by
    rw [← Finset.sum_sub_distrib]
    simp_rw [← mul_sub, hinner, mul_add, Finset.sum_add_distrib]
  -- Factor γ and rearrange to match goal
  have hfact : ∀ a, π.prob s a * M.γ *
      ∑ s', (M.P s a s' - M_hat.P_hat s a s') * V_M s' =
      M.γ * (π.prob s a *
        ∑ s', (M.P s a s' - M_hat.P_hat s a s') * V_M s') :=
    fun a => by ring
  simp_rw [hfact, ← Finset.mul_sum (a := M.γ)]
  -- Goal: r + γ∑π∑PV_M - (r + γ∑π∑P̂V_Mhat)
  --     = γ∑π∑(P-P̂)V_M + γ∑π∑P̂(V_M-V_Mhat)
  -- From houter: ∑π∑PV_M - ∑π∑P̂V_Mhat = houter_RHS
  -- Factor γ from both sides
  -- (r + γA) - (r + γB) = γ(A-B) = γ·houter_RHS
  have hmul : M.γ * (∑ a, π.prob s a *
      ∑ s', M.P s a s' * V_M s') -
      M.γ * (∑ a, π.prob s a *
        ∑ s', M_hat.P_hat s a s' * V_Mhat s') =
      M.γ * (∑ a, π.prob s a *
        ∑ s', (M.P s a s' - M_hat.P_hat s a s') * V_M s' +
        ∑ a, π.prob s a *
          ∑ s', M_hat.P_hat s a s' * (V_M s' - V_Mhat s')) := by
    rw [← mul_sub, houter]
  linarith [hmul]

/-- **Component-wise upper bound** via the resolvent identity.

  If the per-state transition error (P-P̂)V^π_M is bounded:
    ∑_a π(a|s) ∑_{s'} (P-P̂)(s'|s,a) V_M(s') ≤ ε_trans for all s
  then (using the one-sided resolvent bound):
    V^π_M(s) - V^π_{M̂}(s) ≤ γε_trans / (1-γ) -/
theorem value_gap_upper_bound (M_hat : M.ApproxMDP)
    (π : M.StochasticPolicy)
    (V_M V_Mhat : M.StateValueFn)
    (hV_M : M.isValueOf V_M π)
    (hV_Mhat : ∀ s, V_Mhat s =
      (∑ a, π.prob s a * M_hat.r_hat s a) +
      M.γ * (∑ a, π.prob s a *
        ∑ s', M_hat.P_hat s a s' * V_Mhat s'))
    (h_same_r : ∀ s a, M.r s a = M_hat.r_hat s a)
    -- Transition error bound
    (ε_trans : ℝ)
    (h_trans : ∀ s, ∑ a, π.prob s a * M.γ *
      ∑ s', (M.P s a s' - M_hat.P_hat s a s') * V_M s' ≤
      ε_trans) :
    ∀ s, V_M s - V_Mhat s ≤ ε_trans / (1 - M.γ) := by
  -- W = b + γP̂^πW where b ≤ ε_trans. Contraction: sup W ≤ ε_trans/(1-γ).
  set W := fun s => V_M s - V_Mhat s
  set D := Finset.univ.sup' Finset.univ_nonempty W
  have h1g : (0 : ℝ) < 1 - M.γ := by linarith [M.γ_lt_one]
  have hgap := M.value_gap_resolvent M_hat π V_M V_Mhat
    hV_M hV_Mhat h_same_r
  -- W(s) ≤ ε_trans + γD for each s (from resolvent equation)
  have hstep : ∀ s, W s ≤ ε_trans + M.γ * D := by
    intro s
    have := hgap s -- W s = driving + γ∑P̂W
    change W s ≤ _
    have hP_hat_avg : ∑ a, π.prob s a *
        ∑ s', M_hat.P_hat s a s' * W s' ≤ D := by
      exact weighted_sum_le_max (π.prob s) _
        (π.prob_nonneg s) (π.prob_sum_one s) |>.trans
        (Finset.sup'_le _ _ fun a _ =>
          weighted_sum_le_max (M_hat.P_hat s a) W
            (M_hat.P_hat_nonneg s a) (M_hat.P_hat_sum_one s a))
    linarith [h_trans s,
      mul_le_mul_of_nonneg_left hP_hat_avg M.γ_nonneg]
  -- D ≤ ε_trans + γD, so D ≤ ε_trans/(1-γ)
  have hsup : D ≤ ε_trans + M.γ * D :=
    Finset.sup'_le _ _ (fun s _ => hstep s)
  have hD : D ≤ ε_trans / (1 - M.γ) := by
    rw [le_div_iff₀ h1g]; nlinarith
  intro s
  exact le_trans (Finset.le_sup' W (Finset.mem_univ s)) hD

/-! ### Optimal Value Gap: Upper Bound -/

/-- **Upper bound for the optimal-value gap**.

  If π* is any policy, V̂* is the value of an optimal policy
  in M̂ with V̂*(s) ≥ V̂^{π*}(s) for all s, then:
    V*(s) - V̂*(s) ≤ V*(s) - V̂^{π*}(s) ≤ ε_trans/(1-γ)

  This combines:
  1. V̂* ≥ V̂^{π*} (optimality in M̂)
  2. value_gap_upper_bound for the fixed policy π* -/
theorem optimal_value_gap_upper_bound (M_hat : M.ApproxMDP)
    (π : M.StochasticPolicy)
    (V_M V_Mhat V_hat_star : M.StateValueFn)
    (hV_M : M.isValueOf V_M π)
    (hV_Mhat : ∀ s, V_Mhat s =
      (∑ a, π.prob s a * M_hat.r_hat s a) +
      M.γ * (∑ a, π.prob s a *
        ∑ s', M_hat.P_hat s a s' * V_Mhat s'))
    (h_same_r : ∀ s a, M.r s a = M_hat.r_hat s a)
    -- V̂* ≥ V̂^{π} (π̂* is at least as good as π in M̂)
    (h_opt : ∀ s, V_hat_star s ≥ V_Mhat s)
    (ε_trans : ℝ)
    (h_trans : ∀ s, ∑ a, π.prob s a * M.γ *
      ∑ s', (M.P s a s' - M_hat.P_hat s a s') * V_M s' ≤
      ε_trans) :
    ∀ s, V_M s - V_hat_star s ≤ ε_trans / (1 - M.γ) := by
  intro s
  -- V_M - V̂* ≤ V_M - V̂^π (since V̂* ≥ V̂^π)
  have h1 : V_M s - V_hat_star s ≤ V_M s - V_Mhat s := by
    linarith [h_opt s]
  -- V_M - V̂^π ≤ ε_trans/(1-γ) (value_gap_upper_bound)
  have h2 := M.value_gap_upper_bound M_hat π V_M V_Mhat
    hV_M hV_Mhat h_same_r ε_trans h_trans s
  linarith

/-! ### Lower Bound Direction -/

/-- **Lower bound direction for the value comparison**.

  For a policy π̂ that is optimal in M̂, and the value V̂^{π̂}
  evaluated in both M and M̂, with same rewards:

    V_M^{π̂}(s) - V̂^{π̂}(s) ≥ -ε_trans/(1-γ)

  equivalently: V̂^{π̂}(s) - V_M^{π̂}(s) ≤ ε_trans/(1-γ)

  This is the lower bound direction, using the same resolvent
  argument as the upper bound but with reversed signs. -/
theorem policy_value_gap_lower_bound (M_hat : M.ApproxMDP)
    (π : M.StochasticPolicy)
    (V_M V_Mhat : M.StateValueFn)
    (hV_M : M.isValueOf V_M π)
    (hV_Mhat : ∀ s, V_Mhat s =
      (∑ a, π.prob s a * M_hat.r_hat s a) +
      M.γ * (∑ a, π.prob s a *
        ∑ s', M_hat.P_hat s a s' * V_Mhat s'))
    (h_same_r : ∀ s a, M.r s a = M_hat.r_hat s a)
    (ε_trans : ℝ)
    -- Lower bound on the driving term (note: opposite sign)
    (h_trans : ∀ s, -(ε_trans) ≤
      ∑ a, π.prob s a * M.γ *
        ∑ s', (M.P s a s' - M_hat.P_hat s a s') * V_M s') :
    ∀ s, -(ε_trans / (1 - M.γ)) ≤ V_M s - V_Mhat s := by
  -- Same contraction argument as value_gap_upper_bound but
  -- applied to V_Mhat - V_M with negated driving term.
  -- Requires negating sums: ∑P̂(V_M-V_Mhat) = -∑P̂(V_Mhat-V_M)
  intro s
  -- From value_gap_resolvent: V_M - V_Mhat = driving + γP̂(V_M-V_Mhat)
  -- Negating: V_Mhat - V_M = -driving + γP̂(V_Mhat-V_M)
  -- If -driving ≤ ε_trans (i.e., driving ≥ -ε_trans), then
  -- V_Mhat - V_M ≤ ε_trans/(1-γ)
  -- Apply value_gap_upper_bound with swapped roles
  -- Use: V_Mhat - V_M ≤ sup(V_Mhat - V_M) ≤ ε_trans/(1-γ)
  set W := fun s => V_Mhat s - V_M s
  -- W satisfies: W(s) ≤ ε + γ·sup W (contraction)
  -- To show: -ε/(1-γ) ≤ V_M s - V_Mhat s, i.e., W s ≤ ε/(1-γ)
  suffices hW : W s ≤ ε_trans / (1 - M.γ) by linarith
  -- Contraction argument on W
  set D := Finset.univ.sup' Finset.univ_nonempty W
  have h1g : (0 : ℝ) < 1 - M.γ := by linarith [M.γ_lt_one]
  have hgap := M.value_gap_resolvent M_hat π V_M V_Mhat
    hV_M hV_Mhat h_same_r
  -- For each s': W(s') ≤ ε_trans + γD
  have hstep : ∀ s', W s' ≤ ε_trans + M.γ * D := by
    intro s'
    -- V_M(s') - V_Mhat(s') = driving(s') + γ∑P̂(V_M-V_Mhat)(s')
    have hres := hgap s'
    -- W(s') = V_Mhat(s') - V_M(s') = -driving(s') - γ∑P̂(V_M-V_Mhat)
    -- = -driving(s') + γ∑P̂·W  (since V_M-V_Mhat = -W)
    -- -driving ≤ ε_trans (from h_trans: driving ≥ -ε_trans)
    -- ∑P̂·W ≤ D (weighted avg ≤ max)
    have hP_avg : ∑ a, π.prob s' a *
        ∑ s'', M_hat.P_hat s' a s'' * W s'' ≤ D :=
      weighted_sum_le_max (π.prob s') _
        (π.prob_nonneg s') (π.prob_sum_one s') |>.trans
        (Finset.sup'_le _ _ fun a _ =>
          weighted_sum_le_max (M_hat.P_hat s' a) W
            (M_hat.P_hat_nonneg s' a) (M_hat.P_hat_sum_one s' a))
    -- W = -driving + γ P̂ W, and driving = V_M-V_Mhat gap driving term
    -- From hres: V_M - V_Mhat = driving + γ∑P̂(V_M-V_Mhat)
    -- W = -(V_M-V_Mhat) = -driving - γ∑P̂(V_M-V_Mhat)
    -- ∑P̂(V_M-V_Mhat) = ∑P̂(-W) = -∑P̂W ... but linarith doesn't see this
    -- Use: V_Mhat-V_M = -(V_M-V_Mhat) and hres
    -- So W(s') = -(driving(s') + γ∑P̂(V_M-V_Mhat)(s'))
    -- = -driving(s') + γ∑P̂W(s') (KEY: ∑P̂(-W) = -∑P̂W by linearity)
    have hlin : ∑ a, π.prob s' a *
        ∑ s'', M_hat.P_hat s' a s'' * (V_M s'' - V_Mhat s'') =
        -(∑ a, π.prob s' a *
          ∑ s'', M_hat.P_hat s' a s'' * W s'') := by
      have : ∀ a, π.prob s' a *
          ∑ s'', M_hat.P_hat s' a s'' * (V_M s'' - V_Mhat s'') =
          -(π.prob s' a *
            ∑ s'', M_hat.P_hat s' a s'' * W s'') := by
        intro a; simp only [W]
        have : ∀ s'', M_hat.P_hat s' a s'' * (V_M s'' - V_Mhat s'') =
            -(M_hat.P_hat s' a s'' * (V_Mhat s'' - V_M s'')) :=
          fun s'' => by ring
        simp_rw [this, Finset.sum_neg_distrib, mul_neg]
      simp_rw [this, ← Finset.sum_neg_distrib]
    -- W(s') = -(V_M - V_Mhat) = -(driving + γ∑P̂(V_M-V_Mhat))
    -- = -driving + γ∑P̂W (using hlin)
    have hW_eq : W s' = -(∑ a, π.prob s' a * M.γ *
        ∑ s'', (M.P s' a s'' - M_hat.P_hat s' a s'') * V_M s'') +
        M.γ * (∑ a, π.prob s' a *
          ∑ s'', M_hat.P_hat s' a s'' * W s'') := by
      have := hres
      rw [hlin] at this
      linarith
    linarith [h_trans s',
      mul_le_mul_of_nonneg_left hP_avg M.γ_nonneg]
  have hsup : D ≤ ε_trans + M.γ * D :=
    Finset.sup'_le _ _ (fun s _ => hstep s)
  have hD : D ≤ ε_trans / (1 - M.γ) := by
    rw [le_div_iff₀ h1g]; nlinarith
  exact le_trans (Finset.le_sup' W (Finset.mem_univ s)) hD

/-! ### Two-Sided Optimal Value Comparison -/

/-- **Two-sided optimal value comparison**.

    The underlying Q-function resolvent comparison has the form
    `Q* - Q̂* ≤ γ(I - γP̂^{π*})⁻¹(P - P̂)V*`. This theorem is a
    **state-value corollary**: given two MDPs with the same rewards and
    supplied optimality comparisons, it proves the scalar bound
    `|V*_M(s) - V*_M̂(s)| ≤ ε_trans/(1-γ)`.

    The proof combines `optimal_value_gap_upper_bound` and `policy_value_gap_lower_bound` with
    policy-optimality hypotheses `h_opt_M` and `h_opt_Mhat`. The
    transition-value driving-term bound `ε_trans` must hold for both
    the upper direction (using π_M) and the lower direction (using π̂). -/
theorem optimal_value_comparison (M_hat : M.ApproxMDP)
    -- Optimal policy in M with value V_star_M
    (π_M : M.StochasticPolicy) (V_star_M : M.StateValueFn)
    (hV_star_M : M.isValueOf V_star_M π_M)
    -- V^{π_M} evaluated in M̂
    (V_Mhat_piM : M.StateValueFn)
    (hV_Mhat_piM : ∀ s, V_Mhat_piM s =
      (∑ a, π_M.prob s a * M_hat.r_hat s a) +
      M.γ * (∑ a, π_M.prob s a *
        ∑ s', M_hat.P_hat s a s' * V_Mhat_piM s'))
    -- Optimal policy in M̂ with value V_star_Mhat
    (π_Mhat : M.StochasticPolicy) (V_star_Mhat : M.StateValueFn)
    (hV_star_Mhat : ∀ s, V_star_Mhat s =
      (∑ a, π_Mhat.prob s a * M_hat.r_hat s a) +
      M.γ * (∑ a, π_Mhat.prob s a *
        ∑ s', M_hat.P_hat s a s' * V_star_Mhat s'))
    -- V^{π̂} evaluated in M
    (V_M_piMhat : M.StateValueFn)
    (hV_M_piMhat : M.isValueOf V_M_piMhat π_Mhat)
    -- Same rewards
    (h_same_r : ∀ s a, M.r s a = M_hat.r_hat s a)
    -- Optimality: V*_M ≥ V^{π̂}_M and V*_M̂ ≥ V^{π_M}_{M̂}
    (h_opt_M : ∀ s, V_M_piMhat s ≤ V_star_M s)
    (h_opt_Mhat : ∀ s, V_Mhat_piM s ≤ V_star_Mhat s)
    -- Transition-value driving term bounds
    (ε_trans : ℝ)
    (h_upper : ∀ s, ∑ a, π_M.prob s a * M.γ *
      ∑ s', (M.P s a s' - M_hat.P_hat s a s') * V_star_M s' ≤
      ε_trans)
    (h_lower : ∀ s, -(ε_trans) ≤
      ∑ a, π_Mhat.prob s a * M.γ *
        ∑ s', (M.P s a s' - M_hat.P_hat s a s') *
          V_M_piMhat s') :
    ∀ s, |V_star_M s - V_star_Mhat s| ≤ ε_trans / (1 - M.γ) := by
  intro s
  rw [abs_le]
  constructor
  · -- Lower bound: V*_M - V*_M̂ ≥ -ε/(1-γ)
    -- V*_M ≥ V^{π̂}_M (optimality in M)
    -- V^{π̂}_M - V^{π̂}_{M̂} ≥ -ε/(1-γ) (policy_value_gap_lower_bound)
    -- V^{π̂}_{M̂} = V*_{M̂}
    have h_low := M.policy_value_gap_lower_bound M_hat π_Mhat V_M_piMhat
      V_star_Mhat hV_M_piMhat hV_star_Mhat h_same_r ε_trans h_lower s
    linarith [h_opt_M s]
  · -- Upper bound: V*_M - V*_M̂ ≤ ε/(1-γ)
    exact M.optimal_value_gap_upper_bound M_hat π_M V_star_M V_Mhat_piM
      V_star_Mhat hV_star_M hV_Mhat_piM h_same_r
      h_opt_Mhat ε_trans h_upper s

/-! ### Value Function Existence in Approximate Models

  The `hV_Mhat` hypothesis in the theorems above can be discharged
  using Banach's fixed point theorem, provided the approximate model's
  rewards are bounded.

  The construction is:
  1. Lift M̂ to a full `FiniteMDP` via `approxMDP_to_FiniteMDP`
  2. Apply `actionValueFixedPoint_isActionValueOf` to get Q̂
  3. Define V̂(s) = ∑_a π(a|s) Q̂(s,a)
  4. The Bellman equation for Q̂ implies V̂ satisfies `hV_Mhat`

  This makes the ComponentWise bounds fully self-contained modulo
  the bounded-reward assumption on M̂. -/

/-- **Existence of Bellman-consistent value functions in approximate models.**

  For any approximate MDP M̂ with bounded rewards and any stochastic
  policy π, there exists a value function V_Mhat satisfying the
  Bellman evaluation equation in M̂:

    V(s) = ∑_a π(a|s)·r̂(s,a) + γ·∑_a π(a|s)·∑_{s'} P̂(s'|s,a)·V(s')

  This discharges the `hV_Mhat` hypothesis in `value_gap_upper_bound`
  and related theorems. -/
theorem approxMDP_value_exists (M_hat : M.ApproxMDP)
    (h_r_bnd : ∃ R_max : ℝ, 0 < R_max ∧
      ∀ s a, |M_hat.r_hat s a| ≤ R_max)
    (π : M.StochasticPolicy) :
    ∃ V_Mhat : M.StateValueFn,
      ∀ s, V_Mhat s =
        (∑ a, π.prob s a * M_hat.r_hat s a) +
        M.γ * (∑ a, π.prob s a *
          ∑ s', M_hat.P_hat s a s' * V_Mhat s') := by
  -- Lift the approximate model to a full FiniteMDP
  let Mh : FiniteMDP := M.approxMDP_to_FiniteMDP M_hat h_r_bnd
  -- Transport π to the lifted model's policy type
  let pi_h : Mh.StochasticPolicy :=
    ⟨π.prob, π.prob_nonneg, π.prob_sum_one⟩
  -- Get the Banach fixed-point action-value function
  let Qh := Mh.actionValueFixedPoint pi_h
  have hQ : Mh.isActionValueOf Qh pi_h :=
    Mh.actionValueFixedPoint_isActionValueOf pi_h
  -- Define V(s) = ∑_a π(a|s) Q(s,a) as a named let
  let Vh : M.StateValueFn := fun s => ∑ a, π.prob s a * Qh s a
  -- Use Vh as the witness
  refine ⟨Vh, fun s => ?_⟩
  -- Bellman eq for Q: Q(s,a) = r̂(s,a) + γ·∑ P̂·Vh
  have hQ_eq : ∀ a, Qh s a = M_hat.r_hat s a +
      M.γ * ∑ s', M_hat.P_hat s a s' * Vh s' := fun a => hQ s a
  -- Vh(s) = ∑ π·Q = ∑ π·(r̂ + γ·∑P̂·Vh) = ∑ π·r̂ + γ·∑ π·∑P̂·Vh
  change Vh s = _
  -- Goal: ∑ π·Q = ∑ π·r̂ + γ·∑ π·∑P̂·Vh
  change ∑ a, π.prob s a * Qh s a =
    (∑ a, π.prob s a * M_hat.r_hat s a) +
    M.γ * (∑ a, π.prob s a * ∑ s', M_hat.P_hat s a s' * Vh s')
  calc ∑ a, π.prob s a * Qh s a
      = ∑ a, (π.prob s a * M_hat.r_hat s a +
          M.γ * (π.prob s a * ∑ s', M_hat.P_hat s a s' * Vh s')) :=
        Finset.sum_congr rfl (fun a _ => by rw [hQ_eq a]; ring)
    _ = (∑ a, π.prob s a * M_hat.r_hat s a) +
        ∑ a, M.γ * (π.prob s a * ∑ s', M_hat.P_hat s a s' * Vh s') :=
        Finset.sum_add_distrib
    _ = (∑ a, π.prob s a * M_hat.r_hat s a) +
        M.γ * ∑ a, π.prob s a * ∑ s', M_hat.P_hat s a s' * Vh s' := by
        congr 1; rw [← Finset.mul_sum]

end FiniteMDP

end
