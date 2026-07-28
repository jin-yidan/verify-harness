/-
# PAC Sample Complexity for Tabular MDPs

This file formalizes the deterministic reduction from model accuracy
to policy optimality, the key compositional step in PAC-RL theory.

## Main Results

* `empiricalTransition` - Empirical transition (requires N > 0)
* `empiricalTransition_nonneg` - Empirical transitions are nonneg
* `empiricalTransition_sum_one` - Empirical transitions sum to 1
* `model_based_comparison` - If model errors are bounded and π̂
  dominates a reference policy π_ref in M̂, then the value gap
  in M is bounded: V^{π_ref} - V^{π̂} ≤ 2(ε_R+γBε_T)/(1-γ).
  (This is a general comparison lemma; see docstring for the
  distinction from the full PAC optimality guarantee.)

## References

* [Azar, Munos, Kappen, *Sample Complexity of RL with Generative
  Model*][azar2012]
* [Kearns and Singh, *Near-Optimal RL in Polynomial Time*][kearns2002]
-/

import RLGeneralization.MDP.SimulationLemma

open Finset BigOperators

noncomputable section

namespace FiniteMDP

variable (M : FiniteMDP)

/-! ### Empirical Model Construction -/

/-- Empirical transition from N > 0 samples per (s,a).
    P̂(s'|s,a) = #{i : next_i = s'} / N.
    Requires N > 0 to avoid division by zero. -/
def empiricalTransition {N : ℕ} (_hN : 0 < N)
    (next_states : M.S → M.A → Fin N → M.S)
    (s : M.S) (a : M.A) (s' : M.S) : ℝ :=
  ((Finset.univ.filter
    (fun i => next_states s a i = s')).card : ℝ) / N

/-- Empirical reward from N > 0 samples per (s,a).
    Requires N > 0 to avoid division by zero. -/
def empiricalReward {N : ℕ} (_hN : 0 < N)
    (rewards : M.S → M.A → Fin N → ℝ)
    (s : M.S) (a : M.A) : ℝ :=
  (∑ i : Fin N, rewards s a i) / N

/-- Empirical transitions are nonnegative. -/
lemma empiricalTransition_nonneg {N : ℕ} (hN : 0 < N)
    (next_states : M.S → M.A → Fin N → M.S)
    (s : M.S) (a : M.A) (s' : M.S) :
    0 ≤ M.empiricalTransition hN next_states s a s' := by
  unfold empiricalTransition
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- Empirical transitions sum to 1. The filters by next-state
    partition the sample indices. -/
lemma empiricalTransition_sum_one {N : ℕ} (hN : 0 < N)
    (next_states : M.S → M.A → Fin N → M.S)
    (s : M.S) (a : M.A) :
    ∑ s', M.empiricalTransition hN next_states s a s' = 1 := by
  simp only [empiricalTransition]
  have hN_ne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  -- Step 1: Factor 1/N out of the sum
  conv_lhs => arg 2; ext s'; rw [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  -- Step 2: Show ∑ card(filter(= s')) = N
  have hsum : ∑ s' : M.S,
      ((Finset.univ.filter
        (fun i => next_states s a i = s')).card : ℝ) =
      (N : ℝ) := by
    have hfib := Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset (Fin N)))
      (t := (Finset.univ : Finset M.S))
      (f := next_states s a)
      (fun i _ => Finset.mem_univ _)
    simp only [Finset.card_univ, Fintype.card_fin] at hfib
    exact_mod_cast hfib.symm
  rw [hsum, mul_inv_cancel₀ hN_ne]

/-! ### Model-Based Comparison Lemma -/

/-- **Deterministic core of the model-based comparison bound**.

  If two MDPs M and M̂ have transition L1 error ≤ ε_T and reward
  error ≤ ε_R, and value functions in M̂ are bounded by B, then:

    V^{π_ref}_M(s) - V^{π̂}_M(s) ≤ 2(ε_R + γBε_T)/(1-γ)

  **Caveat**: This is the *deterministic* comparison core only.
  The hypothesis `h_opt` requires π̂ ≥ π_ref in M̂, but π_ref
  need not be the optimal policy in M. To recover the full
  model-based PAC statement, instantiate π_ref with π* (the optimal
  policy in M) and compose with the concentration layer. -/
theorem model_based_comparison (M_hat : M.ApproxMDP)
    (π_star π_hat : M.StochasticPolicy)
    -- Value functions in M
    (V_star V_hat_M : M.StateValueFn)
    (hV_star : M.isValueOf V_star π_star)
    (hV_hat_M : M.isValueOf V_hat_M π_hat)
    -- Value functions in M̂
    (V_star_a V_hat_a : M.StateValueFn)
    (hV_star_a : ∀ s, V_star_a s =
      (∑ a, π_star.prob s a * M_hat.r_hat s a) +
      M.γ * (∑ a, π_star.prob s a *
        ∑ s', M_hat.P_hat s a s' * V_star_a s'))
    (hV_hat_a : ∀ s, V_hat_a s =
      (∑ a, π_hat.prob s a * M_hat.r_hat s a) +
      M.γ * (∑ a, π_hat.prob s a *
        ∑ s', M_hat.P_hat s a s' * V_hat_a s'))
    -- π̂ is at least as good as π* in M̂
    (h_opt : ∀ s, V_hat_a s ≥ V_star_a s)
    -- Bounds on approximate value functions
    (B : ℝ) (hB : 0 ≤ B)
    (hVsa_bnd : ∀ s, |V_star_a s| ≤ B)
    (hVha_bnd : ∀ s, |V_hat_a s| ≤ B)
    -- Model error bounds
    (ε_R : ℝ) (hε_R : M.rewardError M_hat ≤ ε_R)
    (ε_T : ℝ) (hε_T : M.transitionError M_hat ≤ ε_T) :
    ∀ s, V_star s - V_hat_M s ≤
      2 * (ε_R + M.γ * B * ε_T) / (1 - M.γ) := by
  intro s
  set Δ := (ε_R + M.γ * B * ε_T) / (1 - M.γ)
  -- 1. Simulation lemma for π*: |V* - V*_a| ≤ Δ
  have h1 : |V_star s - V_star_a s| ≤ Δ :=
    M.simulation_lemma M_hat π_star V_star V_star_a
      hV_star hV_star_a B hB hVsa_bnd
      ε_R hε_R ε_T hε_T s
  -- 2. Simulation lemma for π̂: |V^hat_M - V^hat_a| ≤ Δ
  have h3 : |V_hat_M s - V_hat_a s| ≤ Δ :=
    M.simulation_lemma M_hat π_hat V_hat_M V_hat_a
      hV_hat_M hV_hat_a B hB hVha_bnd
      ε_R hε_R ε_T hε_T s
  -- Extract one-sided bounds
  have h1' : V_star s - V_star_a s ≤ Δ :=
    le_trans (le_abs_self _) h1
  have h2' : V_star_a s ≤ V_hat_a s := h_opt s
  have h3' : V_hat_a s - V_hat_M s ≤ Δ := by
    have := neg_abs_le (V_hat_M s - V_hat_a s)
    linarith [h3]
  -- Combine: V* - V^hat ≤ Δ + Δ = 2Δ
  have h_le : V_star s - V_hat_M s ≤ Δ + Δ := by linarith
  calc V_star s - V_hat_M s
      ≤ Δ + Δ := h_le
    _ = 2 * Δ := by ring
    _ = 2 * ((ε_R + M.γ * B * ε_T) / (1 - M.γ)) := rfl
    _ = 2 * (ε_R + M.γ * B * ε_T) / (1 - M.γ) := by
        rw [mul_div_assoc]

/-! ### Sample Complexity from Transition Error -/

/-- **Pointwise-error form of the model-based comparison bound**.

  If the approximate transition satisfies a pointwise error bound
  |P̂(s'|s,a) - P(s'|s,a)| ≤ ε₀ for all (s,a,s'), and the reward
  error is |r̂(s,a) - r(s,a)| ≤ ε_R, then the value gap satisfies:

    V^{π_ref}(s) - V^{π̂}(s) ≤ 2(ε_R + γB|S|ε₀)/(1-γ)

  **Caveat**: This is purely deterministic -- it converts pointwise
  transition errors to L1 error via |S|ε₀ and applies
  `model_based_comparison`. The probabilistic layer (Hoeffding
  giving ε₀ ~ sqrt(1/N)) is in `pac_from_concentration`. -/
theorem sample_complexity_from_transition_error
    (M_hat_P : M.S → M.A → M.S → ℝ)
    (M_hat_r : M.S → M.A → ℝ)
    -- P̂ is a valid transition kernel
    (hP_nonneg : ∀ s a s', 0 ≤ M_hat_P s a s')
    (hP_sum : ∀ s a, ∑ s', M_hat_P s a s' = 1)
    -- Pointwise transition error bound
    (ε₀ : ℝ) (_hε₀ : 0 ≤ ε₀)
    (h_pw : ∀ s a s', |M.P s a s' - M_hat_P s a s'| ≤ ε₀)
    -- Reward error bound
    (ε_R : ℝ) (hε_R : ∀ s a, |M.r s a - M_hat_r s a| ≤ ε_R)
    -- Policies
    (π_ref π_hat : M.StochasticPolicy)
    -- Value functions in M
    (V_ref V_hat_M : M.StateValueFn)
    (hV_ref : M.isValueOf V_ref π_ref)
    (hV_hat_M : M.isValueOf V_hat_M π_hat)
    -- Value functions in M̂
    (V_ref_a V_hat_a : M.StateValueFn)
    (hV_ref_a : ∀ s, V_ref_a s =
      (∑ a, π_ref.prob s a * M_hat_r s a) +
      M.γ * (∑ a, π_ref.prob s a *
        ∑ s', M_hat_P s a s' * V_ref_a s'))
    (hV_hat_a : ∀ s, V_hat_a s =
      (∑ a, π_hat.prob s a * M_hat_r s a) +
      M.γ * (∑ a, π_hat.prob s a *
        ∑ s', M_hat_P s a s' * V_hat_a s'))
    -- π̂ dominates π_ref in M̂
    (h_opt : ∀ s, V_hat_a s ≥ V_ref_a s)
    -- Value bound in M̂
    (B : ℝ) (hB : 0 ≤ B)
    (hVra_bnd : ∀ s, |V_ref_a s| ≤ B)
    (hVha_bnd : ∀ s, |V_hat_a s| ≤ B) :
    ∀ s, V_ref s - V_hat_M s ≤
      2 * (ε_R + M.γ * B * (↑(Fintype.card M.S) * ε₀)) / (1 - M.γ) := by
  -- Step 1: Construct the approximate MDP
  set M_hat : M.ApproxMDP := {
    P_hat := M_hat_P
    r_hat := M_hat_r
    P_hat_nonneg := hP_nonneg
    P_hat_sum_one := hP_sum
  }
  -- Step 2: Bound the L1 transition error: ∑_{s'} |P - P̂| ≤ |S|·ε₀
  have h_l1 : M.transitionError M_hat ≤ ↑(Fintype.card M.S) * ε₀ := by
    simp only [transitionError]
    apply Finset.sup'_le; intro s _
    apply Finset.sup'_le; intro a _
    calc ∑ s', |M.P s a s' - M_hat_P s a s'|
        ≤ ∑ _s' : M.S, ε₀ :=
          Finset.sum_le_sum (fun s' _ => h_pw s a s')
      _ = Fintype.card M.S * ε₀ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- Step 3: Bound the reward error
  have h_rew : M.rewardError M_hat ≤ ε_R := by
    simp only [rewardError]
    apply Finset.sup'_le; intro s _
    apply Finset.sup'_le; intro a _
    exact hε_R s a
  -- Step 4: Apply model_based_comparison
  exact M.model_based_comparison M_hat π_ref π_hat
    V_ref V_hat_M hV_ref hV_hat_M
    V_ref_a V_hat_a hV_ref_a hV_hat_a
    h_opt B hB hVra_bnd hVha_bnd
    ε_R h_rew (↑(Fintype.card M.S) * ε₀) h_l1

/-! ### Crude Value Bounds -/

/-- **Approximate MDP value bound**.
    If V̂ satisfies the Bellman equation in M̂ with rewards bounded by R_max,
    then |V̂(s)| ≤ R_max/(1-γ).
    This is the same contraction argument as `value_bounded_by_Vmax`,
    but applied to the approximate MDP's Bellman equation. -/
lemma approx_value_bounded
    (M_hat : M.ApproxMDP)
    (π : M.StochasticPolicy)
    (V_Mhat : M.StateValueFn)
    (hV_Mhat : ∀ s, V_Mhat s =
      (∑ a, π.prob s a * M_hat.r_hat s a) +
      M.γ * (∑ a, π.prob s a *
        ∑ s', M_hat.P_hat s a s' * V_Mhat s'))
    (R : ℝ) (_hR : 0 ≤ R)
    (h_rew_bnd : ∀ s a, |M_hat.r_hat s a| ≤ R) :
    ∀ s, |V_Mhat s| ≤ R / (1 - M.γ) := by
  -- Contraction argument: |V̂(s)| ≤ R + γ·sup|V̂|, so sup|V̂| ≤ R/(1-γ)
  set D := M.supNormV V_Mhat
  have h1g : (0 : ℝ) < 1 - M.γ := by linarith [M.γ_lt_one]
  have hstep : ∀ s, |V_Mhat s| ≤ R + M.γ * D := by
    intro s
    rw [hV_Mhat s]
    calc |(∑ a, π.prob s a * M_hat.r_hat s a) +
          M.γ * (∑ a, π.prob s a *
            ∑ s', M_hat.P_hat s a s' * V_Mhat s')|
        ≤ |∑ a, π.prob s a * M_hat.r_hat s a| +
          |M.γ * (∑ a, π.prob s a *
            ∑ s', M_hat.P_hat s a s' * V_Mhat s')| :=
          abs_add_le _ _
      _ ≤ R + M.γ * D := by
          apply add_le_add
          · apply abs_weighted_sum_le_bound _ _ R
              (π.prob_nonneg s) (π.prob_sum_one s)
            intro a; exact h_rew_bnd s a
          · rw [abs_mul, abs_of_nonneg M.γ_nonneg]
            apply mul_le_mul_of_nonneg_left _ M.γ_nonneg
            apply abs_weighted_sum_le_bound _ _ D
              (π.prob_nonneg s) (π.prob_sum_one s)
            intro a
            apply abs_weighted_sum_le_bound _ _ D
              (M_hat.P_hat_nonneg s a) (M_hat.P_hat_sum_one s a)
            intro s'
            exact Finset.le_sup' (fun s => |V_Mhat s|)
              (Finset.mem_univ s')
  have hsup : D ≤ R + M.γ * D :=
    Finset.sup'_le _ _ (fun s _ => hstep s)
  have hD : D ≤ R / (1 - M.γ) := by
    rw [le_div_iff₀ h1g]; nlinarith
  intro s
  exact le_trans
    (Finset.le_sup' (fun s => |V_Mhat s|) (Finset.mem_univ s)) hD

/-- **Single-policy crude value bound**.

  If M̂ has the same rewards as M and transition L1 error
  max_{s,a} ||P(.|s,a) - P_hat(.|s,a)||_1 <= epsilon_T, then
  for any policy pi:

    |V^pi_M(s) - V^pi_{M_hat}(s)| <= gamma * R_max * epsilon_T / (1-gamma)^2

  The proof chains the simulation lemma with B = R_max/(1-gamma)
  and epsilon_R = 0 (same rewards), yielding the characteristic
  1/(1-gamma)^2 scaling.

  **Caveat**: This is the deterministic single-policy bound. The
  full optimality-gap version (with factor 2) is in
  `optimality_gap_from_transition_error`. -/
theorem crude_value_bound_from_transition_error
    (M_hat : M.ApproxMDP)
    (π : M.StochasticPolicy)
    (V_M V_Mhat : M.StateValueFn)
    (hV_M : M.isValueOf V_M π)
    (hV_Mhat : ∀ s, V_Mhat s =
      (∑ a, π.prob s a * M_hat.r_hat s a) +
      M.γ * (∑ a, π.prob s a *
        ∑ s', M_hat.P_hat s a s' * V_Mhat s'))
    -- Same rewards (deterministic rewards, as in the standard tabular setup)
    (h_same_r : ∀ s a, M.r s a = M_hat.r_hat s a)
    -- Transition error bound
    (ε_T : ℝ) (hε_T : M.transitionError M_hat ≤ ε_T) :
    ∀ s, |V_M s - V_Mhat s| ≤
      M.γ * M.R_max * ε_T / (1 - M.γ) ^ 2 := by
  -- Step 1: The M̂ value function is bounded by V_max = R_max/(1-γ)
  have h_rew_bnd : ∀ s a, |M_hat.r_hat s a| ≤ M.R_max := by
    intro s a; rw [← h_same_r]; exact M.r_le_R_max s a
  have hV_bnd := M.approx_value_bounded M_hat π V_Mhat hV_Mhat
    M.R_max (le_of_lt M.R_max_pos) h_rew_bnd
  -- hV_bnd : ∀ s, |V_Mhat s| ≤ R_max/(1-γ) = V_max
  -- Step 2: Reward error is 0 (same rewards)
  have h_rew_err : M.rewardError M_hat ≤ 0 := by
    simp only [rewardError]
    apply Finset.sup'_le; intro s _
    apply Finset.sup'_le; intro a _
    rw [h_same_r s a, sub_self, abs_zero]
  -- Step 3: Apply simulation_lemma with B = V_max
  have h_sim := M.simulation_lemma M_hat π V_M V_Mhat
    hV_M hV_Mhat (M.R_max / (1 - M.γ))
    (le_of_lt M.V_max_pos) hV_bnd
    0 h_rew_err ε_T hε_T
  -- h_sim : |V_M s - V_Mhat s| ≤ (0 + γ·(R_max/(1-γ))·ε_T)/(1-γ)
  -- Step 4: Simplify to γ·R_max·ε_T/(1-γ)²
  intro s
  have h1g : (0 : ℝ) < 1 - M.γ := by linarith [M.γ_lt_one]
  calc |V_M s - V_Mhat s|
      ≤ (0 + M.γ * (M.R_max / (1 - M.γ)) * ε_T) / (1 - M.γ) :=
        h_sim s
    _ = M.γ * M.R_max * ε_T / (1 - M.γ) ^ 2 := by
        rw [zero_add]; field_simp

/-- **Crude optimality-gap bound**.

  If M̂ has the same rewards as M, transition error <= epsilon_T,
  and pi_hat dominates pi_ref in M̂, then the optimality gap in
  the true MDP M satisfies:

    V^{pi_ref}(s) - V^{pi_hat}(s) <= 2*gamma*R_max*epsilon_T / (1-gamma)^2

  Uses `model_based_comparison` with epsilon_R = 0, B = R_max/(1-gamma).

  **Caveat**: To recover the intended optimal-policy statement, set pi_ref = pi*
  (optimal policy in M). The 1/(1-gamma)^2 scaling is the crude
  bound; the sharper Bernstein-style analysis improves it to 1/(1-gamma)^{3/2} via
  Bernstein-based analysis. -/
theorem optimality_gap_from_transition_error
    (M_hat : M.ApproxMDP)
    (π_ref π_hat : M.StochasticPolicy)
    -- Value functions in M
    (V_ref V_hat_M : M.StateValueFn)
    (hV_ref : M.isValueOf V_ref π_ref)
    (hV_hat_M : M.isValueOf V_hat_M π_hat)
    -- Value functions in M̂
    (V_ref_a V_hat_a : M.StateValueFn)
    (hV_ref_a : ∀ s, V_ref_a s =
      (∑ a, π_ref.prob s a * M_hat.r_hat s a) +
      M.γ * (∑ a, π_ref.prob s a *
        ∑ s', M_hat.P_hat s a s' * V_ref_a s'))
    (hV_hat_a : ∀ s, V_hat_a s =
      (∑ a, π_hat.prob s a * M_hat.r_hat s a) +
      M.γ * (∑ a, π_hat.prob s a *
        ∑ s', M_hat.P_hat s a s' * V_hat_a s'))
    -- π̂ dominates π_ref in M̂
    (h_opt : ∀ s, V_hat_a s ≥ V_ref_a s)
    -- Same rewards
    (h_same_r : ∀ s a, M.r s a = M_hat.r_hat s a)
    -- Transition error bound
    (ε_T : ℝ) (hε_T : M.transitionError M_hat ≤ ε_T) :
    ∀ s, V_ref s - V_hat_M s ≤
      2 * M.γ * M.R_max * ε_T / (1 - M.γ) ^ 2 := by
  -- Step 1: M̂ rewards bounded by R_max (since same rewards)
  have h_rew_bnd : ∀ s a, |M_hat.r_hat s a| ≤ M.R_max := by
    intro s a; rw [← h_same_r]; exact M.r_le_R_max s a
  -- Step 2: M̂ value functions bounded by V_max = R_max/(1-γ)
  set B := M.R_max / (1 - M.γ)
  have hB : 0 ≤ B := le_of_lt M.V_max_pos
  have hVra_bnd := M.approx_value_bounded M_hat π_ref V_ref_a
    hV_ref_a M.R_max (le_of_lt M.R_max_pos) h_rew_bnd
  have hVha_bnd := M.approx_value_bounded M_hat π_hat V_hat_a
    hV_hat_a M.R_max (le_of_lt M.R_max_pos) h_rew_bnd
  -- Step 3: Reward error is 0
  have h_rew_err : M.rewardError M_hat ≤ 0 := by
    simp only [rewardError]
    apply Finset.sup'_le; intro s _
    apply Finset.sup'_le; intro a _
    rw [h_same_r s a, sub_self, abs_zero]
  -- Step 4: Apply model_based_comparison
  have h_mbc := M.model_based_comparison M_hat π_ref π_hat
    V_ref V_hat_M hV_ref hV_hat_M
    V_ref_a V_hat_a hV_ref_a hV_hat_a
    h_opt B hB hVra_bnd hVha_bnd
    0 h_rew_err ε_T hε_T
  -- h_mbc : V_ref s - V_hat_M s ≤ 2·(0 + γ·B·ε_T)/(1-γ)
  intro s
  have h1g : (0 : ℝ) < 1 - M.γ := by linarith [M.γ_lt_one]
  calc V_ref s - V_hat_M s
      ≤ 2 * (0 + M.γ * B * ε_T) / (1 - M.γ) := h_mbc s
    _ = 2 * M.γ * M.R_max * ε_T / (1 - M.γ) ^ 2 := by
        rw [zero_add]
        change 2 * (M.γ * (M.R_max / (1 - M.γ)) * ε_T) / (1 - M.γ) =
          2 * M.γ * M.R_max * ε_T / (1 - M.γ) ^ 2
        field_simp

end FiniteMDP

end
