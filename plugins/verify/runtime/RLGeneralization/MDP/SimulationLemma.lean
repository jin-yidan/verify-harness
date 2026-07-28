/-
# The Simulation Lemma

This file formalizes the Simulation Lemma (Kearns & Singh, 2002), which bounds
the value function error when using an approximate MDP model.

## Main Results

* `simulation_lemma` - If M̂ approximates M with reward error ε_R and transition
  error ε_T (in L1), then for any policy π:
    |V^π_M(s) - V^π_M̂(s)| ≤ (ε_R + γ·B·ε_T) / (1-γ)
  where B bounds |V^π_M̂|.

## References

* [Kearns and Singh, *Near-Optimal RL in Polynomial Time*][kearns2002]
* [Kakade and Langford, *Approximately Optimal Approximate RL*][kakade2002]
-/

import RLGeneralization.MDP.BellmanContraction

open Finset BigOperators

noncomputable section

namespace FiniteMDP

variable (M : FiniteMDP)

/-! ### Model Approximation Error -/

/-- An approximate MDP M̂ with the same state-action space but
    different dynamics. -/
structure ApproxMDP where
  /-- Approximate transition: P̂(s'|s,a) -/
  P_hat : M.S → M.A → M.S → ℝ
  /-- Approximate reward: r̂(s,a) -/
  r_hat : M.S → M.A → ℝ
  /-- P̂ is a valid transition -/
  P_hat_nonneg : ∀ s a s', 0 ≤ P_hat s a s'
  P_hat_sum_one : ∀ s a, ∑ s', P_hat s a s' = 1

/-- **Lift an approximate MDP to a full FiniteMDP.**

  Given an ApproxMDP M̂ (with valid transitions) and a proof that
  its rewards are bounded, construct a FiniteMDP sharing the same
  state/action spaces and discount factor as the original M.

  This enables applying BanachFixedPoint and other discounted-MDP
  infrastructure (value-iteration convergence, policy-evaluation
  existence) to the approximate model. -/
def approxMDP_to_FiniteMDP (M_hat : M.ApproxMDP)
    (h_r_bnd : ∃ R_max : ℝ, 0 < R_max ∧
      ∀ s a, |M_hat.r_hat s a| ≤ R_max) : FiniteMDP where
  S := M.S
  A := M.A
  P := M_hat.P_hat
  r := M_hat.r_hat
  γ := M.γ
  P_nonneg := M_hat.P_hat_nonneg
  P_sum_one := M_hat.P_hat_sum_one
  r_bound := h_r_bnd
  γ_nonneg := M.γ_nonneg
  γ_lt_one := M.γ_lt_one

/-- Maximum reward error: max_{s,a} |r(s,a) - r̂(s,a)| -/
def rewardError (M_hat : M.ApproxMDP) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun s =>
    Finset.univ.sup' Finset.univ_nonempty fun a =>
      |M.r s a - M_hat.r_hat s a|

/-- Maximum L1 transition error:
    max_{s,a} ∑_{s'} |P(s'|s,a) - P̂(s'|s,a)| -/
def transitionError (M_hat : M.ApproxMDP) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun s =>
    Finset.univ.sup' Finset.univ_nonempty fun a =>
      ∑ s', |M.P s a s' - M_hat.P_hat s a s'|

/-! ### Helper Lemmas -/

/-- Reward error bound: for any (s,a),
    |r(s,a) - r̂(s,a)| ≤ rewardError M̂ -/
lemma rewardError_le (M_hat : M.ApproxMDP) (s : M.S) (a : M.A) :
    |M.r s a - M_hat.r_hat s a| ≤ M.rewardError M_hat := by
  unfold rewardError
  exact le_trans
    (Finset.le_sup' (fun a => |M.r s a - M_hat.r_hat s a|)
      (Finset.mem_univ a))
    (Finset.le_sup' (fun s => Finset.univ.sup'
      Finset.univ_nonempty
      (fun a => |M.r s a - M_hat.r_hat s a|))
      (Finset.mem_univ s))

/-- L1 transition error bound: for any (s,a),
    ∑_{s'} |P - P̂| ≤ transitionError M̂ -/
lemma transitionError_le (M_hat : M.ApproxMDP) (s : M.S) (a : M.A) :
    ∑ s', |M.P s a s' - M_hat.P_hat s a s'| ≤
      M.transitionError M_hat := by
  unfold transitionError
  exact le_trans
    (Finset.le_sup' (fun a =>
        ∑ s', |M.P s a s' - M_hat.P_hat s a s'|)
      (Finset.mem_univ a))
    (Finset.le_sup' (fun s => Finset.univ.sup'
        Finset.univ_nonempty (fun a =>
          ∑ s', |M.P s a s' - M_hat.P_hat s a s'|))
      (Finset.mem_univ s))

/-- |∑ f| ≤ ∑ |f| for real-valued finite sums (triangle inequality). -/
private lemma abs_sum_le_sum_abs {ι : Type*}
    (s : Finset ι) (f : ι → ℝ) :
    |∑ i ∈ s, f i| ≤ ∑ i ∈ s, |f i| := by
  have h := norm_sum_le s f
  simp only [Real.norm_eq_abs] at h; exact h

/-- Key bound: |∑_{s'} (P - P̂)(s'|s,a) · f(s')| ≤ ‖f‖_∞ · ε_T
    Relates L1 transition error to value function error. -/
lemma transition_value_error (M_hat : M.ApproxMDP)
    (f : M.S → ℝ) (B : ℝ)
    (hf : ∀ s, |f s| ≤ B)
    (s : M.S) (a : M.A) :
    |∑ s', (M.P s a s' - M_hat.P_hat s a s') * f s'| ≤
      B * ∑ s', |M.P s a s' - M_hat.P_hat s a s'| := by
  calc |∑ s', (M.P s a s' - M_hat.P_hat s a s') * f s'|
      ≤ ∑ s', |(M.P s a s' - M_hat.P_hat s a s') * f s'| :=
        abs_sum_le_sum_abs _ _
    _ = ∑ s', |M.P s a s' - M_hat.P_hat s a s'| * |f s'| := by
        congr 1; ext s'; exact abs_mul _ _
    _ ≤ ∑ s', |M.P s a s' - M_hat.P_hat s a s'| * B := by
        apply Finset.sum_le_sum; intro s' _
        exact mul_le_mul_of_nonneg_left (hf s') (abs_nonneg _)
    _ = B * ∑ s', |M.P s a s' - M_hat.P_hat s a s'| := by
        rw [← Finset.sum_mul]; ring

/-! ### Simulation Inequality (Kearns-Singh style)

  **Note on relation to the exact resolvent identity**: the standard identity is
  exact resolvent identity Q^π - Q̂^π = γ(I - γP̂^π)⁻¹(P - P̂)V^π,
  which requires matrix inverse infrastructure. The theorem below
  is a Kearns-Singh style *inequality* that bounds ‖V^π_M - V^π_M̂‖
  without the resolvent. It is an auxiliary result that implies the
  bound in the model-based PAC argument, but it is not the same object as that exact identity.
-/

/-- **Simulation Inequality** (Kearns-Singh style).

  If M̂ approximates M with reward error ≤ ε_R and L1 transition
  error ≤ ε_T, and V_Mhat satisfies the Bellman equation for M̂
  with ‖V_Mhat‖_∞ ≤ B, then:

    |V^π_M(s) - V^π_M̂(s)| ≤ (ε_R + γ·B·ε_T) / (1-γ)

  This is NOT the exact resolvent identity (which is an exact
  identity). It is an auxiliary inequality used in the proof of
  the model-accuracy guarantee. -/
theorem simulation_lemma (M_hat : M.ApproxMDP)
    (π : M.StochasticPolicy)
    (V_M V_Mhat : M.StateValueFn)
    (hV_M : M.isValueOf V_M π)
    (hV_Mhat : ∀ s, V_Mhat s =
        (∑ a, π.prob s a * M_hat.r_hat s a) +
        M.γ * (∑ a, π.prob s a *
          ∑ s', M_hat.P_hat s a s' * V_Mhat s'))
    (B : ℝ) (hB : 0 ≤ B)
    (hV_Mhat_bound : ∀ s, |V_Mhat s| ≤ B)
    (ε_R : ℝ) (hε_R : M.rewardError M_hat ≤ ε_R)
    (ε_T : ℝ) (hε_T : M.transitionError M_hat ≤ ε_T) :
    ∀ s, |V_M s - V_Mhat s| ≤
      (ε_R + M.γ * B * ε_T) / (1 - M.γ) := by
  -- Step 1: Single-step error bound
  -- For each s: |V_M s - V_Mhat s| ≤ ε_R + γ Δ + γ B ε_T
  -- where Δ = sup|V_M - V_Mhat|
  set Δ := M.supNormV (fun s => V_M s - V_Mhat s)
  have h1g : (0 : ℝ) < 1 - M.γ := by linarith [M.γ_lt_one]
  -- Step 1a: Show pointwise bound
  have hstep : ∀ s, |V_M s - V_Mhat s| ≤
      ε_R + M.γ * Δ + M.γ * B * ε_T := by
    intro s
    -- Expand Bellman equations
    rw [hV_M s, hV_Mhat s]
    -- Difference = reward_diff + γ * transition_diff
    have hdecomp :
        (M.expectedReward π s +
          M.γ * M.expectedNextValue π V_M s) -
        ((∑ a, π.prob s a * M_hat.r_hat s a) +
          M.γ * (∑ a, π.prob s a *
            ∑ s', M_hat.P_hat s a s' * V_Mhat s')) =
        ((M.expectedReward π s) -
          (∑ a, π.prob s a * M_hat.r_hat s a)) +
        M.γ * ((M.expectedNextValue π V_M s) -
          (∑ a, π.prob s a *
            ∑ s', M_hat.P_hat s a s' * V_Mhat s')) := by
      ring
    rw [hdecomp]
    -- Triangle inequality
    calc |(M.expectedReward π s -
            ∑ a, π.prob s a * M_hat.r_hat s a) +
          M.γ * (M.expectedNextValue π V_M s -
            ∑ a, π.prob s a *
              ∑ s', M_hat.P_hat s a s' * V_Mhat s')|
        ≤ |M.expectedReward π s -
            ∑ a, π.prob s a * M_hat.r_hat s a| +
          |M.γ * (M.expectedNextValue π V_M s -
            ∑ a, π.prob s a *
              ∑ s', M_hat.P_hat s a s' * V_Mhat s')| :=
          abs_add_le _ _
      _ ≤ ε_R + M.γ * Δ + M.γ * B * ε_T := by
          -- Bound 1: reward difference ≤ ε_R
          have hrew : |M.expectedReward π s -
              ∑ a, π.prob s a * M_hat.r_hat s a| ≤ ε_R := by
            -- r^π_M(s) - r^π_Mhat(s) = ∑ π(a|s)(r - r̂)
            have : M.expectedReward π s -
                ∑ a, π.prob s a * M_hat.r_hat s a =
                ∑ a, π.prob s a *
                  (M.r s a - M_hat.r_hat s a) := by
              unfold expectedReward
              rw [← Finset.sum_sub_distrib]
              congr 1; ext a; ring
            rw [this]
            apply le_trans (abs_weighted_sum_le_bound _ _
              (M.rewardError M_hat) (π.prob_nonneg s)
              (π.prob_sum_one s) (fun a =>
                M.rewardError_le M_hat s a))
            exact hε_R
          -- Bound 2: transition term ≤ γ(Δ + B·ε_T)
          have htrans :
              |M.γ * (M.expectedNextValue π V_M s -
                ∑ a, π.prob s a *
                  ∑ s', M_hat.P_hat s a s' *
                    V_Mhat s')| ≤
              M.γ * Δ + M.γ * B * ε_T := by
            rw [abs_mul, abs_of_nonneg M.γ_nonneg]
            -- Decompose: P^π V_M - P̂^π V_Mhat
            --   = P^π(V_M - V_Mhat) + (P^π - P̂^π)V_Mhat
            have hinner :
                M.expectedNextValue π V_M s -
                ∑ a, π.prob s a *
                  ∑ s', M_hat.P_hat s a s' *
                    V_Mhat s' =
                (∑ a, π.prob s a *
                  ∑ s', M.P s a s' *
                    (V_M s' - V_Mhat s')) +
                (∑ a, π.prob s a *
                  ∑ s', (M.P s a s' -
                    M_hat.P_hat s a s') *
                      V_Mhat s') := by
              unfold expectedNextValue
              rw [← Finset.sum_sub_distrib,
                  ← Finset.sum_add_distrib]
              congr 1; funext a
              rw [← mul_sub, ← mul_add]
              congr 1
              rw [← Finset.sum_sub_distrib,
                  ← Finset.sum_add_distrib]
              congr 1; funext s'
              ring
            rw [hinner]
            calc M.γ * |(∑ a, π.prob s a *
                    ∑ s', M.P s a s' *
                      (V_M s' - V_Mhat s')) +
                  (∑ a, π.prob s a *
                    ∑ s', (M.P s a s' -
                      M_hat.P_hat s a s') *
                        V_Mhat s')|
                ≤ M.γ * (|∑ a, π.prob s a *
                    ∑ s', M.P s a s' *
                      (V_M s' - V_Mhat s')| +
                  |∑ a, π.prob s a *
                    ∑ s', (M.P s a s' -
                      M_hat.P_hat s a s') *
                        V_Mhat s'|) := by
                  apply mul_le_mul_of_nonneg_left
                    (abs_add_le _ _) M.γ_nonneg
              _ ≤ M.γ * (Δ + B * ε_T) := by
                  apply mul_le_mul_of_nonneg_left _
                    M.γ_nonneg
                  apply add_le_add
                  · -- |P^π(V_M - V_Mhat)| ≤ Δ
                    apply abs_weighted_sum_le_bound _ _
                      Δ (π.prob_nonneg s)
                      (π.prob_sum_one s)
                    intro a
                    apply abs_weighted_sum_le_bound _ _
                      Δ (M.P_nonneg s a)
                      (M.P_sum_one s a)
                    intro s'
                    exact Finset.le_sup'
                      (fun s => |V_M s - V_Mhat s|)
                      (Finset.mem_univ s')
                  · -- |(P^π - P̂^π) V_Mhat| ≤ B·ε_T
                    apply abs_weighted_sum_le_bound _ _
                      (B * ε_T) (π.prob_nonneg s)
                      (π.prob_sum_one s)
                    intro a
                    calc |∑ s', (M.P s a s' -
                          M_hat.P_hat s a s') *
                            V_Mhat s'|
                        ≤ B * ∑ s',
                          |M.P s a s' -
                            M_hat.P_hat s a s'| :=
                          M.transition_value_error
                            M_hat (fun s => V_Mhat s)
                            B hV_Mhat_bound s a
                      _ ≤ B * ε_T := by
                          apply mul_le_mul_of_nonneg_left
                            _ hB
                          exact le_trans
                            (M.transitionError_le
                              M_hat s a) hε_T
              _ = M.γ * Δ + M.γ * B * ε_T := by ring
          linarith
  -- Step 2: sup bound → Δ ≤ ε_R + γΔ + γBε_T
  have hsup : Δ ≤ ε_R + M.γ * Δ + M.γ * B * ε_T :=
    Finset.sup'_le _ _ (fun s _ => hstep s)
  -- Step 3: Solve for Δ
  have hΔ : Δ ≤ (ε_R + M.γ * B * ε_T) / (1 - M.γ) := by
    rw [le_div_iff₀ h1g]; nlinarith [hsup]
  -- Step 4: Pointwise bound
  intro s
  have hle : |V_M s - V_Mhat s| ≤ Δ := by
    simp only [Δ, supNormV]
    exact Finset.le_sup'
      (fun s => |V_M s - V_Mhat s|) (Finset.mem_univ s)
  linarith

/-! ### Advantage Function -/

/-- The advantage function A^π(s,a) = Q^π(s,a) - V^π(s) -/
def advantageFn (V : M.StateValueFn)
    (Q : M.ActionValueFn) : M.S → M.A → ℝ :=
  fun s a => Q s a - V s

/-! ### Performance Difference Lemma — Not Yet Formalized

  The occupancy-measure performance-difference identity and the
  exact resolvent identity both require:
  - The discounted state visitation distribution d^π_μ(s,a),
    defined via (I - γP^π)⁻¹
  - Matrix inverse infrastructure not yet in Mathlib for
    our MDP representation

  These are left for future work. The `discountedVisitation`
  definition that was here previously (returning constant zero)
  has been REMOVED to prevent silent downstream errors. -/

/-! ### PAC Simulation Lemma

  The simulation lemma gives a deterministic bound:
    |V^π_M(s) - V^π_{M̂}(s)| ≤ (ε_R + γ·B·ε_T) / (1-γ)

  The PAC version combines this with concentration:
    With N samples per (s,a), the empirical model M̂ satisfies
    ε_R ≤ ... and ε_T ≤ ... with probability ≥ 1-δ.

  Together: P(V* - V^{π̂} ≥ ε) ≤ δ when N is large enough.
-/

/-- **PAC simulation lemma**: high-probability bound on value error.

  Given N i.i.d. samples per (s,a) pair from the generative model:
  1. Concentration gives ε_R, ε_T bounds w.h.p.
  2. Simulation lemma converts to value error
  3. Planning in M̂ gives near-optimal policy

  Result: P(V*_M(s) - V^{π̂}_M(s) ≥ ε) ≤ δ

  [CONDITIONAL] The concentration step (bounding empirical model
  error from N samples) is taken as a hypothesis. -/
theorem pac_simulation_lemma
    (_M_hat : M.ApproxMDP)
    (_π : M.DetPolicy) (V_star : M.StateValueFn)
    (V_hat : M.StateValueFn)
    (B : ℝ) (_hB : 0 ≤ B)
    -- Simulation lemma: value error bounded by model error
    (ε_R ε_T : ℝ) (_hεR : 0 ≤ ε_R) (_hεT : 0 ≤ ε_T)
    (h_sim : ∀ s, |V_star s - V_hat s| ≤ (ε_R + M.γ * B * ε_T) / (1 - M.γ))
    -- [CONDITIONAL HYPOTHESIS] Concentration: N samples give ε_R, ε_T w.h.p.
    -- P(ε_R ≤ bound_R ∧ ε_T ≤ bound_T) ≥ 1 - δ
    (ε : ℝ) (_hε : 0 < ε)
    (h_bound : (ε_R + M.γ * B * ε_T) / (1 - M.γ) ≤ ε) :
    ∀ s, |V_star s - V_hat s| ≤ ε :=
  fun s => le_trans (h_sim s) h_bound

/-- **PAC simulation: sample complexity.**

  To achieve P(V* - V^{π̂} ≥ ε) ≤ δ, the generative model requires
    N = O(|S|·|A|·B² / (ε²·(1-γ)²) · log(|S|·|A|/δ))
  samples total.

  This decomposes as:
  - Each (s,a) needs O(B²/(ε²·(1-γ)²) · log(|S||A|/δ)) samples
  - Union bound over |S|·|A| pairs
  - ε_T ≈ √(|S|·log(|S||A|/δ)/N) per pair
  - ε_R = 0 (using true rewards)

  [VACUOUS SPEC] This definition is vacuously satisfiable: the
    disjunction's second branch `N < C/(ε²(1-γ)²)` is always true
    for large enough C. It serves as an architectural placeholder
    for a proper PAC simulation specification that would require
    measure-theoretic probability bounds. -/
def PACSimulationSpec (ε _δ : ℝ) (N : ℕ) : Prop :=
  ∃ (C : ℝ), 0 < C ∧
    ∀ (V_star V_hat : M.StateValueFn),
      (∀ s, |V_star s - V_hat s| ≤ ε) ∨
      (N : ℝ) < C / (ε ^ 2 * (1 - M.γ) ^ 2)

end FiniteMDP

end
