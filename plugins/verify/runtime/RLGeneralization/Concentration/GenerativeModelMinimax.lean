/-
# Generative Model: Minimax End-to-End Theorems

Deterministic good-event reductions and high-probability minimax lifts
chaining the Bernstein PAC layer with the deterministic minimax core.

## References

* [Azar, Munos, Kappen, *Minimax PAC bounds*][azar2013]
* [Agarwal et al., *RL: Theory and Algorithms*]
-/

import RLGeneralization.Concentration.GenerativeModelEmpirical
import RLGeneralization.Concentration.GenerativeModelBernstein
import RLGeneralization.Generalization.MinimaxSampleComplexity

open Finset BigOperators MeasureTheory ProbabilityTheory ENNReal

noncomputable section

namespace FiniteMDP

variable (M : FiniteMDP)

/-! ### Step 9: End-to-end minimax theorem -/

/-- **Minimax sample complexity from generative model (end-to-end).**

    On the good event {forall s a s', |P_hat - P| < eps_0}:

    1. L1 error: sum_{s'} |P_hat - P| <= |S| * eps_0
    2. Deterministic core: V-gap <= 2*gamma*R_max*|S|*eps_0 / (1-gamma)^2

    The probabilistic layer (Steps 1-8) gives the good event with
    high probability. This theorem chains the deterministic steps. -/
theorem minimax_from_generative_model
    (P_hat_omega : M.S → M.A → M.S → ℝ)
    (hP_hat_nonneg : ∀ s a s', 0 ≤ P_hat_omega s a s')
    (hP_hat_sum : ∀ s a, ∑ s', P_hat_omega s a s' = 1)
    (eps_0 : ℝ) (_heps_0 : 0 < eps_0)
    (h_good : ∀ s a s', |M.P s a s' - P_hat_omega s a s'| < eps_0)
    (r_hat : M.S → M.A → ℝ)
    (h_same_r : ∀ s a, M.r s a = r_hat s a)
    (pi_ref pi_hat : M.StochasticPolicy)
    (V_ref V_hat_M : M.StateValueFn)
    (hV_ref : M.isValueOf V_ref pi_ref)
    (hV_hat_M : M.isValueOf V_hat_M pi_hat)
    (V_ref_a V_hat_a : M.StateValueFn)
    (hV_ref_a : ∀ s, V_ref_a s =
      (∑ a, pi_ref.prob s a * r_hat s a) +
      M.γ * (∑ a, pi_ref.prob s a *
        ∑ s', P_hat_omega s a s' * V_ref_a s'))
    (hV_hat_a : ∀ s, V_hat_a s =
      (∑ a, pi_hat.prob s a * r_hat s a) +
      M.γ * (∑ a, pi_hat.prob s a *
        ∑ s', P_hat_omega s a s' * V_hat_a s'))
    (h_opt : ∀ s, V_hat_a s ≥ V_ref_a s) :
    ∀ s, V_ref s - V_hat_M s ≤
      2 * M.γ * M.R_max * (↑(Fintype.card M.S) * eps_0) /
        (1 - M.γ) ^ 2 := by
  -- Construct the approximate MDP
  set M_hat : M.ApproxMDP := {
    P_hat := P_hat_omega
    r_hat := r_hat
    P_hat_nonneg := hP_hat_nonneg
    P_hat_sum_one := hP_hat_sum
  }
  -- L1 error from pointwise bound
  have h_l1 : M.transitionError M_hat ≤ ↑(Fintype.card M.S) * eps_0 := by
    simp only [transitionError]
    apply Finset.sup'_le; intro s _
    apply Finset.sup'_le; intro a _
    calc ∑ s', |M.P s a s' - P_hat_omega s a s'|
        ≤ ∑ _s' : M.S, eps_0 :=
          Finset.sum_le_sum fun s' _ => le_of_lt (h_good s a s')
      _ = Fintype.card M.S * eps_0 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact M.minimax_deterministic_core M_hat pi_ref pi_hat
    V_ref V_hat_M hV_ref hV_hat_M
    V_ref_a V_hat_a hV_ref_a hV_hat_a
    h_opt h_same_r (↑(Fintype.card M.S) * eps_0) h_l1

/-- Specialization of `minimax_from_generative_model` to the empirical transition
    kernel extracted from a generative-model sample point. -/
theorem minimax_from_empirical_transition_good_event
    {N : ℕ} (hN : 0 < N)
    (ω : M.SampleIndex N → M.S)
    (eps_0 : ℝ) (heps_0 : 0 < eps_0)
    (h_good : ∀ s a s', |M.P s a s' - M.empiricalTransitionRV hN ω s a s'| < eps_0)
    (r_hat : M.S → M.A → ℝ)
    (h_same_r : ∀ s a, M.r s a = r_hat s a)
    (pi_ref pi_hat : M.StochasticPolicy)
    (V_ref V_hat_M : M.StateValueFn)
    (hV_ref : M.isValueOf V_ref pi_ref)
    (hV_hat_M : M.isValueOf V_hat_M pi_hat)
    (V_ref_a V_hat_a : M.StateValueFn)
    (hV_ref_a : ∀ s, V_ref_a s =
      (∑ a, pi_ref.prob s a * r_hat s a) +
      M.γ * (∑ a, pi_ref.prob s a *
        ∑ s', M.empiricalTransitionRV hN ω s a s' * V_ref_a s'))
    (hV_hat_a : ∀ s, V_hat_a s =
      (∑ a, pi_hat.prob s a * r_hat s a) +
      M.γ * (∑ a, pi_hat.prob s a *
        ∑ s', M.empiricalTransitionRV hN ω s a s' * V_hat_a s'))
    (h_opt : ∀ s, V_hat_a s ≥ V_ref_a s) :
    ∀ s, V_ref s - V_hat_M s ≤
      2 * M.γ * M.R_max * (↑(Fintype.card M.S) * eps_0) /
        (1 - M.γ) ^ 2 := by
  exact M.minimax_from_generative_model (M.empiricalTransitionRV hN ω)
    (M.empiricalTransitionRV_nonneg hN ω)
    (M.empiricalTransitionRV_sum_one hN ω)
    eps_0 heps_0 h_good
    r_hat h_same_r pi_ref pi_hat V_ref V_hat_M hV_ref hV_hat_M
    V_ref_a V_hat_a hV_ref_a hV_hat_a h_opt

/-- Same as `minimax_from_empirical_transition_good_event`, but stated for the
    canonical empirical approximate MDP that keeps the true reward function. -/
theorem minimax_from_empirical_model_good_event
    {N : ℕ} (hN : 0 < N)
    (ω : M.SampleIndex N → M.S)
    (eps_0 : ℝ) (heps_0 : 0 < eps_0)
    (h_good : ∀ s a s', |M.P s a s' - (M.empiricalApproxMDPRV hN ω).P_hat s a s'| < eps_0)
    (pi_ref pi_hat : M.StochasticPolicy)
    (V_ref V_hat_M : M.StateValueFn)
    (hV_ref : M.isValueOf V_ref pi_ref)
    (hV_hat_M : M.isValueOf V_hat_M pi_hat)
    (V_ref_a V_hat_a : M.StateValueFn)
    (hV_ref_a : ∀ s, V_ref_a s =
      (∑ a, pi_ref.prob s a * (M.empiricalApproxMDPRV hN ω).r_hat s a) +
      M.γ * (∑ a, pi_ref.prob s a *
        ∑ s', (M.empiricalApproxMDPRV hN ω).P_hat s a s' * V_ref_a s'))
    (hV_hat_a : ∀ s, V_hat_a s =
      (∑ a, pi_hat.prob s a * (M.empiricalApproxMDPRV hN ω).r_hat s a) +
      M.γ * (∑ a, pi_hat.prob s a *
        ∑ s', (M.empiricalApproxMDPRV hN ω).P_hat s a s' * V_hat_a s'))
    (h_opt : ∀ s, V_hat_a s ≥ V_ref_a s) :
    ∀ s, V_ref s - V_hat_M s ≤
      2 * M.γ * M.R_max * (↑(Fintype.card M.S) * eps_0) /
        (1 - M.γ) ^ 2 := by
  exact M.minimax_from_generative_model ((M.empiricalApproxMDPRV hN ω).P_hat)
    ((M.empiricalApproxMDPRV hN ω).P_hat_nonneg)
    ((M.empiricalApproxMDPRV hN ω).P_hat_sum_one)
    eps_0 heps_0 h_good
    M.r (fun s a => rfl) pi_ref pi_hat V_ref V_hat_M hV_ref hV_hat_M
    V_ref_a V_hat_a hV_ref_a hV_hat_a h_opt

/-- Reduce the empirical-model optimality side to a Bellman fixed point of the
    empirical MDP. This removes the free approximate greedy-policy/value and
    dominance hypotheses from `minimax_from_empirical_model_good_event`. -/
theorem minimax_from_empirical_bellman_fixed_point_good_event
    {N : ℕ} (hN : 0 < N)
    (ω : M.SampleIndex N → M.S)
    (eps_0 : ℝ) (heps_0 : 0 < eps_0)
    (h_good : ∀ s a s', |M.P s a s' - (M.empiricalApproxMDPRV hN ω).P_hat s a s'| < eps_0)
    (π_ref : M.StochasticPolicy)
    (V_ref V_hat_M : M.StateValueFn)
    (hV_ref : M.isValueOf V_ref π_ref)
    (V_ref_a : M.StateValueFn)
    (hV_ref_a :
      (M.empiricalModelMDP hN ω).isValueOf V_ref_a
        (M.toEmpiricalModelPolicy hN ω π_ref))
    (Q_hat : (M.empiricalModelMDP hN ω).ActionValueFn)
    (hQ_hat : ∀ s a, Q_hat s a =
      (M.empiricalModelMDP hN ω).bellmanOptOp Q_hat s a)
    (hV_hat_M :
      M.isValueOf V_hat_M
        (M.ofEmpiricalModelPolicy hN ω
          ((M.empiricalModelMDP hN ω).greedyStochasticPolicy Q_hat))) :
    ∀ s, V_ref s - V_hat_M s ≤
      2 * M.γ * M.R_max * (↑(Fintype.card M.S) * eps_0) /
        (1 - M.γ) ^ 2 := by
  let Mω := M.empiricalModelMDP hN ω
  let π_hat_emp : Mω.StochasticPolicy := Mω.greedyStochasticPolicy Q_hat
  let V_hat_a : Mω.StateValueFn :=
    fun s => Finset.univ.sup' Finset.univ_nonempty (Q_hat s)
  have h_opt_exists := Mω.optimal_policy_exists Q_hat hQ_hat
  have hV_hat_a_emp : Mω.isValueOf V_hat_a π_hat_emp := by
    exact h_opt_exists.1
  have h_dom :
      ∀ (π : Mω.StochasticPolicy) (V_pi : Mω.StateValueFn),
        Mω.isValueOf V_pi π → ∀ s, V_pi s ≤ V_hat_a s := by
    exact h_opt_exists.2
  have hV_ref_a_rw :
      ∀ s, V_ref_a s =
        (∑ a, π_ref.prob s a * (M.empiricalApproxMDPRV hN ω).r_hat s a) +
        M.γ * (∑ a, π_ref.prob s a *
          ∑ s', (M.empiricalApproxMDPRV hN ω).P_hat s a s' * V_ref_a s') := by
    simpa [Mω, empiricalModelMDP, toEmpiricalModelPolicy, empiricalApproxMDPRV,
      FiniteMDP.isValueOf, FiniteMDP.expectedReward, FiniteMDP.expectedNextValue]
      using hV_ref_a
  have hV_hat_a_rw :
      ∀ s, V_hat_a s =
        (∑ a, (M.ofEmpiricalModelPolicy hN ω π_hat_emp).prob s a *
          (M.empiricalApproxMDPRV hN ω).r_hat s a) +
        M.γ * (∑ a, (M.ofEmpiricalModelPolicy hN ω π_hat_emp).prob s a *
          ∑ s', (M.empiricalApproxMDPRV hN ω).P_hat s a s' * V_hat_a s') := by
    simpa [Mω, empiricalModelMDP, ofEmpiricalModelPolicy, empiricalApproxMDPRV,
      π_hat_emp, V_hat_a, FiniteMDP.isValueOf, FiniteMDP.expectedReward,
      FiniteMDP.expectedNextValue] using hV_hat_a_emp
  have h_opt :
      ∀ s, V_hat_a s ≥ V_ref_a s := by
    intro s
    exact h_dom (M.toEmpiricalModelPolicy hN ω π_ref) V_ref_a hV_ref_a s
  exact M.minimax_from_empirical_model_good_event hN ω eps_0 heps_0 h_good
    π_ref (M.ofEmpiricalModelPolicy hN ω π_hat_emp) V_ref V_hat_M hV_ref
    hV_hat_M V_ref_a V_hat_a hV_ref_a_rw hV_hat_a_rw h_opt

/-- Further reduce the empirical-model good-event theorem by deriving the
    reference-side empirical value from an empirical action-value fixed point
    for the reference policy. -/
theorem minimax_from_empirical_Q_fixed_points_good_event
    {N : ℕ} (hN : 0 < N)
    (ω : M.SampleIndex N → M.S)
    (eps_0 : ℝ) (heps_0 : 0 < eps_0)
    (h_good : ∀ s a s', |M.P s a s' - (M.empiricalApproxMDPRV hN ω).P_hat s a s'| < eps_0)
    (π_ref : M.StochasticPolicy)
    (V_ref V_hat_M : M.StateValueFn)
    (hV_ref : M.isValueOf V_ref π_ref)
    (Q_ref : (M.empiricalModelMDP hN ω).ActionValueFn)
    (hQ_ref :
      (M.empiricalModelMDP hN ω).isActionValueOf Q_ref
        (M.toEmpiricalModelPolicy hN ω π_ref))
    (Q_hat : (M.empiricalModelMDP hN ω).ActionValueFn)
    (hQ_hat : ∀ s a, Q_hat s a =
      (M.empiricalModelMDP hN ω).bellmanOptOp Q_hat s a)
    (hV_hat_M :
      M.isValueOf V_hat_M
        (M.ofEmpiricalModelPolicy hN ω
          ((M.empiricalModelMDP hN ω).greedyStochasticPolicy Q_hat))) :
    ∀ s, V_ref s - V_hat_M s ≤
      2 * M.γ * M.R_max * (↑(Fintype.card M.S) * eps_0) /
        (1 - M.γ) ^ 2 := by
  let V_ref_a := M.empiricalModelValueFromQ hN ω π_ref Q_ref
  have hV_ref_a :
      (M.empiricalModelMDP hN ω).isValueOf V_ref_a
        (M.toEmpiricalModelPolicy hN ω π_ref) := by
    exact M.empiricalModelValueFromQ_isValueOf hN ω π_ref Q_ref hQ_ref
  exact M.minimax_from_empirical_bellman_fixed_point_good_event hN ω eps_0 heps_0
    h_good π_ref V_ref V_hat_M hV_ref V_ref_a hV_ref_a Q_hat hQ_hat hV_hat_M

/-- Further reduce the empirical-model good-event theorem by constructing the
    reference-side empirical action-value fixed point via the Banach
    fixed-point bridge, leaving only the empirical Bellman-optimal fixed point
    on the greedy side as an explicit hypothesis. -/
theorem minimax_from_empirical_eval_and_bellman_fixed_points_good_event
    {N : ℕ} (hN : 0 < N)
    (ω : M.SampleIndex N → M.S)
    (eps_0 : ℝ) (heps_0 : 0 < eps_0)
    (h_good : ∀ s a s', |M.P s a s' - (M.empiricalApproxMDPRV hN ω).P_hat s a s'| < eps_0)
    (π_ref : M.StochasticPolicy)
    (V_ref V_hat_M : M.StateValueFn)
    (hV_ref : M.isValueOf V_ref π_ref)
    (Q_hat : (M.empiricalModelMDP hN ω).ActionValueFn)
    (hQ_hat : ∀ s a, Q_hat s a =
      (M.empiricalModelMDP hN ω).bellmanOptOp Q_hat s a)
    (hV_hat_M :
      M.isValueOf V_hat_M
        (M.ofEmpiricalModelPolicy hN ω
          ((M.empiricalModelMDP hN ω).greedyStochasticPolicy Q_hat))) :
    ∀ s, V_ref s - V_hat_M s ≤
      2 * M.γ * M.R_max * (↑(Fintype.card M.S) * eps_0) /
        (1 - M.γ) ^ 2 := by
  let Mω := M.empiricalModelMDP hN ω
  let π_ref_emp : Mω.StochasticPolicy := M.toEmpiricalModelPolicy hN ω π_ref
  let Q_ref : Mω.ActionValueFn := Mω.actionValueFixedPoint π_ref_emp
  have hQ_ref : Mω.isActionValueOf Q_ref π_ref_emp := by
    exact Mω.actionValueFixedPoint_isActionValueOf π_ref_emp
  exact M.minimax_from_empirical_Q_fixed_points_good_event hN ω eps_0 heps_0
    h_good π_ref V_ref V_hat_M hV_ref Q_ref hQ_ref Q_hat hQ_hat hV_hat_M

/-- Further reduce the empirical-model good-event theorem by replacing the
    free Bellman-optimal empirical witness with the canonical Banach fixed point
    of the empirical optimality operator. The remaining output-side object is
    the true-model value of the resulting empirical greedy policy. -/
theorem minimax_from_empirical_fixed_points_good_event
    {N : ℕ} (hN : 0 < N)
    (ω : M.SampleIndex N → M.S)
    (eps_0 : ℝ) (heps_0 : 0 < eps_0)
    (h_good : ∀ s a s', |M.P s a s' - (M.empiricalApproxMDPRV hN ω).P_hat s a s'| < eps_0)
    (π_ref : M.StochasticPolicy)
    (V_ref : M.StateValueFn)
    (hV_ref : M.isValueOf V_ref π_ref) :
    ∀ s, V_ref s - M.empiricalGreedyValue hN ω s ≤
      2 * M.γ * M.R_max * (↑(Fintype.card M.S) * eps_0) /
        (1 - M.γ) ^ 2 := by
  let Mω := M.empiricalModelMDP hN ω
  let Q_hat : Mω.ActionValueFn := Mω.optimalQFixedPoint
  have hQ_hat : ∀ s a, Q_hat s a = Mω.bellmanOptOp Q_hat s a := by
    intro s a
    simpa [Q_hat, FiniteMDP.isBellmanOptimalQ, FiniteMDP.bellmanOptOp] using
      (Mω.optimalQFixedPoint_isBellmanOptimalQ s a)
  have hV_hat_M :
      M.isValueOf (M.empiricalGreedyValue hN ω) (M.empiricalGreedyPolicy hN ω) := by
    exact M.empiricalGreedyValue_isValueOf hN ω
  exact M.minimax_from_empirical_eval_and_bellman_fixed_points_good_event
    hN ω eps_0 heps_0 h_good π_ref V_ref (M.empiricalGreedyValue hN ω)
    hV_ref Q_hat hQ_hat hV_hat_M

/-- **High-probability minimax value-gap bound for the empirical transition model.**

    This packages the exact PAC event from `generative_model_pac` with the
    deterministic good-event reduction from
    `minimax_from_empirical_transition_good_event`.

    The approximate-model policies and value functions may depend on the sample
    point `ω`; the theorem only assumes that, for each `ω`, they satisfy the
    stated Bellman/value hypotheses for the empirical kernel extracted from `ω`.
    This keeps the theorem honest: it is an end-to-end probability statement for
    the empirical model, but it still does not derive those approximate-model
    objects from the data. -/
theorem minimax_value_gap_high_probability
    {N : ℕ} (hN : 0 < N)
    (eps_0 : ℝ) (heps_0 : 0 < eps_0)
    (r_hat : M.S → M.A → ℝ)
    (h_same_r : ∀ s a, M.r s a = r_hat s a)
    (pi_ref pi_hat : (M.SampleIndex N → M.S) → M.StochasticPolicy)
    (V_ref V_hat_M : (M.SampleIndex N → M.S) → M.StateValueFn)
    (hV_ref : ∀ ω, M.isValueOf (V_ref ω) (pi_ref ω))
    (hV_hat_M : ∀ ω, M.isValueOf (V_hat_M ω) (pi_hat ω))
    (V_ref_a V_hat_a : (M.SampleIndex N → M.S) → M.StateValueFn)
    (hV_ref_a : ∀ ω s, V_ref_a ω s =
      (∑ a, (pi_ref ω).prob s a * r_hat s a) +
      M.γ * (∑ a, (pi_ref ω).prob s a *
        ∑ s', M.empiricalTransitionRV hN ω s a s' * V_ref_a ω s'))
    (hV_hat_a : ∀ ω s, V_hat_a ω s =
      (∑ a, (pi_hat ω).prob s a * r_hat s a) +
      M.γ * (∑ a, (pi_hat ω).prob s a *
        ∑ s', M.empiricalTransitionRV hN ω s a s' * V_hat_a ω s'))
    (h_opt : ∀ ω s, V_hat_a ω s ≥ V_ref_a ω s) :
    (M.generativeModelMeasure N).real
      {ω | ∀ s, V_ref ω s - V_hat_M ω s ≤
        2 * M.γ * M.R_max * (↑(Fintype.card M.S) * eps_0) /
          (1 - M.γ) ^ 2} ≥
      1 - Fintype.card M.S * Fintype.card M.S *
        Fintype.card M.A * (2 * Real.exp (-2 * (N : ℝ) * eps_0 ^ 2)) := by
  let _ : NeZero N := ⟨Nat.ne_of_gt hN⟩
  let good : Set (M.SampleIndex N → M.S) :=
    {ω | ∀ s a s', |M.P s a s' - M.empiricalTransitionRV hN ω s a s'| < eps_0}
  let target : Set (M.SampleIndex N → M.S) :=
    {ω | ∀ s, V_ref ω s - V_hat_M ω s ≤
      2 * M.γ * M.R_max * (↑(Fintype.card M.S) * eps_0) /
        (1 - M.γ) ^ 2}
  have h_subset : good ⊆ target := by
    intro ω hω
    dsimp [good, target] at hω ⊢
    exact M.minimax_from_empirical_transition_good_event hN ω eps_0 heps_0
      hω r_hat h_same_r (pi_ref ω) (pi_hat ω) (V_ref ω) (V_hat_M ω)
      (hV_ref ω) (hV_hat_M ω) (V_ref_a ω) (V_hat_a ω)
      (hV_ref_a ω) (hV_hat_a ω) (h_opt ω)
  have h_pac := M.generative_model_pac hN eps_0 heps_0
  have htarget_ne_top : (M.generativeModelMeasure N) target ≠ ∞ := by
    have htarget_lt_top : (M.generativeModelMeasure N) target < ∞ := by
      calc
        (M.generativeModelMeasure N) target ≤ (M.generativeModelMeasure N) Set.univ :=
          measure_mono (by intro ω _; simp)
        _ = 1 := by simp
        _ < ∞ := by simp
    exact ne_of_lt htarget_lt_top
  calc
    1 - Fintype.card M.S * Fintype.card M.S *
        Fintype.card M.A * (2 * Real.exp (-2 * (N : ℝ) * eps_0 ^ 2))
      ≤ (M.generativeModelMeasure N).real good := by
        simpa [good] using h_pac
    _ ≤ (M.generativeModelMeasure N).real target :=
        measureReal_mono h_subset htarget_ne_top
    _ = (M.generativeModelMeasure N).real
          {ω | ∀ s, V_ref ω s - V_hat_M ω s ≤
            2 * M.γ * M.R_max * (↑(Fintype.card M.S) * eps_0) /
              (1 - M.γ) ^ 2} := by
        rfl

/-- High-probability value-gap bound stated for the canonical empirical
    approximate MDP that keeps the true reward function. -/
theorem minimax_value_gap_high_probability_same_reward
    {N : ℕ} (hN : 0 < N)
    (eps_0 : ℝ) (heps_0 : 0 < eps_0)
    (pi_ref pi_hat : (M.SampleIndex N → M.S) → M.StochasticPolicy)
    (V_ref V_hat_M : (M.SampleIndex N → M.S) → M.StateValueFn)
    (hV_ref : ∀ ω, M.isValueOf (V_ref ω) (pi_ref ω))
    (hV_hat_M : ∀ ω, M.isValueOf (V_hat_M ω) (pi_hat ω))
    (V_ref_a V_hat_a : (M.SampleIndex N → M.S) → M.StateValueFn)
    (hV_ref_a : ∀ ω s, V_ref_a ω s =
      (∑ a, (pi_ref ω).prob s a * (M.empiricalApproxMDPRV hN ω).r_hat s a) +
      M.γ * (∑ a, (pi_ref ω).prob s a *
        ∑ s', (M.empiricalApproxMDPRV hN ω).P_hat s a s' * V_ref_a ω s'))
    (hV_hat_a : ∀ ω s, V_hat_a ω s =
      (∑ a, (pi_hat ω).prob s a * (M.empiricalApproxMDPRV hN ω).r_hat s a) +
      M.γ * (∑ a, (pi_hat ω).prob s a *
        ∑ s', (M.empiricalApproxMDPRV hN ω).P_hat s a s' * V_hat_a ω s'))
    (h_opt : ∀ ω s, V_hat_a ω s ≥ V_ref_a ω s) :
    (M.generativeModelMeasure N).real
      {ω | ∀ s, V_ref ω s - V_hat_M ω s ≤
        2 * M.γ * M.R_max * (↑(Fintype.card M.S) * eps_0) /
          (1 - M.γ) ^ 2} ≥
      1 - Fintype.card M.S * Fintype.card M.S *
        Fintype.card M.A * (2 * Real.exp (-2 * (N : ℝ) * eps_0 ^ 2)) := by
  exact M.minimax_value_gap_high_probability hN eps_0 heps_0
    M.r (fun s a => rfl) pi_ref pi_hat V_ref V_hat_M hV_ref hV_hat_M
    V_ref_a V_hat_a hV_ref_a hV_hat_a h_opt

/-- High-probability value-gap bound where the empirical greedy policy/value
    side is derived from a Bellman fixed point of the canonical empirical model. -/
theorem minimax_value_gap_high_probability_from_empirical_bellman_fixed_point
    {N : ℕ} (hN : 0 < N)
    (eps_0 : ℝ) (heps_0 : 0 < eps_0)
    (pi_ref : (M.SampleIndex N → M.S) → M.StochasticPolicy)
    (V_ref V_hat_M : (M.SampleIndex N → M.S) → M.StateValueFn)
    (hV_ref : ∀ ω, M.isValueOf (V_ref ω) (pi_ref ω))
    (V_ref_a : (M.SampleIndex N → M.S) → M.StateValueFn)
    (hV_ref_a : ∀ ω,
      (M.empiricalModelMDP hN ω).isValueOf (V_ref_a ω)
        (M.toEmpiricalModelPolicy hN ω (pi_ref ω)))
    (Q_hat : (M.SampleIndex N → M.S) → M.ActionValueFn)
    (hQ_hat : ∀ ω s a, Q_hat ω s a =
      (M.empiricalModelMDP hN ω).bellmanOptOp (Q_hat ω) s a)
    (hV_hat_M : ∀ ω,
      M.isValueOf (V_hat_M ω)
        (M.ofEmpiricalModelPolicy hN ω
          ((M.empiricalModelMDP hN ω).greedyStochasticPolicy (Q_hat ω)))) :
    (M.generativeModelMeasure N).real
      {ω | ∀ s, V_ref ω s - V_hat_M ω s ≤
        2 * M.γ * M.R_max * (↑(Fintype.card M.S) * eps_0) /
          (1 - M.γ) ^ 2} ≥
      1 - Fintype.card M.S * Fintype.card M.S *
        Fintype.card M.A * (2 * Real.exp (-2 * (N : ℝ) * eps_0 ^ 2)) := by
  let _ : NeZero N := ⟨Nat.ne_of_gt hN⟩
  let good : Set (M.SampleIndex N → M.S) :=
    {ω | ∀ s a s', |M.P s a s' - (M.empiricalApproxMDPRV hN ω).P_hat s a s'| < eps_0}
  let target : Set (M.SampleIndex N → M.S) :=
    {ω | ∀ s, V_ref ω s - V_hat_M ω s ≤
      2 * M.γ * M.R_max * (↑(Fintype.card M.S) * eps_0) /
        (1 - M.γ) ^ 2}
  have h_subset : good ⊆ target := by
    intro ω hω
    dsimp [good, target] at hω ⊢
    exact M.minimax_from_empirical_bellman_fixed_point_good_event hN ω eps_0 heps_0
      hω (pi_ref ω) (V_ref ω) (V_hat_M ω) (hV_ref ω) (V_ref_a ω)
      (hV_ref_a ω) (Q_hat ω) (hQ_hat ω) (hV_hat_M ω)
  have h_pac := M.generative_model_pac hN eps_0 heps_0
  have htarget_ne_top : (M.generativeModelMeasure N) target ≠ ∞ := by
    have htarget_lt_top : (M.generativeModelMeasure N) target < ∞ := by
      calc
        (M.generativeModelMeasure N) target ≤ (M.generativeModelMeasure N) Set.univ :=
          measure_mono (by intro ω _; simp)
        _ = 1 := by simp
        _ < ∞ := by simp
    exact ne_of_lt htarget_lt_top
  calc
    1 - Fintype.card M.S * Fintype.card M.S *
        Fintype.card M.A * (2 * Real.exp (-2 * (N : ℝ) * eps_0 ^ 2))
      ≤ (M.generativeModelMeasure N).real good := by
        simpa [good] using h_pac
    _ ≤ (M.generativeModelMeasure N).real target :=
        measureReal_mono h_subset htarget_ne_top
    _ = (M.generativeModelMeasure N).real
          {ω | ∀ s, V_ref ω s - V_hat_M ω s ≤
            2 * M.γ * M.R_max * (↑(Fintype.card M.S) * eps_0) /
              (1 - M.γ) ^ 2} := by
        rfl

/-- High-probability value-gap bound where the reference-side empirical value is
    derived from an empirical action-value fixed point and the empirical greedy
    side is derived from an empirical Bellman fixed point. -/
theorem minimax_value_gap_high_probability_from_empirical_Q_fixed_points
    {N : ℕ} (hN : 0 < N)
    (eps_0 : ℝ) (heps_0 : 0 < eps_0)
    (pi_ref : (M.SampleIndex N → M.S) → M.StochasticPolicy)
    (V_ref V_hat_M : (M.SampleIndex N → M.S) → M.StateValueFn)
    (hV_ref : ∀ ω, M.isValueOf (V_ref ω) (pi_ref ω))
    (Q_ref : (M.SampleIndex N → M.S) → M.ActionValueFn)
    (hQ_ref : ∀ ω,
      (M.empiricalModelMDP hN ω).isActionValueOf (Q_ref ω)
        (M.toEmpiricalModelPolicy hN ω (pi_ref ω)))
    (Q_hat : (M.SampleIndex N → M.S) → M.ActionValueFn)
    (hQ_hat : ∀ ω s a, Q_hat ω s a =
      (M.empiricalModelMDP hN ω).bellmanOptOp (Q_hat ω) s a)
    (hV_hat_M : ∀ ω,
      M.isValueOf (V_hat_M ω)
        (M.ofEmpiricalModelPolicy hN ω
          ((M.empiricalModelMDP hN ω).greedyStochasticPolicy (Q_hat ω)))) :
    (M.generativeModelMeasure N).real
      {ω | ∀ s, V_ref ω s - V_hat_M ω s ≤
        2 * M.γ * M.R_max * (↑(Fintype.card M.S) * eps_0) /
          (1 - M.γ) ^ 2} ≥
      1 - Fintype.card M.S * Fintype.card M.S *
        Fintype.card M.A * (2 * Real.exp (-2 * (N : ℝ) * eps_0 ^ 2)) := by
  let _ : NeZero N := ⟨Nat.ne_of_gt hN⟩
  let good : Set (M.SampleIndex N → M.S) :=
    {ω | ∀ s a s', |M.P s a s' - (M.empiricalApproxMDPRV hN ω).P_hat s a s'| < eps_0}
  let target : Set (M.SampleIndex N → M.S) :=
    {ω | ∀ s, V_ref ω s - V_hat_M ω s ≤
      2 * M.γ * M.R_max * (↑(Fintype.card M.S) * eps_0) /
        (1 - M.γ) ^ 2}
  have h_subset : good ⊆ target := by
    intro ω hω
    dsimp [good, target] at hω ⊢
    exact M.minimax_from_empirical_Q_fixed_points_good_event hN ω eps_0 heps_0
      hω (pi_ref ω) (V_ref ω) (V_hat_M ω) (hV_ref ω)
      (Q_ref ω) (hQ_ref ω) (Q_hat ω) (hQ_hat ω) (hV_hat_M ω)
  have h_pac := M.generative_model_pac hN eps_0 heps_0
  have htarget_ne_top : (M.generativeModelMeasure N) target ≠ ∞ := by
    have htarget_lt_top : (M.generativeModelMeasure N) target < ∞ := by
      calc
        (M.generativeModelMeasure N) target ≤ (M.generativeModelMeasure N) Set.univ :=
          measure_mono (by intro ω _; simp)
        _ = 1 := by simp
        _ < ∞ := by simp
    exact ne_of_lt htarget_lt_top
  calc
    1 - Fintype.card M.S * Fintype.card M.S *
        Fintype.card M.A * (2 * Real.exp (-2 * (N : ℝ) * eps_0 ^ 2))
      ≤ (M.generativeModelMeasure N).real good := by
        simpa [good] using h_pac
    _ ≤ (M.generativeModelMeasure N).real target :=
        measureReal_mono h_subset htarget_ne_top
    _ = (M.generativeModelMeasure N).real
          {ω | ∀ s, V_ref ω s - V_hat_M ω s ≤
            2 * M.γ * M.R_max * (↑(Fintype.card M.S) * eps_0) /
              (1 - M.γ) ^ 2} := by
        rfl

/-- High-probability value-gap bound where the reference-side empirical action
    value is constructed canonically from the empirical model and the
    reference policy, leaving only the empirical Bellman-optimal fixed point as
    an explicit greedy-side hypothesis. -/
theorem minimax_value_gap_high_probability_from_empirical_eval_and_bellman_fixed_point
    {N : ℕ} (hN : 0 < N)
    (eps_0 : ℝ) (heps_0 : 0 < eps_0)
    (pi_ref : (M.SampleIndex N → M.S) → M.StochasticPolicy)
    (V_ref V_hat_M : (M.SampleIndex N → M.S) → M.StateValueFn)
    (hV_ref : ∀ ω, M.isValueOf (V_ref ω) (pi_ref ω))
    (Q_hat : (M.SampleIndex N → M.S) → M.ActionValueFn)
    (hQ_hat : ∀ ω s a, Q_hat ω s a =
      (M.empiricalModelMDP hN ω).bellmanOptOp (Q_hat ω) s a)
    (hV_hat_M : ∀ ω,
      M.isValueOf (V_hat_M ω)
        (M.ofEmpiricalModelPolicy hN ω
          ((M.empiricalModelMDP hN ω).greedyStochasticPolicy (Q_hat ω)))) :
    (M.generativeModelMeasure N).real
      {ω | ∀ s, V_ref ω s - V_hat_M ω s ≤
        2 * M.γ * M.R_max * (↑(Fintype.card M.S) * eps_0) /
          (1 - M.γ) ^ 2} ≥
      1 - Fintype.card M.S * Fintype.card M.S *
        Fintype.card M.A * (2 * Real.exp (-2 * (N : ℝ) * eps_0 ^ 2)) := by
  let _ : NeZero N := ⟨Nat.ne_of_gt hN⟩
  let good : Set (M.SampleIndex N → M.S) :=
    {ω | ∀ s a s', |M.P s a s' - (M.empiricalApproxMDPRV hN ω).P_hat s a s'| < eps_0}
  let target : Set (M.SampleIndex N → M.S) :=
    {ω | ∀ s, V_ref ω s - V_hat_M ω s ≤
      2 * M.γ * M.R_max * (↑(Fintype.card M.S) * eps_0) /
        (1 - M.γ) ^ 2}
  have h_subset : good ⊆ target := by
    intro ω hω
    dsimp [good, target] at hω ⊢
    exact M.minimax_from_empirical_eval_and_bellman_fixed_points_good_event
      hN ω eps_0 heps_0 hω (pi_ref ω) (V_ref ω) (V_hat_M ω)
      (hV_ref ω) (Q_hat ω) (hQ_hat ω) (hV_hat_M ω)
  have h_pac := M.generative_model_pac hN eps_0 heps_0
  have htarget_ne_top : (M.generativeModelMeasure N) target ≠ ∞ := by
    have htarget_lt_top : (M.generativeModelMeasure N) target < ∞ := by
      calc
        (M.generativeModelMeasure N) target ≤ (M.generativeModelMeasure N) Set.univ :=
          measure_mono (by intro ω _; simp)
        _ = 1 := by simp
        _ < ∞ := by simp
    exact ne_of_lt htarget_lt_top
  calc
    1 - Fintype.card M.S * Fintype.card M.S *
        Fintype.card M.A * (2 * Real.exp (-2 * (N : ℝ) * eps_0 ^ 2))
      ≤ (M.generativeModelMeasure N).real good := by
        simpa [good] using h_pac
    _ ≤ (M.generativeModelMeasure N).real target :=
        measureReal_mono h_subset htarget_ne_top
    _ = (M.generativeModelMeasure N).real
          {ω | ∀ s, V_ref ω s - V_hat_M ω s ≤
            2 * M.γ * M.R_max * (↑(Fintype.card M.S) * eps_0) /
              (1 - M.γ) ^ 2} := by
        rfl

/-- High-probability value-gap bound where both empirical-model fixed points
    are canonical: the reference-side value is built from Banach policy
    evaluation in the empirical model, and the greedy side uses the canonical
    Bellman-optimal empirical fixed point together with canonical policy
    evaluation back in the true MDP. -/
theorem minimax_value_gap_high_probability_from_empirical_fixed_points
    {N : ℕ} (hN : 0 < N)
    (eps_0 : ℝ) (heps_0 : 0 < eps_0)
    (pi_ref : (M.SampleIndex N → M.S) → M.StochasticPolicy)
    (V_ref : (M.SampleIndex N → M.S) → M.StateValueFn)
    (hV_ref : ∀ ω, M.isValueOf (V_ref ω) (pi_ref ω)) :
    (M.generativeModelMeasure N).real
      {ω | ∀ s, V_ref ω s - M.empiricalGreedyValue hN ω s ≤
        2 * M.γ * M.R_max * (↑(Fintype.card M.S) * eps_0) /
          (1 - M.γ) ^ 2} ≥
      1 - Fintype.card M.S * Fintype.card M.S *
        Fintype.card M.A * (2 * Real.exp (-2 * (N : ℝ) * eps_0 ^ 2)) := by
  let _ : NeZero N := ⟨Nat.ne_of_gt hN⟩
  let good : Set (M.SampleIndex N → M.S) :=
    {ω | ∀ s a s', |M.P s a s' - (M.empiricalApproxMDPRV hN ω).P_hat s a s'| < eps_0}
  let target : Set (M.SampleIndex N → M.S) :=
    {ω | ∀ s, V_ref ω s - M.empiricalGreedyValue hN ω s ≤
      2 * M.γ * M.R_max * (↑(Fintype.card M.S) * eps_0) /
        (1 - M.γ) ^ 2}
  have h_subset : good ⊆ target := by
    intro ω hω
    dsimp [good, target] at hω ⊢
    exact M.minimax_from_empirical_fixed_points_good_event
      hN ω eps_0 heps_0 hω (pi_ref ω) (V_ref ω) (hV_ref ω)
  have h_pac := M.generative_model_pac hN eps_0 heps_0
  have htarget_ne_top : (M.generativeModelMeasure N) target ≠ ∞ := by
    have htarget_lt_top : (M.generativeModelMeasure N) target < ∞ := by
      calc
        (M.generativeModelMeasure N) target ≤ (M.generativeModelMeasure N) Set.univ :=
          measure_mono (by intro ω _; simp)
        _ = 1 := by simp
        _ < ∞ := by simp
    exact ne_of_lt htarget_lt_top
  calc
    1 - Fintype.card M.S * Fintype.card M.S *
        Fintype.card M.A * (2 * Real.exp (-2 * (N : ℝ) * eps_0 ^ 2))
      ≤ (M.generativeModelMeasure N).real good := by
        simpa [good] using h_pac
    _ ≤ (M.generativeModelMeasure N).real target :=
        measureReal_mono h_subset htarget_ne_top
    _ = (M.generativeModelMeasure N).real
          {ω | ∀ s, V_ref ω s - M.empiricalGreedyValue hN ω s ≤
            2 * M.γ * M.R_max * (↑(Fintype.card M.S) * eps_0) /
              (1 - M.γ) ^ 2} := by
        rfl

/-- Bernstein-flavored high-probability value-gap bound where both
    empirical-model fixed points are canonical. The probabilistic layer now
    comes from the in-file Bernstein specialization with the exact Bernoulli
    variance profile for each transition entry. -/
theorem minimax_value_gap_high_probability_from_empirical_fixed_points_bernstein
    {N : ℕ} (hN : 0 < N)
    (eps_0 : ℝ) (heps_0 : 0 < eps_0)
    (pi_ref : (M.SampleIndex N → M.S) → M.StochasticPolicy)
    (V_ref : (M.SampleIndex N → M.S) → M.StateValueFn)
    (hV_ref : ∀ ω, M.isValueOf (V_ref ω) (pi_ref ω)) :
    (M.generativeModelMeasure N).real
      {ω | ∀ s, V_ref ω s - M.empiricalGreedyValue hN ω s ≤
        2 * M.γ * M.R_max * (↑(Fintype.card M.S) * eps_0) /
          (1 - M.γ) ^ 2} ≥
      1 - ∑ p : M.S × M.A × M.S,
        2 * Real.exp (-((N : ℝ) * eps_0) ^ 2 /
          (2 * ((N : ℝ) * (M.P p.1 p.2.1 p.2.2 - (M.P p.1 p.2.1 p.2.2) ^ 2)) +
            2 * ((N : ℝ) * eps_0) / 3)) := by
  let _ : NeZero N := ⟨Nat.ne_of_gt hN⟩
  let good : Set (M.SampleIndex N → M.S) :=
    {ω | ∀ s a s', |M.P s a s' - (M.empiricalApproxMDPRV hN ω).P_hat s a s'| < eps_0}
  let target : Set (M.SampleIndex N → M.S) :=
    {ω | ∀ s, V_ref ω s - M.empiricalGreedyValue hN ω s ≤
      2 * M.γ * M.R_max * (↑(Fintype.card M.S) * eps_0) /
        (1 - M.γ) ^ 2}
  have h_subset : good ⊆ target := by
    intro ω hω
    dsimp [good, target] at hω ⊢
    exact M.minimax_from_empirical_fixed_points_good_event
      hN ω eps_0 heps_0 hω (pi_ref ω) (V_ref ω) (hV_ref ω)
  have h_pac := M.generative_model_pac_bernstein hN eps_0 heps_0
  have htarget_ne_top : (M.generativeModelMeasure N) target ≠ ∞ := by
    have htarget_lt_top : (M.generativeModelMeasure N) target < ∞ := by
      calc
        (M.generativeModelMeasure N) target ≤ (M.generativeModelMeasure N) Set.univ :=
          measure_mono (by intro ω _; simp)
        _ = 1 := by simp
        _ < ∞ := by simp
    exact ne_of_lt htarget_lt_top
  calc
    1 - ∑ p : M.S × M.A × M.S,
        2 * Real.exp (-((N : ℝ) * eps_0) ^ 2 /
          (2 * ((N : ℝ) * (M.P p.1 p.2.1 p.2.2 - (M.P p.1 p.2.1 p.2.2) ^ 2)) +
            2 * ((N : ℝ) * eps_0) / 3))
      ≤ (M.generativeModelMeasure N).real good := by
        simpa [good] using h_pac
    _ ≤ (M.generativeModelMeasure N).real target :=
        measureReal_mono h_subset htarget_ne_top
    _ = (M.generativeModelMeasure N).real
          {ω | ∀ s, V_ref ω s - M.empiricalGreedyValue hN ω s ≤
            2 * M.γ * M.R_max * (↑(Fintype.card M.S) * eps_0) /
              (1 - M.γ) ^ 2} := by
        rfl

end FiniteMDP

end
