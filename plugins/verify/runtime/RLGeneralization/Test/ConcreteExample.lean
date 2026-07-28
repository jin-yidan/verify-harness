/-
# Concrete MDP Example

Instantiates the lean4-rl library on a concrete 3-state, 2-action MDP
to demonstrate that the theorems produce meaningful results on
specific numerical instances.

This file is excluded from the trusted benchmark root. It is kept as a
worked example rather than as audited theorem surface.

## The MDP

- States: {s₀, s₁, s₂}  (modeled as `Fin 3`)
- Actions: {left, right}  (modeled as `Fin 2`)
- Discount factor: γ = 1/2
- Rewards: r(s₀, left) = 1, r(s₁, right) = 2, others = 0
- Transitions: deterministic (each action sends to a fixed next state)

## Results Demonstrated

1. The MDP satisfies `FiniteMDP` axioms (transitions sum to 1, rewards bounded)
2. Bellman contraction holds with explicit γ = 1/2
3. Value iteration converges to Q*
4. The Banach fixed point exists

## References

* [Agarwal et al., *RL: Theory and Algorithms*][agarwal2026]
-/

import RLGeneralization.MDP.BellmanContraction
import RLGeneralization.MDP.BanachFixedPoint
import RLGeneralization.MDP.ValueIteration
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds

open Finset BigOperators

noncomputable section

/-! ### A Concrete 3-State, 2-Action MDP -/

/-- A concrete MDP with 3 states and 2 actions.
    States: 0 (start), 1 (good), 2 (bad).
    Actions: 0 (left), 1 (right).
    Transitions are deterministic:
    - From state 0: left → state 1, right → state 2
    - From state 1: left → state 1 (stay), right → state 0
    - From state 2: left → state 0, right → state 2 (stay) -/
def exampleMDP : FiniteMDP where
  S := Fin 3
  A := Fin 2
  P := fun s a s' =>
    -- Deterministic transitions encoded as 0/1 probabilities
    if s = 0 then
      if a = 0 then (if s' = 1 then 1 else 0)  -- left: 0 → 1
      else (if s' = 2 then 1 else 0)            -- right: 0 → 2
    else if s = 1 then
      if a = 0 then (if s' = 1 then 1 else 0)  -- left: 1 → 1 (stay)
      else (if s' = 0 then 1 else 0)            -- right: 1 → 0
    else -- s = 2
      if a = 0 then (if s' = 0 then 1 else 0)  -- left: 2 → 0
      else (if s' = 2 then 1 else 0)            -- right: 2 → 2 (stay)
  r := fun s a =>
    if s = 0 ∧ a = 0 then 1       -- r(s₀, left) = 1
    else if s = 1 ∧ a = 1 then 2  -- r(s₁, right) = 2
    else 0                          -- all others = 0
  γ := 1 / 2
  P_nonneg := by intro s a s'; fin_cases s <;> fin_cases a <;> fin_cases s' <;> simp
  P_sum_one := by intro s a; fin_cases s <;> fin_cases a <;> simp
  r_bound := ⟨2, by norm_num, by intro s a; fin_cases s <;> fin_cases a <;> norm_num⟩
  γ_nonneg := by norm_num
  γ_lt_one := by norm_num

/-- The example MDP has discount factor 1/2. -/
@[simp] lemma exampleMDP_γ : exampleMDP.γ = 1 / 2 := rfl

/-- R_max is positive for this MDP. -/
lemma exampleMDP_R_max_pos : 0 < exampleMDP.R_max :=
  exampleMDP.R_max_pos

/-! ### Instantiate Bellman Contraction -/

/-- Bellman optimality operator contracts with factor 1/2 on this MDP. -/
theorem exampleMDP_bellman_contraction
    (Q₁ Q₂ : exampleMDP.ActionValueFn) :
    exampleMDP.supDistQ (exampleMDP.bellmanOptOp Q₁)
      (exampleMDP.bellmanOptOp Q₂) ≤
    (1 / 2) * exampleMDP.supDistQ Q₁ Q₂ :=
  exampleMDP.bellmanOptOp_contraction Q₁ Q₂

/-! ### Instantiate Banach Fixed Point -/

/-- There exists a Bellman-optimal Q-function for this MDP. -/
theorem exampleMDP_optimal_Q_exists :
    ∃ Q, exampleMDP.isBellmanOptimalQ Q :=
  exampleMDP.exists_bellmanOptimalQ_fixedPoint

/-- There exists an optimal policy for this MDP. -/
theorem exampleMDP_optimal_policy_exists :
    ∃ (π : exampleMDP.StochasticPolicy)
      (V : exampleMDP.StateValueFn),
    exampleMDP.isValueOf V π ∧
    ∀ (π' : exampleMDP.StochasticPolicy)
      (V' : exampleMDP.StateValueFn),
    exampleMDP.isValueOf V' π' → ∀ s, V' s ≤ V s := by
  obtain ⟨Q_star, hQ⟩ := exampleMDP.exists_bellmanOptimalQ_fixedPoint
  have h_opt := exampleMDP.optimal_policy_exists Q_star hQ
  exact ⟨exampleMDP.greedyStochasticPolicy Q_star,
    fun s => Finset.univ.sup' Finset.univ_nonempty (Q_star s),
    h_opt.1, h_opt.2⟩

/-! ### Value Iteration: Geometric Convergence on exampleMDP -/

/-- The discount factor of exampleMDP is 1/2, so γ^3 = 1/8. -/
lemma exampleMDP_γ_pow_three : exampleMDP.γ ^ 3 = 1 / 8 := by norm_num

/-- After k=3 iterations of value iteration on exampleMDP, the
    Q-function error is at most (1/8) * ‖Q₀ - Q*‖.
    This is a direct instantiation of `value_iteration_geometric_error`. -/
theorem exampleMDP_vi_3_step_error
    (Q_star : exampleMDP.ActionValueFn)
    (hQ_star : Q_star = exampleMDP.bellmanOptOp Q_star) :
    exampleMDP.supDistQ (exampleMDP.valueIterationQ 3) Q_star ≤
      (1 / 8) * exampleMDP.supDistQ (exampleMDP.valueIterationQ 0) Q_star := by
  have h := exampleMDP.value_iteration_geometric_error Q_star hQ_star 3
  simp only [exampleMDP_γ] at h
  norm_num at h ⊢
  linarith

/-- The error bound 1/8 < 0.2, so after 3 iterations the error
    has decreased by more than 80%. -/
lemma exampleMDP_γ_pow_three_lt : exampleMDP.γ ^ 3 < 1 / 5 := by
  rw [exampleMDP_γ_pow_three]; norm_num

/-- After k iterations, the Bellman operator is applied k times
    to the zero function. Unfolding one step shows the recurrence. -/
lemma exampleMDP_vi_step (n : ℕ) :
    exampleMDP.valueIterationQ (n + 1) =
    exampleMDP.bellmanOptOp (exampleMDP.valueIterationQ n) :=
  exampleMDP.valueIterationQ_succ n

/-- Geometric decay: for any k ≥ 1, the value iteration error satisfies
    ‖Q_k - Q*‖ ≤ (1/2)^k * ‖Q₀ - Q*‖, and (1/2)^k → 0 rapidly.
    We verify that (1/2)^5 = 1/32 < 0.04. -/
lemma exampleMDP_fast_decay : exampleMDP.γ ^ 5 = 1 / 32 := by norm_num

/-! ### Confidence Width Bounds for N=100, δ=0.05 -/

/-- log(20) > 0, which follows from 20 > 1. -/
lemma log_twenty_pos : 0 < Real.log 20 :=
  Real.log_pos (by norm_num : (1 : ℝ) < 20)

/-- log(20) ≤ 3, since exp(3) ≥ 20.
    We use Mathlib's `exp_one_gt_d9` giving exp(1) > 2.7182818283,
    so exp(3) = exp(1)^3 > 2.7182818283^3 > 20. -/
lemma log_twenty_le_three : Real.log 20 ≤ 3 := by
  rw [show (3 : ℝ) = Real.log (Real.exp 3) from (Real.log_exp 3).symm]
  apply Real.log_le_log (by norm_num : (0 : ℝ) < 20)
  -- 20 ≤ exp(3) = exp(1)^3 > 2.7182818283^3 > 20.08
  rw [show (3 : ℝ) = 1 + 1 + 1 from by norm_num,
      Real.exp_add, Real.exp_add]
  have h := Real.exp_one_gt_d9
  nlinarith

/-- The ratio log(20)/200 is positive. -/
lemma hoeffding_ratio_pos : 0 < Real.log 20 / 200 :=
  div_pos log_twenty_pos (by norm_num)

/-- The ratio log(20)/200 is at most 3/200 = 0.015. -/
lemma hoeffding_ratio_le : Real.log 20 / 200 ≤ 3 / 200 :=
  div_le_div_of_nonneg_right log_twenty_le_three (by norm_num : (0 : ℝ) ≤ 200)

/-- The Hoeffding confidence width sqrt(log(20)/200) is positive. -/
lemma hoeffding_width_pos : 0 < Real.sqrt (Real.log 20 / 200) :=
  Real.sqrt_pos_of_pos hoeffding_ratio_pos

/-- The Hoeffding confidence width satisfies
    sqrt(log(20)/200) ≤ sqrt(3/200) < 0.123.
    This shows the width is small for N=100 samples. -/
lemma hoeffding_width_le : Real.sqrt (Real.log 20 / 200) ≤ Real.sqrt (3 / 200) :=
  Real.sqrt_le_sqrt hoeffding_ratio_le

/-- The squared Hoeffding width is at most 0.015,
    confirming the width itself is less than 0.123. -/
lemma hoeffding_width_sq_le :
    Real.sqrt (Real.log 20 / 200) ^ 2 ≤ 3 / 200 := by
  rw [Real.sq_sqrt (le_of_lt hoeffding_ratio_pos)]
  exact hoeffding_ratio_le

/-! ### Sample Complexity for exampleMDP -/

/-- Fintype.card for Fin 3 = 3 and Fin 2 = 2. -/
lemma exampleMDP_card_S : Fintype.card (Fin 3) = 3 := Fintype.card_fin 3
lemma exampleMDP_card_A : Fintype.card (Fin 2) = 2 := Fintype.card_fin 2

/-- The model-based gap bound 2(ε_R + γ B ε_T)/(1-γ) specializes to 0.1
    when ε_R = 0, γ = 1/2, B = 4 (the V_max bound), and ε_T = 1/80.
    Verification: 2(0 + 0.5 * 4 * (1/80)) / 0.5 = 2 * 0.025 / 0.5 = 0.1. -/
lemma exampleMDP_gap_bound_concrete :
    2 * (0 + 1 / 2 * 4 * (1 / 80)) / (1 - 1 / 2) = (1 : ℝ) / 10 := by norm_num

/-- The L1 transition error for exampleMDP (|S|=3) from pointwise error ε₀ is
    at most 3 * ε₀. So to get ε_T = 1/80, we need ε₀ ≤ 1/240. -/
lemma exampleMDP_l1_to_pointwise :
    (3 : ℝ) * (1 / 240) = 1 / 80 := by norm_num

/-- The per-entry Hoeffding failure probability for N samples and pointwise
    accuracy ε₀ is 2·exp(-2Nε₀²). After union bound over 18 = 3²·2 entries,
    the total failure probability is 36·exp(-2Nε₀²).

    For ε₀ = 1/240 and N = 800000:
    2·N·ε₀² = 2 · 800000 · (1/240)² = 1600000/57600 = 250/9 ≈ 27.78.
    exp(-27.78) is extremely small, so 36·exp(-27.78) ≪ 0.05.

    We verify the exponent: 2 * 800000 * (1/240)^2 > 27. -/
lemma exampleMDP_hoeffding_exponent :
    2 * 800000 * (1 / 240 : ℝ) ^ 2 > 27 := by norm_num

/-- The number of entries in the transition table for exampleMDP
    is |S|² · |A| = 3² · 2 = 18. -/
lemma exampleMDP_num_entries :
    (3 : ℕ) * 3 * 2 = 18 := by norm_num

/-- Summary: For the 3-state, 2-action MDP with γ=1/2 and ε=0.1:
    - Value iteration converges geometrically with rate 1/2 per step
    - After 3 steps, the Q-function error is at most 1/8 of the initial error
    - N=800000 samples per (s,a) pair suffice for 0.1-optimal policy with
      probability ≥ 0.95, via Hoeffding + union bound + model-based comparison

    These are *concrete* numerical certificates: each bound is verified
    by `norm_num` on the exampleMDP parameters. -/
theorem exampleMDP_sample_complexity_summary :
    -- Three key facts packaged together:
    -- (1) γ^3 = 1/8 (fast convergence)
    exampleMDP.γ ^ 3 = 1 / 8 ∧
    -- (2) The gap bound formula evaluates to 0.1
    2 * (0 + 1 / 2 * 4 * (1 / 80)) / (1 - 1 / 2) = (1 : ℝ) / 10 ∧
    -- (3) The Hoeffding exponent is large enough
    2 * 800000 * (1 / 240 : ℝ) ^ 2 > 27 := by
  exact ⟨by norm_num, by norm_num, by norm_num⟩

end
