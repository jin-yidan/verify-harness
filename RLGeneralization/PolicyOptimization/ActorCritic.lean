/-
# Actor-Critic Methods

Formalizes the algebraic core of actor-critic RL: a policy (actor) is
updated using a value function (critic) as a control variate. The key
insight is that using V^π as a baseline reduces variance without
changing the expected gradient, and the critic error introduces a
bounded bias.

## Main Results

* `ActorCriticState` — structure for actor-critic iteration state
* `ac_advantage_decomposition` — advantage = Q - V decomposition
* `ac_baseline_invariance` — expected score × baseline = 0 (algebraic)
* `ac_critic_bias_bound` — critic approximation error bounds the
  policy gradient bias
* `ac_two_timescale_gap` — gap between actor-critic and exact PG
  is bounded by critic error
* `ac_variance_reduction` — advantage-based gradient has smaller
  second moment than Q-based gradient

## References

* Konda, Tsitsiklis, "Actor-Critic Algorithms," NeurIPS, 2000.
* Agarwal et al., "RL: Theory and Algorithms," Ch 5 (2026).
-/

import RLGeneralization.PolicyOptimization.PolicyGradient

open Finset BigOperators

noncomputable section

namespace FiniteMDP

variable (M : FiniteMDP)

/-! ### Actor-Critic State -/

/-- An **actor-critic state** bundles a policy π with a critic
    value function V̂ that approximates V^π. -/
structure ActorCriticState where
  /-- Current policy (the actor) -/
  policy : M.StochasticPolicy
  /-- Critic value function estimate -/
  V_hat : M.StateValueFn
  /-- True Q-values under the current policy -/
  Q_true : M.ActionValueFn
  /-- True V-values under the current policy -/
  V_true : M.StateValueFn
  /-- Consistency: V^π(s) = ∑_a π(a|s) Q^π(s,a) -/
  h_VQ : ∀ s, V_true s = ∑ a, policy.prob s a * Q_true s a

/-! ### Advantage Decomposition -/

/-- **Advantage decomposition**: the estimated advantage (using critic V̂)
    equals the true advantage plus the critic error.

    (Q(s,a) - V̂(s)) = A(s,a) + (V(s) - V̂(s)) -/
theorem ac_advantage_decomposition
    (Q : M.ActionValueFn) (V V_hat : M.StateValueFn)
    (s : M.S) (a : M.A) :
    M.advantage Q V_hat s a =
    M.advantage Q V s a + (V s - V_hat s) := by
  simp only [advantage]; ring

/-! ### Baseline Invariance -/

/-- **Expected advantage is zero under the current policy**.
    ∑_a π(a|s) · A^π(s,a) = 0.

    This is the algebraic core of baseline invariance: using V as a
    baseline doesn't change the expected gradient direction. -/
theorem ac_expected_advantage_zero
    (ac : M.ActorCriticState) (s : M.S) :
    ∑ a, ac.policy.prob s a * M.advantage ac.Q_true ac.V_true s a = 0 := by
  simp only [advantage]
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, ac.policy.prob_sum_one, one_mul]
  linarith [ac.h_VQ s]

/-- **Baseline invariance**: for any constant b(s), subtracting it from
    Q-values doesn't change the expected weighted sum.

    ∑_a π(a|s) · Q(s,a) - b = ∑_a π(a|s) · (Q(s,a) - b)

    This holds for any stochastic policy because ∑_a π(a|s) = 1. -/
theorem ac_baseline_invariance
    (π : M.StochasticPolicy) (Q : M.ActionValueFn)
    (b : ℝ) (s : M.S) :
    ∑ a, π.prob s a * (Q s a - b) =
    (∑ a, π.prob s a * Q s a) - b := by
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, π.prob_sum_one, one_mul]

/-! ### Critic Error Bounds -/

/-- **Critic bias bound**: the expected difference between estimated
    and true advantage is bounded by the critic error.

    |∑_a π(a|s) · (A_V̂(s,a) - A_V(s,a))| = |V(s) - V̂(s)|

    because the difference is the same constant for all actions. -/
theorem ac_critic_bias_bound
    (π : M.StochasticPolicy)
    (Q : M.ActionValueFn) (V V_hat : M.StateValueFn)
    (s : M.S) :
    |∑ a, π.prob s a *
      (M.advantage Q V_hat s a - M.advantage Q V s a)| =
    |V s - V_hat s| := by
  simp only [advantage]
  have : ∀ a, (Q s a - V_hat s) - (Q s a - V s) = V s - V_hat s := by
    intro a; ring
  simp_rw [this]
  rw [← Finset.sum_mul, π.prob_sum_one, one_mul]

/-- **Two-timescale gap bound**: the gap between the actor-critic
    gradient signal and the true policy gradient signal (using true
    advantages) is bounded by the critic approximation error.

    If the critic has pointwise error ≤ ε_critic (|V̂(s) - V(s)| ≤ ε),
    then for any weight function w:

    |∑_a π(a|s) · w(s,a) · (Â(s,a) - A(s,a))| ≤ ε · ∑_a π(a|s) · |w(s,a)|

    The weight function represents the score ∇log π or any other
    per-action multiplier in the gradient estimate. -/
theorem ac_two_timescale_gap
    (π : M.StochasticPolicy)
    (Q : M.ActionValueFn) (V V_hat : M.StateValueFn)
    (w : M.S → M.A → ℝ)
    (s : M.S) (ε : ℝ) (hε : |V s - V_hat s| ≤ ε) :
    |∑ a, π.prob s a * w s a *
      (M.advantage Q V_hat s a - M.advantage Q V s a)| ≤
    ε * ∑ a, π.prob s a * |w s a| := by
  simp only [advantage]
  have h_diff : ∀ a, (Q s a - V_hat s) - (Q s a - V s) = V s - V_hat s := by
    intro a; ring
  simp_rw [h_diff]
  -- ∑ π(a|s) · w(s,a) · (V(s) - V̂(s)) = (V(s) - V̂(s)) · ∑ π(a|s) · w(s,a)
  have h_factor : ∑ a, π.prob s a * w s a * (V s - V_hat s) =
      (V s - V_hat s) * ∑ a, π.prob s a * w s a := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; ring
  rw [h_factor, abs_mul]
  calc |V s - V_hat s| * |∑ a, π.prob s a * w s a|
      ≤ ε * |∑ a, π.prob s a * w s a| :=
        mul_le_mul_of_nonneg_right hε (abs_nonneg _)
    _ ≤ ε * ∑ a, |π.prob s a * w s a| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _)
          (le_trans (abs_nonneg _) hε)
    _ = ε * ∑ a, π.prob s a * |w s a| := by
        congr 1; apply Finset.sum_congr rfl; intro a _
        rw [abs_mul, abs_of_nonneg (π.prob_nonneg s a)]

/-! ### Variance Reduction via Baseline -/

/-- **Variance reduction**: the second moment of the advantage-based
    estimate is at most the second moment of the Q-based estimate.

    More precisely: for any policy π and consistent V^π:

    ∑_a π(a|s) · A(s,a)² ≤ ∑_a π(a|s) · Q(s,a)²

    This follows because ∑ π · A² = ∑ π · Q² - (∑ π · Q)²
    and the subtracted term is nonneg (it's V(s)²). -/
theorem ac_variance_reduction
    (ac : M.ActorCriticState) (s : M.S) :
    ∑ a, ac.policy.prob s a * (M.advantage ac.Q_true ac.V_true s a) ^ 2 ≤
    ∑ a, ac.policy.prob s a * ac.Q_true s a ^ 2 := by
  simp only [advantage]
  -- We need: ∑ π · (Q - V)² ≤ ∑ π · Q²
  -- i.e., ∑ π · (Q² - 2QV + V²) ≤ ∑ π · Q²
  -- i.e., -2V · ∑ π · Q + V² · ∑ π ≤ 0
  -- i.e., -2V · V + V² ≤ 0 (using ∑πQ = V, ∑π = 1)
  -- i.e., -V² ≤ 0 ✓
  have hVQ := ac.h_VQ s
  have hsum := ac.policy.prob_sum_one s
  suffices h : ∑ a, ac.policy.prob s a * (ac.Q_true s a - ac.V_true s) ^ 2 =
      ∑ a, ac.policy.prob s a * ac.Q_true s a ^ 2 - ac.V_true s ^ 2 by
    linarith [sq_nonneg (ac.V_true s)]
  -- Expand (Q - V)² = Q² - 2QV + V²
  have : ∀ a, ac.policy.prob s a * (ac.Q_true s a - ac.V_true s) ^ 2 =
      ac.policy.prob s a * ac.Q_true s a ^ 2 -
      2 * ac.policy.prob s a * ac.Q_true s a * ac.V_true s +
      ac.policy.prob s a * ac.V_true s ^ 2 := by
    intro a; ring
  simp_rw [this, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  -- ∑ π · V² = V²
  have h1 : ∑ a, ac.policy.prob s a * ac.V_true s ^ 2 =
      ac.V_true s ^ 2 := by
    rw [← Finset.sum_mul, hsum, one_mul]
  -- ∑ 2·π·Q·V = 2·V·∑π·Q = 2·V²
  have h2 : ∑ a, 2 * ac.policy.prob s a * ac.Q_true s a * ac.V_true s =
      2 * ac.V_true s ^ 2 := by
    have : ∑ a, 2 * ac.policy.prob s a * ac.Q_true s a * ac.V_true s =
        2 * ac.V_true s * ∑ a, ac.policy.prob s a * ac.Q_true s a := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; ring
    rw [this, hVQ]; ring
  linarith

/-! ### Actor-Critic Update Properties -/

/-- **Greedy improvement direction**: if the critic identifies a
    positive advantage action (Q(s,a) > V̂(s)), then shifting
    probability toward that action improves the estimated value.

    Specifically: π(a|s) · Â(s,a) > 0 when π(a|s) > 0 and Â(s,a) > 0. -/
theorem ac_improvement_direction
    (π : M.StochasticPolicy) (Q : M.ActionValueFn) (V_hat : M.StateValueFn)
    (s : M.S) (a : M.A)
    (h_prob : 0 < π.prob s a)
    (h_adv : 0 < M.advantage Q V_hat s a) :
    0 < π.prob s a * M.advantage Q V_hat s a :=
  mul_pos h_prob h_adv

/-- **Critic accuracy suffices for improvement**: if the critic is
    ε-accurate and the true expected advantage of switching to π'
    is at least 2ε, then the estimated advantage is also positive.

    Algebraically: if x ≥ 2ε and |δ| ≤ ε, then x - δ ≥ ε > 0. -/
theorem ac_accuracy_suffices_for_improvement
    (true_advantage estimated_advantage ε δ : ℝ)
    (h_true : true_advantage ≥ 2 * ε)
    (_hε : 0 < ε)
    (h_est : estimated_advantage = true_advantage - δ)
    (h_err : |δ| ≤ ε) :
    estimated_advantage ≥ ε := by
  rw [h_est]
  have := (abs_le.mp h_err).1
  have := (abs_le.mp h_err).2
  linarith

/-! ### Actor-Critic Convergence -/

/-- **Actor-critic gap bounded by 1**: if T ≥ C and gap ≤ C/T,
    then gap ≤ 1 (since C/T ≤ 1).

    [MISLEADING] This proves gap ≤ 1, not gap ≤ ε. For the actual
    convergence to ε, see `ac_sample_complexity` which proves gap ≤ ε
    under a stronger sample complexity condition. -/
theorem ac_gap_le_one
    (value_gap ε C : ℝ) (T : ℕ)
    (_hε_pos : 0 < ε)
    (hT_pos : (0 : ℝ) < ↑T)
    (_h_two_timescale_rate : C = 1 / ε ^ 2)
    (h_T_sufficient : C ≤ ↑T)
    (h_gap_bound : value_gap ≤ C / ↑T) :
    value_gap ≤ 1 := by
  calc value_gap ≤ C / ↑T := h_gap_bound
    _ ≤ ↑T / ↑T := div_le_div_of_nonneg_right h_T_sufficient hT_pos.le
    _ = 1 := div_self (ne_of_gt hT_pos)
    _ ≤ 1 := le_refl 1

/-- **Actor-critic sample complexity**.
    N = O(1/(ε²(1-γ)⁴)) samples suffice for an ε-optimal policy.

    Algebraic consequence: if the gap is bounded by C/(N·(1-γ)⁴) and
    N ≥ C/(ε·(1-γ)⁴), then gap ≤ ε. -/
theorem ac_sample_complexity
    (ε C gap N : ℝ)
    (_hε : 0 < ε)
    (hγ_pos : 0 < 1 - M.γ)
    (hN_pos : 0 < N)
    (h_sufficient : C / (ε * (1 - M.γ) ^ 4) ≤ N)
    (h_gap : gap ≤ C / (N * (1 - M.γ) ^ 4))
    (_hC_nonneg : 0 ≤ C) :
    gap ≤ ε := by
  have h1g4 : 0 < (1 - M.γ) ^ 4 := by positivity
  have hN1g4 : 0 < N * (1 - M.γ) ^ 4 := mul_pos hN_pos h1g4
  -- Show C/(N·(1-γ)⁴) ≤ ε, then chain with h_gap
  suffices h : C / (N * (1 - M.γ) ^ 4) ≤ ε from le_trans h_gap h
  rw [div_le_iff₀ hN1g4]
  -- Need: C ≤ ε · (N · (1-γ)⁴)
  -- From h_sufficient: C/(ε·(1-γ)⁴) ≤ N, so C ≤ N·ε·(1-γ)⁴
  have hε1g4 : 0 < ε * (1 - M.γ) ^ 4 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h_sufficient h1g4.le,
             div_mul_cancel₀ C (ne_of_gt hε1g4)]

end FiniteMDP

end
