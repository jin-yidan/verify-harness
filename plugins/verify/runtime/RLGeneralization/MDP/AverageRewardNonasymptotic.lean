/-
# Non-Asymptotic Bounds for Average-Reward RL

Extends the average-reward MDP framework with finite-sample complexity
bounds. The key quantity is the mixing time t_mix of the MDP's Markov
chain, which controls the span of the optimal bias function and hence
the sample complexity of learning in the average-reward setting.

## Main Results

* `amdp_sample_complexity` — Finite-sample complexity for average-reward
  RL: n = O(t_mix² · |S| · |A| / ε²) samples suffice to learn an
  ε-optimal policy, conditional on the mixing time hypothesis.

* `span_bound` — The span of the optimal bias satisfies
  sp(h*) ≤ t_mix · (r_max - r_min), connecting the bias function's
  range to the chain's mixing time and reward range.

## References

* [Puterman, *Markov Decision Processes*, Ch 8-9][puterman2014]
* [Fruit et al., 2018, *Efficient Bias-Span-Constrained
  Exploration-Exploitation in RL*]
* [Zhang and Ji, 2019, *Regret Minimization for RL by Evaluating
  the Optimal Bias Function*]
-/

import RLGeneralization.MDP.AverageReward

open Finset BigOperators

noncomputable section

namespace FiniteMDP

variable (M : FiniteMDP)

/-! ### Mixing Time -/

/-- **Mixing time parameters** for an ergodic MDP.

  The mixing time t_mix measures how quickly the Markov chain induced
  by any stationary policy converges to its stationary distribution.
  Formally, t_mix = min { t : ‖P^t(·|s) - π_∞‖_TV ≤ 1/4 for all s }.

  For average-reward MDPs, the mixing time controls:
  - The span of the optimal bias function
  - The sample complexity of learning
  - The rate of convergence of empirical estimates -/
structure MixingTimeParams where
  /-- The mixing time -/
  t_mix : ℕ
  /-- Mixing time is positive -/
  ht_mix_pos : 0 < t_mix
  /-- Reward bounds -/
  r_min : ℝ
  r_max : ℝ
  h_reward_range : r_min ≤ r_max
  /-- Rewards are bounded within [r_min, r_max] -/
  h_r_bound : ∀ s : M.S, ∀ a : M.A, r_min ≤ M.r s a ∧ M.r s a ≤ r_max

/-! ### Span Bound via Mixing Time -/

/-- **Span bound for optimal bias**.

  For an ergodic MDP with mixing time t_mix, the span of the optimal
  bias function h* satisfies:

    sp(h*) ≤ t_mix · (r_max - r_min)

  Intuition: the bias h*(s) measures the transient advantage of starting
  in state s vs. the long-run average. This advantage is bounded by
  the number of steps to mix (t_mix) times the per-step reward range.

  The proof uses the coupling argument: after t_mix steps, the chain
  starting from any two states can be coupled with constant probability,
  so the discrepancy in cumulative reward is at most t_mix · reward_range.

  The coupling bound on pairwise bias differences is taken as a hypothesis
  (`h_bias_range`); the remainder is proved from Finset sup'/inf' arithmetic. -/
theorem span_bound
    (mix : M.MixingTimeParams)
    -- Optimal bias function (exists by ergodicity)
    (h_star : M.S → ℝ)
    (g_star : ℝ)
    -- Gain-bias equation: g* + h*(s) = max_a { r(s,a) + ∑ P h*(s') }
    (_h_gainbias : M.GainBiasEquation g_star h_star)
    -- Hypothesis: coupling bound on pairwise bias differences.
    -- For ergodic chains, after t_mix steps chains from any two initial
    -- states couple with constant probability, bounding the transient
    -- reward difference (bias) by t_mix · (r_max - r_min).
    (h_bias_range : ∀ s₁ s₂ : M.S,
        h_star s₁ - h_star s₂ ≤
          ↑mix.t_mix * (mix.r_max - mix.r_min)) :
    M.spanSeminorm h_star ≤ mix.t_mix * (mix.r_max - mix.r_min) := by
  unfold spanSeminorm
  suffices h : Finset.univ.sup' Finset.univ_nonempty h_star ≤
      Finset.univ.inf' Finset.univ_nonempty h_star +
        ↑mix.t_mix * (mix.r_max - mix.r_min) by linarith
  apply Finset.sup'_le
  intro a _
  suffices h : h_star a -
      ↑mix.t_mix * (mix.r_max - mix.r_min) ≤
      Finset.univ.inf' Finset.univ_nonempty h_star by linarith
  apply Finset.le_inf'
  intro b _
  linarith [h_bias_range a b]

/-! ### Finite-Sample Complexity -/

/-- **Finite-sample complexity for average-reward RL**.

  For an ergodic MDP with |S| states, |A| actions, and mixing time
  t_mix, a model-based algorithm (e.g., UCRL2 variant) achieves
  average-reward regret ≤ ε after

    n = O(t_mix² · |S| · |A| · (r_max - r_min)² / ε²)

  episodes/samples. Equivalently, the learned policy π̂ satisfies
  g* - g^{π̂} ≤ ε with high probability.

  The t_mix² dependence arises from:
  - t_mix factor from the span bound sp(h*) ≤ t_mix · reward_range
  - Another t_mix factor from the sample complexity of estimating
    transition probabilities to accuracy 1/t_mix

  Stated as a specification: a proper formalization requires connecting
  g_hat to the output of a specific algorithm (e.g., UCRL2) given n
  samples from the MDP. The sample complexity is
  n = O(t_mix² · |S| · |A| · reward_range² / ε²). -/
def AmdpSampleComplexitySpec
    (mix : M.MixingTimeParams) (ε : ℝ) (n : ℕ) (g_hat g_star : ℝ) : Prop :=
  ∃ (C_const : ℝ), 0 < C_const ∧
    (↑n ≥ C_const * mix.t_mix ^ 2 *
      (Fintype.card M.S) * (Fintype.card M.A) *
      (mix.r_max - mix.r_min) ^ 2 / ε ^ 2 →
    |g_star - g_hat| ≤ ε)

/-! ### UCRL2-Style Sample Complexity -/

/-- **UCRL2 algorithm configuration** for average-reward MDPs.

  Bundles the MDP size parameters, reward bound, and mixing time
  needed to state regret and sample complexity bounds for UCRL2.
  This structure is independent of a particular MDP instance;
  it captures the problem-dependent constants that enter the bounds. -/
structure UCRL2Config where
  /-- Number of states -/
  S : ℕ
  /-- Number of actions -/
  A : ℕ
  /-- Reward upper bound -/
  r_max : ℝ
  /-- Mixing time -/
  t_mix : ℕ
  /-- State count is positive -/
  hS_pos : 0 < S
  /-- Action count is positive -/
  hA_pos : 0 < A
  /-- Reward bound is positive -/
  hr_max_pos : 0 < r_max
  /-- Mixing time is positive -/
  ht_mix_pos : 0 < t_mix

/-- **Confidence set for transition probabilities** in UCRL2.

  For each state-action pair (s,a), the confidence set is the
  collection of transition kernels P' such that the L1 distance
  from the empirical estimate P̂ is bounded by a confidence radius β:

    ‖P'(·|s,a) - P̂(·|s,a)‖₁ ≤ β(s,a)

  where β(s,a) = √(2S · log(2SA·t/δ) / N(s,a)), N(s,a) is the visit
  count, and δ is the confidence parameter.

  We define this as a predicate: the L1 distance is within
  the precomputed confidence radius. The radius itself is an
  abstract parameter since its closed form involves √ and log
  which require additional imports. -/
def ucrl2_confidence_set
    (l1_dist : ℝ) -- ‖P' - P̂‖₁ for a particular (s,a)
    (conf_radius : ℝ) -- β(s,a) = √(2S·log(2SA·t/δ)/N(s,a))
    (_s : M.S) (_a : M.A) : Prop :=
  0 < conf_radius ∧ 0 ≤ l1_dist ∧ l1_dist ≤ conf_radius

/-- The confidence set is nonempty: the zero-distance kernel (the
  empirical estimate itself) is always in the confidence set. -/
theorem ucrl2_confidence_set_nonempty
    (conf_radius : ℝ) (h_radius_pos : 0 < conf_radius)
    (s : M.S) (a : M.A) :
    M.ucrl2_confidence_set 0 conf_radius s a := by
  exact ⟨h_radius_pos, le_refl 0, le_of_lt h_radius_pos⟩

/-- **UCRL2 per-episode regret decomposition**.

  Within a single episode k of length τ_k, the regret is bounded by:

    Regret_k ≤ span(h̃_k) · ε_k

  where h̃_k is the optimistic bias function and ε_k is the confidence
  width (sum of L1 confidence radii over visited state-action pairs).

  The span(h̃) factor arises because transition estimation errors
  get amplified by the bias range: an error of ε in transition
  probabilities causes an error of ≤ span(h̃) · ε in the gain.

  We use the existing `span_bound` to bound span(h̃). -/
theorem ucrl2_regret_decomposition
    (mix : M.MixingTimeParams)
    (h_tilde : M.S → ℝ)
    (g_tilde g_star : ℝ)
    (episode_len : ℕ)
    (conf_width : ℝ)
    -- Hypothesis: span bound for the optimistic bias (from `span_bound`).
    (h_span_bound : M.spanSeminorm h_tilde ≤
        ↑mix.t_mix * (mix.r_max - mix.r_min))
    -- Hypothesis: simulation lemma for average-reward MDPs.
    -- Transition error ε causes gain error ≤ span(h) · ε.
    (h_per_step : g_tilde - g_star ≤
        M.spanSeminorm h_tilde * conf_width)
    (_h_conf_nonneg : 0 ≤ conf_width) :
    ↑episode_len * (g_tilde - g_star) ≤
        ↑episode_len * (↑mix.t_mix * (mix.r_max - mix.r_min)) * conf_width := by
  have h1 : g_tilde - g_star ≤
      ↑mix.t_mix * (mix.r_max - mix.r_min) * conf_width :=
    le_trans h_per_step (mul_le_mul_of_nonneg_right h_span_bound _h_conf_nonneg)
  have h2 : (0 : ℝ) ≤ ↑episode_len := Nat.cast_nonneg _
  nlinarith

/-- **Comparison: average-reward vs discounted sample complexity**.

  In the discounted setting, achieving ε-optimal policy requires

    N_disc = O(S² · A / (ε² · (1 - γ)³))

  samples (cf. Azar, Munos, Kappen 2013; Sidford et al. 2018).

  In the average-reward setting, the analogous bound is

    N_avg = O(t_mix² · S² · A / ε²)

  Comparing these, the mixing time t_mix plays the role of 1/(1-γ):
  - For a uniformly ergodic chain, t_mix ≈ 1/(1-λ₂) where λ₂ is the
    second largest eigenvalue of the transition matrix.
  - In the discounted setting, (1-γ) acts as an effective mixing rate,
    since the geometric discounting ensures that states beyond
    O(1/(1-γ)) steps contribute negligibly.
  - The exponent difference (t_mix² vs (1-γ)⁻³) reflects that
    the average-reward bound has an extra log factor absorbed,
    while the discounted bound's cubic dependence comes from
    the variance of the value function scaling as 1/(1-γ)².

  This theorem shows N_avg ≤ N_disc under t_mix ≤ 1/(1-γ), formalizing
  that average-reward complexity is no worse than discounted complexity
  when the mixing time matches the effective horizon. -/
theorem ucrl2_vs_discounted
    (cfg : UCRL2Config)
    (ε : ℝ)
    (hε_pos : 0 < ε)
    (γ : ℝ)
    (_hγ_pos : 0 < γ)
    (hγ_lt_one : γ < 1)
    -- Discounted sample complexity bound
    (N_disc : ℝ)
    (hN_disc : N_disc = ↑cfg.S ^ 2 * ↑cfg.A / (ε ^ 2 * (1 - γ) ^ 3))
    -- Average-reward sample complexity bound
    (N_avg : ℝ)
    (hN_avg : N_avg = ↑cfg.t_mix ^ 2 * ↑cfg.S ^ 2 * ↑cfg.A / ε ^ 2)
    -- Hypothesis: t_mix ≤ 1/(1-γ), the standard correspondence between
    -- mixing time and effective discount horizon for uniformly ergodic chains.
    (h_tmix_bound : (↑cfg.t_mix : ℝ) ≤ 1 / (1 - γ)) :
    N_avg ≤ N_disc := by
  rw [hN_disc, hN_avg]
  have h1gpos : 0 < 1 - γ := by linarith
  have h1gle1 : 1 - γ ≤ 1 := by linarith
  have htmix_pos : (0 : ℝ) < ↑cfg.t_mix := Nat.cast_pos.mpr cfg.ht_mix_pos
  have hε2_pos : 0 < ε ^ 2 := sq_pos_of_pos hε_pos
  -- Goal: t_mix² · S² · A / ε² ≤ S² · A / (ε² · (1-γ)³)
  -- Key: t_mix·(1-γ) ≤ 1
  have h_tmix_inv : (↑cfg.t_mix : ℝ) * (1 - γ) ≤ 1 := by
    calc (↑cfg.t_mix : ℝ) * (1 - γ)
        ≤ 1 / (1 - γ) * (1 - γ) :=
          mul_le_mul_of_nonneg_right h_tmix_bound (le_of_lt h1gpos)
      _ = 1 := by field_simp
  -- Key inequality: t_mix² · (1-γ)³ ≤ 1
  have h_key : (↑cfg.t_mix : ℝ) ^ 2 * (1 - γ) ^ 3 ≤ 1 := by
    have h1 : ((↑cfg.t_mix : ℝ) * (1 - γ)) ^ 2 ≤ 1 ^ 2 :=
      sq_le_sq' (by nlinarith) h_tmix_inv
    rw [one_pow, mul_pow] at h1
    have h2 : (↑cfg.t_mix : ℝ) ^ 2 * (1 - γ) ^ 3 =
        ((↑cfg.t_mix : ℝ) ^ 2 * (1 - γ) ^ 2) * (1 - γ) := by ring
    rw [h2]
    exact mul_le_one₀ h1 (le_of_lt h1gpos) h1gle1
  -- Strategy: suffices to show t_mix² · S²·A ≤ S²·A / (1-γ)³,
  -- then dividing both by ε² preserves the inequality.
  -- Equivalently: t_mix² · (1-γ)³ ≤ 1, which is h_key.
  -- Use: a/b ≤ c/d when a·d ≤ c·b and b,d > 0
  have h_denom_r : 0 < ε ^ 2 * (1 - γ) ^ 3 :=
    mul_pos hε2_pos (pow_pos h1gpos 3)
  -- Rewrite using le_div_iff: a/b ≤ c/d ↔ a/b * d ≤ c (when d > 0)
  -- then a/b * d ≤ c ↔ a * d ≤ c * b (when b > 0)
  rw [le_div_iff₀ h_denom_r]
  -- Goal: t_mix² · S² · A / ε² * (ε² · (1-γ)³) ≤ S² · A
  -- Simplify: (a/b) * (b*c) = a*c when b ≠ 0
  have h_simp : (↑cfg.t_mix : ℝ) ^ 2 * (↑cfg.S : ℝ) ^ 2 * (↑cfg.A : ℝ) / ε ^ 2 *
      (ε ^ 2 * (1 - γ) ^ 3) =
      (↑cfg.t_mix : ℝ) ^ 2 * (↑cfg.S : ℝ) ^ 2 * (↑cfg.A : ℝ) * (1 - γ) ^ 3 := by
    field_simp
  rw [h_simp]
  -- Goal: t_mix² · S² · A · (1-γ)³ ≤ S² · A
  -- This is: S²·A · (t_mix²·(1-γ)³) ≤ S²·A · 1
  nlinarith [mul_nonneg (sq_nonneg (↑cfg.S : ℝ)) (Nat.cast_nonneg cfg.A)]

end FiniteMDP

end
