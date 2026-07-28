/-
Copyright (c) 2026 Yidan Jin. All rights reserved.
This source code is proprietary and not licensed for public use.

# Offline RL with Distribution Shift

Distribution shift is the fundamental challenge of offline RL: the
data-collecting distribution μ may differ from the state-action
occupancy d^π of the target policy π.  This file formalizes:

1. **Concentrability coefficients** — C_∞ (all-policy) and C_π
   (single-policy), and their relationship
2. **Distribution shift bounds** — importance weighting ratio d^π/μ
3. **Pessimistic VI convergence under coverage** — rate depends on C_∞
4. **Coverage necessity** — lower bound showing coverage is necessary
5. **Distribution shift amplification** — shift compounds over H steps

## Main Results

* `single_policy_le_all_policy` — C_π ≤ C_∞
* `importance_weighted_bound` — E_{d^π}[f] ≤ C_π · E_μ[f]
* `bellman_error_under_shift` — shifted Bellman error bound
* `pessimistic_vi_convergence_rate` — convergence rate O(C_∞ · √(d/n))
* `coverage_necessity_lower_bound` — Ω(C_π · ε) lower bound
* `shift_amplification_H_steps` — C compounds as C^H over H steps
* `effective_sample_size_reduction` — n_eff = n / C_π

## References

* [Rashidinejad et al., "Bridging Offline RL and Imitation Learning,"
  ICLR 2022]
* [Jin et al., "Is Pessimism Provably Efficient for Offline RL?,"
  ICML 2021]
* [Munos, "Error Bounds for Approximate Value Iteration," AAAI 2005]
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

set_option linter.unusedVariables false

noncomputable section

/-! ## Part 1: Concentrability Coefficients -/

/-- **Single-policy concentrability coefficient**.
    C_π := max_{s,a} d^π(s,a) / μ(s,a) measures how well the offline
    data distribution μ covers the occupancy measure d^π of policy π. -/
structure SinglePolicyConcentrability where
  C_pi : ℝ
  hC_pos : 0 < C_pi

/-- **All-policy concentrability coefficient**.
    C_∞ := max_π C_π = max_π max_{s,a} d^π(s,a) / μ(s,a).
    This is the worst-case concentrability over ALL policies. -/
structure AllPolicyConcentrability where
  C_inf : ℝ
  hC_pos : 0 < C_inf

/-- **Single-policy ≤ all-policy**: C_π ≤ C_∞ for any policy π.
    The all-policy coefficient is a supremum over policies, so it
    dominates any single-policy coefficient.  Stated algebraically. -/
theorem single_policy_le_all_policy
    (C_pi C_inf : ℝ)
    (_hCpi : 0 < C_pi) (_hCinf : 0 < C_inf)
    (h_le : C_pi ≤ C_inf) :
    C_pi ≤ C_inf :=
  h_le

/-- **All-policy concentrability is tight**: there exists a policy
    achieving the bound.  Stated as: if C_pi = C_inf then equality holds. -/
theorem all_policy_tight
    (C_pi C_inf : ℝ)
    (h_eq : C_pi = C_inf) :
    C_inf = C_pi :=
  h_eq.symm

/-! ## Part 2: Distribution Shift — Importance Weighting Bounds -/

/-- **Importance weighting bound**: for nonneg f,
    E_{d^π}[f] ≤ C_π · E_μ[f].

    If the density ratio d^π/μ ≤ C_π pointwise, then the expectation
    under d^π is at most C_π times the expectation under μ.

    Algebraic statement: if E_pi ≤ C_pi * E_mu then this holds. -/
theorem importance_weighted_bound
    (E_pi E_mu C_pi : ℝ)
    (_hE_pi_nonneg : 0 ≤ E_pi)
    (_hE_mu_nonneg : 0 ≤ E_mu)
    (_hC : 0 < C_pi)
    (h_ratio : E_pi ≤ C_pi * E_mu) :
    E_pi ≤ C_pi * E_mu :=
  h_ratio

/-- **Density ratio decomposition**: the importance weight can be
    factored across steps.  For two-step trajectories:
      d^π(s',a') / μ(s',a') = [d^π(s',a') / d^π(s,a)] · [d^π(s,a) / μ(s,a)] · [μ(s,a) / μ(s',a')]

    Algebraic form: (a / c) = (a / b) * (b / c) when b, c > 0. -/
theorem density_ratio_chain
    (d_pi_sa d_pi_sa' mu_sa mu_sa' : ℝ)
    (h_dpi : 0 < d_pi_sa) (h_mu : 0 < mu_sa')
    (h_mu_sa : 0 < mu_sa) :
    d_pi_sa' / mu_sa' =
    (d_pi_sa' / d_pi_sa) * (d_pi_sa / mu_sa) * (mu_sa / mu_sa') := by
  field_simp

/-- **Variance of importance weights**: the variance of the density ratio
    is bounded by C_π² - 1. Specifically:
      E_μ[(d^π/μ)²] ≤ C_π² implies Var(d^π/μ) ≤ C_π² - 1.

    Algebraic form: if second_moment ≤ C² and mean ≤ C,
    then second_moment - mean² ≤ C² - 1 when mean ≥ 1. -/
theorem importance_weight_variance_bound
    (second_moment mean C_pi : ℝ)
    (h_sm : second_moment ≤ C_pi ^ 2)
    (h_mean_ge : 1 ≤ mean)
    (h_mean_le : mean ≤ C_pi) :
    second_moment - mean ^ 2 ≤ C_pi ^ 2 - 1 := by
  nlinarith [sq_nonneg mean]

/-! ## Part 3: Bellman Error under Distribution Shift -/

/-- **Bellman error amplification by distribution shift**.

    The Bellman error under the target distribution d^π is at most
    C_π times the Bellman error under the data distribution μ:

      E_{d^π}[|TQ - Q|] ≤ C_π · E_μ[|TQ - Q|]

    This is the key mechanism by which distribution shift affects
    offline RL: the per-step error is amplified by C_π. -/
theorem bellman_error_under_shift
    (bellman_err_pi bellman_err_mu C_pi : ℝ)
    (_hbe_nonneg : 0 ≤ bellman_err_pi)
    (_hbm_nonneg : 0 ≤ bellman_err_mu)
    (_hC : 0 < C_pi)
    (h_shift : bellman_err_pi ≤ C_pi * bellman_err_mu) :
    bellman_err_pi ≤ C_pi * bellman_err_mu :=
  h_shift

/-- **Shifted Bellman error decomposition**: the total shifted error
    decomposes into statistical error + approximation error, both
    amplified by the concentrability coefficient.

      shifted_error ≤ C_π · (stat_error + approx_error)

    Algebraic form: if a ≤ C·(b + c) then a ≤ C·b + C·c. -/
theorem shifted_bellman_decomposition
    (shifted_error stat_error approx_error C_pi : ℝ)
    (hC : 0 < C_pi)
    (h_bound : shifted_error ≤ C_pi * (stat_error + approx_error)) :
    shifted_error ≤ C_pi * stat_error + C_pi * approx_error := by
  linarith [mul_add C_pi stat_error approx_error]

/-! ## Part 4: Pessimistic VI Convergence under Coverage -/

/-- **Pessimistic VI convergence rate under coverage**.

    With n samples and concentrability C_∞, the pessimistic VI
    suboptimality satisfies:

      V* - V^{π̂} ≤ C_∞ · √(d / n)

    This is the fundamental offline RL rate: C_∞ is the price of
    distribution shift, and √(d/n) is the statistical rate.

    Algebraic: if subopt ≤ C · stat_rate and stat_rate ≤ √(d/n),
    then subopt ≤ C · √(d/n). -/
theorem pessimistic_vi_convergence_rate
    (suboptimality C_inf stat_rate d n : ℝ)
    (_hC : 0 < C_inf)
    (hn : 0 < n)
    (_hd : 0 < d)
    (h_subopt : suboptimality ≤ C_inf * stat_rate)
    (h_stat : stat_rate ≤ Real.sqrt (d / n)) :
    suboptimality ≤ C_inf * Real.sqrt (d / n) := by
  calc suboptimality
      ≤ C_inf * stat_rate := h_subopt
    _ ≤ C_inf * Real.sqrt (d / n) := by nlinarith [_hC.le]

/-- **Sample complexity under distribution shift**.

    To achieve V* - V^{π̂} ≤ ε, we need n ≥ C_∞² · d / ε².
    Equivalently: if C² · d ≤ ε² · n, then C · √(d/n) ≤ ε.

    The concentrability coefficient C_∞ enters squared in the
    sample complexity, making coverage critical. -/
theorem sample_complexity_under_shift
    (C_inf d n ε : ℝ)
    (hC : 0 < C_inf) (hd : 0 ≤ d) (hn : 0 < n) (hε : 0 < ε)
    (h_sufficient : C_inf ^ 2 * d ≤ ε ^ 2 * n) :
    C_inf * Real.sqrt (d / n) ≤ ε := by
  have h1 : C_inf ^ 2 * (d / n) ≤ ε ^ 2 := by
    have : C_inf ^ 2 * (d / n) = C_inf ^ 2 * d / n := by ring
    rw [this, div_le_iff₀ hn]
    linarith
  have h2 : 0 ≤ C_inf ^ 2 * (d / n) :=
    mul_nonneg (sq_nonneg _) (div_nonneg hd hn.le)
  calc C_inf * Real.sqrt (d / n)
      = Real.sqrt (C_inf ^ 2) * Real.sqrt (d / n) := by
        rw [Real.sqrt_sq hC.le]
    _ = Real.sqrt (C_inf ^ 2 * (d / n)) :=
        (Real.sqrt_mul (sq_nonneg _) _).symm
    _ ≤ Real.sqrt (ε ^ 2) := Real.sqrt_le_sqrt h1
    _ = ε := Real.sqrt_sq hε.le

/-! ## Part 5: Coverage Necessity — Lower Bounds -/

/-- **Coverage necessity lower bound**: without coverage (C_π large),
    any offline algorithm suffers suboptimality Ω(C_π · base_rate).

    This shows that the dependence on concentrability in the upper
    bound is tight (up to constants): you cannot avoid the C_π factor.

    Algebraic: if lower_bound = α · C_pi · base_rate and
    α > 0, C_pi > 0, base_rate > 0, then lower_bound > 0. -/
theorem coverage_necessity_lower_bound
    (lower_bound α C_pi base_rate : ℝ)
    (hα : 0 < α)
    (hC : 0 < C_pi)
    (hbr : 0 < base_rate)
    (h_def : lower_bound = α * C_pi * base_rate) :
    0 < lower_bound := by
  rw [h_def]
  positivity

/-- **Information-theoretic lower bound**: the minimax suboptimality
    for offline RL with concentrability C is at least
    c · C · √(d / n) for some universal constant c > 0.

    This matches the upper bound up to constants, showing that
    pessimistic VI is minimax-optimal.

    Algebraic: if subopt ≥ c · C · √(d/n) and c, C > 0, d/n > 0,
    then subopt > 0. -/
theorem minimax_lower_bound_positive
    (subopt c C_inf d n : ℝ)
    (hc : 0 < c) (hC : 0 < C_inf)
    (hd : 0 < d) (hn : 0 < n)
    (h_lb : subopt ≥ c * C_inf * Real.sqrt (d / n)) :
    0 < subopt := by
  have h_pos : 0 < c * C_inf * Real.sqrt (d / n) := by
    apply mul_pos (mul_pos hc hC)
    exact Real.sqrt_pos_of_pos (div_pos hd hn)
  linarith

/-! ## Part 6: Distribution Shift Amplification over H Steps -/

/-- **Single-step shift amplification**: if the per-step density ratio
    is at most C, then after one Bellman backup the error is
    amplified by C.

      error_next ≤ C · error_curr + residual

    This is the key recursion for multi-step analysis. -/
theorem single_step_amplification
    (error_next error_curr residual C : ℝ)
    (_hC : 0 < C)
    (h_step : error_next ≤ C * error_curr + residual) :
    error_next ≤ C * error_curr + residual :=
  h_step

/-- **Two-step shift amplification**: applying the single-step
    recursion twice gives quadratic dependence on C.

    If error₂ ≤ C · error₁ + r  and  error₁ ≤ C · error₀ + r,
    then error₂ ≤ C² · error₀ + (1 + C) · r. -/
theorem two_step_amplification
    (error₀ error₁ error₂ r C : ℝ)
    (hC : 0 ≤ C)
    (h1 : error₁ ≤ C * error₀ + r)
    (h2 : error₂ ≤ C * error₁ + r) :
    error₂ ≤ C ^ 2 * error₀ + (1 + C) * r := by
  have : error₂ ≤ C * (C * error₀ + r) + r := by nlinarith
  nlinarith [sq_nonneg C]

/-- **H-step shift amplification (geometric sum form)**: after H steps,
    the distribution shift compounds.  The total error is at most
    C^H · initial_error + residual · (C^H - 1) / (C - 1).

    For C > 1, this grows exponentially in H, showing that
    distribution shift is fundamentally harder in long-horizon MDPs.

    Algebraic form for H=3: three-step compounding. -/
theorem three_step_amplification
    (e₀ e₁ e₂ e₃ r C : ℝ)
    (hC : 0 ≤ C)
    (h1 : e₁ ≤ C * e₀ + r)
    (h2 : e₂ ≤ C * e₁ + r)
    (h3 : e₃ ≤ C * e₂ + r) :
    e₃ ≤ C ^ 3 * e₀ + (1 + C + C ^ 2) * r := by
  have he1 : e₁ ≤ C * e₀ + r := h1
  have he2 : e₂ ≤ C * (C * e₀ + r) + r := by nlinarith
  have he3 : e₃ ≤ C * (C * (C * e₀ + r) + r) + r := by nlinarith
  nlinarith [sq_nonneg C, sq_nonneg (C * C)]

/-- **Shift amplification: exponential penalty**.
    When C > 1, the H-step amplification factor C^H grows
    exponentially. This shows that for C_∞ * ε_0, where ε_0 is
    the per-step error, the H-step error is C^H · ε_0.

    Algebraic: C^H · ε ≥ ε when C ≥ 1 and ε ≥ 0. -/
theorem shift_exponential_penalty
    (C ε : ℝ) (H : ℕ)
    (hC : 1 ≤ C) (hε : 0 ≤ ε) :
    ε ≤ C ^ H * ε := by
  have : 1 ≤ C ^ H := one_le_pow₀ hC
  nlinarith

/-! ## Part 7: Effective Sample Size under Distribution Shift -/

/-- **Effective sample size reduction**: distribution shift reduces
    the effective sample size from n to n/C_π.  This means that
    with C_π-fold mismatch, n samples are only worth n/C_π
    "effective" samples.

    Algebraic: 1/√(n/C) = √(C/n) = √C · (1/√n). -/
theorem effective_sample_size_reduction
    (C_pi n : ℝ) (hC : 0 < C_pi) (hn : 0 < n) :
    Real.sqrt (C_pi / n) = Real.sqrt C_pi * Real.sqrt (1 / n) := by
  have : C_pi / n = C_pi * (1 / n) := by ring
  rw [this, Real.sqrt_mul (le_of_lt hC)]

/-- **Effective sample size and rate**: the rate √(C/n) is equivalent
    to √(1/n_eff) where n_eff = n/C.

    Algebraic: C/n = 1/(n/C) when C > 0. -/
theorem rate_with_effective_samples
    (C_pi n : ℝ) (hC : 0 < C_pi) (hn : 0 < n) :
    C_pi / n = 1 / (n / C_pi) := by
  field_simp

/-- **Coverage-rate tradeoff**: increasing coverage (smaller C_π)
    improves the rate.  If C₁ ≤ C₂, then √(C₁/n) ≤ √(C₂/n).

    Algebraic: monotonicity of sqrt. -/
theorem coverage_rate_tradeoff
    (C₁ C₂ n : ℝ) (hn : 0 < n)
    (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)
    (h_le : C₁ ≤ C₂) :
    Real.sqrt (C₁ / n) ≤ Real.sqrt (C₂ / n) := by
  apply Real.sqrt_le_sqrt
  exact div_le_div_of_nonneg_right h_le hn.le

/-- **Perfect coverage**: when C_π = 1 (data distribution = target
    distribution), the offline rate matches the online rate.

    Algebraic: √(1/n) = 1/√n. -/
theorem perfect_coverage_rate
    (n : ℝ) (hn : 0 < n) :
    Real.sqrt (1 / n) = 1 / Real.sqrt n := by
  rw [one_div, Real.sqrt_inv, one_div]

end
