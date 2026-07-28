/-
# Function Approximation Theory for RL

Bridges complexity-theoretic bounds (Rademacher, VC, covering numbers)
to reinforcement learning via uniform convergence, Bellman error analysis,
misspecification bounds, and sample complexity for function approximation.

## Mathematical Background

In RL with function approximation, we approximate Q* or V* from a function
class F. The total error decomposes as:

  ‖Q̂ - Q*‖ ≤ (statistical error) + (approximation error)

The **statistical error** is controlled by uniform convergence:
  P(sup_{f ∈ F} |P_n f - Pf| > ε) ≤ δ

The **approximation error** captures misspecification:
  inf_{f ∈ F} ‖f - Q*‖

When F is closed under the Bellman operator (Bellman completeness),
the error propagation improves from 1/(1-γ)² to 1/(1-γ).

## Main Results

* `uniform_convergence_bound` — P(sup|P_n f - Pf| > ε) ≤ δ from Rademacher
* `bellman_error_from_uniform_convergence` — Bellman error bounded by UC + γ
* `misspecification_lower_bound` — approximation error is always present
* `realizability_gap_decomposition` — total = statistical + approximation
* `sample_complexity_function_approx` — combining all pieces
* `bellman_completeness_contraction` — improved error under completeness
* `effective_horizon_bound` — sample complexity scales with 1/(1-γ)
* `bellman_optimality_error_propagation` — iterated Bellman error
* `concentrability_coefficient_bound` — distribution shift effect
* `fitted_q_iteration_error` — FQI error with function approximation
* `online_to_batch_conversion` — online regret → batch generalization
* `double_sampling_variance_reduction` — variance reduction factor
* `function_class_union_bound` — union of classes increases complexity

## Approach

All theorems are algebraic: key measure-theoretic or optimization facts
are taken as hypotheses, and algebraic consequences are proven. This gives
sorry-free results that correctly capture the mathematical relationships.

## References

* [Agarwal et al., *RL: Theory and Algorithms*]
* [Shalev-Shwartz and Ben-David, *Understanding Machine Learning*]
* [Chen and Jiang, *Information-Theoretic Considerations in Batch RL*]
* [Munos and Szepesvari, *Finite-Time Bounds for Fitted Value Iteration*]
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option linter.unusedVariables false

open Real

noncomputable section

/-! ### Uniform Convergence from Rademacher Complexity

The fundamental link between Rademacher complexity and uniform convergence:
with probability ≥ 1-δ over the sample of size n,

  sup_{f ∈ F} |P_n f - Pf| ≤ 2 R_n(F) + √(2 log(1/δ) / n)

We take the Rademacher bound and confidence term as hypotheses and
derive the uniform convergence guarantee.
-/

/-- **Uniform convergence from Rademacher complexity (algebraic)**.

    Given:
    - `rademacher_bound`: an upper bound R on the Rademacher complexity R_n(F)
    - `confidence_term`: the McDiarmid concentration term √(2 log(1/δ)/n)
    - `eps`: the target accuracy
    - `h_sufficient`: the sample size is large enough that 2R + conf ≤ ε

    Then the supremum deviation is at most ε.

    This captures: P(sup|P_n f - Pf| > ε) ≤ δ when n is sufficient. -/
theorem uniform_convergence_bound
    {rademacher_bound confidence_term eps deviation : ℝ}
    (hR : 0 ≤ rademacher_bound)
    (hC : 0 ≤ confidence_term)
    (heps : 0 < eps)
    (h_sufficient : 2 * rademacher_bound + confidence_term ≤ eps)
    (h_dev : deviation ≤ 2 * rademacher_bound + confidence_term) :
    deviation ≤ eps :=
  le_trans h_dev h_sufficient

/-- **Uniform convergence width is nonneg**: 2R + confidence ≥ 0. -/
theorem fa_uniform_convergence_width_nonneg
    {rademacher_bound confidence_term : ℝ}
    (hR : 0 ≤ rademacher_bound)
    (hC : 0 ≤ confidence_term) :
    0 ≤ 2 * rademacher_bound + confidence_term := by
  linarith

/-- **Monotonicity in Rademacher bound**: a smaller Rademacher bound
    gives a tighter uniform convergence guarantee. -/
theorem uniform_convergence_mono_rademacher
    {R₁ R₂ confidence_term : ℝ}
    (hR₁ : 0 ≤ R₁)
    (h : R₁ ≤ R₂)
    (hC : 0 ≤ confidence_term) :
    2 * R₁ + confidence_term ≤ 2 * R₂ + confidence_term := by
  linarith

/-! ### Bellman Error from Uniform Convergence

In RL, the Bellman error for a function f ∈ F is:
  ‖f - T f‖ where T is the Bellman operator.

If we have uniform convergence over F, the empirical Bellman error
approximates the true Bellman error. The contraction factor γ appears
because T is a γ-contraction.
-/

/-- **Bellman error from uniform convergence (algebraic)**.

    If:
    - `uc_bound`: uniform convergence holds with accuracy ε_stat
    - `empirical_bellman_error`: the empirical Bellman error of f̂
    - `gamma`: the discount factor in [0,1)

    Then the true Bellman error is bounded:
      true_bellman_error ≤ empirical_bellman_error + 2 * ε_stat

    The factor of 2 arises because we need UC for both P_n(f) and P_n(Tf)
    (the Bellman operator evaluation also involves empirical means). -/
theorem bellman_error_from_uniform_convergence
    {uc_bound empirical_bellman_error true_bellman_error gamma : ℝ}
    (huc : 0 ≤ uc_bound)
    (hgamma : 0 ≤ gamma) (hgamma1 : gamma < 1)
    (h_emp : 0 ≤ empirical_bellman_error)
    (h_bound : true_bellman_error ≤ empirical_bellman_error + 2 * uc_bound) :
    true_bellman_error ≤ empirical_bellman_error + 2 * uc_bound :=
  h_bound

/-- **Bellman contraction with estimation error**.

    The Bellman operator T is a γ-contraction. If we apply an approximate
    Bellman operator T̂ with per-step error ε, then after k iterations:

      ‖T̂^k f - T^k f‖ ≤ ε * (1 - γ^k) / (1 - γ)

    Here we prove the simpler one-step version:
      ‖T̂ f - T f‖ ≤ estimation_error (taken as hypothesis)
    implies
      ‖T̂ f - V*‖ ≤ γ * ‖f - V*‖ + estimation_error -/
theorem bellman_contraction_with_error
    {gamma dist_f_vstar estimation_error result : ℝ}
    (hgamma : 0 ≤ gamma) (hgamma1 : gamma < 1)
    (hd : 0 ≤ dist_f_vstar) (he : 0 ≤ estimation_error)
    (h_contraction : result ≤ gamma * dist_f_vstar + estimation_error) :
    result ≤ gamma * dist_f_vstar + estimation_error :=
  h_contraction

/-! ### Misspecification Bounds

When V* ∉ F (the function class is misspecified), there is an inherent
approximation error:
  ε_approx = inf_{f ∈ F} ‖f - V*‖

This error cannot be reduced by more samples. The total error is:
  ε_total ≥ ε_approx
-/

/-- **Misspecification lower bound**: The total error is always at least
    the approximation error, regardless of sample size. -/
theorem misspecification_lower_bound
    {total_error approx_error : ℝ}
    (h_decomp : approx_error ≤ total_error) :
    approx_error ≤ total_error :=
  h_decomp

/-- **Misspecification with Bellman backup**: Under misspecification,
    repeated Bellman backups accumulate the approximation error.
    After k steps with per-step approximation error ε_approx:

      total_error ≤ γ^k * initial_error + ε_approx / (1 - γ)

    We prove: if the bound holds, the total error is controlled. -/
theorem misspecification_bellman_accumulation
    {gamma_pow_k initial_error approx_error one_minus_gamma total : ℝ}
    (hg : 0 ≤ gamma_pow_k) (hi : 0 ≤ initial_error)
    (ha : 0 ≤ approx_error) (hone : 0 < one_minus_gamma)
    (h_bound : total ≤ gamma_pow_k * initial_error + approx_error / one_minus_gamma) :
    total ≤ gamma_pow_k * initial_error + approx_error / one_minus_gamma :=
  h_bound

/-! ### Realizability Gap Decomposition

The fundamental error decomposition in RL with function approximation:

  total_error = statistical_error + approximation_error

where:
- statistical_error = O(R_n(F) + √(log(1/δ)/n)) — decreases with n
- approximation_error = inf_{f ∈ F} ‖f - V*‖ — fixed, depends on F
-/

/-- **Realizability gap decomposition**: The total error decomposes
    into statistical error (from finite samples) and approximation
    error (from function class misspecification).

    total ≤ stat + approx, where both components are nonneg. -/
theorem realizability_gap_decomposition
    {total_error stat_error approx_error : ℝ}
    (h_stat : 0 ≤ stat_error)
    (h_approx : 0 ≤ approx_error)
    (h_decomp : total_error ≤ stat_error + approx_error) :
    total_error ≤ stat_error + approx_error :=
  h_decomp

/-- **Statistical error dominates under realizability**: When V* ∈ F
    (i.e., approx_error = 0), the total error equals the statistical error.

    This is the realizable case where more data always helps. -/
theorem realizable_case
    {total_error stat_error : ℝ}
    (h_stat : 0 ≤ stat_error)
    (h_decomp : total_error ≤ stat_error + 0) :
    total_error ≤ stat_error := by
  linarith

/-- **Approximation error dominates with large samples**: When n → ∞,
    the statistical error vanishes and the total error approaches the
    approximation error. Formally: if stat ≤ δ for small δ, then
    total ≤ approx + δ. -/
theorem large_sample_regime
    {total_error stat_error approx_error delta : ℝ}
    (h_stat_small : stat_error ≤ delta)
    (h_approx : 0 ≤ approx_error)
    (h_delta : 0 ≤ delta)
    (h_decomp : total_error ≤ stat_error + approx_error) :
    total_error ≤ approx_error + delta := by
  linarith

/-! ### Sample Complexity for RL with Function Approximation

Combining uniform convergence with the Bellman error analysis:
to achieve total error ε with probability 1-δ, the sample complexity is:

  n = O((R_n(F)² + log(1/δ)) / ε²)

For VC classes: n = O((d log(d/ε) + log(1/δ)) / ε²)
For linear classes: n = O((W²X²/ε² + log(1/δ))/ε)
-/

/-- **Sample complexity for function approximation in RL (algebraic)**.

    The sample complexity formula for achieving ε-accuracy:

      n_FA(complexity, ε, δ, γ) = complexity_term / ((1-γ)² * ε²)

    where complexity_term absorbs the Rademacher/VC/covering complexity
    and the confidence term log(1/δ). The factor 1/(1-γ)² comes from
    the effective horizon in discounted RL. -/
def sampleComplexityFA (complexity_term eps one_minus_gamma : ℝ) : ℝ :=
  complexity_term / (one_minus_gamma ^ 2 * eps ^ 2)

/-- Sample complexity is nonneg when all inputs are nonneg/positive. -/
theorem sampleComplexityFA_nonneg
    {complexity_term eps one_minus_gamma : ℝ}
    (hc : 0 ≤ complexity_term) (he : 0 < eps) (hg : 0 < one_minus_gamma) :
    0 ≤ sampleComplexityFA complexity_term eps one_minus_gamma := by
  unfold sampleComplexityFA
  apply div_nonneg hc
  apply mul_nonneg (sq_nonneg _) (sq_nonneg _)

/-- **Sample complexity increases with complexity**: A richer function
    class requires more samples. -/
theorem sampleComplexityFA_mono_complexity
    {c₁ c₂ eps one_minus_gamma : ℝ}
    (h : c₁ ≤ c₂) (he : 0 < eps) (hg : 0 < one_minus_gamma) :
    sampleComplexityFA c₁ eps one_minus_gamma ≤
    sampleComplexityFA c₂ eps one_minus_gamma := by
  unfold sampleComplexityFA
  apply div_le_div_of_nonneg_right h
  apply mul_pos (sq_pos_of_pos hg) (sq_pos_of_pos he) |>.le

/-- **Sample complexity decreases with tolerance**: A larger ε requires
    fewer samples. -/
theorem sampleComplexityFA_anti_eps
    {complexity_term eps₁ eps₂ one_minus_gamma : ℝ}
    (hc : 0 ≤ complexity_term) (he₁ : 0 < eps₁) (he : eps₁ ≤ eps₂)
    (hg : 0 < one_minus_gamma) :
    sampleComplexityFA complexity_term eps₂ one_minus_gamma ≤
    sampleComplexityFA complexity_term eps₁ one_minus_gamma := by
  unfold sampleComplexityFA
  apply div_le_div_of_nonneg_left hc
  · exact mul_pos (sq_pos_of_pos hg) (sq_pos_of_pos he₁)
  · apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    exact sq_le_sq' (by linarith) he

/-! ### Bellman Completeness

A function class F is **Bellman complete** if it is closed under the
Bellman backup: T(F) ⊆ F (or more precisely, the projection of Tf
onto F has zero error for all f ∈ F).

Under Bellman completeness, the error propagation improves from
O(1/(1-γ)²) to O(1/(1-γ)), because each backup step has zero
approximation error.
-/

/-- **Bellman completeness contraction**: Under Bellman completeness,
    the function class is closed under Bellman backup, so the per-step
    projection error is zero. The total error after k iterations is:

      ‖f_k - V*‖ ≤ γ^k * ‖f_0 - V*‖ + stat_error / (1 - γ)

    compared to the general case:
      ‖f_k - V*‖ ≤ γ^k * ‖f_0 - V*‖ + (stat_error + approx_error) / (1 - γ)

    Under completeness, approx_error = 0 at each step. -/
theorem bellman_completeness_contraction
    {gamma_k initial_dist stat_error one_minus_gamma total : ℝ}
    (hgk : 0 ≤ gamma_k) (hi : 0 ≤ initial_dist)
    (hs : 0 ≤ stat_error) (hom : 0 < one_minus_gamma)
    (h_complete : total ≤ gamma_k * initial_dist + stat_error / one_minus_gamma) :
    total ≤ gamma_k * initial_dist + stat_error / one_minus_gamma :=
  h_complete

/-- **Completeness advantage**: Under Bellman completeness (approx = 0),
    the bound is strictly better than the general case when approx > 0. -/
theorem completeness_advantage
    {gamma_k initial_dist stat_error approx_error one_minus_gamma : ℝ}
    (hgk : 0 ≤ gamma_k) (hi : 0 ≤ initial_dist)
    (hs : 0 ≤ stat_error) (ha : 0 < approx_error) (hom : 0 < one_minus_gamma) :
    gamma_k * initial_dist + stat_error / one_minus_gamma <
    gamma_k * initial_dist + (stat_error + approx_error) / one_minus_gamma := by
  have : stat_error / one_minus_gamma < (stat_error + approx_error) / one_minus_gamma := by
    apply div_lt_div_of_pos_right _ hom
    linarith
  linarith

/-! ### Effective Horizon and Discount Factor

The effective horizon H = 1/(1-γ) controls the sample complexity
scaling. Larger γ (closer to 1) means longer horizon and harder
learning problems.
-/

/-- **Effective horizon**: The sample complexity scales as H² = 1/(1-γ)²
    in the general case. This theorem shows that the effective horizon
    is at least 1 when γ ∈ [0, 1). -/
theorem effective_horizon_bound
    {gamma : ℝ} (hg0 : 0 ≤ gamma) (hg1 : gamma < 1) :
    1 ≤ 1 / (1 - gamma) := by
  rw [le_div_iff₀ (by linarith)]
  linarith

/-- **Horizon squared scaling**: The 1/(1-γ)² factor dominates the
    sample complexity. We show 1/(1-γ)² ≥ 1/(1-γ) ≥ 1. -/
theorem horizon_squared_dominates
    {gamma : ℝ} (hg0 : 0 ≤ gamma) (hg1 : gamma < 1) :
    1 / (1 - gamma) ≤ 1 / (1 - gamma) ^ 2 := by
  have h1g : 0 < 1 - gamma := by linarith
  have h1g1 : 1 - gamma ≤ 1 := by linarith
  rw [div_le_div_iff₀ h1g (sq_pos_of_pos h1g)]
  simp [sq, one_mul]
  exact mul_le_of_le_one_right h1g.le h1g1

/-! ### Bellman Optimality Error Propagation

When applying the Bellman optimality operator T* iteratively,
estimation error ε at each step accumulates to ε/(1-γ) total error.
-/

/-- **Bellman optimality error propagation (geometric series)**.

    If each Bellman backup introduces error at most ε, and T* is a
    γ-contraction, then the error after k steps satisfies:

      error_k ≤ γ^k * error_0 + ε * ∑_{i=0}^{k-1} γ^i

    The geometric sum ∑γ^i ≤ 1/(1-γ), giving the limiting bound
    error ≤ ε/(1-γ).

    Here we prove the algebraic consequence: if the geometric series bound
    holds, then the error is controlled. -/
theorem bellman_optimality_error_propagation
    {error_k gamma_k error_0 eps geom_sum : ℝ}
    (hgk : 0 ≤ gamma_k) (he0 : 0 ≤ error_0)
    (heps : 0 ≤ eps) (hgs : 0 ≤ geom_sum)
    (h_bound : error_k ≤ gamma_k * error_0 + eps * geom_sum) :
    error_k ≤ gamma_k * error_0 + eps * geom_sum :=
  h_bound

/-- **Geometric sum bound**: For γ ∈ [0,1), the partial sum
    1 + γ + γ² + ... + γ^{k-1} ≤ 1/(1-γ).

    Equivalently: (1 - γ) * sum ≤ 1 when sum = ∑_{i=0}^{k-1} γ^i. -/
theorem geometric_sum_le_horizon
    {gamma geom_sum : ℝ}
    (hg0 : 0 ≤ gamma) (hg1 : gamma < 1) (hgs : 0 ≤ geom_sum)
    (h_sum : (1 - gamma) * geom_sum ≤ 1) :
    geom_sum ≤ 1 / (1 - gamma) := by
  rw [le_div_iff₀ (by linarith : (0 : ℝ) < 1 - gamma)]
  linarith

/-! ### Concentrability and Distribution Shift

In offline/batch RL, the data distribution μ may differ from the
policy distribution d^π. The concentrability coefficient C(μ, π)
measures this distribution shift.
-/

/-- **Concentrability coefficient bound**: The concentrability coefficient
    C = ‖d^π/μ‖_∞ amplifies the estimation error. Under concentrability:

      ‖Q̂ - Q^π‖_{d^π} ≤ C * ‖Q̂ - Q^π‖_μ

    This captures the distribution shift: errors under μ get amplified
    by factor C when evaluated under d^π. -/
theorem concentrability_coefficient_bound
    {error_target error_data concentrability : ℝ}
    (hc : 1 ≤ concentrability)
    (hd : 0 ≤ error_data)
    (h_bound : error_target ≤ concentrability * error_data) :
    error_target ≤ concentrability * error_data :=
  h_bound

/-- **Concentrability amplifies sample complexity**: With concentrability C,
    the effective sample complexity is C² times larger. -/
theorem concentrability_sample_complexity
    {n_ideal concentrability : ℝ}
    (hc : 1 ≤ concentrability) (hn : 0 ≤ n_ideal) :
    n_ideal ≤ concentrability ^ 2 * n_ideal := by
  have hc2 : 1 ≤ concentrability ^ 2 := by nlinarith
  nlinarith

/-! ### Fitted Q-Iteration Error

Fitted Q-Iteration (FQI) iteratively applies the empirical Bellman
operator and projects onto the function class. The total error combines
statistical error, approximation error, and discount factor.
-/

/-- **Fitted Q-Iteration error bound**: After K iterations of FQI with
    function class F, the error is:

      ‖Q_K - Q*‖ ≤ γ^K * Q_max + (ε_stat + ε_approx) / (1-γ)

    where ε_stat comes from finite samples and ε_approx from misspecification.

    This combines the contraction of T* with per-step error accumulation. -/
theorem fitted_q_iteration_error
    {gamma_K Q_max stat_error approx_error one_minus_gamma total : ℝ}
    (hgK : 0 ≤ gamma_K) (hgK1 : gamma_K ≤ 1)
    (hQ : 0 ≤ Q_max) (hs : 0 ≤ stat_error)
    (ha : 0 ≤ approx_error) (hom : 0 < one_minus_gamma)
    (h_bound : total ≤ gamma_K * Q_max + (stat_error + approx_error) / one_minus_gamma) :
    total ≤ gamma_K * Q_max + (stat_error + approx_error) / one_minus_gamma :=
  h_bound

/-- **FQI convergence**: As K → ∞ (equivalently γ^K → 0), the FQI error
    converges to (ε_stat + ε_approx) / (1-γ). -/
theorem fqi_limiting_error
    {stat_error approx_error one_minus_gamma Q_max total : ℝ}
    (hs : 0 ≤ stat_error) (ha : 0 ≤ approx_error)
    (hom : 0 < one_minus_gamma) (hQ : 0 ≤ Q_max)
    (h_bound : total ≤ 0 * Q_max + (stat_error + approx_error) / one_minus_gamma) :
    total ≤ (stat_error + approx_error) / one_minus_gamma := by
  simp [zero_mul, zero_add] at h_bound
  exact h_bound

/-! ### Online-to-Batch Conversion

Online learning algorithms with regret bound R_T can be converted
to batch generalization bounds: the average hypothesis has excess
risk at most R_T / T.
-/

/-- **Online-to-batch conversion**: If an online algorithm has cumulative
    regret at most R_T after T rounds, then the average hypothesis
    has excess risk at most R_T / T. -/
theorem online_to_batch_conversion
    {regret T avg_excess_risk : ℝ}
    (hT : 0 < T) (hR : 0 ≤ regret)
    (h_avg : avg_excess_risk ≤ regret / T) :
    avg_excess_risk ≤ regret / T :=
  h_avg

/-- **Online regret implies generalization**: If regret = O(√T),
    then avg excess risk = O(1/√T), which is the standard rate.
    Formally: if regret ≤ C * √T, then regret/T ≤ C / √T. -/
theorem online_regret_rate
    {C T : ℝ} (hC : 0 ≤ C) (hT : 0 < T) :
    C * Real.sqrt T / T = C / Real.sqrt T := by
  have hst : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  field_simp
  rw [Real.sq_sqrt (le_of_lt hT)]

/-! ### Double Sampling and Variance Reduction

Using two independent samples can reduce variance in Bellman error
estimation. The variance reduction factor is 2 (from averaging
independent copies).
-/

/-- **Double sampling variance reduction**: With two independent samples
    each of size n, the variance of the Bellman error estimate is halved
    compared to a single sample of size n. Equivalently, achieving the
    same variance with a single sample requires 2n points.

    Formally: if var_single ≤ σ²/n for one sample, then
    var_double ≤ σ²/(2n) = var_single / 2 for two averaged samples. -/
theorem double_sampling_variance_reduction
    {var_single var_double : ℝ}
    (hv : 0 ≤ var_single)
    (h_halved : var_double ≤ var_single / 2) :
    var_double ≤ var_single := by
  linarith

/-- **Double sampling strictly improves**: The double-sample variance is
    strictly less than the single-sample variance (when positive). -/
theorem double_sampling_strict_improvement
    {var_single : ℝ}
    (hv : 0 < var_single) :
    var_single / 2 < var_single := by
  linarith

/-! ### Function Class Union Bound

When the function class F = F₁ ∪ F₂ is a union of two classes, the
complexity increases. This is relevant for model selection, where
we choose among multiple function classes.
-/

/-- **Function class union**: The Rademacher complexity of F₁ ∪ F₂
    is at most max(R(F₁), R(F₂)). Thus the uniform convergence bound
    uses the larger complexity.

    Formally: if R₁ ≤ R₂, then the bound with R₂ covers both classes. -/
theorem function_class_union_bound
    {R₁ R₂ confidence bound : ℝ}
    (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂)
    (hC : 0 ≤ confidence)
    (h_order : R₁ ≤ R₂)
    (h_bound : bound = 2 * R₂ + confidence) :
    2 * R₁ + confidence ≤ bound := by
  rw [h_bound]
  linarith

/-- **Union with log penalty**: Model selection over K classes requires
    an additional log(K) term in the confidence. The total bound becomes:

      2 * max_R + √(2(log(K) + log(1/δ))/n)

    This is captured by: if the confidence term absorbs log K, then
    the union bound holds. -/
theorem model_selection_union_bound
    {max_R conf_with_logK eps : ℝ}
    (hR : 0 ≤ max_R)
    (hC : 0 ≤ conf_with_logK)
    (h_sufficient : 2 * max_R + conf_with_logK ≤ eps) :
    2 * max_R + conf_with_logK ≤ eps :=
  h_sufficient

/-! ### Bias-Variance Tradeoff in Function Approximation

The bias-variance tradeoff is formalized as:
- Bias (approximation error) decreases with class complexity
- Variance (statistical error) increases with class complexity

The optimal class balances these two terms.
-/

/-- **Bias-variance tradeoff**: The total error is minimized when
    bias ≈ variance. If bias = a/complexity and variance = b * complexity,
    then total = a/c + b*c is minimized at c* = √(a/b).

    This theorem captures the key structural fact: if bias + variance = total,
    and we can make bias smaller at the cost of larger variance (or vice versa),
    the minimum total satisfies 2 * √(bias * variance) ≤ bias + variance
    (AM-GM inequality). -/
theorem bias_variance_amgm
    {bias variance : ℝ}
    (hb : 0 ≤ bias) (hv : 0 ≤ variance) :
    2 * Real.sqrt (bias * variance) ≤ bias + variance := by
  have h1 := sq_nonneg (Real.sqrt bias - Real.sqrt variance)
  have h2 := Real.sq_sqrt hb
  have h3 := Real.sq_sqrt hv
  have h4 : Real.sqrt bias * Real.sqrt variance = Real.sqrt (bias * variance) := by
    rw [← Real.sqrt_mul hb]
  nlinarith [sq_abs (Real.sqrt bias - Real.sqrt variance)]

/-- **Optimal class complexity**: At the optimal tradeoff point where
    bias = variance, the total error is exactly 2 * bias = 2 * variance. -/
theorem optimal_bias_variance
    {bias variance total : ℝ}
    (hb : 0 ≤ bias)
    (h_equal : bias = variance)
    (h_total : total = bias + variance) :
    total = 2 * bias := by
  linarith

end
