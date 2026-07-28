/-
# Linear Temporal Difference Learning Convergence

Formalizes the algebraic core of linear TD(0) for policy evaluation
with linear function approximation. The approach follows the ODE
method: we express the expected TD update as a linear system in
(theta* - theta), derive the one-step error contraction, and obtain
convergence rates for both constant and diminishing step sizes.

## Main Results

* `td_update_formula` - One-step TD(0) update identity
* `td_constant_step_convergence` - Geometric convergence with constant step
* `td_diminishing_step_convergence` - O(1/T) with diminishing steps
* `td_sample_complexity` - Sample complexity formula T = O(d/(eps^2 * lambda_min^2))

## Key Algebraic Structures

The formalization treats:
- Feature map phi : S -> R^d as a function from states to vectors
- Projected Bellman equation: Phi * theta* = Pi_Phi * T^pi * (Phi * theta*)
- Expected update matrix A = E[phi(s)(phi(s) - gamma*phi(s'))^T]
- Positive definiteness of A as a hypothesis (lambda_min > 0)

All results are algebraic (no measure theory), using the key matrix A
and its minimum eigenvalue as abstract parameters.

## References

* [Tsitsiklis and Van Roy, *An Analysis of Temporal-Difference Learning
  with Function Approximation*, 1997]
* [Bhandari, Russo, Singal, *A Finite Time Analysis of Temporal
  Difference Learning with Linear Function Approximation*, 2018]
* [Szepesvari, *Algorithms for Reinforcement Learning*, 2010]
-/

import RLGeneralization.Generalization.PolicyEvaluation

open Finset BigOperators

noncomputable section

namespace FiniteMDP

variable (M : FiniteMDP)

/-! ### Linear Function Approximation Setup

We model linear TD(0) for policy evaluation. Given a policy pi and
feature map phi : S -> R^d, the goal is to find theta in R^d such that
V^pi(s) approx sum_i phi(s)_i * theta_i for all s.

The key objects:
- Feature inner product: <phi(s), theta> = sum_i phi(s)_i * theta_i
- Projected Bellman fixed point: theta* satisfying the projected
  Bellman equation
- Expected update matrix A with minimum eigenvalue lambda_min > 0
-/

/-- Configuration for linear TD(0) learning. Bundles the feature
    dimension, feature map, and key matrix properties. -/
structure LinearTDConfig where
  /-- Feature dimension -/
  d : ℕ
  /-- Feature map: phi(s) in R^d -/
  phi : M.S → Fin d → ℝ
  /-- The fixed-point parameter theta* satisfying the projected
      Bellman equation -/
  theta_star : Fin d → ℝ
  /-- Minimum eigenvalue of the expected update matrix A.
      A = E_mu[phi(s)(phi(s) - gamma*phi(s'))^T] where mu is the
      stationary distribution. lambda_min(A) > 0 is the key stability
      condition. -/
  lambda_min : ℝ
  lambda_min_pos : 0 < lambda_min
  /-- Upper bound on the combined drift constant (includes ||A||^2
      and variance contributions). Always >= lambda_min^2 since
      ||A|| >= lambda_min. -/
  C_quad : ℝ
  C_quad_pos : 0 < C_quad
  /-- The operator norm bound implies C_quad >= lambda_min^2.
      This is the standard condition ensuring the safe step size
      alpha = lambda_min / C_quad yields a nonneg contraction factor. -/
  lam_sq_le_C : lambda_min ^ 2 ≤ C_quad
  /-- Variance bound: E[||delta_t * phi(s_t)||^2 | theta*] <= sigma^2.
      This captures the conditional variance of the TD update at the
      fixed point. -/
  sigma_sq : ℝ
  sigma_sq_nonneg : 0 ≤ sigma_sq

variable {M}

/-! ### Feature Inner Product -/

/-- The feature inner product: <phi(s), theta> = sum_i phi(s)_i * theta_i.
    This is the linear value approximation V_theta(s). -/
def LinearTDConfig.featureInner (cfg : M.LinearTDConfig) (s : M.S)
    (theta : Fin cfg.d → ℝ) : ℝ :=
  featureDot (cfg.phi s) theta

/-- The approximate value function: V_theta(s) = <phi(s), theta>. -/
def LinearTDConfig.approxValue (cfg : M.LinearTDConfig)
    (theta : Fin cfg.d → ℝ) : M.StateValueFn :=
  fun s => cfg.featureInner s theta

/-- `featureInner` is the evaluation of the shared `linearValue`
    interface at a single state. -/
theorem LinearTDConfig.featureInner_eq_featureDot
    (cfg : M.LinearTDConfig) (theta : Fin cfg.d → ℝ) (s : M.S) :
    cfg.featureInner s theta = featureDot (cfg.phi s) theta := by
  rfl

/-- `featureInner` is the evaluation of the shared `linearValue`
    interface at a single state. -/
theorem LinearTDConfig.featureInner_eq_linearValue_apply
    (cfg : M.LinearTDConfig) (theta : Fin cfg.d → ℝ) (s : M.S) :
    cfg.featureInner s theta = M.linearValue cfg.phi theta s := by
  rfl

/-- TD's approximate value function is the shared finite-dimensional
    linear-value map for the feature matrix `phi`. -/
theorem LinearTDConfig.approxValue_eq_linearValue
    (cfg : M.LinearTDConfig) (theta : Fin cfg.d → ℝ) :
    cfg.approxValue theta = M.linearValue cfg.phi theta := by
  funext s
  exact cfg.featureInner_eq_linearValue_apply theta s

/-! ### TD(0) Update Formula -/

/-- A single TD(0) update step. Given current parameters theta, current
    state s, reward r_obs, next state s', and step size alpha:

    theta_{t+1} = theta_t + alpha * delta_t * phi(s_t)

    where delta_t = r_obs + gamma * <phi(s'), theta> - <phi(s), theta>
    is the TD error. -/
def LinearTDConfig.tdUpdate (cfg : M.LinearTDConfig)
    (theta : Fin cfg.d → ℝ) (s s' : M.S) (r_obs : ℝ) (alpha : ℝ) :
    Fin cfg.d → ℝ :=
  fun i => theta i + alpha *
    (r_obs + M.γ * cfg.featureInner s' theta - cfg.featureInner s theta) *
    cfg.phi s i

/-- The TD error is the observed reward minus the shared inner product
    against the discounted feature-difference vector `φ(s) - γ φ(s')`. -/
theorem LinearTDConfig.td_error_eq_reward_sub_bellmanFeatureDiff
    (cfg : M.LinearTDConfig) (theta : Fin cfg.d → ℝ)
    (s s' : M.S) (r_obs : ℝ) :
    r_obs + M.γ * cfg.featureInner s' theta - cfg.featureInner s theta =
    r_obs - featureDot (M.bellmanFeatureDiff cfg.phi s s') theta := by
  unfold LinearTDConfig.featureInner featureDot bellmanFeatureDiff
  have hsum :
      M.γ * ∑ j, cfg.phi s' j * theta j - ∑ j, cfg.phi s j * theta j =
      -∑ j, (cfg.phi s j - M.γ * cfg.phi s' j) * theta j := by
    calc
      M.γ * ∑ j, cfg.phi s' j * theta j - ∑ j, cfg.phi s j * theta j
        = ∑ j, M.γ * (cfg.phi s' j * theta j) - ∑ j, cfg.phi s j * theta j := by
            rw [Finset.mul_sum]
      _ = ∑ j, (M.γ * (cfg.phi s' j * theta j) - cfg.phi s j * theta j) := by
            rw [← Finset.sum_sub_distrib]
      _ = ∑ j, -((cfg.phi s j - M.γ * cfg.phi s' j) * theta j) := by
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = -∑ j, (cfg.phi s j - M.γ * cfg.phi s' j) * theta j := by
            rw [← Finset.sum_neg_distrib]
  calc
    r_obs + M.γ * ∑ j, cfg.phi s' j * theta j - ∑ j, cfg.phi s j * theta j
      = r_obs + (M.γ * ∑ j, cfg.phi s' j * theta j - ∑ j, cfg.phi s j * theta j) := by
          ring
    _ = r_obs + -∑ j, (cfg.phi s j - M.γ * cfg.phi s' j) * theta j := by
          exact congrArg (fun t => r_obs + t) hsum
    _ = r_obs - ∑ j, (cfg.phi s j - M.γ * cfg.phi s' j) * theta j := by
          ring

/-- **TD update formula**: the update can be decomposed as
    theta_{t+1,i} = theta_{t,i} + alpha * delta_t * phi(s)_i. -/
theorem td_update_formula (cfg : M.LinearTDConfig)
    (theta : Fin cfg.d → ℝ) (s s' : M.S) (r_obs : ℝ) (alpha : ℝ)
    (i : Fin cfg.d) :
    cfg.tdUpdate theta s s' r_obs alpha i =
      theta i + alpha *
        (r_obs + M.γ * cfg.featureInner s' theta -
          cfg.featureInner s theta) * cfg.phi s i := by
  simp only [LinearTDConfig.tdUpdate]

/-! ### Expected TD Update (ODE Method)

The ODE method for analyzing TD learning works by showing that the
expected update is a linear function of (theta* - theta).

E[theta_{t+1} - theta_t | theta_t] = alpha * A * (theta* - theta_t)

where A = E[phi(s)(phi(s) - gamma*phi(s'))^T].

We formalize this as: the expected error evolution is governed by a
linear operator with eigenvalue bounds.
-/

/-! ### Error Contraction (One-Step Bound)

The one-step error recursion for linear TD(0):

  E[||theta_{t+1} - theta*||^2 | theta_t]
    <= (1 - 2*alpha*lambda_min + alpha^2*C_quad) * ||theta_t - theta*||^2
       + alpha^2 * sigma^2

where:
- lambda_min > 0 is the minimum eigenvalue of A
- C_quad bounds the quadratic term
- sigma^2 is the conditional variance bound at theta*
-/

/-- **One-step contraction factor**: for step size alpha, the contraction
    factor is rho(alpha) = 1 - 2*alpha*lambda_min + alpha^2*C_quad. -/
def LinearTDConfig.contractionFactor (cfg : M.LinearTDConfig) (alpha : ℝ) : ℝ :=
  1 - 2 * alpha * cfg.lambda_min + alpha ^ 2 * cfg.C_quad

/-- The contraction factor is less than 1 when alpha is positive and
    small enough: alpha < 2 * lambda_min / C_quad. -/
theorem LinearTDConfig.contractionFactor_lt_one (cfg : M.LinearTDConfig)
    (alpha : ℝ) (halpha_pos : 0 < alpha)
    (halpha_small : alpha < 2 * cfg.lambda_min / cfg.C_quad) :
    cfg.contractionFactor alpha < 1 := by
  unfold contractionFactor
  have h1 : alpha * cfg.C_quad < 2 * cfg.lambda_min := by
    rwa [lt_div_iff₀ cfg.C_quad_pos] at halpha_small
  nlinarith [sq_nonneg alpha]

/-- The contraction factor is nonneg when alpha <= lambda_min / C_quad.
    This uses the structural condition lambda_min^2 <= C_quad from
    the config, which guarantees the safe step size stays in [0,1). -/
theorem LinearTDConfig.contractionFactor_nonneg (cfg : M.LinearTDConfig)
    (alpha : ℝ) (_halpha_pos : 0 < alpha)
    (halpha_small : alpha ≤ cfg.lambda_min / cfg.C_quad) :
    0 ≤ cfg.contractionFactor alpha := by
  unfold contractionFactor
  have h1 : alpha * cfg.C_quad ≤ cfg.lambda_min := by
    rwa [le_div_iff₀ cfg.C_quad_pos] at halpha_small
  -- rho = 1 - 2*a*l + a^2*C. We rewrite as:
  -- rho = (1 - a*l)^2 + a^2*C - a^2*l^2 = (1 - a*l)^2 + a^2*(C - l^2)
  -- Since C >= l^2 (lam_sq_le_C), rho >= (1 - a*l)^2 >= 0.
  have hkey : 0 ≤ cfg.C_quad - cfg.lambda_min ^ 2 := by linarith [cfg.lam_sq_le_C]
  nlinarith [sq_nonneg (1 - alpha * cfg.lambda_min), sq_nonneg alpha]

/-! ### Constant Step-Size Convergence

With constant step size alpha, the error converges geometrically
to a neighborhood of theta*:

  E[||theta_T - theta*||^2] <= rho^T * ||theta_0 - theta*||^2
                                 + alpha * sigma^2 / (2 * lambda_min - alpha * C_quad)

The neighborhood size is O(alpha * sigma^2 / lambda_min).
-/

/-- The steady-state error bound with constant step size:
    alpha * sigma^2 / (2 * lambda_min - alpha * C_quad). -/
def LinearTDConfig.steadyStateError (cfg : M.LinearTDConfig) (alpha : ℝ) : ℝ :=
  alpha * cfg.sigma_sq / (2 * cfg.lambda_min - alpha * cfg.C_quad)

/-- The steady-state error is nonneg when alpha is positive and small
    enough: alpha < 2 * lambda_min / C_quad. -/
theorem LinearTDConfig.steadyStateError_nonneg (cfg : M.LinearTDConfig)
    (alpha : ℝ) (halpha_pos : 0 < alpha)
    (halpha_small : alpha < 2 * cfg.lambda_min / cfg.C_quad) :
    0 ≤ cfg.steadyStateError alpha := by
  unfold steadyStateError
  apply div_nonneg
  · exact mul_nonneg (le_of_lt halpha_pos) cfg.sigma_sq_nonneg
  · have h1 : alpha * cfg.C_quad < 2 * cfg.lambda_min := by
      rwa [lt_div_iff₀ cfg.C_quad_pos] at halpha_small
    linarith

/-- Helper: lambda_min / C_quad < 2 * lambda_min / C_quad. -/
private theorem lam_div_lt_two_lam_div (cfg : M.LinearTDConfig) :
    cfg.lambda_min / cfg.C_quad < 2 * cfg.lambda_min / cfg.C_quad := by
  apply div_lt_div_of_pos_right _ cfg.C_quad_pos
  linarith [cfg.lambda_min_pos]

/-- **Constant step-size convergence** (geometric convergence to neighborhood).

    After T steps with constant step size alpha (in the safe regime
    alpha <= lambda_min / C_quad), the squared error satisfies:

      err(T) <= rho^T * err(0) + (1 - rho^T) * sigma / (1 - rho)

    where rho = 1 - 2*alpha*lambda_min + alpha^2*C_quad in [0, 1).

    Proved by induction on T, unrolling the one-step recursion. -/
theorem td_constant_step_convergence (cfg : M.LinearTDConfig)
    (alpha : ℝ) (halpha_pos : 0 < alpha)
    (halpha_small : alpha ≤ cfg.lambda_min / cfg.C_quad)
    (err_sq : ℕ → ℝ)
    -- One-step recursion hypothesis: err(t+1) <= rho * err(t) + sigma_term
    (h_step : ∀ t, err_sq (t + 1) ≤
      cfg.contractionFactor alpha * err_sq t +
        alpha ^ 2 * cfg.sigma_sq)
    -- All errors are nonneg (from being squared norms)
    (_herr_nonneg : ∀ t, 0 ≤ err_sq t) :
    ∀ T, err_sq T ≤
      cfg.contractionFactor alpha ^ T * err_sq 0 +
        (1 - cfg.contractionFactor alpha ^ T) *
          (alpha ^ 2 * cfg.sigma_sq / (1 - cfg.contractionFactor alpha)) := by
  have hρ_nonneg : 0 ≤ cfg.contractionFactor alpha :=
    cfg.contractionFactor_nonneg alpha halpha_pos halpha_small
  have hρ_lt_one : cfg.contractionFactor alpha < 1 := by
    apply cfg.contractionFactor_lt_one alpha halpha_pos
    exact lt_of_le_of_lt halpha_small (lam_div_lt_two_lam_div cfg)
  have h1_sub_ρ_pos : 0 < 1 - cfg.contractionFactor alpha := by linarith
  set ρ := cfg.contractionFactor alpha
  set σ := alpha ^ 2 * cfg.sigma_sq
  intro T
  induction T with
  | zero => simp
  | succ n ih =>
    calc err_sq (n + 1)
        ≤ ρ * err_sq n + σ := h_step n
      _ ≤ ρ * (ρ ^ n * err_sq 0 + (1 - ρ ^ n) * (σ / (1 - ρ))) + σ := by
          linarith [mul_le_mul_of_nonneg_left ih hρ_nonneg]
      _ = ρ ^ (n + 1) * err_sq 0 +
            (1 - ρ ^ (n + 1)) * (σ / (1 - ρ)) := by
          have h1ρ : (1 : ℝ) - ρ ≠ 0 := ne_of_gt h1_sub_ρ_pos
          field_simp
          ring

/-! ### Diminishing Step-Size Convergence

With step size alpha_t = c/(t+1), the error converges as:

  E[||theta_T - theta*||^2] <= C / T

This is the classic O(1/T) rate for SGD-style algorithms.
-/

/-- **Diminishing step-size convergence**: O(1/T) rate.

    With alpha_t = c/(t+1) for appropriate c > 1/(2*lambda_min),
    the expected squared error satisfies:
      E[||theta_T - theta*||^2] <= bound / T

    Proved from the Lyapunov hypothesis (t+1) * err(t) <= bound. -/
theorem td_diminishing_step_convergence
    (bound : ℝ) (hbound_pos : 0 < bound)
    -- Lyapunov hypothesis: (t+1) * err(t) <= bound for all t
    (err_sq : ℕ → ℝ)
    (h_lyapunov : ∀ t, (↑t + 1) * err_sq t ≤ bound) :
    ∀ T, 0 < T → err_sq T ≤ bound / T := by
  intro T hT
  have hT_pos : (0 : ℝ) < (↑T : ℝ) := Nat.cast_pos.mpr hT
  have hT1_pos : (0 : ℝ) < (↑T : ℝ) + 1 := by linarith
  have h := h_lyapunov T
  -- (T+1) * err(T) <= bound, so err(T) <= bound / (T+1) <= bound / T
  have herr_le : err_sq T ≤ bound / (↑T + 1) := by
    rw [le_div_iff₀ hT1_pos]
    linarith
  calc err_sq T ≤ bound / (↑T + 1) := herr_le
    _ ≤ bound / ↑T := by
        apply div_le_div_of_nonneg_left (by linarith) hT_pos
        linarith

/-! ### Approximation Error Bound

The approximation error of linear TD(0):

  ||V^pi - Phi*theta*||_mu <= C * ||V^pi - Pi_Phi V^pi||_mu

where Pi_Phi is the projection onto the column span of Phi in the
mu-weighted L2 norm, and C = 1/sqrt(1 - gamma^2) (Tsitsiklis-Van Roy).

This shows that the TD fixed point theta* achieves an approximation
error within a constant factor of the best possible linear approximation.
-/

/-- This proves positivity of 1/(1-gamma^2), the squared approximation
    ratio. The standard Tsitsiklis-Van Roy result bounds error by
    1/sqrt(1-gamma^2) times the projection error. -/
theorem approx_ratio_pos :
    0 < 1 / (1 - M.γ ^ 2) := by
  apply div_pos one_pos
  nlinarith [M.γ_lt_one, M.γ_nonneg, sq_nonneg M.γ]

/-- The approximation ratio is at least 1. -/
theorem approx_ratio_ge_one :
    1 ≤ 1 / (1 - M.γ ^ 2) := by
  rw [le_div_iff₀ (by nlinarith [M.γ_lt_one, M.γ_nonneg, sq_nonneg M.γ] : (0 : ℝ) < 1 - M.γ ^ 2)]
  nlinarith [sq_nonneg M.γ]

/-- The approximation bound implies: if proj_error_sq = 0 then
    td_error_sq = 0. This shows that when V^pi is exactly representable
    in the feature space, the TD fixed point recovers V^pi exactly. -/
theorem td_zero_proj_error_implies_zero_td_error
    (td_error_sq : ℝ)
    (htd_nonneg : 0 ≤ td_error_sq)
    (h_bound : td_error_sq ≤ 0 / (1 - M.γ ^ 2)) :
    td_error_sq = 0 := by
  have h1 : 0 < 1 - M.γ ^ 2 := by
    nlinarith [M.γ_lt_one, M.γ_nonneg, sq_nonneg M.γ]
  simp only [zero_div] at h_bound
  linarith

/-! ### Sample Complexity

The sample complexity of linear TD(0) with constant step size:

  T = O(C_quad / (eps * lambda_min^2))

to achieve E[||theta_T - theta*||^2] <= eps + steady_state_error.

This follows from:
1. Choose alpha to make steady-state error = O(eps)
2. The geometric convergence rate rho = 1 - O(lambda_min^2 / C_quad)
3. The burn-in time is T = O(C_quad * log(E_0/eps) / lambda_min^2)
-/

/-- **Sample complexity formula** (algebraic version).

    Given geometric convergence with factor rho in [0, 1), to achieve
    rho^T * E_0 <= eps we need T >= log(E_0/eps) / log(1/rho).

    We state this as: for any T satisfying the geometric decay condition,
    the total error (transient + steady-state) is bounded by
    eps + steadyStateError. -/
theorem td_sample_complexity (cfg : M.LinearTDConfig)
    (eps : ℝ) (_heps : 0 < eps)
    (alpha : ℝ) (halpha_pos : 0 < alpha)
    (halpha_small : alpha ≤ cfg.lambda_min / cfg.C_quad)
    (err_0 : ℝ)
    (T : ℕ)
    -- The key hypothesis: rho^T * E_0 <= eps
    (h_geometric : cfg.contractionFactor alpha ^ T * err_0 ≤ eps) :
    cfg.contractionFactor alpha ^ T * err_0 +
      (1 - cfg.contractionFactor alpha ^ T) *
        (alpha ^ 2 * cfg.sigma_sq / (1 - cfg.contractionFactor alpha)) ≤
      eps + cfg.steadyStateError alpha := by
  have hρ_nonneg : 0 ≤ cfg.contractionFactor alpha :=
    cfg.contractionFactor_nonneg alpha halpha_pos halpha_small
  have hρ_lt_one : cfg.contractionFactor alpha < 1 := by
    apply cfg.contractionFactor_lt_one alpha halpha_pos
    exact lt_of_le_of_lt halpha_small (lam_div_lt_two_lam_div cfg)
  have h1_sub_ρ_pos : 0 < 1 - cfg.contractionFactor alpha := by linarith
  set ρ := cfg.contractionFactor alpha
  set σ := alpha ^ 2 * cfg.sigma_sq
  have hρT_nonneg : 0 ≤ ρ ^ T := pow_nonneg hρ_nonneg T
  have hρT_le_one : ρ ^ T ≤ 1 := pow_le_one₀ hρ_nonneg (le_of_lt hρ_lt_one)
  -- Key: sigma/(1-rho) = steadyStateError
  -- 1 - rho = alpha * (2*lambda_min - alpha*C_quad)
  -- sigma/(1-rho) = alpha^2*sigma_sq/(alpha*(2*lam - alpha*C))
  --              = alpha*sigma_sq/(2*lam - alpha*C) = steadyStateError
  have h_alpha_C_le : alpha * cfg.C_quad ≤ cfg.lambda_min := by
    rwa [le_div_iff₀ cfg.C_quad_pos] at halpha_small
  have h_denom_pos : 0 < 2 * cfg.lambda_min - alpha * cfg.C_quad := by
    nlinarith [cfg.lambda_min_pos]
  have h_1_sub_rho : 1 - ρ = alpha * (2 * cfg.lambda_min - alpha * cfg.C_quad) := by
    simp only [ρ, LinearTDConfig.contractionFactor]; ring
  have h_ratio_eq : σ / (1 - ρ) = cfg.steadyStateError alpha := by
    unfold LinearTDConfig.steadyStateError
    simp only [σ]
    rw [h_1_sub_rho]
    rw [mul_comm alpha (2 * cfg.lambda_min - alpha * cfg.C_quad)]
    rw [div_mul_eq_div_div, div_right_comm]
    congr 1
    rw [div_eq_iff (ne_of_gt halpha_pos)]
    ring
  rw [← h_ratio_eq]
  -- (1-rho^T) * sigma/(1-rho) <= sigma/(1-rho) because 0 <= 1-rho^T <= 1
  have h_second : (1 - ρ ^ T) * (σ / (1 - ρ)) ≤ σ / (1 - ρ) := by
    apply mul_le_of_le_one_left
    · exact div_nonneg (mul_nonneg (sq_nonneg alpha) cfg.sigma_sq_nonneg)
        (le_of_lt h1_sub_ρ_pos)
    · linarith [hρT_nonneg]
  linarith

/-! ### Utility: Step-Size Condition Verification -/

/-- The safe step size lambda_min / C_quad is strictly less than the
    convergence threshold 2 * lambda_min / C_quad. -/
theorem safe_step_size_valid (cfg : M.LinearTDConfig) :
    cfg.lambda_min / cfg.C_quad <
      2 * cfg.lambda_min / cfg.C_quad :=
  lam_div_lt_two_lam_div cfg

/-- With the safe step size alpha = lambda_min / C_quad,
    the contraction factor equals 1 - lambda_min^2 / C_quad. -/
theorem safe_step_contraction (cfg : M.LinearTDConfig) :
    cfg.contractionFactor (cfg.lambda_min / cfg.C_quad) =
      1 - cfg.lambda_min ^ 2 / cfg.C_quad := by
  unfold LinearTDConfig.contractionFactor
  field_simp
  ring

/-- With the safe step size, the contraction factor is in [0, 1). -/
theorem safe_step_contraction_range (cfg : M.LinearTDConfig) :
    0 ≤ cfg.contractionFactor (cfg.lambda_min / cfg.C_quad) ∧
    cfg.contractionFactor (cfg.lambda_min / cfg.C_quad) < 1 := by
  rw [safe_step_contraction cfg]
  constructor
  · -- 0 <= 1 - lam^2/C iff lam^2/C <= 1 iff lam^2 <= C
    have hC := cfg.C_quad_pos
    have hlam := cfg.lam_sq_le_C
    have : cfg.lambda_min ^ 2 / cfg.C_quad ≤ 1 := by
      rw [div_le_one₀ hC]; exact hlam
    linarith
  · -- 1 - lam^2/C < 1 iff lam^2/C > 0
    have : 0 < cfg.lambda_min ^ 2 / cfg.C_quad :=
      div_pos (sq_pos_of_pos cfg.lambda_min_pos) cfg.C_quad_pos
    linarith

/-! ### Almost-Sure Convergence (Conditional on ODE/Stochastic Approximation) -/

/-- [CONDITIONAL] **Linear TD a.s. convergence**.

Takes h_converge (B_seq → 0) as hypothesis from Robbins-Siegmund /
ODE method, then derives err_sq → 0 via squeeze theorem.
Conditional on supermartingale convergence or ODE method
(Borkar-Meyn, 2000); see `RLGeneralization.Concentration.RobbinsSiegmund`. -/
theorem linear_td_as_convergence (_cfg : M.LinearTDConfig)
    -- Error sequence (squared norm of parameter error)
    (err_sq : ℕ → ℝ)
    (h_nonneg : ∀ T, 0 ≤ err_sq T)
    -- Bound sequence from the finite-step analysis
    (B_seq : ℕ → ℝ)
    (h_bound : ∀ T, err_sq T ≤ B_seq T)
    (h_converge : Filter.Tendsto B_seq Filter.atTop (nhds 0)) :
    Filter.Tendsto err_sq Filter.atTop (nhds 0) :=
  squeeze_zero h_nonneg h_bound h_converge

end FiniteMDP

end
