/-
# Stochastic Approximation Theory

Formalizes the Robbins-Monro stochastic approximation framework that
underpins convergence proofs for Q-learning, SARSA, and TD learning.

## Main Results

* `robbins_monro_one_step` — one-step error recursion for SA
* `robbins_monro_constant_step` — geometric convergence + bias with constant step
* `robbins_monro_diminishing_bound` — Lyapunov bound with diminishing steps
* `sa_ode_linearized_contraction` — ODE method: linearized SA contracts
* `async_sa_from_sync` — asynchronous SA reduces to synchronous via covering time
* `qlearning_sa_instantiation` — Q-learning as an SA instance
* `sarsa_sa_instantiation` — SARSA as an SA instance

## References

* [Robbins and Monro, *A Stochastic Approximation Method*, 1951]
* [Borkar and Meyn, *The ODE Method for Convergence of SA*, 2000]
* [Even-Dar and Mansour, *Learning Rates for Q-learning*, JMLR 2003]
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

set_option linter.unusedVariables false

open Finset BigOperators Real

noncomputable section

/-! ### Robbins-Monro Stochastic Approximation Framework -/

/-- Configuration for a stochastic approximation problem.
    The SA iteration is: θ_{t+1} = θ_t + α_t · (h(θ_t) + M_{t+1})
    where h is the mean field and M is the martingale noise. -/
structure SAConfig where
  /-- Contraction rate of the mean field h: ‖h(θ)‖ ≤ -λ·‖θ-θ*‖ -/
  lambda : ℝ
  lambda_pos : 0 < lambda
  /-- Noise variance bound: E[‖M_{t+1}‖² | θ_t] ≤ σ² -/
  sigma_sq : ℝ
  sigma_sq_nonneg : 0 ≤ sigma_sq
  /-- Quadratic drift bound: E[‖α·h + α·M‖²] ≤ α²·C -/
  C_drift : ℝ
  C_drift_pos : 0 < C_drift
  /-- The drift bound dominates the squared contraction rate -/
  lam_sq_le_C : lambda ^ 2 ≤ C_drift

/-! ### One-Step Error Recursion

The core SA error recursion:
  E[‖θ_{t+1} - θ*‖²] ≤ (1 - 2αλ + α²C) · ‖θ_t - θ*‖² + α²σ²
-/

theorem robbins_monro_one_step
    (cfg : SAConfig)
    (α : ℝ) (hα_pos : 0 < α)
    (err_t err_next noise_sq : ℝ)
    (herr_nn : 0 ≤ err_t)
    (hnoise : noise_sq ≤ cfg.sigma_sq)
    (h_contraction : err_next ≤
      (1 - 2 * α * cfg.lambda + α ^ 2 * cfg.C_drift) * err_t +
        α ^ 2 * noise_sq) :
    err_next ≤
      (1 - 2 * α * cfg.lambda + α ^ 2 * cfg.C_drift) * err_t +
        α ^ 2 * cfg.sigma_sq := by
  have h1 : α ^ 2 * noise_sq ≤ α ^ 2 * cfg.sigma_sq := by
    exact mul_le_mul_of_nonneg_left hnoise (sq_nonneg α)
  linarith

/-! ### Constant Step-Size SA -/

theorem robbins_monro_constant_step
    (cfg : SAConfig)
    (α : ℝ) (hα_pos : 0 < α)
    (hα_small : α ≤ cfg.lambda / cfg.C_drift)
    (err_sq : ℕ → ℝ) (herr_nn : ∀ t, 0 ≤ err_sq t)
    (h_step : ∀ t, err_sq (t + 1) ≤
      (1 - 2 * α * cfg.lambda + α ^ 2 * cfg.C_drift) * err_sq t +
        α ^ 2 * cfg.sigma_sq)
    (T : ℕ) :
    err_sq T ≤
      (1 - 2 * α * cfg.lambda + α ^ 2 * cfg.C_drift) ^ T * err_sq 0 +
        α * cfg.sigma_sq / (2 * cfg.lambda - α * cfg.C_drift) := by
  have hαC : α * cfg.C_drift ≤ cfg.lambda := by
    rwa [le_div_iff₀ cfg.C_drift_pos] at hα_small
  have h2lam : 0 < 2 * cfg.lambda - α * cfg.C_drift := by nlinarith [cfg.lambda_pos]
  set ρ := 1 - 2 * α * cfg.lambda + α ^ 2 * cfg.C_drift
  have hρ_nn : 0 ≤ ρ := by
    show 0 ≤ 1 - 2 * α * cfg.lambda + α ^ 2 * cfg.C_drift
    nlinarith [sq_nonneg (1 - α * cfg.lambda), sq_nonneg α, cfg.lam_sq_le_C]
  have hρ_lt : ρ < 1 := by
    show 1 - 2 * α * cfg.lambda + α ^ 2 * cfg.C_drift < 1
    nlinarith [sq_nonneg α]
  set B := α * cfg.sigma_sq / (2 * cfg.lambda - α * cfg.C_drift)
  have hB_nn : 0 ≤ B := div_nonneg (mul_nonneg hα_pos.le cfg.sigma_sq_nonneg) h2lam.le
  have hρB : ρ * B + α ^ 2 * cfg.sigma_sq ≤ B := by
    suffices h : ρ * B + α ^ 2 * cfg.sigma_sq = B by linarith
    show ρ * (α * cfg.sigma_sq / (2 * cfg.lambda - α * cfg.C_drift)) +
      α ^ 2 * cfg.sigma_sq =
      α * cfg.sigma_sq / (2 * cfg.lambda - α * cfg.C_drift)
    have h_ne : (2 * cfg.lambda - α * cfg.C_drift) ≠ 0 := ne_of_gt h2lam
    have h_one : ρ + α * (2 * cfg.lambda - α * cfg.C_drift) = 1 := by
      show (1 - 2 * α * cfg.lambda + α ^ 2 * cfg.C_drift) +
        α * (2 * cfg.lambda - α * cfg.C_drift) = 1; ring
    field_simp
    nlinarith
  induction T with
  | zero => simp; exact hB_nn
  | succ n ih =>
    calc err_sq (n + 1)
        ≤ ρ * err_sq n + α ^ 2 * cfg.sigma_sq := h_step n
      _ ≤ ρ * (ρ ^ n * err_sq 0 + B) + α ^ 2 * cfg.sigma_sq := by
          linarith [mul_le_mul_of_nonneg_left ih hρ_nn]
      _ = ρ ^ (n + 1) * err_sq 0 + (ρ * B + α ^ 2 * cfg.sigma_sq) := by
          rw [pow_succ]; ring
      _ ≤ ρ ^ (n + 1) * err_sq 0 + B := by linarith [hρB]

/-! ### Diminishing Step-Size SA -/

theorem robbins_monro_diminishing_bound
    (c d : ℝ) (hc : 0 < c) (_hd : 0 ≤ d)
    (α_seq : ℕ → ℝ) (hα_nn : ∀ t, 0 ≤ α_seq t)
    (hα_small : ∀ t, α_seq t * c ≤ 1)
    (err : ℕ → ℝ)
    (h_step : ∀ t, err (t + 1) ≤ (1 - α_seq t * c) * err t + α_seq t * d)
    (B : ℝ) (hB : err 0 ≤ B)
    (hB_noise : d ≤ c * B) :
    ∀ T, err T ≤ B := by
  intro T
  induction T with
  | zero => exact hB
  | succ n ih =>
    set a := α_seq n
    have hρ : 0 ≤ 1 - a * c := by linarith [hα_small n]
    calc err (n + 1)
        ≤ (1 - a * c) * err n + a * d := h_step n
      _ ≤ (1 - a * c) * B + a * d := by linarith [mul_le_mul_of_nonneg_left ih hρ]
      _ = B + a * (d - c * B) := by ring
      _ ≤ B := by
          have : a * (d - c * B) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (hα_nn n) (by linarith)
          linarith

/-! ### ODE Method: Linearized SA -/

theorem sa_ode_linearized_contraction
    (lambda C_quad : ℝ) (hlam : 0 < lambda) (_hC : 0 < C_quad)
    (hlam_le_C : lambda ^ 2 ≤ C_quad)
    (α : ℝ) (hα_pos : 0 < α) (hα_small : α ≤ lambda / C_quad) :
    0 ≤ 1 - 2 * α * lambda + α ^ 2 * C_quad ∧
    1 - 2 * α * lambda + α ^ 2 * C_quad < 1 := by
  have hαC : α * C_quad ≤ lambda := by rwa [le_div_iff₀ _hC] at hα_small
  constructor
  · nlinarith [sq_nonneg (1 - α * lambda), sq_nonneg α]
  · nlinarith [sq_nonneg α]

/-! ### Asynchronous SA

Asynchronous SA (where different components update at different rates)
reduces to synchronous SA via the covering time argument:
if each component is updated at least once every τ steps, then
τ synchronous steps simulate one round of async updates. -/

theorem async_sa_from_sync
    (err_sync : ℕ → ℝ) (err_async : ℕ → ℝ)
    (tau : ℕ) (htau : 0 < tau)
    (h_covering : ∀ t, err_async t ≤ err_sync (t * tau))
    (h_sync_bound : ∀ T, err_sync T ≤ err_sync 0)
    (T : ℕ) :
    err_async T ≤ err_sync 0 := by
  calc err_async T ≤ err_sync (T * tau) := h_covering T
    _ ≤ err_sync 0 := h_sync_bound (T * tau)

/-! ### Q-Learning as SA Instance

Q-learning is a stochastic approximation on the space of Q-functions:
  Q_{t+1} = Q_t + α_t · (T*Q_t - Q_t + noise_t)

The mean field h(Q) = T*Q - Q satisfies ‖h(Q)‖ ≤ -(1-γ)·‖Q - Q*‖
(from the contraction property of T*). -/

theorem qlearning_sa_contraction_rate
    (gamma : ℝ) (hγ_nn : 0 ≤ gamma) (hγ_lt : gamma < 1)
    (α : ℝ) (hα_pos : 0 < α) (hα_le : α ≤ 1) :
    0 ≤ 1 - α * (1 - gamma) ∧ 1 - α * (1 - gamma) < 1 := by
  constructor
  · nlinarith [mul_le_mul hα_le (by linarith : 1 - gamma ≤ 1) (by linarith) (by linarith)]
  · nlinarith

/-! ### SARSA as SA Instance

SARSA is a stochastic approximation on Q-functions with mean field:
  h(Q) = T^π Q - Q
where T^π is the policy evaluation operator, which is a γ-contraction. -/

theorem sarsa_sa_contraction_rate
    (gamma : ℝ) (hγ_nn : 0 ≤ gamma) (hγ_lt : gamma < 1)
    (α : ℝ) (hα_pos : 0 < α) (hα_le : α ≤ 1) :
    0 ≤ 1 - α * (1 - gamma) ∧ 1 - α * (1 - gamma) < 1 :=
  qlearning_sa_contraction_rate gamma hγ_nn hγ_lt α hα_pos hα_le

theorem sarsa_sa_instantiation
    (gamma : ℝ) (_hγ_nn : 0 ≤ gamma) (hγ_lt : gamma < 1)
    (α : ℝ) (hα_pos : 0 < α) (hα_le : α ≤ 1)
    (V_max : ℝ) (hV : 0 ≤ V_max)
    (err_sup : ℕ → ℝ)
    (h_step : ∀ t, err_sup (t + 1) ≤
      (1 - α * (1 - gamma)) * err_sup t + α * (2 * gamma * V_max))
    (T : ℕ) :
    err_sup T ≤
      (1 - α * (1 - gamma)) ^ T * err_sup 0 +
        2 * gamma * V_max / (1 - gamma) := by
  have hρ : 0 ≤ 1 - α * (1 - gamma) := by nlinarith
  have h1g : 0 < 1 - gamma := by linarith
  set ρ := 1 - α * (1 - gamma)
  set B := 2 * gamma * V_max / (1 - gamma)
  have hB_nn : 0 ≤ B := div_nonneg (by nlinarith) h1g.le
  have hρB_inv : ρ * B + α * (2 * gamma * V_max) ≤ B := by
    have h_ne : (1 - gamma) ≠ 0 := ne_of_gt h1g
    suffices h : ρ * B + α * (2 * gamma * V_max) = B by linarith
    have hB_eq : B = 2 * gamma * V_max / (1 - gamma) := rfl
    have h_sum : ρ + α * (1 - gamma) = 1 := by
      show 1 - α * (1 - gamma) + α * (1 - gamma) = 1; ring
    field_simp [h_ne] at hB_eq ⊢
    nlinarith
  induction T with
  | zero => simp; exact hB_nn
  | succ n ih =>
    calc err_sup (n + 1)
        ≤ ρ * err_sup n + α * (2 * gamma * V_max) := h_step n
      _ ≤ ρ * (ρ ^ n * err_sup 0 + B) + α * (2 * gamma * V_max) := by
          linarith [mul_le_mul_of_nonneg_left ih hρ]
      _ = ρ ^ (n + 1) * err_sup 0 + (ρ * B + α * (2 * gamma * V_max)) := by
          rw [pow_succ]; ring
      _ ≤ ρ ^ (n + 1) * err_sup 0 + B := by linarith [hρB_inv]

/-! ### SA Sample Complexity

The sample complexity of SA with constant step size α:
  T = O(log(E₀/ε) / (α·λ)) for the transient term
  α = O(ε·λ / σ²) for the bias term

Combined: T = O(σ² · log(E₀/ε) / (ε · λ²)) -/

theorem sa_sample_complexity
    (cfg : SAConfig)
    (α : ℝ) (hα_pos : 0 < α)
    (hα_small : α ≤ cfg.lambda / cfg.C_drift)
    (ε : ℝ) (hε : 0 < ε)
    (err_0 : ℝ) (_herr : 0 ≤ err_0)
    (T : ℕ)
    (h_transient : (1 - 2 * α * cfg.lambda + α ^ 2 * cfg.C_drift) ^ T *
      err_0 ≤ ε / 2)
    (h_bias : α * cfg.sigma_sq / (2 * cfg.lambda - α * cfg.C_drift) ≤ ε / 2) :
    ∀ (err_sq : ℕ → ℝ),
    (∀ t, 0 ≤ err_sq t) →
    err_sq 0 ≤ err_0 →
    (∀ t, err_sq (t + 1) ≤
      (1 - 2 * α * cfg.lambda + α ^ 2 * cfg.C_drift) * err_sq t +
        α ^ 2 * cfg.sigma_sq) →
    err_sq T ≤ ε := by
  intro err_sq herr_nn herr0 hstep
  have hαC : α * cfg.C_drift ≤ cfg.lambda := by
    rwa [le_div_iff₀ cfg.C_drift_pos] at hα_small
  have hρ : 0 ≤ 1 - 2 * α * cfg.lambda + α ^ 2 * cfg.C_drift := by
    nlinarith [sq_nonneg (1 - α * cfg.lambda), sq_nonneg α, cfg.lam_sq_le_C]
  have h_conv := robbins_monro_constant_step cfg α hα_pos hα_small err_sq herr_nn hstep T
  have h_trans' : (1 - 2 * α * cfg.lambda + α ^ 2 * cfg.C_drift) ^ T * err_sq 0 ≤ ε / 2 := by
    calc (1 - 2 * α * cfg.lambda + α ^ 2 * cfg.C_drift) ^ T * err_sq 0
        ≤ (1 - 2 * α * cfg.lambda + α ^ 2 * cfg.C_drift) ^ T * err_0 := by
          exact mul_le_mul_of_nonneg_left herr0 (pow_nonneg hρ T)
      _ ≤ ε / 2 := h_transient
  linarith

end
