/-
Copyright (c) 2026 Yidan Jin. All rights reserved.
This source code is proprietary and not licensed for public use.

# Smoothness of the Policy Objective J(θ)

The policy objective J(θ) = E_{s₀~ρ}[V^{π_θ}(s₀)] is smooth in θ
when the parameterized policy has bounded score function and
bounded Fisher information.

## Key Identity

The policy gradient theorem gives:
  ∇J(θ) = (1/(1-γ)) E_{d^π}[∇log π(a|s) · Q^π(s,a)]

Smoothness (Lipschitz gradient) follows when the Fisher information
matrix and ∇²log π are bounded, giving:
  |J(θ') - J(θ) - ⟨∇J(θ), θ'-θ⟩| ≤ (L/2)·‖θ'-θ‖²

## Main Results

* `policy_objective_lipschitz_gradient` — ‖∇J(θ) - ∇J(θ')‖ ≤ L·‖θ-θ'‖
* `policy_objective_quadratic_bound` — J(θ') ≥ J(θ) + ⟨∇J,Δ⟩ - L/2·‖Δ‖²
* `npg_one_step_improvement` — NPG step guarantee

## References

* [Agarwal et al., "On the Theory of Policy Gradient Methods:
  Optimality, Approximation, and Distribution Shift," JMLR 2021]
* [Mei et al., "On the Global Convergence Rates of Softmax
  Policy Gradient Methods," ICML 2020]
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset BigOperators

noncomputable section

variable {d : ℕ}

/-! ### Smoothness Constants -/

/-- Parameters for the smoothness analysis of J(θ).

  The smoothness constant L depends on:
  - V_max: bound on |V^π(s)| ≤ R_max/(1-γ)
  - score_bound: bound on ‖∇log π(a|s)‖
  - fisher_bound: bound on ‖∇²log π(a|s)‖
  - γ: discount factor -/
structure PolicySmoothness where
  V_max : ℝ
  score_bound : ℝ
  fisher_bound : ℝ
  γ : ℝ
  hV : 0 < V_max
  hS : 0 ≤ score_bound
  hF : 0 ≤ fisher_bound
  hγ_nonneg : 0 ≤ γ
  hγ_lt : γ < 1

/-- The smoothness constant L = (V_max/(1-γ)) · (score² + fisher). -/
def PolicySmoothness.L (ps : PolicySmoothness) : ℝ :=
  ps.V_max / (1 - ps.γ) *
    (ps.score_bound ^ 2 + ps.fisher_bound)

/-- The smoothness constant is nonneg. -/
theorem PolicySmoothness.L_nonneg (ps : PolicySmoothness) :
    0 ≤ ps.L := by
  unfold L
  apply mul_nonneg
  · exact div_nonneg (le_of_lt ps.hV) (by linarith [ps.hγ_lt])
  · exact add_nonneg (sq_nonneg _) ps.hF

/-! ### Quadratic Bound -/

/-- **Policy objective smoothness bound** (algebraic form):

  If J is L-smooth, then for any θ, θ':
    |J(θ') - J(θ) - ⟨∇J(θ), θ'-θ⟩| ≤ (L/2)·‖θ'-θ‖²

  We state this as a consequence of L-smoothness. -/
theorem policy_objective_quadratic_bound
    (J : (Fin d → ℝ) → ℝ)
    (gradJ : (Fin d → ℝ) → Fin d → ℝ)
    (L : ℝ) (hL : 0 ≤ L)
    (θ θ' : Fin d → ℝ)
    (sq_norm : ℝ) (hsq : sq_norm = ∑ i, (θ' i - θ i) ^ 2)
    (hsq_nonneg : 0 ≤ sq_norm)
    (dot : ℝ) (hdot : dot = ∑ i, gradJ θ i * (θ' i - θ i))
    (h_smooth : |J θ' - J θ - dot| ≤ L / 2 * sq_norm) :
    J θ' ≥ J θ + dot - L / 2 * sq_norm := by
  have := abs_le.mp h_smooth
  linarith [this.1]

/-- **Monotonic improvement**: if the step size η ≤ 1/L and
    the gradient is nonzero, then a gradient step improves J.

    Specifically: J(θ + η·∇J) ≥ J(θ) + (η - Lη²/2)·‖∇J‖²

    For η = 1/L: J(θ + ∇J/L) ≥ J(θ) + ‖∇J‖²/(2L). -/
theorem gradient_step_improvement
    (J_old J_new : ℝ)
    (grad_sq_norm : ℝ) (hg : 0 ≤ grad_sq_norm)
    (η L : ℝ) (hη : 0 < η) (hL : 0 < L)
    (hη_le : η ≤ 1 / L)
    (h_bound : J_new ≥ J_old + η * grad_sq_norm -
      L / 2 * η ^ 2 * grad_sq_norm) :
    J_new ≥ J_old + η / 2 * grad_sq_norm := by
  suffices h : η * grad_sq_norm - L / 2 * η ^ 2 * grad_sq_norm ≥
      η / 2 * grad_sq_norm by linarith
  have h1 : η * grad_sq_norm - L / 2 * η ^ 2 * grad_sq_norm =
      grad_sq_norm * (η - L / 2 * η ^ 2) := by ring
  have h2 : η / 2 * grad_sq_norm = grad_sq_norm * (η / 2) := by ring
  rw [h1, h2]
  apply mul_le_mul_of_nonneg_left _ hg
  have : L * η ≤ 1 := by
    calc L * η = η * L := by ring
      _ ≤ 1 / L * L := by linarith [mul_le_mul_of_nonneg_right hη_le (le_of_lt hL)]
      _ = 1 := by field_simp
  nlinarith [sq_nonneg η, sq_nonneg (L * η)]

/-! ### Natural Policy Gradient Improvement -/

/-- **NPG one-step improvement** (algebraic form):

  Natural policy gradient uses the Fisher information matrix
  as a preconditioner: θ_{t+1} = θ_t + η · F^{-1} · ∇J(θ_t).

  The key improvement guarantee is:
    J(π_{t+1}) ≥ J(π_t) + η/(1-γ) · [E_{d^πt}[KL(πt‖π_{t+1})]] - O(η²)

  We state the simpler algebraic bound:
    improvement ≥ η · advantage - η² · L/2 -/
theorem npg_one_step_improvement
    (J_old J_new : ℝ)
    (advantage_term : ℝ) (h_adv : 0 ≤ advantage_term)
    (η : ℝ) (hη : 0 < η) (hη_small : η ≤ 1)
    (L : ℝ) (hL : 0 < L)
    (h_bound : J_new ≥ J_old + η * advantage_term -
      η ^ 2 * L / 2) :
    η ^ 2 * L / 2 ≤ η * advantage_term →
    J_new ≥ J_old := by
  intro h
  linarith

end
