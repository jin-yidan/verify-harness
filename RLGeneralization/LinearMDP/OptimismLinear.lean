/-
# Optimism from Confidence Ellipsoid

Connects confidence ellipsoid containment (θ* ∈ C_T) to per-step optimism
(Q̂ ≥ Q*) in linear MDPs with UCB-style exploration bonuses.

## Main Results

* `linear_ucb_optimism_from_confidence` — Cauchy-Schwarz + confidence → Q* ≤ Q̂
* `per_step_regret_from_optimism` — optimism implies one-step regret bound
-/

import RLGeneralization.MDP.FiniteHorizon
import RLGeneralization.LinearMDP.Basic
import Mathlib.Tactic

set_option linter.unusedVariables false

open Finset BigOperators

noncomputable section

namespace FiniteHorizonMDP

variable (M : FiniteHorizonMDP)

def dotProduct' {d : ℕ} (u v : Fin d → ℝ) : ℝ := ∑ i, u i * v i

theorem linear_ucb_optimism_from_confidence
    (d : ℕ) (theta_star theta_hat : Fin d → ℝ)
    (phi : Fin d → ℝ)
    (beta : ℝ) (hbeta : 0 < beta)
    (gram_inv_norm : ℝ) (hginv : 0 ≤ gram_inv_norm)
    (h_cauchy_schwarz :
      (dotProduct' phi (fun i => theta_hat i - theta_star i)) ^ 2 ≤
        gram_inv_norm * beta ^ 2)
    (Q_star Q_hat : ℝ)
    (h_Qstar : Q_star = dotProduct' phi theta_star)
    (h_Qhat : Q_hat = dotProduct' phi theta_hat + beta * Real.sqrt gram_inv_norm) :
    Q_star ≤ Q_hat := by
  rw [h_Qstar, h_Qhat]
  have h_diff : dotProduct' phi theta_hat - dotProduct' phi theta_star =
      dotProduct' phi (fun i => theta_hat i - theta_star i) := by
    simp only [dotProduct', ← Finset.sum_sub_distrib]
    congr 1; ext i; ring
  suffices h : dotProduct' phi theta_star ≤
      dotProduct' phi theta_hat + beta * Real.sqrt gram_inv_norm by exact h
  have h_sq : (dotProduct' phi theta_star - dotProduct' phi theta_hat) ^ 2 ≤
      (beta * Real.sqrt gram_inv_norm) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hginv]
    have : dotProduct' phi theta_star - dotProduct' phi theta_hat =
        -(dotProduct' phi (fun i => theta_hat i - theta_star i)) := by
      linarith [h_diff]
    rw [this, neg_sq]
    linarith [h_cauchy_schwarz]
  have hbs : 0 ≤ beta * Real.sqrt gram_inv_norm := by positivity
  nlinarith [sq_abs (dotProduct' phi theta_star - dotProduct' phi theta_hat),
    sq_nonneg (dotProduct' phi theta_star - dotProduct' phi theta_hat - beta * Real.sqrt gram_inv_norm)]

theorem per_step_regret_from_optimism
    (Q_star Q_hat V_hat : ℝ)
    (h_opt : Q_star ≤ Q_hat)
    (h_val : V_hat ≤ Q_hat) :
    Q_star - V_hat ≤ Q_hat - V_hat := by linarith

end FiniteHorizonMDP

end
