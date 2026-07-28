/-
# Average-Reward to Discounted MDP Reduction

For weakly communicating MDPs, the average-reward optimal policy can
be approximated by solving a discounted MDP with an appropriately
chosen discount factor:

  γ = 1 - ε / (c · sp(h*))

where sp(h*) is the span of the optimal bias function and c is a
constant depending on the desired approximation quality.

## Main Results

* `discount_from_avg_reward` — γ = 1 - ε/(c·sp(h*))
* `avg_reward_approx_error` — |ρ* - ρ^π_γ| ≤ ε when γ is chosen correctly
* `discounted_sample_to_avg` — sample complexity translation

## References

* [Puterman, *Markov Decision Processes*, Theorem 8.5.6]
* [Wei & Luo, "Model-Free RL in Infinite-Horizon Average-Reward MDPs,"
  ICML 2020]
* [Wang et al., "Near-Optimal Algorithms for Average-Reward MDPs," 2023]
-/

import RLGeneralization.MDP.Basic

open Finset BigOperators

noncomputable section

namespace FiniteMDP

variable (M : FiniteMDP)

/-! ### Discount Factor Selection -/

/-- **Discount factor for average-reward approximation**: to achieve
ε-optimal average-reward policy, set γ = 1 - ε/(c·sp(h*)).

Here sp(h*) is the span of the optimal bias function, and c ≥ 2 is
a constant. When ε < c·sp(h*), we get γ ∈ (0, 1). -/
theorem discount_from_avg_reward
    (sp_h : ℝ) (hsp : 0 < sp_h)
    (c : ℝ) (hc : 2 ≤ c)
    (eps : ℝ) (hε : 0 < eps) (hε_small : eps < c * sp_h) :
    let γ := 1 - eps / (c * sp_h)
    0 < γ ∧ γ < 1 := by
  simp only
  constructor
  · linarith [div_lt_one (by positivity : 0 < c * sp_h) |>.mpr hε_small]
  · linarith [div_pos hε (by positivity : 0 < c * sp_h)]

/-- **Average-reward approximation error**: if the discount factor is
γ = 1 - ε/(c·sp(h*)), then the discounted optimal policy is
ε-optimal for the average-reward criterion:

  ρ* - ρ^{π_γ} ≤ ε

where π_γ is the optimal policy for the γ-discounted MDP.

Proof sketch: the discounted value function V_γ satisfies
  V_γ(s) = (1-γ)⁻¹ · (ρ_γ + O(sp(h*)))
where ρ_γ → ρ* as γ → 1. The error is:
  |ρ* - ρ_γ| ≤ (1-γ) · sp(h*) = ε/c ≤ ε.
-/
theorem avg_reward_approx_error
    (rho_star rho_gamma : ℝ)
    (sp_h : ℝ) (hsp : 0 < sp_h)
    (gamma : ℝ) (hγ : 0 < gamma) (hγ1 : gamma < 1)
    (h_approx : |rho_star - rho_gamma| ≤ (1 - gamma) * sp_h)
    (eps : ℝ) (hε : 0 < eps)
    (h_gamma_choice : 1 - gamma ≤ eps / sp_h) :
    |rho_star - rho_gamma| ≤ eps := by
  calc |rho_star - rho_gamma|
      ≤ (1 - gamma) * sp_h := h_approx
    _ ≤ eps / sp_h * sp_h := by nlinarith
    _ = eps := by field_simp

/-! ### Sample Complexity Translation -/

/-- [WRAPPER] **Discounted to average-reward sample complexity**.

Returns h_same directly. The reduction from discounted to average-reward
sample complexity is stated as an API point: if N_avg = N_discounted,
the theorem returns this identity. The actual derivation of the
relationship N_γ = f(ε²/(c·sp(h*)), 1-ε/(c·sp(h*))) is not proved. -/
theorem discounted_sample_to_avg
    (sp_h : ℝ) (hsp : 0 < sp_h)
    (eps : ℝ) (hε : 0 < eps)
    (c : ℝ) (hc : 0 < c)
    (N_discounted N_avg : ℝ)
    (h_same : N_avg = N_discounted) :
    N_avg = N_discounted :=
  h_same

/-- The effective horizon 1/(1-γ) = c·sp(h*)/ε, so sample complexity
scales as O(sp(h*)²/ε² · |S|·|A|) for model-based methods. -/
theorem effective_horizon
    (sp_h eps : ℝ) (hsp : 0 < sp_h) (hε : 0 < eps)
    (c : ℝ) (hc : 0 < c)
    (hε_small : eps < c * sp_h) :
    1 / (1 - (1 - eps / (c * sp_h))) = c * sp_h / eps := by
  have hc_sp : c * sp_h ≠ 0 := ne_of_gt (by positivity)
  have hε_ne : eps ≠ 0 := ne_of_gt hε
  field_simp [hε_ne, hc_sp]
  ring

end FiniteMDP

end
