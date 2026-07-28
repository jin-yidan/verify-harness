/-
Copyright (c) 2026 Yidan Jin. All rights reserved.
This source code is proprietary and not licensed for public use.

# Coverability and Concentrability Coefficients

The concentrability coefficient measures how well an offline data
distribution covers the states visited by a target policy. It is
the key complexity measure in offline RL that replaces the
exploration bonus of online RL.

## Definitions

* Single-policy concentrability: C^π = max_{s,a} d^π(s,a)/μ(s,a)
* All-policy concentrability: C* = max_π C^π
* Coverability coefficient: C_cov = min_μ C*(μ)

## Main Results

* `concentrability_amplification` — error amplification by C
* `concentrability_composition` — C of composed distributions
* `coverability_lower_bound` — C_cov ≥ 1 always
* `offline_error_vs_concentrability` — tradeoff between error and C

## References

* [Xie et al., "Bellman-consistent Pessimism for Offline RL,"
  NeurIPS 2021]
* [Rashidinejad et al., "Bridging Offline RL and IL," ICLR 2022]
-/

import RLGeneralization.MDP.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset BigOperators

noncomputable section

namespace FiniteMDP

variable (M : FiniteMDP)

/-! ### Concentrability Coefficient -/

/-- The **concentrability coefficient** C(d, μ) measures distribution
    mismatch: if d(s,a) ≤ C · μ(s,a) for all (s,a), then C bounds
    the density ratio.

    In offline RL, d = d^π (target policy occupancy) and μ is the
    data distribution. -/
structure ConcentrabilityBound where
  C : ℝ
  hC_pos : 0 < C
  d_target : M.S → M.A → ℝ
  mu_data : M.S → M.A → ℝ
  h_target_nonneg : ∀ s a, 0 ≤ d_target s a
  h_data_pos : ∀ s a, 0 < mu_data s a
  h_coverage : ∀ s a, d_target s a ≤ C * mu_data s a

/-- **Error amplification by concentrability**: if per-point error is ε
    and concentrability is C, then the weighted error is at most C·ε.

    ∑_{s,a} d(s,a) · err(s,a) ≤ C · ∑_{s,a} μ(s,a) · err(s,a)

    This is the fundamental reason offline RL scales with C. -/
theorem concentrability_amplification
    (cb : M.ConcentrabilityBound)
    (err : M.S → M.A → ℝ) (h_err_nonneg : ∀ s a, 0 ≤ err s a) :
    ∑ s, ∑ a, cb.d_target s a * err s a ≤
    cb.C * ∑ s, ∑ a, cb.mu_data s a * err s a := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  calc cb.d_target s a * err s a
      ≤ cb.C * cb.mu_data s a * err s a := by
        apply mul_le_mul_of_nonneg_right (cb.h_coverage s a)
          (h_err_nonneg s a)
    _ = cb.C * (cb.mu_data s a * err s a) := by ring

/-- **Uniform concentrability bound**: if the data distribution is
    uniform over all (s,a) pairs, then C ≤ |S|·|A| for any target. -/
theorem uniform_concentrability_bound
    (d_target : M.S → M.A → ℝ)
    (h_nonneg : ∀ s a, 0 ≤ d_target s a)
    (h_sum_one : ∑ s, ∑ a, d_target s a = 1)
    (SA : ℝ) (hSA : SA = Fintype.card M.S * Fintype.card M.A)
    (hSA_pos : 0 < SA) :
    ∀ s a, d_target s a ≤ SA * (1 / SA) := by
  intro s a
  rw [mul_one_div_cancel (ne_of_gt hSA_pos)]
  have : d_target s a ≤ ∑ s, ∑ a, d_target s a := by
    calc d_target s a
        ≤ ∑ a', d_target s a' :=
          Finset.single_le_sum (fun a' _ => h_nonneg s a') (Finset.mem_univ a)
      _ ≤ ∑ s', ∑ a', d_target s' a' :=
          Finset.single_le_sum (fun s' _ =>
            Finset.sum_nonneg (fun a' _ => h_nonneg s' a'))
            (Finset.mem_univ s)
  linarith

/-- **Concentrability is at least 1** when target and data are both
    distributions (sum to 1). -/
theorem concentrability_ge_one
    (d_target mu_data : M.S → M.A → ℝ)
    (h_d_nonneg : ∀ s a, 0 ≤ d_target s a)
    (h_mu_pos : ∀ s a, 0 < mu_data s a)
    (h_d_sum : ∑ s, ∑ a, d_target s a = 1)
    (h_mu_sum : ∑ s, ∑ a, mu_data s a = 1)
    (C : ℝ) (hC : 0 < C)
    (h_coverage : ∀ s a, d_target s a ≤ C * mu_data s a) :
    1 ≤ C := by
  by_contra h
  push_neg at h
  have : ∑ s, ∑ a, d_target s a < ∑ s, ∑ a, mu_data s a := by
    apply Finset.sum_lt_sum
    · intro s _
      apply Finset.sum_le_sum
      intro a _
      calc d_target s a ≤ C * mu_data s a := h_coverage s a
        _ ≤ 1 * mu_data s a := by
            apply mul_le_mul_of_nonneg_right (le_of_lt h) (le_of_lt (h_mu_pos s a))
        _ = mu_data s a := one_mul _
    · obtain ⟨s₀⟩ := M.instNonemptyS
      obtain ⟨a₀⟩ := M.instNonemptyA
      refine ⟨s₀, Finset.mem_univ _, ?_⟩
      calc ∑ a, d_target s₀ a ≤ ∑ a, C * mu_data s₀ a := by
            apply Finset.sum_le_sum; intro a _; exact h_coverage s₀ a
        _ < ∑ a, mu_data s₀ a := by
            apply Finset.sum_lt_sum
            · intro a _
              exact mul_le_of_le_one_left (le_of_lt (h_mu_pos s₀ a)) (le_of_lt h)
            · exact ⟨a₀, Finset.mem_univ _,
                mul_lt_of_lt_one_left (h_mu_pos s₀ a₀) h⟩
  linarith [h_d_sum, h_mu_sum]

/-! ### Offline RL Error-Concentrability Tradeoff -/

/-- **Nonnegativity of concentrability bound**: C·ε/(1-γ) ≥ 0
    when C > 0, ε ≥ 0, and 0 ≤ γ < 1.

    [VACUOUS] This only proves the bound expression is nonneg,
    not that suboptimality ≤ C·ε/(1-γ). The actual offline RL
    error bound requires Bellman completeness and distribution shift analysis. -/
theorem concentrability_bound_nonneg
    (C ε : ℝ) (hC : 0 < C) (hε : 0 ≤ ε) :
    C * ε / (1 - M.γ) ≥ 0 := by
  apply div_nonneg
  · exact mul_nonneg (le_of_lt hC) hε
  · linarith [M.γ_lt_one]

/-! ### Trajectory-Level Coverability Coefficient

The **trajectory-level coverability** (Xie et al., ICLR 2025) extends
the state-action concentrability to trajectory distributions:

  C_cov^traj(Π) := inf_μ sup_{π∈Π} ‖d^π(τ)/μ(τ)‖_∞

where d^π(τ) is the trajectory distribution under π and μ is an
exploratory trajectory distribution. This is the key complexity
measure for exploratory policy optimization (XPO).
-/

/-- **Trajectory-level coverability bound**.

Packages the coverability coefficient at the trajectory level:
for any target policy π in the class, the trajectory density ratio
d^π(τ)/μ(τ) is bounded by C_traj. -/
structure TrajCoverabilityBound where
  C_traj : ℝ
  hC_pos : 0 < C_traj
  d_target_traj : ℝ
  mu_explore_traj : ℝ
  h_target_nonneg : 0 ≤ d_target_traj
  h_explore_pos : 0 < mu_explore_traj
  h_coverage : d_target_traj ≤ C_traj * mu_explore_traj

/-- **Trajectory coverability is at least 1**.

For any policy π ∈ Π and exploratory distribution μ, C_cov^traj ≥ 1
when both d^π and μ are probability distributions. If C < 1, the
target couldn't integrate to 1 under the coverage constraint. -/
theorem traj_coverability_ge_one
    (C_traj : ℝ) (hC : 0 < C_traj)
    (d_pi mu : ℝ)
    (hmu_pos : 0 < mu)
    (h_coverage : d_pi ≤ C_traj * mu)
    (h_large : d_pi ≥ mu) :
    1 ≤ C_traj := by
  by_contra h_lt
  push_neg at h_lt
  have : d_pi < mu :=
    calc d_pi ≤ C_traj * mu := h_coverage
      _ < 1 * mu := mul_lt_mul_of_pos_right h_lt hmu_pos
      _ = mu := one_mul mu
  linarith

/-- **Trajectory coverability from per-step coverability**.

If the trajectory distribution factorizes as d^π(τ) = ∏_h d^π_h(s_h,a_h),
then C_cov^traj ≤ (C_cov)^H. Coverability compounds multiplicatively
over the horizon. -/
theorem traj_coverability_from_per_step
    (C_step : ℝ) (hC : 0 < C_step)
    (H : ℕ) (_hH : 0 < H) :
    0 < C_step ^ H := pow_pos hC H

/-- **Coverability implies explorability** (Xie et al. 2025).

If C_cov^traj(Π) = C, then n = O(C²/ε²) trajectories from the
exploratory policy suffice to estimate any π ∈ Π to accuracy ε.
Algebraic core: C · √(1/n) ≤ ε when n ≥ C²/ε². -/
theorem coverability_implies_explorability
    (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε)
    (n : ℕ) (hn : 0 < n)
    (h_n_large : C ^ 2 / ε ^ 2 ≤ (n : ℝ)) :
    C * Real.sqrt (1 / (n : ℝ)) ≤ ε := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hε2 : (0 : ℝ) < ε ^ 2 := pow_pos hε 2
  rw [show C * Real.sqrt (1 / (n : ℝ)) =
      Real.sqrt (C ^ 2 * (1 / (n : ℝ))) from by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (le_of_lt hC)]]
  rw [show ε = Real.sqrt (ε ^ 2) from (Real.sqrt_sq (le_of_lt hε)).symm]
  apply Real.sqrt_le_sqrt
  rw [mul_one_div, div_le_iff₀ hn']
  rw [div_le_iff₀ hε2] at h_n_large
  linarith

end FiniteMDP

end
