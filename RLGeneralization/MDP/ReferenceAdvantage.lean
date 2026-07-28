/-
Copyright (c) 2026 Yidan Jin. All rights reserved.
This source code is proprietary and not licensed for public use.

# Reference-Advantage Decomposition

In RLHF and KL-regularized RL, rewards are decomposed relative
to a reference policy via the advantage function:

  A^π(s,a) = Q^π(s,a) - V^π(s)

Key properties:
- E_{a~π}[A^π(s,a)] = 0
- r(s,a) = Q(s,a) - γ·E[V(s')]

## Main Results

* `advantage_sum_zero` — E_{a~π}[A^π(s,a)] = 0
* `advantage_bound` — |A| ≤ 2·V_max from bounded rewards

## References

* [Rafailov et al., "DPO," NeurIPS 2023]
* [Kakade and Langford, "Approximately Optimal Approximate RL," 2002]
-/

import RLGeneralization.MDP.Basic
import RLGeneralization.MDP.SimulationLemma

open Finset BigOperators

noncomputable section

namespace FiniteMDP

variable (M : FiniteMDP)

/-! ### Advantage Function

Uses `FiniteMDP.advantageFn` from `SimulationLemma`:
`advantageFn V Q = fun s a => Q s a - V s`. -/

/-- **Expected advantage is zero**: E_{a~π}[A^π(s,a)] = 0.

    This is the algebraic consequence of V(s) = E_π[Q(s,·)].
    It's why baselines don't change the policy gradient. -/
theorem advantage_sum_zero
    (Q : M.ActionValueFn) (V : M.StateValueFn)
    (π : M.StochasticPolicy)
    (hV_eq : ∀ s, V s = ∑ a, π.prob s a * Q s a) :
    ∀ s, ∑ a, π.prob s a * M.advantageFn V Q s a = 0 := by
  intro s
  simp only [advantageFn]
  simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    π.prob_sum_one, one_mul]
  linarith [hV_eq s]

/-- **Advantage decomposes reward**: when V(s) = ∑_a π(a|s)·Q(s,a)
    and Q(s,a) = r(s,a) + γ·∑P·V, we get
    r(s,a) = V(s) + A(s,a) - γ·(∑P·V(s') - V(s)). -/
theorem reward_from_advantage
    (Q : M.ActionValueFn) (V : M.StateValueFn)
    (hQ : ∀ s a, Q s a = M.r s a + M.γ * ∑ s', M.P s a s' * V s') :
    ∀ s a, M.r s a = Q s a - M.γ * ∑ s', M.P s a s' * V s' := by
  intro s a
  rw [hQ s a]; ring

/-! ### Advantage Bounds -/

/-- **Advantage bounded by 2·V_max**: when Q = r + γPV and |r| ≤ R,
    |V| ≤ V_bnd, |∑P·V| ≤ V_bnd, we get |A| ≤ R + (1+γ)·V_bnd. -/
theorem advantage_bound_from_q
    (Q : M.ActionValueFn) (V : M.StateValueFn)
    (hQ : ∀ s a, Q s a = M.r s a + M.γ * ∑ s', M.P s a s' * V s')
    (V_bnd : ℝ) (hVb : 0 ≤ V_bnd)
    (hv : ∀ s, |V s| ≤ V_bnd)
    (hpv : ∀ s a, |∑ s', M.P s a s' * V s'| ≤ V_bnd) :
    ∀ s a, |M.advantageFn V Q s a| ≤
      M.R_max + (1 + M.γ) * V_bnd := by
  intro s a
  simp only [advantageFn]
  rw [hQ s a]
  have hr := M.r_le_R_max s a
  have hv' := hv s
  have hpv' := hpv s a
  calc |M.r s a + M.γ * ∑ s', M.P s a s' * V s' - V s|
      ≤ |M.r s a| + |M.γ * ∑ s', M.P s a s' * V s'| + |V s| := by
        calc |M.r s a + M.γ * ∑ s', M.P s a s' * V s' - V s|
            = |(M.r s a + M.γ * ∑ s', M.P s a s' * V s') + (-V s)| := by ring_nf
          _ ≤ |M.r s a + M.γ * ∑ s', M.P s a s' * V s'| + |-V s| :=
              abs_add_le _ _
          _ ≤ (|M.r s a| + |M.γ * ∑ s', M.P s a s' * V s'|) + |V s| := by
              rw [abs_neg]; linarith [abs_add_le (M.r s a) (M.γ * ∑ s', M.P s a s' * V s')]
    _ ≤ M.R_max + M.γ * V_bnd + V_bnd := by
        have hgpv : |M.γ * ∑ s', M.P s a s' * V s'| ≤ M.γ * V_bnd := by
          rw [abs_mul, abs_of_nonneg M.γ_nonneg]
          exact mul_le_mul_of_nonneg_left hpv' M.γ_nonneg
        linarith
    _ = M.R_max + (1 + M.γ) * V_bnd := by ring

/-- The transition-weighted value is bounded by V_bnd when V is bounded. -/
theorem transition_weighted_value_bound
    (V : M.StateValueFn) (V_bnd : ℝ)
    (hv : ∀ s, |V s| ≤ V_bnd) (s : M.S) (a : M.A) :
    |∑ s', M.P s a s' * V s'| ≤ V_bnd := by
  calc |∑ s', M.P s a s' * V s'|
      ≤ ∑ s', |M.P s a s' * V s'| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ s', M.P s a s' * |V s'| := by
        apply Finset.sum_congr rfl; intro s' _
        rw [abs_mul, abs_of_nonneg (M.P_nonneg s a s')]
    _ ≤ ∑ s', M.P s a s' * V_bnd := by
        apply Finset.sum_le_sum; intro s' _
        exact mul_le_mul_of_nonneg_left (hv s') (M.P_nonneg s a s')
    _ = V_bnd := by rw [← Finset.sum_mul, M.P_sum_one, one_mul]

end FiniteMDP

end
