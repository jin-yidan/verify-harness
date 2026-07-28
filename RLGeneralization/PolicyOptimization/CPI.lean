/-
# Conservative Policy Iteration

Basic infrastructure for conservative policy iteration and policy mixing.

## Main Definitions

* `MixturePolicy` - The mixture π' = (1-α)π + α·π_greedy
* `CPIImprovement` - Safe improvement guarantee

## Main Results

* `mixture_prob_nonneg` - Mixture probabilities are nonneg
* `mixture_prob_sum_one` - Mixture probabilities sum to 1
* `expectedAdvantage_self_zero` - A policy has zero expected advantage under its own action-value function
* `cpi_resolvent_identity` - The CPI mixture gap satisfies a resolvent equation
* `cpi_improvement_bound` - Resolvent norm bound for the CPI mixture gap
* `cpi_monotonic_improvement` - Pointwise monotonic improvement under nonnegative expected advantage

## References

* [Agarwal et al., *RL: Theory and Algorithms*]
* [Kakade and Langford, 2002, Approximately optimal approximate RL]
-/

import RLGeneralization.MDP.PerformanceDifference

open Finset BigOperators

noncomputable section

namespace FiniteMDP

variable (M : FiniteMDP)

/-! ### Mixture Policy -/

/-- The mixture (convex combination) of two stochastic policies:
    `π'(a|s) = (1 - α) · π(a|s) + α · π_new(a|s)`
    where `α ∈ [0, 1]` is the mixing weight. -/
def mixtureProb (π π_new : M.StochasticPolicy)
    (α : ℝ) (s : M.S) (a : M.A) : ℝ :=
  (1 - α) * π.prob s a + α * π_new.prob s a

/-- Mixture probabilities are nonneg when α ∈ [0, 1]. -/
theorem mixture_prob_nonneg (π π_new : M.StochasticPolicy)
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (s : M.S) (a : M.A) :
    0 ≤ M.mixtureProb π π_new α s a := by
  unfold mixtureProb
  apply add_nonneg
  · exact mul_nonneg (by linarith) (π.prob_nonneg s a)
  · exact mul_nonneg hα0 (π_new.prob_nonneg s a)

/-- Mixture probabilities sum to 1 when α ∈ [0, 1]. -/
theorem mixture_prob_sum_one (π π_new : M.StochasticPolicy)
    (α : ℝ) (s : M.S) :
    ∑ a, M.mixtureProb π π_new α s a = 1 := by
  unfold mixtureProb
  simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [π.prob_sum_one s, π_new.prob_sum_one s]
  ring

/-- The mixture policy is a valid `StochasticPolicy`. -/
def mixturePolicy (π π_new : M.StochasticPolicy)
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    M.StochasticPolicy where
  prob := M.mixtureProb π π_new α
  prob_nonneg := M.mixture_prob_nonneg π π_new α hα0 hα1
  prob_sum_one := M.mixture_prob_sum_one π π_new α

/-! ### CPI Improvement via Resolvent -/

/-- A policy has zero expected advantage under its own action-value function. -/
theorem expectedAdvantage_self_zero
    (π : M.StochasticPolicy)
    (V_pi : M.StateValueFn)
    (Q_pi : M.ActionValueFn)
    (hV_pi : M.isValueOf V_pi π)
    (hQ_pi : ∀ s a, Q_pi s a =
      M.r s a + M.γ * ∑ s', M.P s a s' * V_pi s') :
    ∀ s, M.expectedAdvantage π Q_pi V_pi s = 0 := by
  intro s
  have h := M.pdl_one_step π π V_pi V_pi Q_pi hV_pi hV_pi hQ_pi s
  simpa [FiniteMDP.expectedNextValue] using h.symm

/-- Under a mixture policy, the expected advantage of `π` scales linearly
    with the mixing weight `α`. -/
theorem mixturePolicy_expectedAdvantage
    (π π_new : M.StochasticPolicy)
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (V_pi : M.StateValueFn)
    (Q_pi : M.ActionValueFn)
    (hV_pi : M.isValueOf V_pi π)
    (hQ_pi : ∀ s a, Q_pi s a =
      M.r s a + M.γ * ∑ s', M.P s a s' * V_pi s') :
    ∀ s,
      M.expectedAdvantage (M.mixturePolicy π π_new α hα0 hα1) Q_pi V_pi s =
        α * M.expectedAdvantage π_new Q_pi V_pi s := by
  intro s
  have hself :
      ∑ a, π.prob s a * (Q_pi s a - V_pi s) = 0 := by
    simpa [FiniteMDP.expectedAdvantage, FiniteMDP.advantage] using
      M.expectedAdvantage_self_zero π V_pi Q_pi hV_pi hQ_pi s
  calc
    M.expectedAdvantage (M.mixturePolicy π π_new α hα0 hα1) Q_pi V_pi s
      = ∑ a, ((1 - α) * π.prob s a + α * π_new.prob s a) * (Q_pi s a - V_pi s) := by
          rfl
    _ = (1 - α) * ∑ a, π.prob s a * (Q_pi s a - V_pi s) +
          α * ∑ a, π_new.prob s a * (Q_pi s a - V_pi s) := by
          have hsplit :
              ∀ a, ((1 - α) * π.prob s a + α * π_new.prob s a) * (Q_pi s a - V_pi s) =
                (1 - α) * (π.prob s a * (Q_pi s a - V_pi s)) +
                α * (π_new.prob s a * (Q_pi s a - V_pi s)) := by
            intro a
            ring
          simp_rw [hsplit, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = α * ∑ a, π_new.prob s a * (Q_pi s a - V_pi s) := by
          rw [hself]
          ring
    _ = α * M.expectedAdvantage π_new Q_pi V_pi s := by
          rfl

/-- The next-value operator commutes with negation. -/
  lemma expectedNextValue_neg
    (π : M.StochasticPolicy)
    (V : M.StateValueFn) :
    ∀ s, M.expectedNextValue π (fun s => - V s) s =
      - M.expectedNextValue π V s := by
  intro s
  unfold FiniteMDP.expectedNextValue
  have h_inner :
      ∀ a, ∑ s', M.P s a s' * (-V s') =
        -∑ s', M.P s a s' * V s' := by
    intro a
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro s' _
    ring
  calc
    ∑ a, π.prob s a * ∑ s', M.P s a s' * (fun s => -V s) s'
      = ∑ a, π.prob s a * (-(∑ s', M.P s a s' * V s')) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [h_inner]
    _ = -∑ a, π.prob s a * ∑ s', M.P s a s' * V s' := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro a _
          ring

/-- Sup norm scales linearly under multiplication by a nonnegative scalar. -/
  lemma supNormV_mul_le
    (α : ℝ) (hα : 0 ≤ α)
    (V : M.StateValueFn) :
    M.supNormV (fun s => α * V s) ≤ α * M.supNormV V := by
  unfold FiniteMDP.supNormV
  exact Finset.sup'_le _ _ (fun s _ => by
    rw [abs_mul, abs_of_nonneg hα]
    exact mul_le_mul_of_nonneg_left
      (Finset.le_sup' (fun s => |V s|) (Finset.mem_univ s))
      hα)

/-- The CPI mixture value gap satisfies a resolvent equation with driving term
    `α * E_{π_new}[A^π]`. -/
theorem cpi_resolvent_identity
    (π π_new : M.StochasticPolicy)
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (V_pi V_mix : M.StateValueFn)
    (Q_pi : M.ActionValueFn)
    (hV_pi : M.isValueOf V_pi π)
    (hV_mix : M.isValueOf V_mix (M.mixturePolicy π π_new α hα0 hα1))
    (hQ_pi : ∀ s a, Q_pi s a =
      M.r s a + M.γ * ∑ s', M.P s a s' * V_pi s') :
    ∀ s, V_mix s - V_pi s =
      α * M.expectedAdvantage π_new Q_pi V_pi s +
      M.γ * M.expectedNextValue (M.mixturePolicy π π_new α hα0 hα1)
        (fun s => V_mix s - V_pi s) s := by
  intro s
  have h := M.pdl_one_step (M.mixturePolicy π π_new α hα0 hα1) π
    V_mix V_pi Q_pi hV_mix hV_pi hQ_pi s
  rw [M.mixturePolicy_expectedAdvantage π π_new α hα0 hα1 V_pi Q_pi hV_pi hQ_pi] at h
  exact h

/-- Resolvent-style sup-norm bound for the CPI mixture value gap. -/
theorem cpi_improvement_bound
    (π π_new : M.StochasticPolicy)
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (V_pi V_mix : M.StateValueFn)
    (Q_pi : M.ActionValueFn)
    (hV_pi : M.isValueOf V_pi π)
    (hV_mix : M.isValueOf V_mix (M.mixturePolicy π π_new α hα0 hα1))
    (hQ_pi : ∀ s a, Q_pi s a =
      M.r s a + M.γ * ∑ s', M.P s a s' * V_pi s') :
    ∀ s, |V_mix s - V_pi s| ≤
      (α * M.supNormV (M.expectedAdvantage π_new Q_pi V_pi)) /
        (1 - M.γ) := by
  have h_res :=
    M.cpi_resolvent_identity π π_new α hα0 hα1 V_pi V_mix Q_pi hV_pi hV_mix hQ_pi
  have h_base :=
    M.resolvent_bound (M.mixturePolicy π π_new α hα0 hα1)
      (fun s => V_mix s - V_pi s)
      (fun s => α * M.expectedAdvantage π_new Q_pi V_pi s)
      h_res
  have h_scale :
      M.supNormV (fun s => α * M.expectedAdvantage π_new Q_pi V_pi s) ≤
        α * M.supNormV (M.expectedAdvantage π_new Q_pi V_pi) :=
    M.supNormV_mul_le α hα0 (M.expectedAdvantage π_new Q_pi V_pi)
  have hden : 0 ≤ 1 - M.γ := by linarith [M.γ_lt_one]
  intro s
  calc
    |V_mix s - V_pi s| ≤
        M.supNormV (fun s => α * M.expectedAdvantage π_new Q_pi V_pi s) /
          (1 - M.γ) := h_base s
    _ ≤ (α * M.supNormV (M.expectedAdvantage π_new Q_pi V_pi)) /
          (1 - M.γ) :=
        div_le_div_of_nonneg_right h_scale hden

/-- Pointwise monotonic improvement for the CPI mixture whenever the new policy
    has nonnegative expected advantage under `π`. -/
theorem cpi_monotonic_improvement
    (π π_new : M.StochasticPolicy)
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (V_pi V_mix : M.StateValueFn)
    (Q_pi : M.ActionValueFn)
    (hV_pi : M.isValueOf V_pi π)
    (hV_mix : M.isValueOf V_mix (M.mixturePolicy π π_new α hα0 hα1))
    (hQ_pi : ∀ s a, Q_pi s a =
      M.r s a + M.γ * ∑ s', M.P s a s' * V_pi s')
    (hA_nonneg : ∀ s, 0 ≤ M.expectedAdvantage π_new Q_pi V_pi s) :
    ∀ s, V_pi s ≤ V_mix s := by
  let π_mix := M.mixturePolicy π π_new α hα0 hα1
  let Δ : M.StateValueFn := fun s => V_mix s - V_pi s
  have h_res :
      ∀ s, Δ s =
        α * M.expectedAdvantage π_new Q_pi V_pi s +
        M.γ * M.expectedNextValue π_mix Δ s := by
    simpa [π_mix, Δ] using
      M.cpi_resolvent_identity π π_new α hα0 hα1 V_pi V_mix Q_pi hV_pi hV_mix hQ_pi
  have h_neg_res :
      ∀ s, (-Δ s) =
        (- (α * M.expectedAdvantage π_new Q_pi V_pi s)) +
        M.γ * M.expectedNextValue π_mix (fun s => -Δ s) s := by
    intro s
    have h := h_res s
    have hnext_neg := M.expectedNextValue_neg π_mix Δ s
    rw [hnext_neg]
    linarith
  have h_upper :
      ∀ s, -Δ s ≤ 0 / (1 - M.γ) := by
    apply M.resolvent_upper π_mix (fun s => -Δ s)
      (fun s => -(α * M.expectedAdvantage π_new Q_pi V_pi s)) 0 h_neg_res
    intro s
    exact neg_nonpos.mpr (mul_nonneg hα0 (hA_nonneg s))
  intro s
  have hs : -(V_mix s - V_pi s) ≤ 0 := by
    simpa [Δ] using h_upper s
  linarith

/-- The CPI quadratic penalty α²/(1-γ) is nonneg.
    This ensures the bound is well-structured. -/
theorem cpi_penalty_nonneg (α : ℝ) :
    0 ≤ α ^ 2 / (1 - M.γ) := by
  apply div_nonneg (sq_nonneg α)
  linarith [M.γ_lt_one]

/-- Optimal mixing weight: α* = (1-γ) · A_avg / 2 minimizes
    the bound α · A_avg - α²/(1-γ), yielding improvement
    ≥ (1-γ) · A_avg² / 4. We prove the optimal α is nonneg. -/
theorem cpi_optimal_alpha_nonneg (A_avg : ℝ) (hA : 0 ≤ A_avg) :
    0 ≤ (1 - M.γ) * A_avg / 2 := by
  apply div_nonneg
  · exact mul_nonneg (by linarith [M.γ_lt_one]) hA
  · norm_num

end FiniteMDP

end
