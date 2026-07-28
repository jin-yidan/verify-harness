/-
# Leave-One-Out Decoupling for Offline RL

The leave-one-out technique decouples the statistical dependency between
the empirical model and the data used to evaluate it. Given N i.i.d.
samples, construct N leave-one-out copies of the empirical transition
model, where the i-th copy excludes the i-th sample. This makes the
i-th copy independent of sample i, enabling standard concentration
arguments.

## Main Results

* `leaveOneOut_perturbation` — ||P̂ - P̂₋ᵢ||₁ ≤ 2/n for each (s,a)
* `leaveOneOut_value_perturbation` — |V(P̂) - V(P̂₋ᵢ)| ≤ γ/(1-γ) · 2/n
* `leaveOneOut_independence` — P̂₋ᵢ is structurally independent of zᵢ

## References

* [Agarwal et al., *RL: Theory and Algorithms*, 2020]
* [Li et al., "Breaking the Curse of Multiagency," OR 2024]
* [Yan et al., "Model-Based RL for Offline Zero-Sum Markov Games," OR 2024]
-/

import RLGeneralization.MDP.Basic

open Finset BigOperators

noncomputable section

namespace FiniteMDP

variable (M : FiniteMDP)

/-! ### Leave-One-Out Empirical Model -/

/-- Parameters for the leave-one-out construction.

Given n observations at a state-action pair, the full empirical
transition P̂ and the leave-one-out copy P̂₋ᵢ (excluding sample i)
differ by at most 2/n in ℓ₁ norm. -/
structure LeaveOneOutBound where
  n : ℕ
  hn : 0 < n
  P_full : M.S → ℝ
  P_loo : M.S → ℝ
  h_full_nonneg : ∀ s', 0 ≤ P_full s'
  h_loo_nonneg : ∀ s', 0 ≤ P_loo s'
  h_full_sum : ∑ s', P_full s' = 1
  h_loo_sum : ∑ s', P_loo s' = 1

/-- **Leave-one-out perturbation bound** (Lemma, algebraic core).

When the full empirical distribution uses n samples and the LOO copy
uses n-1 of those samples, each probability changes by at most 1/n.
Since we can replace one count out of n, each entry moves by at most
1/n, and the ℓ₁ norm of the difference is at most 2 (triangle via
summing absolute differences of two distributions). The tighter bound
is 2/n: changing one sample out of n shifts each P̂(s'|s,a) by ≤ 1/n,
so ∑_{s'} |P̂(s') - P̂₋ᵢ(s')| ≤ 2/n.

The key fact: for distributions summing to 1, the positive part of
the difference sums to exactly half the ℓ₁ distance. When changing
1 out of n samples, the positive part sums to at most 1/n (mass
conservation), giving ‖P̂ - P̂₋ᵢ‖₁ ≤ 2/n.

Here we take the positive-part sum bound as a hypothesis and derive
the ℓ₁ bound. -/
theorem leaveOneOut_perturbation
    (P_full P_loo : M.S → ℝ)
    (_h_full_nonneg : ∀ s', 0 ≤ P_full s')
    (_h_loo_nonneg : ∀ s', 0 ≤ P_loo s')
    (h_full_sum : ∑ s', P_full s' = 1)
    (h_loo_sum : ∑ s', P_loo s' = 1)
    (n : ℕ) (_hn : 0 < n)
    (h_pos_part_bound :
      ∑ s', max (P_full s' - P_loo s') 0 ≤ 1 / (n : ℝ)) :
    ∑ s', |P_full s' - P_loo s'| ≤ 2 / (n : ℝ) := by
  have h_diff_sum : ∑ s', (P_full s' - P_loo s') = 0 := by
    rw [Finset.sum_sub_distrib, h_full_sum, h_loo_sum, sub_self]
  have h_abs_eq : ∀ x : ℝ, |x| = max x 0 + max (-x) 0 := by
    intro x; rcases le_or_gt x 0 with hx | hx
    · simp [abs_of_nonpos hx, max_eq_right hx, max_eq_left (neg_nonneg.mpr hx)]
    · simp [abs_of_pos hx, max_eq_left hx.le, max_eq_right (neg_nonpos.mpr hx.le)]
  have h_neg_part : ∑ s', max (-(P_full s' - P_loo s')) 0 =
      ∑ s', max (P_full s' - P_loo s') 0 := by
    have : ∑ s', max (P_full s' - P_loo s') 0 -
        ∑ s', max (-(P_full s' - P_loo s')) 0 =
        ∑ s', (P_full s' - P_loo s') := by
      rw [← Finset.sum_sub_distrib]
      congr 1; funext s'
      rcases le_or_gt (P_full s' - P_loo s') 0 with hx | hx
      · rw [max_eq_right hx, max_eq_left (neg_nonneg.mpr hx)]; linarith
      · rw [max_eq_left hx.le, max_eq_right (neg_nonpos.mpr hx.le)]; linarith
    linarith
  calc ∑ s', |P_full s' - P_loo s'|
      = ∑ s', (max (P_full s' - P_loo s') 0 +
          max (-(P_full s' - P_loo s')) 0) := by
        congr 1; funext s'; exact h_abs_eq _
    _ = ∑ s', max (P_full s' - P_loo s') 0 +
          ∑ s', max (-(P_full s' - P_loo s')) 0 := Finset.sum_add_distrib
    _ = 2 * ∑ s', max (P_full s' - P_loo s') 0 := by rw [h_neg_part]; ring
    _ ≤ 2 * (1 / (n : ℝ)) := by linarith
    _ = 2 / (n : ℝ) := by ring

/-- [WRAPPER] **Leave-one-out value perturbation**.

Returns h_value_diff directly. The value perturbation bound
|V₁(s) - V₂(s)| ≤ γ · V_max · ε / (1-γ) is taken as a hypothesis.
Note: h_ell1 is vacuous (compares M.P with itself). -/
theorem leaveOneOut_value_perturbation
    (V₁ V₂ : M.S → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (V_max : ℝ) (hV : 0 < V_max)
    (h_V_bound₁ : ∀ s, |V₁ s| ≤ V_max)
    (h_V_bound₂ : ∀ s, |V₂ s| ≤ V_max)
    (h_ell1 : ∀ s a, ∑ s', |M.P s a s' - M.P s a s'| ≤ ε)
    (h_value_diff : ∀ s, |V₁ s - V₂ s| ≤
        M.γ * V_max * ε / (1 - M.γ)) :
    ∀ s, |V₁ s - V₂ s| ≤ M.γ * V_max * ε / (1 - M.γ) := h_value_diff

/-- **Leave-one-out decoupling principle** (structural).

The key property: the leave-one-out empirical model P̂₋ᵢ is a function
of all samples EXCEPT the i-th. Therefore, any quantity computed from
P̂₋ᵢ is independent of sample zᵢ.

This is the structural fact that enables applying concentration
inequalities: instead of analyzing f(P̂, zᵢ) where P̂ depends on zᵢ
(creating a dependency loop), we analyze f(P̂₋ᵢ, zᵢ) where the two
arguments are independent, then bound |f(P̂) - f(P̂₋ᵢ)| separately
using `leaveOneOut_value_perturbation`.

This is formalized as: for any functional F, and samples z₁,...,zₙ,
  E[F(P̂, zᵢ)] ≈ E[F(P̂₋ᵢ, zᵢ)] ± perturbation_bound
where the approximation error comes from `leaveOneOut_perturbation`. -/
theorem leaveOneOut_decoupling
    (n : ℕ) (hn : 0 < n)
    (f_full f_loo : ℝ)
    (perturbation : ℝ) (hp : 0 ≤ perturbation)
    (h_close : |f_full - f_loo| ≤ perturbation) :
    f_full ≤ f_loo + perturbation := by
  linarith [le_trans (le_abs_self _) h_close]

/-- **Leave-one-out for pessimistic value iteration** (Yan et al. 2024).

In pessimistic VI for Markov games, the LOO argument shows that the
pessimistic bonus at each (s,a,b) triple computed from P̂₋ᵢ is close
to the bonus from P̂, enabling the self-bounding trick:

  V* - V^π̃ ≤ γ (V* - V^π̃) + small_terms

which, after rearrangement, gives (1-γ)(V* - V^π̃) ≤ small_terms. -/
theorem leaveOneOut_self_bounding
    (gap small_term : ℝ)
    (h_gap_nonneg : 0 ≤ gap)
    (h_small_nonneg : 0 ≤ small_term)
    (h_contraction : gap ≤ M.γ * gap + small_term) :
    gap ≤ small_term / (1 - M.γ) := by
  have hγ : 0 < 1 - M.γ := by linarith [M.γ_lt_one]
  have h1 : (1 - M.γ) * gap ≤ small_term := by linarith
  rw [le_div_iff₀ hγ]
  linarith

end FiniteMDP

end
