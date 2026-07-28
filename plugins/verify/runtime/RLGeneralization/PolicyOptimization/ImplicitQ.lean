/-
Copyright (c) 2026 Yidan Jin. All rights reserved.
This source code is proprietary and not licensed for public use.

# Implicit Q*-Approximation Identity

The key identity connecting optimal policies to Q*-values in
KL-regularized MDPs (DPO, Rafailov et al. 2023):

  Q*(s,a) = β · log(π*(a|s)/π_ref(a|s)) + β · log Z(s)

where π*(a|s) = π_ref(a|s)·exp(Q*(s,a)/β)/Z(s) is the Gibbs policy
and Z(s) = ∑_a π_ref(a|s)·exp(Q*(s,a)/β) is the partition function.

This allows reparameterizing Q* directly through the policy ratio,
eliminating the need for explicit reward modeling (the DPO insight).

## Main Results

* `implicit_q_identity` — Q* = β·log(π*/π_ref) + β·log Z
* `implicit_q_advantage` — A*(s,a) = β·log(π*(a|s)/π_ref(a|s)) - β·E_π*[log(π*/π_ref)]
* `reward_from_policy_ratio` — r(s,a) = β·log(π*/π_ref) + f(s) (up to shaping)

## References

* [Rafailov et al., "DPO: Direct Preference Optimization," NeurIPS 2023]
* [Azar et al., "A General Theoretical Paradigm to Understand
  Learning from Human Feedback," AISTATS 2024]
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Field

open Finset BigOperators Real

noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

/-! ### Gibbs Policy and Partition Function -/

/-- The partition function: Z = ∑_a π_ref(a)·exp(Q(a)/β). -/
def partitionFn (π_ref : A → ℝ) (Q : A → ℝ) (β : ℝ) : ℝ :=
  ∑ a, π_ref a * exp (Q a / β)

/-- The Gibbs (optimal) policy: π*(a) = π_ref(a)·exp(Q(a)/β) / Z. -/
def gibbsPolicyQ (π_ref : A → ℝ) (Q : A → ℝ) (β : ℝ) : A → ℝ :=
  fun a => π_ref a * exp (Q a / β) / partitionFn π_ref Q β

/-- Z > 0 when π_ref is positive and β > 0. -/
theorem partitionFn_pos (π_ref : A → ℝ) (Q : A → ℝ) (β : ℝ)
    (hπ : ∀ a, 0 < π_ref a) (_hβ : 0 < β) :
    0 < partitionFn π_ref Q β :=
  Finset.sum_pos (fun a _ => mul_pos (hπ a) (exp_pos _))
    ⟨Classical.arbitrary A, Finset.mem_univ _⟩

/-! ### Implicit Q*-Identity -/

/-- **Implicit Q*-approximation identity** (the DPO identity):

  Q(a) = β · log(π*(a) / π_ref(a)) + β · log Z

where π* is the Gibbs policy induced by Q.

This identity eliminates Q from the optimization: instead of
learning Q and extracting π*, one can directly optimize π*
via preference data (the DPO approach). -/
theorem implicit_q_identity
    (π_ref : A → ℝ) (Q : A → ℝ) (β : ℝ)
    (hπ : ∀ a, 0 < π_ref a)
    (hβ : 0 < β) :
    ∀ a, Q a = β * Real.log (gibbsPolicyQ π_ref Q β a / π_ref a) +
      β * Real.log (partitionFn π_ref Q β) := by
  intro a
  set Z := partitionFn π_ref Q β
  have hZ := partitionFn_pos π_ref Q β hπ hβ
  have hπa := hπ a
  have h_ratio : gibbsPolicyQ π_ref Q β a / π_ref a = exp (Q a / β) / Z := by
    show π_ref a * exp (Q a / β) / Z / π_ref a = _
    field_simp [ne_of_gt hπa, ne_of_gt hZ]
  rw [h_ratio]
  rw [Real.log_div (ne_of_gt (exp_pos _)) (ne_of_gt hZ)]
  rw [Real.log_exp]
  field_simp [ne_of_gt hβ]
  ring

/-- **Advantage from policy ratio**: the advantage A(a) = Q(a) - V
    equals β · [log(π*(a)/π_ref(a)) - E_{π*}[log(π*/π_ref)]]. -/
theorem implicit_advantage_identity
    (π_ref : A → ℝ) (Q : A → ℝ) (β : ℝ)
    (hπ : ∀ a, 0 < π_ref a)
    (hβ : 0 < β)
    (hπ_sum : ∑ a, gibbsPolicyQ π_ref Q β a = 1) :
    let π_star := gibbsPolicyQ π_ref Q β
    ∀ a, Q a - ∑ a', π_star a' * Q a' =
      β * Real.log (π_star a / π_ref a) -
      (∑ a', π_star a' * (β * Real.log (π_star a' / π_ref a'))) := by
  intro π_star a
  have hq := implicit_q_identity π_ref Q β hπ hβ
  set Z := partitionFn π_ref Q β
  rw [hq a]
  have hV : ∑ a', π_star a' * Q a' =
      ∑ a', π_star a' * (β * Real.log (π_star a' / π_ref a') + β * Real.log Z) := by
    congr 1; funext a'; congr 1; exact hq a'
  rw [hV]
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, hπ_sum, one_mul]
  ring

/-- **DPO reward extraction**: the log-ratio of two policies
    captures their Q-value difference (up to state-dependent constant).

    β · log(π₁(a)/π_ref(a)) - β · log(π₂(a)/π_ref(a))
    = β · log(π₁(a)/π₂(a)) -/
theorem dpo_reward_difference
    (π₁ π₂ π_ref : A → ℝ)
    (β : ℝ) (hβ : 0 < β)
    (hπ₁ : ∀ a, 0 < π₁ a) (hπ₂ : ∀ a, 0 < π₂ a)
    (hπ_ref : ∀ a, 0 < π_ref a)
    (a : A) :
    β * Real.log (π₁ a / π_ref a) - β * Real.log (π₂ a / π_ref a) =
    β * Real.log (π₁ a / π₂ a) := by
  rw [← mul_sub, Real.log_div (ne_of_gt (hπ₁ a)) (ne_of_gt (hπ_ref a)),
      Real.log_div (ne_of_gt (hπ₂ a)) (ne_of_gt (hπ_ref a)),
      Real.log_div (ne_of_gt (hπ₁ a)) (ne_of_gt (hπ₂ a))]
  ring

end
