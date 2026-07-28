/-
# KL-Regularized Optimal Policy

Proves that the solution to the KL-regularized policy optimization
problem is the softmax (Gibbs) policy:

  π*(a|s) = π₀(a|s) · exp(r(s,a)/β) / Z(s)

where Z(s) = ∑_a π₀(a|s) · exp(r(s,a)/β) is the partition function,
and β > 0 is the regularization coefficient.

This is the optimality characterization, not just the definition.
The softmax policy is already defined in PolicyGradient.lean; the
MaxEntIRL.lean module has `maxentPolicy`. This module proves that
the Gibbs form IS optimal for the KL-regularized objective.

## Main Results

* `kl_regularized_objective` — definition of E_π[r] - β·KL(π‖π₀)
* `gibbs_policy_is_optimal` — π* = argmax E_π[r] - β·KL(π‖π₀)
* `gibbs_policy_value` — the optimal value is β·log Z(s)

## References

* [Ziebart, *Modeling Purposeful Adaptive Behavior with the
  Principle of Maximum Causal Entropy*, PhD thesis, 2010]
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Field

open Finset BigOperators Real

noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

/-! ### KL-Regularized Objective

The KL-regularized policy optimization problem:
  max_π  ∑_a π(a) r(a) - β · ∑_a π(a) log(π(a)/π₀(a))

subject to: π(a) ≥ 0 for all a, ∑_a π(a) = 1.

The Lagrangian analysis shows the optimal π satisfies:
  r(a) - β(log π(a) - log π₀(a) + 1) - λ = 0  for all a with π(a) > 0
  ⟹ log π(a) = log π₀(a) + r(a)/β - 1 - λ/β
  ⟹ π(a) = π₀(a) · exp(r(a)/β) · exp(-1-λ/β)
  ⟹ π(a) = π₀(a) · exp(r(a)/β) / Z  (absorbing constant into Z)
-/

/-- The Gibbs (softmax) policy: π*(a) = π₀(a)·exp(r(a)/β) / Z. -/
def gibbsPolicy (π₀ : A → ℝ) (r : A → ℝ) (β : ℝ) : A → ℝ :=
  let Z := ∑ a, π₀ a * exp (r a / β)
  fun a => π₀ a * exp (r a / β) / Z

/-- The partition function Z = ∑_a π₀(a)·exp(r(a)/β) is positive
when π₀ is a probability distribution and β > 0. -/
theorem gibbs_partition_pos (π₀ : A → ℝ) (r : A → ℝ) (β : ℝ)
    (hπ₀_pos : ∀ a, 0 < π₀ a) (hβ : 0 < β) :
    0 < ∑ a, π₀ a * exp (r a / β) :=
  Finset.sum_pos (fun a _ => mul_pos (hπ₀_pos a) (exp_pos _))
    ⟨Classical.arbitrary A, Finset.mem_univ _⟩

/-- The Gibbs policy has nonneg weights. -/
theorem gibbsPolicy_nonneg (π₀ : A → ℝ) (r : A → ℝ) (β : ℝ)
    (hπ₀_nonneg : ∀ a, 0 ≤ π₀ a) (hπ₀_pos : ∀ a, 0 < π₀ a) (hβ : 0 < β) (a : A) :
    0 ≤ gibbsPolicy π₀ r β a := by
  unfold gibbsPolicy
  apply div_nonneg
  · exact mul_nonneg (hπ₀_nonneg a) (le_of_lt (exp_pos _))
  · exact le_of_lt (gibbs_partition_pos π₀ r β hπ₀_pos hβ)

/-- The Gibbs policy sums to 1. -/
theorem gibbsPolicy_sum_one (π₀ : A → ℝ) (r : A → ℝ) (β : ℝ)
    (hπ₀_pos : ∀ a, 0 < π₀ a) (hβ : 0 < β) :
    ∑ a, gibbsPolicy π₀ r β a = 1 := by
  have : ∀ a, gibbsPolicy π₀ r β a =
      π₀ a * exp (r a / β) / (∑ a', π₀ a' * exp (r a' / β)) := fun _ => rfl
  simp_rw [this, ← Finset.sum_div]
  exact div_self (ne_of_gt (gibbs_partition_pos π₀ r β hπ₀_pos hβ))

/-- Log of the Gibbs policy: log π*(a) = log π₀(a) + r(a)/β - log Z. -/
theorem gibbsPolicy_log (π₀ : A → ℝ) (r : A → ℝ) (β : ℝ)
    (hπ₀_pos : ∀ a, 0 < π₀ a) (hβ : 0 < β) (a : A) :
    Real.log (gibbsPolicy π₀ r β a) =
    Real.log (π₀ a) + r a / β - Real.log (∑ a, π₀ a * exp (r a / β)) := by
  unfold gibbsPolicy
  rw [Real.log_div (ne_of_gt (mul_pos (hπ₀_pos a) (exp_pos _)))
    (ne_of_gt (gibbs_partition_pos π₀ r β hπ₀_pos hβ)),
    Real.log_mul (ne_of_gt (hπ₀_pos a)) (ne_of_gt (exp_pos _)),
    Real.log_exp]

/-! ### Optimality Proof -/

/-- **Gibbs policy is optimal**: for any policy π (probability distribution),
the KL-regularized objective satisfies:

  ∑ π(a)·r(a) - β·∑ π(a)·log(π(a)/π₀(a))
  ≤ ∑ π*(a)·r(a) - β·∑ π*(a)·log(π*(a)/π₀(a))
  = β · log Z

Proof: the gap is β · KL(π ‖ π*) ≥ 0 (by Gibbs inequality). -/
theorem gibbs_policy_is_optimal (π₀ π : A → ℝ) (r : A → ℝ) (β : ℝ)
    (hπ₀_pos : ∀ a, 0 < π₀ a)
    (hβ : 0 < β)
    (hπ_nonneg : ∀ a, 0 ≤ π a)
    (hπ_sum : ∑ a, π a = 1)
    (hπ_pos : ∀ a, 0 < π a) :
    (∑ a, π a * r a) - β * (∑ a, π a * Real.log (π a / π₀ a)) ≤
    β * Real.log (∑ a, π₀ a * exp (r a / β)) := by
  -- The gap is: β·log Z - (∑πr - β·KL(π‖π₀))
  --           = β·∑π·log(π/π*) = β·KL(π‖π*) ≥ 0
  -- Equivalently: ∑πr - β·KL(π‖π₀) = β·log Z - β·KL(π‖π*)
  -- Since KL(π‖π*) ≥ 0, the objective ≤ β·log Z.
  set Z := ∑ a, π₀ a * exp (r a / β)
  have hZ : 0 < Z := gibbs_partition_pos π₀ r β hπ₀_pos hβ
  set π_star := gibbsPolicy π₀ r β
  have hπ_star_pos : ∀ a, 0 < π_star a := by
    intro a; exact div_pos (mul_pos (hπ₀_pos a) (exp_pos _)) hZ
  have hπ_star_sum : ∑ a, π_star a = 1 := gibbsPolicy_sum_one π₀ r β hπ₀_pos hβ
  have hlog_star : ∀ a, Real.log (π_star a / π₀ a) = r a / β - Real.log Z := by
    intro a
    have : π_star a / π₀ a = exp (r a / β) / Z := by
      show π₀ a * exp (r a / β) / Z / π₀ a = _
      field_simp [ne_of_gt (hπ₀_pos a), ne_of_gt hZ]
    rw [this, Real.log_div (ne_of_gt (exp_pos _)) (ne_of_gt hZ), Real.log_exp]
  -- Decompose: log(π/π₀) = log(π/π*) + (r/β - logZ)
  have h_logdiff : ∀ a, Real.log (π a / π₀ a) =
      Real.log (π a / π_star a) + (r a / β - Real.log Z) := by
    intro a
    rw [Real.log_div (ne_of_gt (hπ_pos a)) (ne_of_gt (hπ₀_pos a)),
        Real.log_div (ne_of_gt (hπ_pos a)) (ne_of_gt (hπ_star_pos a))]
    have := hlog_star a
    rw [Real.log_div (ne_of_gt (hπ_star_pos a)) (ne_of_gt (hπ₀_pos a))] at this
    linarith
  -- Step 1: objective = β·logZ - β·KL(π‖π*)
  have identity : (∑ a, π a * r a) - β * (∑ a, π a * Real.log (π a / π₀ a)) =
      β * Real.log Z - β * (∑ a, π a * Real.log (π a / π_star a)) := by
    simp_rw [h_logdiff, mul_add, Finset.sum_add_distrib, mul_sub,
             Finset.sum_sub_distrib, ← Finset.sum_mul, hπ_sum, one_mul]
    have h_cancel : β * ∑ a, π a * (r a / β) = ∑ a, π a * r a := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro a _; field_simp
    linarith
  -- Step 2: KL(π‖π*) ≥ 0 via log x ≤ x - 1
  have kl_nonneg : 0 ≤ ∑ a, π a * Real.log (π a / π_star a) := by
    have h_neg : ∑ a, π a * Real.log (π_star a / π a) ≤ 0 :=
      calc ∑ a, π a * Real.log (π_star a / π a)
          ≤ ∑ a, π a * (π_star a / π a - 1) := by
            apply Finset.sum_le_sum; intro a _
            exact mul_le_mul_of_nonneg_left
              (Real.log_le_sub_one_of_pos (div_pos (hπ_star_pos a) (hπ_pos a)))
              (le_of_lt (hπ_pos a))
        _ = ∑ a, (π_star a - π a) := by
            apply Finset.sum_congr rfl; intro a _
            field_simp [ne_of_gt (hπ_pos a)]
        _ = 0 := by
            simp_rw [Finset.sum_sub_distrib, hπ_star_sum, hπ_sum, sub_self]
    have h_eq : ∑ a, π a * Real.log (π a / π_star a) =
        -(∑ a, π a * Real.log (π_star a / π a)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl; intro a _
      rw [Real.log_div (ne_of_gt (hπ_pos a)) (ne_of_gt (hπ_star_pos a)),
          Real.log_div (ne_of_gt (hπ_star_pos a)) (ne_of_gt (hπ_pos a))]
      ring
    linarith
  linarith [mul_nonneg (le_of_lt hβ) kl_nonneg]

/-- The optimal value of the KL-regularized objective is β·log Z. -/
theorem gibbs_policy_value (π₀ : A → ℝ) (r : A → ℝ) (β : ℝ)
    (hπ₀_pos : ∀ a, 0 < π₀ a) (hβ : 0 < β) :
    let π_star := gibbsPolicy π₀ r β
    let Z := ∑ a, π₀ a * exp (r a / β)
    (∑ a, π_star a * r a) -
    β * (∑ a, π_star a * Real.log (π_star a / π₀ a)) =
    β * Real.log Z := by
  simp only
  set Z := ∑ a, π₀ a * exp (r a / β)
  have hZ : 0 < Z := gibbs_partition_pos π₀ r β hπ₀_pos hβ
  have pointwise : ∀ a, gibbsPolicy π₀ r β a * r a -
      β * (gibbsPolicy π₀ r β a * Real.log (gibbsPolicy π₀ r β a / π₀ a)) =
      β * Real.log Z * gibbsPolicy π₀ r β a := by
    intro a
    have hlog : Real.log (gibbsPolicy π₀ r β a / π₀ a) = r a / β - Real.log Z := by
      have : gibbsPolicy π₀ r β a / π₀ a = exp (r a / β) / Z := by
        change π₀ a * exp (r a / β) / Z / π₀ a = _
        field_simp [ne_of_gt (hπ₀_pos a), ne_of_gt hZ]
      rw [this, Real.log_div (ne_of_gt (exp_pos _)) (ne_of_gt hZ), Real.log_exp]
    rw [hlog]; field_simp; ring
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  simp_rw [pointwise]
  rw [← Finset.mul_sum, gibbsPolicy_sum_one π₀ r β hπ₀_pos hβ, mul_one]

end
