/-
# Policy Gradient Optimality

Abstract infrastructure for gradient-domination style optimality assumptions
in policy-gradient analysis.

## Main Definitions

* `GradientDomination` - A structure packaging the objective, gradient data,
  and domination inequality

## Main Results

* `gradient_domination_nonneg` - The domination gap is nonneg

## References

* [Agarwal et al., *RL: Theory and Algorithms*]
-/

import RLGeneralization.PolicyOptimization.PolicyGradient

open Finset BigOperators

noncomputable section

namespace FiniteMDP

variable (M : FiniteMDP)

/-! ### Gradient Domination Condition -/

/-- The gradient domination condition.

  For softmax parameterized policies, the suboptimality gap is
  bounded by the gradient norm:

    J(θ*) - J(θ) ≤ C · ‖∇J(θ)‖

  where C depends on the distribution mismatch coefficient and
  the effective horizon 1/(1-γ). This is the key structural
  property used in global policy-gradient optimality arguments. -/
structure GradientDomination (d : ℕ) where
  /-- The policy objective as a function of parameters -/
  J : (Fin d → ℝ) → ℝ
  /-- Gradient of J -/
  gradJ : (Fin d → ℝ) → (Fin d → ℝ)
  /-- Gradient norm function
      NOTE: gradNorm is an abstract field. The standard PL condition
      (Agarwal et al.) uses the squared gradient norm ||∇J||².
      Users should instantiate gradNorm with ||∇J||² to match
      the standard form. -/
  gradNorm : (Fin d → ℝ) → ℝ
  /-- Optimal parameter value -/
  θ_star : Fin d → ℝ
  /-- Domination constant C > 0 -/
  C : ℝ
  /-- C is positive -/
  C_pos : 0 < C
  /-- θ* is optimal: J(θ*) ≥ J(θ) for all θ -/
  θ_star_optimal : ∀ θ, J θ ≤ J θ_star
  /-- Gradient norm is nonneg -/
  gradNorm_nonneg : ∀ θ, 0 ≤ gradNorm θ
  /-- The gradient domination condition: `J(θ*) - J(θ) ≤ C · gradNorm(θ)`.
      NOTE: gradNorm is an abstract field. The standard PL condition
      (Agarwal et al.) uses the squared gradient norm ||∇J||².
      Users should instantiate gradNorm with ||∇J||² to match
      the standard form. -/
  domination : ∀ θ, J θ_star - J θ ≤ C * gradNorm θ

/-- The suboptimality gap `J(θ*) - J(θ)` is nonnegative when `θ*` is optimal.
    This is an immediate corollary of the stored optimality hypothesis. -/
theorem gradient_domination_nonneg {d : ℕ}
    (gd : GradientDomination d) (θ : Fin d → ℝ) :
    0 ≤ gd.J gd.θ_star - gd.J θ := by
  linarith [gd.θ_star_optimal θ]

end FiniteMDP

end
