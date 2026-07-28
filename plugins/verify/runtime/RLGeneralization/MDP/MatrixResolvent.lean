/-
# Matrix Resolvent for Discounted MDPs

Formalizes the resolvent (I - γP^π)⁻¹ for discounted MDPs using
Mathlib's Neumann series infrastructure. This provides the exact
matrix-level identity underlying the simulation lemma and
component-wise comparison bounds.

## Architecture

1. Define the policy transition matrix P^π as `Matrix M.S M.S ℝ`.
2. Prove stochastic matrix properties (nonneg entries, rows sum to 1).
3. Open `Matrix.Norms.Operator` to get `NormedRing (Matrix M.S M.S ℝ)`.
4. Prove `‖γ • P^π‖ < 1` from the L∞ operator norm bound.
5. Apply `geom_series_eq_inverse` to get `(I - γP^π)⁻¹ = ∑' t, (γP^π)^t`.
6. Bridge to `transitionPow` from OccupancyMeasure.lean.

## References

* [Agarwal et al., *RL: Theory and Algorithms*][agarwal2026]
-/

import RLGeneralization.MDP.OccupancyMeasure
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.SpecificLimits.Normed

open Finset BigOperators Matrix

noncomputable section

-- Use the L∞ operator norm for matrices, which gives NormedRing
open scoped Matrix.Norms.Operator

namespace FiniteMDP

variable (M : FiniteMDP)

/-! ### Policy Transition Matrix -/

/-- The policy transition matrix: `(P^π)_{s,s'} = ∑_a π(a|s) P(s'|s,a)`.
    This packages the transition probabilities for a fixed policy
    as a `Matrix M.S M.S ℝ`. -/
def policyTransitionMat (π : M.StochasticPolicy) :
    Matrix M.S M.S ℝ :=
  Matrix.of fun s s' => ∑ a, π.prob s a * M.P s a s'

/-- Entries of the policy transition matrix are nonneg. -/
lemma policyTransitionMat_nonneg (π : M.StochasticPolicy)
    (s s' : M.S) : 0 ≤ M.policyTransitionMat π s s' := by
  unfold policyTransitionMat
  simp only [Matrix.of_apply]
  exact Finset.sum_nonneg fun a _ =>
    mul_nonneg (π.prob_nonneg s a) (M.P_nonneg s a s')

/-- Rows of the policy transition matrix sum to 1 (stochastic). -/
lemma policyTransitionMat_row_sum (π : M.StochasticPolicy)
    (s : M.S) : ∑ s', M.policyTransitionMat π s s' = 1 := by
  unfold policyTransitionMat
  simp only [Matrix.of_apply]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have : ∀ a, π.prob s a * ∑ s', M.P s a s' =
      π.prob s a := by
    intro a; rw [M.P_sum_one s a, mul_one]
  simp_rw [this]
  exact π.prob_sum_one s

/-! ### L∞ Operator Norm Bound

The L∞ operator norm of a matrix A is `sup_i (∑_j |A_{i,j}|)`.
For a stochastic matrix (nonneg entries, rows sum to 1), this equals 1. -/

/-- The L∞ operator norm of the policy transition matrix is at most 1. -/
lemma policyTransitionMat_norm_le_one (π : M.StochasticPolicy) :
    ‖M.policyTransitionMat π‖ ≤ 1 := by
  -- ‖A‖ = ↑(sup_i (∑_j ‖A_{ij}‖₊)) for the linfty op norm
  -- For stochastic matrices: ∑_j ‖A_{ij}‖₊ = ∑_j A_{ij} = 1
  rw [Matrix.linfty_opNorm_def (M.policyTransitionMat π)]
  suffices h : (Finset.univ : Finset M.S).sup
      (fun i => ∑ j, ‖M.policyTransitionMat π i j‖₊) ≤ 1 by
    exact_mod_cast h
  apply Finset.sup_le
  intro s _
  -- ∑_j ‖A_{s,j}‖₊ = 1 since entries are nonneg and rows sum to 1
  -- Strategy: convert ℝ≥0 inequality to ℝ inequality via NNReal.coe_le_coe
  rw [← NNReal.coe_le_coe]
  simp only [NNReal.coe_one, NNReal.coe_sum]
  calc (∑ s', (‖M.policyTransitionMat π s s'‖₊ : ℝ))
      = ∑ s', M.policyTransitionMat π s s' := by
        congr 1; ext s'
        exact Real.norm_of_nonneg (M.policyTransitionMat_nonneg π s s')
    _ = 1 := M.policyTransitionMat_row_sum π s
    _ ≤ 1 := le_refl _

/-- `‖γ • P^π‖ < 1` since γ < 1 and ‖P^π‖ ≤ 1. -/
lemma gamma_smul_policyTransitionMat_norm_lt_one
    (π : M.StochasticPolicy) :
    ‖M.γ • M.policyTransitionMat π‖ < 1 := by
  calc ‖M.γ • M.policyTransitionMat π‖
      ≤ ‖M.γ‖ * ‖M.policyTransitionMat π‖ := norm_smul_le _ _
    _ ≤ |M.γ| * 1 := by
        apply mul_le_mul_of_nonneg_left
          (M.policyTransitionMat_norm_le_one π) (abs_nonneg _)
    _ = |M.γ| := mul_one _
    _ < 1 := by rw [abs_of_nonneg M.γ_nonneg]; exact M.γ_lt_one

/-! ### Neumann Series (Resolvent Identity) -/

/-- `Matrix M.S M.S ℝ` is a complete normed ring under the L∞ operator norm. -/
instance : CompleteSpace (Matrix M.S M.S ℝ) :=
  FiniteDimensional.complete ℝ _

/-- The Neumann series `∑' t, (γ P^π)^t` converges. -/
lemma summable_gamma_policyTransitionMat_pow
    (π : M.StochasticPolicy) :
    Summable (fun t => (M.γ • M.policyTransitionMat π) ^ t) :=
  summable_geometric_of_norm_lt_one
    (M.gamma_smul_policyTransitionMat_norm_lt_one π)

/-- **Neumann series identity for the resolvent.**
    `∑' t, (γ P^π)^t = (I - γ P^π)⁻¹` as matrices. -/
theorem resolvent_neumann_series (π : M.StochasticPolicy) :
    ∑' t, (M.γ • M.policyTransitionMat π) ^ t =
    Ring.inverse (1 - M.γ • M.policyTransitionMat π) :=
  geom_series_eq_inverse _
    (M.gamma_smul_policyTransitionMat_norm_lt_one π)

/-- The resolvent is the `nonsing_inv` (⁻¹ notation). -/
theorem resolvent_eq_nonsing_inv (π : M.StochasticPolicy) :
    ∑' t, (M.γ • M.policyTransitionMat π) ^ t =
    (1 - M.γ • M.policyTransitionMat π)⁻¹ := by
  rw [M.resolvent_neumann_series π, nonsing_inv_eq_ringInverse]

/-- `(I - γP^π) * resolvent = I`. -/
theorem one_sub_smul_mul_resolvent (π : M.StochasticPolicy) :
    (1 - M.γ • M.policyTransitionMat π) *
    ∑' t, (M.γ • M.policyTransitionMat π) ^ t = 1 :=
  mul_neg_geom_series _
    (M.gamma_smul_policyTransitionMat_norm_lt_one π)

/-- `resolvent * (I - γP^π) = I`. -/
theorem resolvent_mul_one_sub_smul (π : M.StochasticPolicy) :
    (∑' t, (M.γ • M.policyTransitionMat π) ^ t) *
    (1 - M.γ • M.policyTransitionMat π) = 1 :=
  geom_series_mul_neg _
    (M.gamma_smul_policyTransitionMat_norm_lt_one π)

/-! ### Bridge: transitionPow ↔ Matrix Powers

The function-level `transitionPow π t s s'` (defined recursively in
OccupancyMeasure.lean) equals the matrix power `(policyTransitionMat π ^ t) s s'`.
This bridge connects the occupancy-measure infrastructure to the matrix resolvent. -/

/-- `transitionPow` at step 0 equals the identity matrix. -/
lemma transitionPow_zero_eq_one (π : M.StochasticPolicy) (s s' : M.S) :
    M.transitionPow π 0 s s' = (1 : Matrix M.S M.S ℝ) s s' := by
  simp [transitionPow, Matrix.one_apply]

/-- The one-step transition `∑_a π(a|s) P(s'|s,a)` equals the matrix entry. -/
lemma transitionPow_one_step (π : M.StochasticPolicy) (s s' : M.S) :
    ∑ a, π.prob s a * M.P s a s' = M.policyTransitionMat π s s' := by
  simp [policyTransitionMat, Matrix.of_apply]

/-- **transitionPow equals matrix power** (bridge lemma).
    `transitionPow π t s s' = (P^π_mat ^ t) s s'` for all t, s, s'. -/
theorem transitionPow_eq_matPow (π : M.StochasticPolicy) (t : ℕ) (s s' : M.S) :
    M.transitionPow π t s s' = (M.policyTransitionMat π ^ t) s s' := by
  induction t generalizing s s' with
  | zero =>
    simp [transitionPow, Matrix.one_apply, pow_zero]
  | succ n ih =>
    -- LHS: transitionPow π (n+1) s s'
    --     = ∑ s'', transitionPow π n s s'' * (∑ a, π.prob s'' a * P s'' a s')
    -- RHS: (P_mat ^ (n+1)) s s'
    --     = (P_mat ^ n * P_mat) s s'
    --     = ∑ s'', (P_mat ^ n) s s'' * P_mat s'' s'
    simp only [transitionPow, pow_succ]
    rw [Matrix.mul_apply]
    congr 1; ext s''
    rw [ih s s'', M.transitionPow_one_step π s'' s']

/-- The scalar-matrix power `(γ • P^π)^t` equals `γ^t • P^π^t` entrywise. -/
lemma smul_pow_apply (π : M.StochasticPolicy) (t : ℕ) (s s' : M.S) :
    ((M.γ • M.policyTransitionMat π) ^ t) s s' =
    M.γ ^ t * (M.policyTransitionMat π ^ t) s s' := by
  induction t generalizing s s' with
  | zero => simp [Matrix.one_apply]
  | succ n ih =>
    simp only [pow_succ, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    congr 1; ext s''
    rw [ih s s'']
    simp [policyTransitionMat, Matrix.of_apply]
    ring

/-- Connect the resolvent Neumann series to `discountedVisitation`. -/
theorem resolvent_entry_eq_discountedVisitation
    (π : M.StochasticPolicy) (s s' : M.S) :
    (∑' t, (M.γ • M.policyTransitionMat π) ^ t) s s' =
    M.discountedVisitation π s s' := by
  -- LHS = ∑' t, (γ • P_mat)^t s s' = ∑' t, γ^t * (P_mat^t) s s'
  -- RHS = ∑' t, γ^t * transitionPow π t s s'
  -- These are equal by transitionPow_eq_matPow.
  -- (∑' t, A^t) s s' = ∑' t, A^t s s'  (tsum commutes with evaluation)
  -- Then A^t s s' = γ^t * P^t s s' = γ^t * transitionPow
  -- (∑' t, A^t) s s' = ∑' t, (A^t s s')
  -- Matrix M.S M.S ℝ = M.S → M.S → ℝ, so evaluation at (s, s') commutes with tsum
  -- via Pi.tsum_apply (twice)
  have h_sum : (∑' t, (M.γ • M.policyTransitionMat π) ^ t) s s' =
      ∑' t, ((M.γ • M.policyTransitionMat π) ^ t) s s' := by
    have h1 : (∑' t, (M.γ • M.policyTransitionMat π) ^ t) s =
        ∑' t, ((M.γ • M.policyTransitionMat π) ^ t) s :=
      tsum_apply (M.summable_gamma_policyTransitionMat_pow π)
    change (∑' t, (M.γ • M.policyTransitionMat π) ^ t) s s' = _
    rw [show (∑' t, (M.γ • M.policyTransitionMat π) ^ t) s = _ from h1]
    exact tsum_apply (Pi.summable.mp
      (M.summable_gamma_policyTransitionMat_pow π) s)
  rw [h_sum, discountedVisitation]
  congr 1; funext t
  rw [M.smul_pow_apply π t s s', M.transitionPow_eq_matPow π t s s']

end FiniteMDP

end
