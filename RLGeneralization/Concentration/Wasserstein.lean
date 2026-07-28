/-
# Wasserstein-1 Distance for Finite Distributions

Defines the Wasserstein-1 (earth mover's) distance for distributions on
finite metric spaces and proves key properties used in RL theory:
nonnegativity, self-distance zero, the Lipschitz expectation bound,
and a bound relating W₁ to total variation distance.

## Mathematical Background

The Wasserstein-1 distance between distributions P, Q on (S, ρ) is

  W₁(P, Q) = inf_{coupling γ} ∑_{s,s'} γ(s,s') · ρ(s,s')

By Kantorovich-Rubinstein duality:

  W₁(P, Q) = sup_{f : 1-Lipschitz} |E_P[f] - E_Q[f]|

We define a computable lower bound via "distance-from-point" witness
functions f_{s₀}(s) = ρ(s₀, s), which are 1-Lipschitz when the metric
satisfies the triangle inequality. This yields:

  wassersteinDist1 P Q ρ = max_{s₀ ∈ S} |∑_s (P(s) - Q(s)) · ρ(s₀, s)|

## Main Results

* `wassersteinDist1` — W₁(P, Q) via sup of |expected metric differences|
* `wassersteinDist_nonneg` — W₁(P, Q) ≥ 0
* `wassersteinDist_self` — W₁(P, P) = 0
* `lipschitz_expectation_bound` — |E_P[f] - E_Q[f]| ≤ L · W for L-Lipschitz f,
  conditioned on W bounding the weighted absolute deviation
* `wasserstein_tv_bound` — W₁(P, Q) ≤ diam(S) · ∑|P - Q|

## References

* [Villani, *Optimal Transport: Old and New*, Ch 6]
* [Gibbs & Su, "On Choosing and Bounding Probability Metrics", 2002]
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open Finset BigOperators

noncomputable section

variable {S : Type*} [Fintype S] [Nonempty S]

/-! ### Expected Metric Difference -/

/-- Expected metric difference from a reference point s₀:
  EMD(P, Q, ρ, s₀) = ∑_s (P(s) - Q(s)) · ρ(s₀, s).

When ρ(s₀, ·) is 1-Lipschitz, this quantity appears in the
Kantorovich-Rubinstein dual formulation of W₁. -/
def expectedMetricDiff (P Q : S → ℝ) (ρ : S → S → ℝ) (s₀ : S) : ℝ :=
  ∑ s, (P s - Q s) * ρ s₀ s

/-! ### Wasserstein-1 Distance -/

/-- **Wasserstein-1 distance** (lower bound via distance-from-point witnesses):

  W₁(P, Q) = max_{s₀ ∈ S} |∑_s (P(s) - Q(s)) · ρ(s₀, s)|

The absolute value matches the Kantorovich-Rubinstein dual form
sup_{f : 1-Lip} |E_P[f] - E_Q[f]|. Since distance-from-point functions
s ↦ ρ(s₀, s) are 1-Lipschitz under the triangle inequality, this gives
a lower bound on the true W₁ defined via couplings. -/
def wassersteinDist1 (P Q : S → ℝ) (ρ : S → S → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun s₀ =>
    |expectedMetricDiff P Q ρ s₀|

/-! ### Basic Properties -/

/-- W₁(P, Q) ≥ 0: immediate from the definition as a sup of absolute values. -/
theorem wassersteinDist_nonneg (P Q : S → ℝ) (ρ : S → S → ℝ) :
    0 ≤ wassersteinDist1 P Q ρ := by
  unfold wassersteinDist1
  obtain ⟨s₀⟩ : Nonempty S := inferInstance
  exact le_trans (abs_nonneg _)
    (Finset.le_sup' (fun s₀ => |expectedMetricDiff P Q ρ s₀|) (Finset.mem_univ s₀))

/-- W₁(P, P) = 0: self-distance vanishes. -/
theorem wassersteinDist_self (P : S → ℝ) (ρ : S → S → ℝ) :
    wassersteinDist1 P P ρ = 0 := by
  unfold wassersteinDist1 expectedMetricDiff
  simp only [sub_self, zero_mul, Finset.sum_const_zero, abs_zero]
  exact Finset.sup'_const Finset.univ_nonempty 0

/-! ### Lipschitz Expectation Bound -/

set_option linter.unusedSectionVars false in
/-- **Lipschitz expectation bound** (conditional).

For an L-Lipschitz function f under metric ρ, and distributions P, Q
that sum to 1:
  |E_P[f] - E_Q[f]| ≤ L · W

where W ≥ ∑_s |P(s) - Q(s)| · ρ(s₀, s) for some reference point s₀.

This is the key result for RL applications: if the value function
is L-Lipschitz in the state metric, then expected values under nearby
distributions are close. The bound W can be taken as any quantity
dominating the weighted absolute deviation ∑|P-Q|·ρ(s₀,·). -/
theorem lipschitz_expectation_bound
    (P Q : S → ℝ) (f : S → ℝ) (ρ : S → S → ℝ)
    (L : ℝ) (hL_nonneg : 0 ≤ L)
    (hP_sum : ∑ x, P x = 1) (hQ_sum : ∑ x, Q x = 1)
    (s₀ : S) (W : ℝ)
    (hW_bound : ∑ s, |P s - Q s| * ρ s₀ s ≤ W)
    (hf_lip : ∀ s, |f s - f s₀| ≤ L * ρ s₀ s) :
    |∑ s, (P s - Q s) * f s| ≤ L * W := by
  -- Step 1: center f at s₀ using ∑(P-Q) = 0
  have h_cancel : ∑ s, (P s - Q s) = 0 := by
    rw [Finset.sum_sub_distrib, hP_sum, hQ_sum, sub_self]
  -- Show ∑ w(s) * c = 0 when ∑w = 0
  have h_const_zero : ∑ s, (P s - Q s) * f s₀ = 0 := by
    calc ∑ s, (P s - Q s) * f s₀
        = (∑ s, (P s - Q s)) * f s₀ := (Finset.sum_mul _ _ _).symm
      _ = 0 * f s₀ := by rw [h_cancel]
      _ = 0 := zero_mul _
  -- Shift: ∑ w*f = ∑ w*(f - f₀)
  have h_shift : ∀ s, (P s - Q s) * f s =
      (P s - Q s) * (f s - f s₀) + (P s - Q s) * f s₀ := fun s => by ring
  -- Rewrite goal using shift
  conv_lhs => arg 1; arg 2; ext s; rw [h_shift]
  rw [Finset.sum_add_distrib, h_const_zero, add_zero]
  -- Step 2: bound via triangle inequality + Lipschitz
  have h_factor : ∀ s, |P s - Q s| * (L * ρ s₀ s) = L * (|P s - Q s| * ρ s₀ s) :=
    fun s => by ring
  calc |∑ s, (P s - Q s) * (f s - f s₀)|
      ≤ ∑ s, |(P s - Q s) * (f s - f s₀)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ s, |P s - Q s| * |f s - f s₀| := by
        congr 1; ext s; exact abs_mul _ _
    _ ≤ ∑ s, |P s - Q s| * (L * ρ s₀ s) :=
        Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hf_lip s) (abs_nonneg _)
    _ = L * ∑ s, |P s - Q s| * ρ s₀ s := by
        simp_rw [h_factor]
        symm
        exact Finset.mul_sum Finset.univ _ L
    _ ≤ L * W := by
        have h_diff_nonneg : 0 ≤ W - ∑ s, |P s - Q s| * ρ s₀ s := by linarith
        have h_prod_nonneg := mul_nonneg hL_nonneg h_diff_nonneg
        have h_expand : L * W - L * ∑ s, |P s - Q s| * ρ s₀ s =
            L * (W - ∑ s, |P s - Q s| * ρ s₀ s) := by ring
        linarith

/-! ### Wasserstein-TV Bound -/

/-- **Wasserstein-TV bound**.

  W₁(P, Q) ≤ diam(S, ρ) · ∑_s |P(s) - Q(s)|

where diam(S, ρ) = max_{s,s'} ρ(s, s').

Proof: for each s₀,
  |∑(P-Q)·ρ(s₀,·)| ≤ ∑|P-Q|·|ρ(s₀,·)| ≤ diam·∑|P-Q|

since ρ(s₀, s) ≤ diam for all s₀, s. -/
theorem wasserstein_tv_bound (P Q : S → ℝ) (ρ : S → S → ℝ)
    (diam : ℝ)
    (hρ_nonneg : ∀ s s', 0 ≤ ρ s s')
    (hρ_le_diam : ∀ s s', ρ s s' ≤ diam) :
    wassersteinDist1 P Q ρ ≤ diam * ∑ s, |P s - Q s| := by
  unfold wassersteinDist1
  apply Finset.sup'_le
  intro s₀ _
  have h_comm : ∀ s, |P s - Q s| * diam = diam * |P s - Q s| :=
    fun s => by ring
  calc |expectedMetricDiff P Q ρ s₀|
      = |∑ s, (P s - Q s) * ρ s₀ s| := rfl
    _ ≤ ∑ s, |(P s - Q s) * ρ s₀ s| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ s, |P s - Q s| * ρ s₀ s := by
        congr 1; ext s; rw [abs_mul, abs_of_nonneg (hρ_nonneg s₀ s)]
    _ ≤ ∑ s, |P s - Q s| * diam :=
        Finset.sum_le_sum fun s _ =>
          mul_le_mul_of_nonneg_left (hρ_le_diam s₀ s) (abs_nonneg _)
    _ = diam * ∑ s, |P s - Q s| := by
        simp_rw [h_comm]
        symm
        exact Finset.mul_sum Finset.univ _ diam

end
