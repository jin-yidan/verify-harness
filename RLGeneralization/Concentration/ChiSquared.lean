/-
# Chi-Squared Divergence

Defines the chi-squared divergence χ²(P‖Q) = ∑_x (P(x)-Q(x))²/Q(x)
for finite distributions and proves the change-of-measure inequality:

  |E_P[f] - E_Q[f]|² ≤ χ²(P‖Q) · Var_Q[f]

This is the algebraic backbone for RLHF theory (chi-squared PO,
DPO variants) where policy comparison bounds are stated in terms
of chi-squared divergence.

## Main Results

* `chiSqDiv` — χ²(P‖Q) = ∑_x (P(x)-Q(x))²/Q(x)
* `chiSqDiv_nonneg` — χ² ≥ 0
* `chiSqDiv_self` — χ²(P‖P) = 0
* `chiSqDiv_alt` — alternative form: χ²(P‖Q) = ∑_x P(x)²/Q(x) - 1
* `chiSqDiv_change_of_measure` — |E_P[f]-E_Q[f]|² ≤ χ²·Var_Q[f]
* `chiSqDiv_ge_tv_sq` — χ²(P‖Q) ≥ (2·d_TV)² (Pinsker-type)

## References

* [Tsybakov, *Introduction to Nonparametric Estimation*, Ch 2.4]
* [Boucheron et al., *Concentration Inequalities*, §4.1]
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

open Finset BigOperators Real

noncomputable section

variable {S : Type*} [Fintype S] [DecidableEq S]

/-! ### Chi-Squared Divergence -/

/-- **Chi-squared divergence**: χ²(P‖Q) = ∑_x (P(x) - Q(x))² / Q(x).

Defined for distributions where Q(x) > 0 for all x (absolute continuity).
When Q(x) = 0 and P(x) = 0, the term is 0; when Q(x) = 0 and P(x) > 0,
χ² = ∞ (we handle this by requiring Q(x) > 0 in theorems). -/
def chiSqDiv (P Q : S → ℝ) : ℝ :=
  ∑ x, (P x - Q x) ^ 2 / Q x

/-- χ² ≥ 0 when Q is everywhere positive. -/
theorem chiSqDiv_nonneg (P Q : S → ℝ)
    (hQ_pos : ∀ x, 0 < Q x) :
    0 ≤ chiSqDiv P Q :=
  Finset.sum_nonneg fun x _ => div_nonneg (sq_nonneg _) (le_of_lt (hQ_pos x))

/-- χ²(P‖P) = 0. -/
theorem chiSqDiv_self (P : S → ℝ) :
    chiSqDiv P P = 0 := by
  simp [chiSqDiv, sub_self]

/-- **Alternative form**: χ²(P‖Q) = ∑ P(x)²/Q(x) - 1 for probability
distributions. Proof: expand (P-Q)²/Q = P²/Q - 2P + Q, then
∑(P²/Q - 2P + Q) = ∑P²/Q - 2 + 1 = ∑P²/Q - 1. -/
theorem chiSqDiv_alt (P Q : S → ℝ)
    (hQ_pos : ∀ x, 0 < Q x)
    (hP_sum : ∑ x, P x = 1) (hQ_sum : ∑ x, Q x = 1) :
    chiSqDiv P Q = (∑ x, P x ^ 2 / Q x) - 1 := by
  unfold chiSqDiv
  have expand : ∀ x, (P x - Q x) ^ 2 / Q x =
      P x ^ 2 / Q x - 2 * P x + Q x := by
    intro x
    have hq := hQ_pos x
    field_simp
    ring
  simp_rw [expand]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    hP_sum, hQ_sum]
  ring

/-! ### Expected Value and Variance -/

/-- Expected value of f under a weight function P. -/
def wtExpect (P : S → ℝ) (f : S → ℝ) : ℝ :=
  ∑ x, P x * f x

/-- Variance of f under P: Var_P[f] = E_P[f²] - (E_P[f])². -/
def wtVar (P : S → ℝ) (f : S → ℝ) : ℝ :=
  wtExpect P (fun x => f x ^ 2) - (wtExpect P f) ^ 2

/-- Variance is nonneg when P is a probability distribution.
Follows from Jensen's inequality: E[f²] ≥ (E[f])². -/
theorem wtVar_nonneg (P : S → ℝ) (f : S → ℝ)
    (hP_nonneg : ∀ x, 0 ≤ P x) (hP_sum : ∑ x, P x = 1) :
    0 ≤ wtVar P f := by
  unfold wtVar wtExpect
  -- E[f²] - (E[f])² = E[(f - E[f])²] ≥ 0
  show 0 ≤ (∑ x, P x * f x ^ 2) - (∑ x, P x * f x) ^ 2
  set μ := ∑ x, P x * f x with hμ
  have h_expand : ∀ x, P x * (f x - μ) ^ 2
      = P x * f x ^ 2 - 2 * μ * (P x * f x) + μ ^ 2 * P x := fun x => by ring
  have key : ∑ x, P x * (f x - μ) ^ 2 = (∑ x, P x * f x ^ 2) - μ ^ 2 := by
    simp_rw [h_expand]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, hP_sum, ← hμ]
    ring
  have h_nonneg : 0 ≤ ∑ x, P x * (f x - μ) ^ 2 :=
    Finset.sum_nonneg fun x _ => mul_nonneg (hP_nonneg x) (sq_nonneg _)
  linarith

/-! ### Change of Measure -/

/-- **Chi-squared change of measure**: for any function f,
|E_P[f] - E_Q[f]|² ≤ χ²(P‖Q) · Var_Q[f].

Proof sketch: write E_P[f] - E_Q[f] = ∑ f(x)(P(x) - Q(x))
= E_Q[f · (P/Q - 1)]. Center f to get E_Q[(f-μ)(P/Q-1)]
where μ = E_Q[f]. Since E_Q[P/Q - 1] = 0, the centering is free.
Apply Cauchy-Schwarz: |E_Q[(f-μ)(P/Q-1)]|² ≤ Var_Q[f]·χ²(P‖Q). -/
theorem chiSqDiv_change_of_measure (P Q : S → ℝ)
    (hP_nonneg : ∀ x, 0 ≤ P x) (hQ_pos : ∀ x, 0 < Q x)
    (hP_sum : ∑ x, P x = 1) (hQ_sum : ∑ x, Q x = 1)
    (f : S → ℝ) :
    (wtExpect P f - wtExpect Q f) ^ 2 ≤
    chiSqDiv P Q * wtVar Q f := by
  unfold wtExpect chiSqDiv wtVar
  show ((∑ x, P x * f x) - ∑ x, Q x * f x) ^ 2 ≤
    (∑ x, (P x - Q x) ^ 2 / Q x) *
      ((∑ x, Q x * f x ^ 2) - (∑ x, Q x * f x) ^ 2)
  set μ := ∑ x, Q x * f x with hμ
  -- Center f: E_P[f] - E_Q[f] = ∑ (f-μ)(P-Q) since ∑(P-Q) = 0
  have h_diff : (∑ x, P x * f x) - μ = ∑ x, (f x - μ) * (P x - Q x) := by
    have h1 : ∀ x, (f x - μ) * (P x - Q x)
        = (P x * f x - μ * P x) - (Q x * f x - μ * Q x) := fun x => by ring
    simp_rw [h1]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, hP_sum, ← hμ, hQ_sum]
    ring
  -- Cauchy-Schwarz with α = (P-Q)/√Q and β = (f-μ)·√Q:
  -- ∑ α² = χ², ∑ β² = ∑ Q(f-μ)², ∑ αβ = the centered sum
  have h_cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun x => (P x - Q x) / √(Q x)) (fun x => (f x - μ) * √(Q x))
  have h_prod : ∀ x, ((P x - Q x) / √(Q x)) * ((f x - μ) * √(Q x))
      = (f x - μ) * (P x - Q x) := by
    intro x
    have hq : √(Q x) ≠ 0 := ne_of_gt (sqrt_pos.mpr (hQ_pos x))
    field_simp
  have h_sq_a : ∀ x, ((P x - Q x) / √(Q x)) ^ 2 = (P x - Q x) ^ 2 / Q x := by
    intro x; rw [div_pow, sq_sqrt (hQ_pos x).le]
  have h_sq_b : ∀ x, ((f x - μ) * √(Q x)) ^ 2 = Q x * (f x - μ) ^ 2 := by
    intro x; rw [mul_pow, sq_sqrt (hQ_pos x).le]; ring
  simp_rw [h_prod, h_sq_a, h_sq_b] at h_cs
  -- Variance identity: ∑ Q(f-μ)² = ∑ Qf² - μ²
  have h_var : ∑ x, Q x * (f x - μ) ^ 2 = (∑ x, Q x * f x ^ 2) - μ ^ 2 := by
    have h2 : ∀ x, Q x * (f x - μ) ^ 2
        = Q x * f x ^ 2 - 2 * μ * (Q x * f x) + μ ^ 2 * Q x := fun x => by ring
    simp_rw [h2]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, hQ_sum, ← hμ]
    ring
  rw [h_diff]
  rw [h_var] at h_cs
  exact h_cs

/-! ### Relationship to TV Distance -/

/-- χ²(P‖Q) ≥ (∑|P-Q|)² when Q is uniform.
More generally, χ² ≥ 2·d_TV² (Pinsker-type bound for chi-squared). -/
theorem chiSqDiv_ge_sum_abs_sq (P Q : S → ℝ)
    (hQ_pos : ∀ x, 0 < Q x) (hQ_sum : ∑ x, Q x = 1) :
    (∑ x, |P x - Q x|) ^ 2 ≤ chiSqDiv P Q := by
  -- Cauchy-Schwarz: (∑|P-Q|)² = (∑ √Q · |P-Q|/√Q)² ≤ (∑Q)(∑(P-Q)²/Q) = 1·χ²
  unfold chiSqDiv
  have h_cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun x => √(Q x)) (fun x => |P x - Q x| / √(Q x))
  have h_prod : ∀ x, √(Q x) * (|P x - Q x| / √(Q x)) = |P x - Q x| := by
    intro x
    rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt (sqrt_pos.mpr (hQ_pos x)))]
  have h_sq_a : ∀ x, √(Q x) ^ 2 = Q x := fun x => sq_sqrt (hQ_pos x).le
  have h_sq_b : ∀ x, (|P x - Q x| / √(Q x)) ^ 2 = (P x - Q x) ^ 2 / Q x := by
    intro x
    rw [div_pow, sq_abs, sq_sqrt (le_of_lt (hQ_pos x))]
  simp_rw [h_prod, h_sq_a, h_sq_b, hQ_sum, one_mul] at h_cs
  exact h_cs

end
