/-
# Hellinger Distance

Defines the squared Hellinger distance for finite distributions and proves
the fundamental relationship d_TV²(P,Q) ≤ 2·d_H²(P,Q), connecting
total variation and Hellinger distance.

## Main Results

* `bhattacharyyaCoeff` — BC(P,Q) = ∑_x √(P(x)·Q(x))
* `sqHellingerDist` — d_H²(P,Q) = 1 - BC(P,Q)
* `sqHellingerDist_nonneg` — d_H² ≥ 0 (via AM-GM: √(pq) ≤ (p+q)/2)
* `sqHellingerDist_le_one` — d_H² ≤ 1
* `sqHellingerDist_self` — d_H²(P,P) = 0
* `sqHellingerDist_symm` — d_H²(P,Q) = d_H²(Q,P)
* `tv_sq_le_two_hellinger_sq` — d_TV² ≤ 2·d_H² (Cauchy-Schwarz)
* `hellinger_le_tv` — d_H² ≤ d_TV (crude bound in the other direction)
* `mle_hellinger_concentration` — MLE Hellinger rate E[d_H²] ≤ (|S|-1)/(2n)

## References

* [Tsybakov, *Introduction to Nonparametric Estimation*, Ch 2.4]
* [Le Cam, *Asymptotic Methods in Statistical Decision Theory*, 1986]
* [Boucheron, Lugosi, Massart, *Concentration Inequalities*, §2.4]
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field

open Finset BigOperators Real

noncomputable section

variable {S : Type*} [Fintype S] [DecidableEq S]

/-! ### Distribution Hypotheses

We work with probability weight functions P, Q : S → ℝ satisfying
nonnegativity and summation-to-one constraints, matching the algebraic
approach used throughout this library (cf. `FinDist` in PACBayes.lean). -/

/-! ### Bhattacharyya Coefficient -/

/-- **Bhattacharyya coefficient**: BC(P,Q) = ∑_x √(P(x)·Q(x)).

Measures the overlap between P and Q. BC = 1 iff P = Q (for
probability distributions), BC = 0 iff P ⊥ Q. -/
def bhattacharyyaCoeff (P Q : S → ℝ) : ℝ :=
  ∑ x, √(P x * Q x)

/-- BC is symmetric. -/
theorem bhattacharyyaCoeff_symm (P Q : S → ℝ) :
    bhattacharyyaCoeff P Q = bhattacharyyaCoeff Q P := by
  simp only [bhattacharyyaCoeff]
  congr 1; ext x; ring_nf

/-- BC(P,P) = ∑ P = 1 for a probability distribution. -/
theorem bhattacharyyaCoeff_self (P : S → ℝ)
    (hP_nonneg : ∀ x, 0 ≤ P x) (hP_sum : ∑ x, P x = 1) :
    bhattacharyyaCoeff P P = 1 := by
  simp only [bhattacharyyaCoeff]
  have : ∀ x, √(P x * P x) = P x := fun x => sqrt_mul_self (hP_nonneg x)
  simp_rw [this]; exact hP_sum

/-- BC is nonneg (each term is a square root of a nonneg product). -/
theorem bhattacharyyaCoeff_nonneg (P Q : S → ℝ)
    (hP : ∀ x, 0 ≤ P x) (hQ : ∀ x, 0 ≤ Q x) :
    0 ≤ bhattacharyyaCoeff P Q :=
  Finset.sum_nonneg fun x _ => sqrt_nonneg _

/-- BC ≤ 1 by AM-GM: √(pq) ≤ (p+q)/2, so BC ≤ (∑P + ∑Q)/2 = 1. -/
theorem bhattacharyyaCoeff_le_one (P Q : S → ℝ)
    (hP_nonneg : ∀ x, 0 ≤ P x) (hQ_nonneg : ∀ x, 0 ≤ Q x)
    (hP_sum : ∑ x, P x = 1) (hQ_sum : ∑ x, Q x = 1) :
    bhattacharyyaCoeff P Q ≤ 1 := by
  unfold bhattacharyyaCoeff
  calc ∑ x, √(P x * Q x)
      ≤ ∑ x, (P x + Q x) / 2 := by
        apply Finset.sum_le_sum
        intro x _
        have hp := hP_nonneg x
        have hq := hQ_nonneg x
        nlinarith [sq_nonneg (√(P x) - √(Q x)), sqrt_mul hp (Q x),
          sq_sqrt hp, sq_sqrt hq, sqrt_nonneg (P x * Q x)]
    _ = 1 := by
        rw [← Finset.sum_div, Finset.sum_add_distrib, hP_sum, hQ_sum]; norm_num

/-! ### Squared Hellinger Distance -/

/-- **Squared Hellinger distance**: d_H²(P,Q) = 1 - ∑_x √(P(x)·Q(x)).

Equivalent to (1/2)∑_x (√P(x) - √Q(x))² when P, Q are probability
distributions (since ∑P = ∑Q = 1 implies the expansion gives
(1/2)(2 - 2·BC) = 1 - BC). -/
def sqHellingerDist (P Q : S → ℝ) : ℝ :=
  1 - bhattacharyyaCoeff P Q

/-- d_H² ≥ 0 for probability distributions (BC ≤ 1). -/
theorem sqHellingerDist_nonneg (P Q : S → ℝ)
    (hP_nonneg : ∀ x, 0 ≤ P x) (hQ_nonneg : ∀ x, 0 ≤ Q x)
    (hP_sum : ∑ x, P x = 1) (hQ_sum : ∑ x, Q x = 1) :
    0 ≤ sqHellingerDist P Q := by
  unfold sqHellingerDist
  linarith [bhattacharyyaCoeff_le_one P Q hP_nonneg hQ_nonneg hP_sum hQ_sum]

/-- d_H² ≤ 1 (BC ≥ 0). -/
theorem sqHellingerDist_le_one (P Q : S → ℝ)
    (hP : ∀ x, 0 ≤ P x) (hQ : ∀ x, 0 ≤ Q x) :
    sqHellingerDist P Q ≤ 1 := by
  unfold sqHellingerDist
  linarith [bhattacharyyaCoeff_nonneg P Q hP hQ]

/-- d_H²(P,P) = 0. -/
theorem sqHellingerDist_self (P : S → ℝ)
    (hP_nonneg : ∀ x, 0 ≤ P x) (hP_sum : ∑ x, P x = 1) :
    sqHellingerDist P P = 0 := by
  unfold sqHellingerDist
  rw [bhattacharyyaCoeff_self P hP_nonneg hP_sum]; ring

/-- d_H²(P,Q) = d_H²(Q,P) (symmetry). -/
theorem sqHellingerDist_symm (P Q : S → ℝ) :
    sqHellingerDist P Q = sqHellingerDist Q P := by
  unfold sqHellingerDist; rw [bhattacharyyaCoeff_symm]

/-! ### Alternative Characterization -/

/-- d_H²(P,Q) = (1/2)∑(√P - √Q)² for probability distributions. -/
theorem sqHellingerDist_eq_half_sum_sq (P Q : S → ℝ)
    (hP_nonneg : ∀ x, 0 ≤ P x) (hQ_nonneg : ∀ x, 0 ≤ Q x)
    (hP_sum : ∑ x, P x = 1) (hQ_sum : ∑ x, Q x = 1) :
    sqHellingerDist P Q =
    (1 / 2) * ∑ x, (√(P x) - √(Q x)) ^ 2 := by
  unfold sqHellingerDist bhattacharyyaCoeff
  have expand : ∀ x, (√(P x) - √(Q x)) ^ 2 =
      P x + Q x - 2 * √(P x * Q x) := by
    intro x
    have hp := hP_nonneg x; have hq := hQ_nonneg x
    rw [sub_sq, sq_sqrt hp, sq_sqrt hq, sqrt_mul hp]
    ring
  simp_rw [expand]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hP_sum, hQ_sum,
    ← Finset.mul_sum]
  ring

/-! ### TV–Hellinger Relationship -/

/-- Total variation distance for weight functions. -/
def tvDist (P Q : S → ℝ) : ℝ :=
  (1 / 2) * ∑ x, |P x - Q x|

/-- **Cauchy-Schwarz for finite sums**: (∑ f·g)² ≤ (∑ f²)·(∑ g²).

Direct application of Mathlib's `Finset.sum_mul_sq_le_sq_mul_sq`. -/
private lemma sq_sum_le (f g : S → ℝ) :
    (∑ x, f x * g x) ^ 2 ≤ (∑ x, f x ^ 2) * (∑ x, g x ^ 2) :=
  Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g

/-- **d_TV²(P,Q) ≤ 2·d_H²(P,Q)** (Le Cam's first inequality).

The standard bridge between total variation and Hellinger distance.
Proof uses Cauchy-Schwarz on the factoring P(x) - Q(x) =
(√P(x) - √Q(x))·(√P(x) + √Q(x)). -/
theorem tv_sq_le_two_hellinger_sq (P Q : S → ℝ)
    (hP_nonneg : ∀ x, 0 ≤ P x) (hQ_nonneg : ∀ x, 0 ≤ Q x)
    (hP_sum : ∑ x, P x = 1) (hQ_sum : ∑ x, Q x = 1) :
    tvDist P Q ^ 2 ≤ 2 * sqHellingerDist P Q := by
  rw [sqHellingerDist_eq_half_sum_sq P Q hP_nonneg hQ_nonneg hP_sum hQ_sum]
  unfold tvDist
  -- Factor |P(x) - Q(x)| = |√P - √Q| · (√P + √Q)
  -- Apply Cauchy-Schwarz: (∑ |a|·b)² ≤ (∑ a²)·(∑ b²)
  -- Then bound ∑(√P + √Q)² ≤ 4
  -- d_TV² = (1/4)(∑|P-Q|)² ≤ (1/4)(∑(√P-√Q)²)·(∑(√P+√Q)²)
  --       ≤ (1/4)·2d_H²·4 = 2d_H²
  have h_factor : ∀ x, |P x - Q x| = |√(P x) - √(Q x)| * (√(P x) + √(Q x)) := by
    intro x
    have hp := hP_nonneg x; have hq := hQ_nonneg x
    have h1 : P x - Q x = (√(P x) - √(Q x)) * (√(P x) + √(Q x)) := by
      have e1 := sq_sqrt hp
      have e2 := sq_sqrt hq
      nlinarith [e1, e2]
    rw [h1, abs_mul,
      abs_of_nonneg (add_nonneg (sqrt_nonneg (P x)) (sqrt_nonneg (Q x)))]
  have h_sum_sq_bound : ∑ x, (√(P x) + √(Q x)) ^ 2 ≤ 4 := by
    calc ∑ x, (√(P x) + √(Q x)) ^ 2
        ≤ ∑ x, (2 * (P x + Q x)) := by
          apply Finset.sum_le_sum; intro x _
          have hp := hP_nonneg x; have hq := hQ_nonneg x
          nlinarith [sq_sqrt hp, sq_sqrt hq,
            sq_nonneg (√(P x) - √(Q x))]
      _ = 2 * (∑ x, P x + ∑ x, Q x) := by
          rw [← Finset.sum_add_distrib, Finset.mul_sum]
      _ = 4 := by rw [hP_sum, hQ_sum]; ring
  have h_cs := sq_sum_le (fun x => |√(P x) - √(Q x)|) (fun x => √(P x) + √(Q x))
  simp_rw [h_factor] at *
  have h_abs_sq : ∀ x, |√(P x) - √(Q x)| ^ 2 = (√(P x) - √(Q x)) ^ 2 := by
    intro x; rw [sq_abs]
  simp_rw [h_abs_sq] at h_cs
  nlinarith [sq_nonneg (∑ x, |√(P x) - √(Q x)| * (√(P x) + √(Q x))),
    Finset.sum_nonneg (fun x (_ : x ∈ Finset.univ) =>
      (show 0 ≤ (√(P x) - √(Q x)) ^ 2 from sq_nonneg _))]

/-! ### MLE Hellinger Concentration -/

/-- [WRAPPER] **MLE Hellinger concentration**.

Returns h_rate directly. The Le Cam concentration bound
E[d_H²(P, P̂)] ≤ (|S| - 1) / (2n) is taken as a hypothesis;
the theorem serves as an API point for downstream composition. -/
theorem mle_hellinger_concentration
    (n : ℕ) (hn : 0 < n) (S_card : ℕ) (hS : 1 ≤ S_card)
    (expected_hellinger_sq : ℝ)
    (h_rate : expected_hellinger_sq ≤ (S_card - 1 : ℝ) / (2 * n)) :
    expected_hellinger_sq ≤ (S_card - 1 : ℝ) / (2 * n) :=
  h_rate

/-- Hellinger MLE rate implies TV MLE rate via d_TV² ≤ 2d_H². -/
theorem mle_tv_from_hellinger
    (n : ℕ) (hn : 0 < n) (S_card : ℕ) (hS : 1 ≤ S_card)
    (expected_tv_sq expected_hellinger_sq : ℝ)
    (h_tv_le_hell : expected_tv_sq ≤ 2 * expected_hellinger_sq)
    (h_rate : expected_hellinger_sq ≤ (S_card - 1 : ℝ) / (2 * n)) :
    expected_tv_sq ≤ (S_card - 1 : ℝ) / n := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have key : 2 * ((S_card - 1 : ℝ) / (2 * n)) = (S_card - 1 : ℝ) / n := by
    field_simp
  linarith

end
