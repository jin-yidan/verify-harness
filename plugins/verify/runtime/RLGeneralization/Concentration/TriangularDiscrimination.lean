/-
# Triangular Discrimination

Defines the triangular discrimination (Le Cam divergence):

  Δ(P,Q) = ∑_x (P(x) - Q(x))² / (P(x) + Q(x))

and proves its relationships to other divergences.

## Divergence Hierarchy

The correct ordering (for probability distributions P, Q) is:

  d_TV²(P,Q) ≤ Δ(P,Q)/2 ≤ H²(P,Q) ... NO!

**CORRECTION**: The checklist stated d_Δ ≤ 2·d_H², but this is
FALSE — the correct direction is:

  d_TV²(P,Q) ≤ Δ(P,Q)/2    (TV bounded by triangular)
  2·d_H²(P,Q) ≤ Δ(P,Q)     (Hellinger bounded by triangular)
  Δ(P,Q) ≤ χ²(P‖Q)         (triangular bounded by chi-squared)

So the full chain is:  d_TV² ≤ Δ/2  and  2·H² ≤ Δ ≤ χ².

Counterexample for the wrong direction:
  P = (0.9, 0.1), Q = (0.1, 0.9)
  d_H² = 0.4,  Δ = 1.28,  so Δ > 2·d_H² = 0.8.

## Main Results

* `triangularDisc` — Δ(P,Q) = ∑ (P-Q)²/(P+Q)
* `triangularDisc_nonneg` — Δ ≥ 0
* `triangularDisc_self` — Δ(P,P) = 0
* `triangularDisc_symm` — Δ(P,Q) = Δ(Q,P)
* `tv_sq_le_triangular_half` — d_TV² ≤ Δ/2
* `two_hellinger_le_triangular` — 2·d_H² ≤ Δ
* `triangular_le_chiSq` — Δ ≤ χ²

## References

* [Topsøe, "Some Inequalities for Information Divergence," 2000]
* [Le Cam, "Asymptotic Methods in Statistical Decision Theory," 1986]
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.LinearCombination

open Finset BigOperators Real

noncomputable section

variable {S : Type*} [Fintype S] [DecidableEq S]

/-! ### Triangular Discrimination -/

/-- **Triangular discrimination** (Le Cam divergence):
Δ(P,Q) = ∑_x (P(x) - Q(x))² / (P(x) + Q(x)).

Interpolates between TV distance and chi-squared divergence.
Each term is well-defined when P(x) + Q(x) > 0 (which holds
for probability distributions except at mutual zeros). -/
def triangularDisc (P Q : S → ℝ) : ℝ :=
  ∑ x, (P x - Q x) ^ 2 / (P x + Q x)

/-- Δ ≥ 0 for nonneg weight functions. -/
theorem triangularDisc_nonneg (P Q : S → ℝ)
    (hP : ∀ x, 0 ≤ P x) (hQ : ∀ x, 0 ≤ Q x) :
    0 ≤ triangularDisc P Q :=
  Finset.sum_nonneg fun x _ =>
    div_nonneg (sq_nonneg _) (by linarith [hP x, hQ x])

/-- Δ(P,P) = 0. -/
theorem triangularDisc_self (P : S → ℝ) :
    triangularDisc P P = 0 := by
  simp [triangularDisc, sub_self]

/-- Δ(P,Q) = Δ(Q,P) (symmetry). -/
theorem triangularDisc_symm (P Q : S → ℝ) :
    triangularDisc P Q = triangularDisc Q P := by
  unfold triangularDisc
  congr 1; ext x
  rw [show (Q x - P x) ^ 2 = (P x - Q x) ^ 2 from by ring,
      show Q x + P x = P x + Q x from by ring]

/-! ### Relationship to TV Distance -/

/-- **d_TV²(P,Q) ≤ Δ(P,Q)/2** via Cauchy-Schwarz.

Proof: ∑|P-Q| = ∑ |P-Q|/√(P+Q) · √(P+Q).
By Cauchy-Schwarz: (∑ |P-Q|)² ≤ (∑(P-Q)²/(P+Q))(∑(P+Q)) = Δ·2.
So d_TV² = (1/4)(∑|P-Q|)² ≤ Δ/2. -/
theorem tv_sq_le_triangular_half (P Q : S → ℝ)
    (hP_nonneg : ∀ x, 0 ≤ P x) (hQ_nonneg : ∀ x, 0 ≤ Q x)
    (hP_sum : ∑ x, P x = 1) (hQ_sum : ∑ x, Q x = 1) :
    ((1 / 2 : ℝ) * ∑ x, |P x - Q x|) ^ 2 ≤
    triangularDisc P Q / 2 := by
  unfold triangularDisc
  -- (1/2 · ∑|P-Q|)² ≤ (1/4) · Δ · (∑(P+Q)) = (1/4) · Δ · 2 = Δ/2
  -- Need: (∑|P-Q|)² ≤ Δ · (∑(P+Q)) = Δ · 2
  -- Cauchy-Schwarz: (∑ f·g)² ≤ (∑f²)(∑g²) with f = |P-Q|/√(P+Q), g = √(P+Q)
  have h_sum_pq : ∑ x, (P x + Q x) = 2 := by
    rw [Finset.sum_add_distrib, hP_sum, hQ_sum]; norm_num
  -- Cauchy-Schwarz with f = |P-Q|/√(P+Q), g = √(P+Q):
  -- (∑ |P-Q|)² ≤ (∑ (P-Q)²/(P+Q)) · (∑ (P+Q)) = Δ · 2
  have h_cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun x => |P x - Q x| / √(P x + Q x)) (fun x => √(P x + Q x))
  have h_prod : ∀ x, |P x - Q x| / √(P x + Q x) * √(P x + Q x) = |P x - Q x| := by
    intro x
    rcases eq_or_lt_of_le (add_nonneg (hP_nonneg x) (hQ_nonneg x)) with h0 | hpos
    · have hp0 : P x = 0 := by linarith [hP_nonneg x, hQ_nonneg x]
      have hq0 : Q x = 0 := by linarith [hP_nonneg x, hQ_nonneg x]
      simp [hp0, hq0]
    · rw [div_mul_cancel₀ _ (ne_of_gt (sqrt_pos.mpr hpos))]
  have h_sq_f : ∀ x, (|P x - Q x| / √(P x + Q x)) ^ 2
      = (P x - Q x) ^ 2 / (P x + Q x) := by
    intro x
    rw [div_pow, sq_abs, sq_sqrt (add_nonneg (hP_nonneg x) (hQ_nonneg x))]
  have h_sq_g : ∀ x, √(P x + Q x) ^ 2 = P x + Q x :=
    fun x => sq_sqrt (add_nonneg (hP_nonneg x) (hQ_nonneg x))
  simp_rw [h_prod, h_sq_f, h_sq_g, h_sum_pq] at h_cs
  nlinarith [h_cs]

/-! ### Relationship to Hellinger Distance -/

/-- **2·d_H²(P,Q) ≤ Δ(P,Q)** (Hellinger bounded by triangular).

This corrects the erroneous claim in the checklist that Δ ≤ 2·H².
The correct direction is 2·H² ≤ Δ.

Proof: per-element, √(pq) ≥ 2pq/(p+q) by AM-GM on √(p/q), √(q/p).
So 2·H² = ∑(√p - √q)² = 2 - 2∑√(pq) ≤ 2 - 4∑pq/(p+q)
       = ∑(p+q) - 4∑pq/(p+q) = ∑((p+q)² - 4pq)/(p+q)
       = ∑(p-q)²/(p+q) = Δ. -/
theorem two_hellinger_le_triangular (P Q : S → ℝ)
    (hP_nonneg : ∀ x, 0 ≤ P x) (hQ_nonneg : ∀ x, 0 ≤ Q x)
    (hP_sum : ∑ x, P x = 1) (hQ_sum : ∑ x, Q x = 1)
    (hPQ_pos : ∀ x, 0 < P x + Q x) :
    2 * (1 - ∑ x, √(P x * Q x)) ≤ triangularDisc P Q := by
  unfold triangularDisc
  -- Per element: √(pq) ≥ 2pq/(p+q), so -2√(pq) ≤ -4pq/(p+q)
  -- Therefore: (p-q)²/(p+q) = (p+q) - 4pq/(p+q) ≥ (p+q) - 2·2√(pq)
  --   ... wait, we need: (p-q)²/(p+q) ≥ p + q - 2√(pq) = (√p - √q)²
  -- Per element: (p-q)²/(p+q) ≥ (√p - √q)²
  -- Proof: (p-q)²/(p+q) = (√p-√q)²(√p+√q)²/(p+q)
  --   and (√p+√q)²/(p+q) = (p+q+2√(pq))/(p+q) = 1 + 2√(pq)/(p+q) ≥ 1
  suffices h : ∀ x, (√(P x) - √(Q x)) ^ 2 ≤
      (P x - Q x) ^ 2 / (P x + Q x) by
    have h_sum : ∑ x, (√(P x) - √(Q x)) ^ 2 ≤
        ∑ x, (P x - Q x) ^ 2 / (P x + Q x) :=
      Finset.sum_le_sum fun x _ => h x
    have h_expand : ∑ x, (√(P x) - √(Q x)) ^ 2 =
        2 - 2 * ∑ x, √(P x * Q x) := by
      have h1 : ∀ x, (√(P x) - √(Q x)) ^ 2
          = P x + Q x - 2 * √(P x * Q x) := by
        intro x
        rw [sub_sq, sq_sqrt (hP_nonneg x), sq_sqrt (hQ_nonneg x),
          sqrt_mul (hP_nonneg x)]
        ring
      simp_rw [h1]
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hP_sum, hQ_sum,
        ← Finset.mul_sum]
      ring
    linarith
  intro x
  have hp := hP_nonneg x; have hq := hQ_nonneg x
  have hpq := hPQ_pos x
  rw [le_div_iff₀ hpq]
  -- (√p - √q)²(p+q) ≤ (p-q)² = (√p-√q)²(√p+√q)²,
  -- reduces to p+q ≤ (√p+√q)² = p + 2√(pq) + q, i.e. 0 ≤ 2√p·√q.
  have hdiff : (√(P x) - √(Q x)) * (√(P x) + √(Q x)) = P x - Q x := by
    have e1 := sq_sqrt hp
    have e2 := sq_sqrt hq
    linear_combination e1 - e2
  rw [show (P x - Q x) ^ 2 = (√(P x) - √(Q x)) ^ 2 * (√(P x) + √(Q x)) ^ 2 from by
    rw [← mul_pow, hdiff]]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  nlinarith [sq_sqrt hp, sq_sqrt hq,
    mul_nonneg (sqrt_nonneg (P x)) (sqrt_nonneg (Q x))]

/-! ### Relationship to Chi-Squared -/

/-- **Δ(P,Q) ≤ χ²(P‖Q)** (triangular bounded by chi-squared).

Proof: per-element, P+Q ≥ Q, so (P-Q)²/(P+Q) ≤ (P-Q)²/Q. -/
theorem triangular_le_chiSq (P Q : S → ℝ)
    (hP_nonneg : ∀ x, 0 ≤ P x) (hQ_pos : ∀ x, 0 < Q x) :
    triangularDisc P Q ≤ ∑ x, (P x - Q x) ^ 2 / Q x := by
  apply Finset.sum_le_sum
  intro x _
  apply div_le_div_of_nonneg_left (sq_nonneg (P x - Q x))
  · exact hQ_pos x
  · linarith [hP_nonneg x, hQ_pos x]

end
