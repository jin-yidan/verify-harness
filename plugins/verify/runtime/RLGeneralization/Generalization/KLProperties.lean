/-
# KL Divergence Properties

Extends the KL divergence infrastructure in PACBayes.lean with:
- Chain rule for product distributions
- Data processing inequality
- Donsker-Varadhan variational representation

## Main Results

* `klDiv_chain_rule` — KL(P⊗Q ‖ P'⊗Q') = KL(P‖P') + KL(Q‖Q')
* `klDiv_data_processing` — KL(f#P ‖ f#Q) ≤ KL(P‖Q)
* `klDiv_donsker_varadhan` — KL(P‖Q) ≥ E_P[f] - log(E_Q[exp(f)])
* `klDiv_pinsker` — d_TV(P,Q)² ≤ KL(P‖Q)/2 (Pinsker's inequality)

## References

* [Cover & Thomas, *Elements of Information Theory*, Ch 2]
* [Boucheron et al., *Concentration Inequalities*, §4.3]
-/

import RLGeneralization.Generalization.PACBayes
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Algebra.BigOperators.Field

open Finset BigOperators Real

noncomputable section

variable {H : Type*} [Fintype H] [DecidableEq H]

/-! ### Chain Rule -/

/-- **KL chain rule for product distributions**: if (P, Q) are
distributions over H₁ × H₂ that factor as P = P₁ ⊗ P₂ and
Q = Q₁ ⊗ Q₂, then KL(P‖Q) = KL(P₁‖Q₁) + KL(P₂‖Q₂).

The algebraic proof: KL(P₁⊗P₂ ‖ Q₁⊗Q₂)
  = ∑_{h₁,h₂} P₁(h₁)P₂(h₂) log(P₁(h₁)P₂(h₂)/(Q₁(h₁)Q₂(h₂)))
  = ∑_{h₁,h₂} P₁(h₁)P₂(h₂) [log(P₁(h₁)/Q₁(h₁)) + log(P₂(h₂)/Q₂(h₂))]
  = (∑P₂) · ∑P₁·log(P₁/Q₁) + (∑P₁) · ∑P₂·log(P₂/Q₂)
  = KL(P₁‖Q₁) + KL(P₂‖Q₂). -/
theorem klDiv_chain_rule
    {H₁ H₂ : Type*} [Fintype H₁] [Fintype H₂]
    (P₁ Q₁ : FinDist H₁) (P₂ Q₂ : FinDist H₂)
    (hQ₁_pos : ∀ h, 0 < Q₁.wt h) (hQ₂_pos : ∀ h, 0 < Q₂.wt h) :
    let P_prod : FinDist (H₁ × H₂) :=
      { wt := fun ⟨h₁, h₂⟩ => P₁.wt h₁ * P₂.wt h₂
        wt_nonneg := fun ⟨h₁, h₂⟩ => mul_nonneg (P₁.wt_nonneg h₁) (P₂.wt_nonneg h₂)
        wt_sum_one := by
          rw [Fintype.sum_prod_type]
          simp_rw [← Finset.mul_sum, P₂.wt_sum_one, mul_one, P₁.wt_sum_one] }
    let Q_prod : FinDist (H₁ × H₂) :=
      { wt := fun ⟨h₁, h₂⟩ => Q₁.wt h₁ * Q₂.wt h₂
        wt_nonneg := fun ⟨h₁, h₂⟩ => mul_nonneg (Q₁.wt_nonneg h₁) (Q₂.wt_nonneg h₂)
        wt_sum_one := by
          rw [Fintype.sum_prod_type]
          simp_rw [← Finset.mul_sum, Q₂.wt_sum_one, mul_one, Q₁.wt_sum_one] }
    klDiv P_prod Q_prod = klDiv P₁ Q₁ + klDiv P₂ Q₂ := by
  simp only [klDiv]
  rw [Fintype.sum_prod_type]
  have key : ∀ h₁ h₂, P₁.wt h₁ * P₂.wt h₂ *
      Real.log (P₁.wt h₁ * P₂.wt h₂ / (Q₁.wt h₁ * Q₂.wt h₂)) =
      P₂.wt h₂ * (P₁.wt h₁ * Real.log (P₁.wt h₁ / Q₁.wt h₁)) +
      P₁.wt h₁ * (P₂.wt h₂ * Real.log (P₂.wt h₂ / Q₂.wt h₂)) := by
    intro h₁ h₂
    by_cases hp₁ : P₁.wt h₁ = 0
    · simp [hp₁]
    · by_cases hp₂ : P₂.wt h₂ = 0
      · simp [hp₂]
      · have hp₁_pos := lt_of_le_of_ne (P₁.wt_nonneg h₁) (Ne.symm hp₁)
        have hp₂_pos := lt_of_le_of_ne (P₂.wt_nonneg h₂) (Ne.symm hp₂)
        rw [mul_div_mul_comm,
            Real.log_mul (div_ne_zero (ne_of_gt hp₁_pos) (ne_of_gt (hQ₁_pos h₁)))
              (div_ne_zero (ne_of_gt hp₂_pos) (ne_of_gt (hQ₂_pos h₂)))]
        ring
  simp_rw [key, Finset.sum_add_distrib]
  congr 1
  · simp_rw [← Finset.sum_mul, P₂.wt_sum_one, one_mul]
  · simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul, P₁.wt_sum_one, one_mul]

/-! ### Log-Sum Inequality -/

/-- **Log-sum inequality** (Cover & Thomas, Thm 2.7.1):
    (∑ aᵢ)·log(∑aᵢ/∑bᵢ) ≤ ∑ aᵢ·log(aᵢ/bᵢ) for aᵢ ≥ 0, bᵢ > 0.

    The unnormalized generalization of KL non-negativity; the standard tool
    for KL convexity and the data-processing inequality (used below).
    Promoted from `private` after the 2026-06-10 gate audit found external
    demand for it (see rlverify/results/gate_ab_test.md). -/
lemma log_sum_le_sum_log {ι : Type*} (s : Finset ι)
    (a b : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 < b i)
    (hB : 0 < ∑ i ∈ s, b i) :
    (∑ i ∈ s, a i) * Real.log ((∑ i ∈ s, a i) / (∑ i ∈ s, b i)) ≤
    ∑ i ∈ s, a i * Real.log (a i / b i) := by
  set A := ∑ i ∈ s, a i
  set B := ∑ i ∈ s, b i
  by_cases hA : A = 0
  · have h_zero : ∀ i ∈ s, a i = 0 := fun i hi =>
      le_antisymm (by linarith [Finset.single_le_sum (fun j hj => ha j hj) hi]) (ha i hi)
    simp only [hA, zero_mul]
    exact Finset.sum_nonneg fun i hi => by simp [h_zero i hi]
  · have hA_pos : 0 < A := lt_of_le_of_ne (Finset.sum_nonneg ha) (Ne.symm hA)
    suffices h : 0 ≤ ∑ i ∈ s, (a i * Real.log (a i / b i) -
        a i * Real.log (A / B)) by
      have : ∑ i ∈ s, (a i * Real.log (a i / b i) - a i * Real.log (A / B)) =
          (∑ i ∈ s, a i * Real.log (a i / b i)) - A * Real.log (A / B) := by
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
      linarith
    have h_sum_zero : ∑ i ∈ s, (a i - A * b i / B) = 0 := by
      have : ∑ i ∈ s, A * b i / B = A := by
        rw [← Finset.sum_div, ← Finset.mul_sum,
          mul_div_cancel_right₀ A (ne_of_gt hB)]
      rw [Finset.sum_sub_distrib, this, sub_self]
    calc (0 : ℝ) = ∑ i ∈ s, (a i - A * b i / B) := h_sum_zero.symm
      _ ≤ ∑ i ∈ s, (a i * Real.log (a i / b i) -
            a i * Real.log (A / B)) := by
          apply Finset.sum_le_sum; intro i hi
          by_cases hai : a i = 0
          · simp only [hai, zero_mul, zero_sub, neg_zero]
            exact neg_nonpos_of_nonneg (div_nonneg
              (mul_nonneg (le_of_lt hA_pos) (le_of_lt (hb i hi))) (le_of_lt hB))
          · have hai_pos : 0 < a i := lt_of_le_of_ne (ha i hi) (Ne.symm hai)
            have h_t_pos : 0 < a i * B / (b i * A) :=
              div_pos (mul_pos hai_pos hB) (mul_pos (hb i hi) hA_pos)
            have h_log_eq : a i * Real.log (a i / b i) -
                a i * Real.log (A / B) =
                a i * Real.log (a i * B / (b i * A)) := by
              rw [← mul_sub]; congr 1
              rw [Real.log_div (ne_of_gt hai_pos) (ne_of_gt (hb i hi)),
                  Real.log_div (ne_of_gt hA_pos) (ne_of_gt hB),
                  Real.log_div (ne_of_gt (mul_pos hai_pos hB))
                    (ne_of_gt (mul_pos (hb i hi) hA_pos)),
                  Real.log_mul (ne_of_gt hai_pos) (ne_of_gt hB),
                  Real.log_mul (ne_of_gt (hb i hi)) (ne_of_gt hA_pos)]
              ring
            have h_log_ge : 1 - b i * A / (a i * B) ≤
                Real.log (a i * B / (b i * A)) := by
              have h_inv := Real.log_le_sub_one_of_pos (inv_pos.mpr h_t_pos)
              rw [inv_div] at h_inv
              have h_neg : Real.log (a i * B / (b i * A)) =
                  -Real.log (b i * A / (a i * B)) := by
                rw [Real.log_div (ne_of_gt (mul_pos hai_pos hB))
                      (ne_of_gt (mul_pos (hb i hi) hA_pos)),
                    Real.log_div (ne_of_gt (mul_pos (hb i hi) hA_pos))
                      (ne_of_gt (mul_pos hai_pos hB))]
                ring
              linarith
            have h_mul : a i * (1 - b i * A / (a i * B)) =
                a i - A * b i / B := by
              field_simp [ne_of_gt hai_pos, ne_of_gt hB]
            calc a i - A * b i / B
                = a i * (1 - b i * A / (a i * B)) := h_mul.symm
              _ ≤ a i * Real.log (a i * B / (b i * A)) :=
                  mul_le_mul_of_nonneg_left h_log_ge (le_of_lt hai_pos)
              _ = a i * Real.log (a i / b i) -
                  a i * Real.log (A / B) := h_log_eq.symm

/-! ### Data Processing Inequality -/

/-- **KL data processing inequality**: for any deterministic map f,
KL(f#P ‖ f#Q) ≤ KL(P‖Q).

Processing data can only lose information, never create it.
For finite types, f#P(y) = ∑_{x: f(x)=y} P(x). -/
theorem klDiv_data_processing
    {H₁ H₂ : Type*} [Fintype H₁] [Fintype H₂] [DecidableEq H₁] [DecidableEq H₂]
    (P Q : FinDist H₁)
    (hQ_pos : ∀ h, 0 < Q.wt h)
    (f : H₁ → H₂)
    (hQ_push_pos : ∀ y, 0 < ∑ x ∈ Finset.univ.filter (fun x => f x = y), Q.wt x) :
    let P_push : FinDist H₂ :=
      { wt := fun y => ∑ x ∈ Finset.univ.filter (fun x => f x = y), P.wt x
        wt_nonneg := fun y => Finset.sum_nonneg fun x _ => P.wt_nonneg x
        wt_sum_one := by
          rw [Finset.sum_fiberwise_of_maps_to (fun x _ => Finset.mem_univ (f x))]
          exact P.wt_sum_one }
    let Q_push : FinDist H₂ :=
      { wt := fun y => ∑ x ∈ Finset.univ.filter (fun x => f x = y), Q.wt x
        wt_nonneg := fun y => Finset.sum_nonneg fun x _ => Q.wt_nonneg x
        wt_sum_one := by
          rw [Finset.sum_fiberwise_of_maps_to (fun x _ => Finset.mem_univ (f x))]
          exact Q.wt_sum_one }
    klDiv P_push Q_push ≤ klDiv P Q := by
  simp only [klDiv]
  suffices h : ∀ y : H₂, (∑ x ∈ Finset.univ.filter (fun x => f x = y), P.wt x) *
      Real.log ((∑ x ∈ Finset.univ.filter (fun x => f x = y), P.wt x) /
        (∑ x ∈ Finset.univ.filter (fun x => f x = y), Q.wt x)) ≤
      ∑ x ∈ Finset.univ.filter (fun x => f x = y),
        P.wt x * Real.log (P.wt x / Q.wt x) by
    calc ∑ y : H₂, (∑ x ∈ Finset.univ.filter (fun x => f x = y), P.wt x) *
            Real.log ((∑ x ∈ Finset.univ.filter (fun x => f x = y), P.wt x) /
              (∑ x ∈ Finset.univ.filter (fun x => f x = y), Q.wt x))
        ≤ ∑ y : H₂, ∑ x ∈ Finset.univ.filter (fun x => f x = y),
            P.wt x * Real.log (P.wt x / Q.wt x) :=
          Finset.sum_le_sum (fun y _ => h y)
      _ = ∑ h₁ : H₁, P.wt h₁ * Real.log (P.wt h₁ / Q.wt h₁) :=
          Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
            (fun x _ => Finset.mem_univ (f x))
            (fun x => P.wt x * Real.log (P.wt x / Q.wt x))
  intro y
  exact log_sum_le_sum_log _ _ _ (fun x _ => P.wt_nonneg x) (fun x _ => hQ_pos x)
    (hQ_push_pos y)

/-! ### Donsker-Varadhan Variational Form -/

/-- **Donsker-Varadhan variational representation** (one direction):
for any function f : H → ℝ,

  E_P[f] - log(E_Q[exp(f)]) ≤ KL(P‖Q)

This is the correct form of the "density ratio bound" — NOT the
false claim that KL ≤ η implies pointwise π/π₀ ≤ exp(η).

The Donsker-Varadhan formula says KL(P‖Q) = sup_f {E_P[f] - log E_Q[e^f]}.
We prove the ≤ direction (sufficient for RL applications). -/
theorem klDiv_donsker_varadhan_le
    (P Q : FinDist H)
    (hQ_pos : ∀ h, 0 < Q.wt h)
    (f : H → ℝ) :
    FinDist.expect P f - Real.log (FinDist.expect Q (fun h => exp (f h))) ≤
    klDiv P Q := by
  simp only [FinDist.expect, klDiv]
  have hne : (Finset.univ : Finset H).Nonempty := by
    by_contra h; rw [Finset.not_nonempty_iff_eq_empty] at h
    have := Q.wt_sum_one; simp [h] at this
  set M := ∑ h, Q.wt h * exp (f h)
  have hM : 0 < M := Finset.sum_pos (fun h _ => mul_pos (hQ_pos h) (exp_pos _)) hne
  suffices h : ∑ h, P.wt h * Real.log (Q.wt h * exp (f h) / (M * P.wt h)) ≤ 0 by
    have h_eq : ∑ h, P.wt h * Real.log (Q.wt h * exp (f h) / (M * P.wt h)) =
        (∑ h, P.wt h * f h) - (∑ h, P.wt h * Real.log (P.wt h / Q.wt h)) -
        Real.log M := by
      have h_pw : ∀ a, P.wt a * Real.log (Q.wt a * exp (f a) / (M * P.wt a)) =
          P.wt a * f a - P.wt a * Real.log (P.wt a / Q.wt a) -
          P.wt a * Real.log M := by
        intro a
        by_cases ha : P.wt a = 0
        · simp [ha]
        · have hPa : 0 < P.wt a := lt_of_le_of_ne (P.wt_nonneg a) (Ne.symm ha)
          rw [Real.log_div (ne_of_gt (mul_pos (hQ_pos a) (exp_pos _)))
                (ne_of_gt (mul_pos hM hPa)),
              Real.log_mul (ne_of_gt (hQ_pos a)) (ne_of_gt (exp_pos _)),
              Real.log_exp,
              Real.log_mul (ne_of_gt hM) (ne_of_gt hPa),
              Real.log_div (ne_of_gt hPa) (ne_of_gt (hQ_pos a))]
          ring
      simp_rw [h_pw, Finset.sum_sub_distrib, ← Finset.sum_mul, P.wt_sum_one, one_mul]
    linarith
  calc ∑ h, P.wt h * Real.log (Q.wt h * exp (f h) / (M * P.wt h))
      ≤ ∑ h, P.wt h * (Q.wt h * exp (f h) / (M * P.wt h) - 1) := by
        apply Finset.sum_le_sum; intro a _
        by_cases ha : P.wt a = 0
        · simp [ha]
        · exact mul_le_mul_of_nonneg_left
            (Real.log_le_sub_one_of_pos (div_pos (mul_pos (hQ_pos a) (exp_pos _))
              (mul_pos hM (lt_of_le_of_ne (P.wt_nonneg a) (Ne.symm ha)))))
            (P.wt_nonneg a)
    _ ≤ ∑ h, (Q.wt h * exp (f h) / M - P.wt h) := by
        apply Finset.sum_le_sum; intro a _
        by_cases ha : P.wt a = 0
        · simp [ha]
          exact div_nonneg (mul_nonneg (le_of_lt (hQ_pos a)) (le_of_lt (exp_pos _)))
            (le_of_lt hM)
        · have hPa : 0 < P.wt a := lt_of_le_of_ne (P.wt_nonneg a) (Ne.symm ha)
          rw [mul_sub, mul_one]
          have : P.wt a * (Q.wt a * exp (f a) / (M * P.wt a)) =
              Q.wt a * exp (f a) / M := by
            field_simp [ne_of_gt hPa, ne_of_gt hM]
          linarith
    _ = 0 := by
        have hg_sum : ∑ h, Q.wt h * exp (f h) / M = 1 := by
          simp_rw [div_eq_mul_inv, ← Finset.sum_mul]
          exact mul_inv_cancel₀ (ne_of_gt hM)
        simp_rw [Finset.sum_sub_distrib, hg_sum, P.wt_sum_one, sub_self]

/-! ### Pinsker's Inequality -/

/-- Binary Pinsker's inequality: for p, q ∈ (0,1),
    2(p-q)² ≤ p·log(p/q) + (1-p)·log((1-p)/(1-q)).
    Proof: the function g(t) = binaryKL(t,q) - 2(t-q)² is convex
    (since g''(t) = 1/(t(1-t)) - 4 ≥ 0) with g(q) = 0 and g'(q) = 0,
    hence g ≥ 0. -/
private lemma binary_pinsker {p q : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 0 < q) (hq1 : q < 1) :
    2 * (p - q) ^ 2 ≤
    p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q)) := by
  set g : ℝ → ℝ := fun t =>
    t * Real.log (t / q) + (1 - t) * Real.log ((1 - t) / (1 - q)) - 2 * (t - q) ^ 2
  suffices hgp : 0 ≤ g p by simp only [g] at hgp; linarith
  set g' : ℝ → ℝ := fun t =>
    Real.log (t / q) - Real.log ((1 - t) / (1 - q)) - 4 * (t - q)
  have hgq : g q = 0 := by
    simp only [g, sub_self, mul_zero, Real.log_one, div_self (ne_of_gt hq),
      div_self (ne_of_gt (sub_pos.mpr hq1))]; ring
  have hg'q : g' q = 0 := by
    simp only [g', sub_self, mul_zero, Real.log_one, div_self (ne_of_gt hq),
      div_self (ne_of_gt (sub_pos.mpr hq1))]
  have hg_deriv : ∀ t ∈ Set.Ioo (0:ℝ) 1, HasDerivAt g (g' t) t := by
    intro t ⟨ht0, ht1⟩
    have ht_ne : t ≠ 0 := ne_of_gt ht0
    have h1t_ne : 1 - t ≠ 0 := ne_of_gt (sub_pos.mpr ht1)
    have hq_ne : (q : ℝ) ≠ 0 := ne_of_gt hq
    have h1q_ne : (1 - q : ℝ) ≠ 0 := ne_of_gt (sub_pos.mpr hq1)
    have hd1 : HasDerivAt (fun t => t * Real.log (t / q)) (Real.log (t / q) + 1) t := by
      have := (hasDerivAt_id t).mul
        ((hasDerivAt_log (div_ne_zero ht_ne hq_ne)).comp t
          ((hasDerivAt_id t).div_const q))
      simp only [id, one_div, mul_comm t, inv_mul_cancel₀ ht_ne] at this
      convert this using 1
      simp only [Function.comp]; field_simp [ht_ne, hq_ne]
    have hd2 : HasDerivAt (fun t => (1 - t) * Real.log ((1 - t) / (1 - q)))
        (-(Real.log ((1 - t) / (1 - q)) + 1)) t := by
      have h1t_pos : 0 < 1 - t := sub_pos.mpr ht1
      have := ((hasDerivAt_const t 1).sub (hasDerivAt_id t)).mul
        ((hasDerivAt_log (div_ne_zero h1t_ne h1q_ne)).comp t
          (((hasDerivAt_const t 1).sub (hasDerivAt_id t)).div_const (1 - q)))
      simp only [sub_self, zero_sub, neg_one_mul, id, one_div,
        mul_comm (1-t), inv_mul_cancel₀ h1t_ne] at this
      convert this using 1
      simp only [Function.comp, Pi.sub_apply, id]; field_simp [h1t_ne, h1q_ne]; ring
    have hd3 : HasDerivAt (fun t => -2 * (t - q) ^ 2) (-4 * (t - q)) t := by
      have := (hasDerivAt_id t).sub (hasDerivAt_const t q)
      have := this.pow 2
      have := (hasDerivAt_const t (-2 : ℝ)).mul this
      convert this using 1
      simp only [Pi.sub_apply, Pi.pow_apply, Pi.mul_apply, id]; push_cast; ring
    have hd := hd1.add (hd2.add hd3)
    exact (hd.congr_of_eventuallyEq (by
      filter_upwards with x; simp only [g, Pi.add_apply]; ring
    )).congr_deriv (by simp only [g']; ring)
  have hg'_deriv : ∀ t ∈ Set.Ioo (0:ℝ) 1, HasDerivAt g' (t⁻¹ + (1 - t)⁻¹ - 4) t := by
    intro t ⟨ht0, ht1⟩
    have ht_ne : t ≠ 0 := ne_of_gt ht0
    have h1t_ne : 1 - t ≠ 0 := ne_of_gt (sub_pos.mpr ht1)
    have hq_ne : (q : ℝ) ≠ 0 := ne_of_gt hq
    have h1q_ne : (1 - q : ℝ) ≠ 0 := ne_of_gt (sub_pos.mpr hq1)
    have hd1 : HasDerivAt (fun t => Real.log (t / q)) t⁻¹ t := by
      have := (hasDerivAt_log (div_ne_zero ht_ne hq_ne)).comp t
        ((hasDerivAt_id t).div_const q)
      exact (this.congr_of_eventuallyEq (by
        filter_upwards with x; simp [Function.comp]
      )).congr_deriv (by simp [id]; field_simp [ht_ne, hq_ne])
    have hd2 : HasDerivAt (fun t => -Real.log ((1 - t) / (1 - q))) (1 - t)⁻¹ t := by
      have h1t_pos : 0 < 1 - t := sub_pos.mpr ht1
      have := (hasDerivAt_log (div_ne_zero h1t_ne h1q_ne)).comp t
        (((hasDerivAt_const t 1).sub (hasDerivAt_id t)).div_const (1 - q))
      exact (this.neg.congr_of_eventuallyEq (by
        filter_upwards with x; simp [Function.comp, Pi.neg_apply]
      )).congr_deriv (by simp [Pi.neg_apply, id]; field_simp [h1t_ne, h1q_ne])
    have hd3 : HasDerivAt (fun t => -4 * (t - q)) (-4 : ℝ) t := by
      have := ((hasDerivAt_id t).sub (hasDerivAt_const t q)).const_mul (-4 : ℝ)
      exact (this.congr_of_eventuallyEq (by
        filter_upwards with x; simp [id, Pi.sub_apply, Pi.smul_apply]
      )).congr_deriv (by simp [id, Pi.sub_apply])
    have hd := hd1.add (hd2.add hd3)
    exact (hd.congr_of_eventuallyEq (by
      filter_upwards with x; simp only [g', Pi.add_apply]; ring
    )).congr_deriv (by ring)
  have hg''_nonneg : ∀ t ∈ Set.Ioo (0:ℝ) 1, 0 ≤ t⁻¹ + (1 - t)⁻¹ - 4 := by
    intro t ⟨ht0, ht1⟩
    have h1 : 0 < t * (1 - t) := mul_pos ht0 (sub_pos.mpr ht1)
    have h2 : t * (1 - t) ≤ 1 / 4 := by nlinarith [sq_nonneg (2 * t - 1)]
    have h3 : t⁻¹ + (1 - t)⁻¹ = 1 / (t * (1 - t)) := by
      field_simp [ne_of_gt ht0, ne_of_gt (sub_pos.mpr ht1)]; ring
    rw [h3]
    have h4 : (4 : ℝ) ≤ 1 / (t * (1 - t)) := by
      rw [le_div_iff₀ h1]; linarith
    linarith
  have hg_convex : ConvexOn ℝ (Set.Ioo 0 1) g := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioo 0 1)
    · apply ContinuousOn.sub
      · apply ContinuousOn.add
        · apply ContinuousOn.mul continuousOn_id
          exact (continuousOn_log.comp
            (ContinuousOn.div continuousOn_id continuousOn_const (fun _ _ =>
              ne_of_gt hq))
            (fun t ⟨ht, _⟩ => div_ne_zero (ne_of_gt ht) (ne_of_gt hq)))
        · apply ContinuousOn.mul (continuousOn_const.sub continuousOn_id)
          exact (continuousOn_log.comp
            (ContinuousOn.div (continuousOn_const.sub continuousOn_id) continuousOn_const
              (fun _ _ => ne_of_gt (sub_pos.mpr hq1)))
            (fun t ⟨_, ht⟩ => div_ne_zero (ne_of_gt (sub_pos.mpr ht))
              (ne_of_gt (sub_pos.mpr hq1))))
      · exact (continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).pow 2))
    · intro t ht
      rw [interior_Ioo] at ht
      exact (hg_deriv t ht).hasDerivWithinAt
    · intro t ht
      rw [interior_Ioo] at ht
      exact (hg'_deriv t ht).hasDerivWithinAt
    · intro t ht
      rw [interior_Ioo] at ht
      exact hg''_nonneg t ht
  have hq_mem : q ∈ Set.Ioo (0:ℝ) 1 := ⟨hq, hq1⟩
  have hp_mem : p ∈ Set.Ioo (0:ℝ) 1 := ⟨hp, hp1⟩
  rcases lt_trichotomy p q with hpq | rfl | hqp
  · have h_slope := hg_convex.slope_le_of_hasDerivWithinAt_Iio hp_mem hq_mem hpq
      (hg_deriv q hq_mem).hasDerivWithinAt
    rw [hg'q] at h_slope
    have h_eq : slope g p q = (g q - g p) / (q - p) := slope_def_field g p q
    rw [h_eq, hgq, zero_sub, div_le_iff₀ (sub_pos.mpr hpq), zero_mul] at h_slope
    linarith
  · rw [hgq]
  · have h_slope := hg_convex.le_slope_of_hasDerivAt hq_mem hp_mem hqp
      (hg_deriv q hq_mem)
    rw [hg'q] at h_slope
    have h_eq : slope g q p = (g p - g q) / (p - q) := slope_def_field g q p
    rw [h_eq, hgq, sub_zero, le_div_iff₀ (sub_pos.mpr hqp), zero_mul] at h_slope
    exact h_slope

private lemma neg_log_ge_two_sq {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) :
    2 * (1 - q) ^ 2 ≤ -Real.log q := by
  rcases eq_or_lt_of_le hq1 with rfl | hq1
  · simp [Real.log_one]
  suffices h : 0 ≤ -Real.log q - 2 * (1 - q) ^ 2 by linarith
  set k : ℝ → ℝ := fun t => -Real.log t - 2 * (1 - t) ^ 2
  change 0 ≤ k q
  have hk1 : k 1 = 0 := by simp [k, Real.log_one]
  have hk_anti : AntitoneOn k (Set.Icc q 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc q 1)
    · exact (continuousOn_log.mono (fun t (ht : t ∈ Set.Icc q 1) =>
        ne_of_gt (lt_of_lt_of_le hq ht.1))).neg.sub
        ((continuous_const.mul ((continuous_const.sub continuous_id).pow 2)).continuousOn)
    · intro x hx
      rw [interior_Icc] at hx
      have hx0 : 0 < x := lt_trans hq hx.1
      exact ((differentiableAt_log (ne_of_gt hx0)).neg.sub
        ((differentiableAt_const 2).mul
          ((differentiableAt_const 1).sub differentiableAt_id |>.pow 2))).differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hx0 : 0 < x := lt_trans hq hx.1
      have hd : HasDerivAt k (-x⁻¹ + 4 * (1 - x)) x := by
        have h1 := (hasDerivAt_log (ne_of_gt hx0)).neg
        have h2 : HasDerivAt (fun t => 2 * (1 - t) ^ 2) (-4 * (1 - x)) x := by
          have := ((hasDerivAt_const x 1).sub (hasDerivAt_id x)).pow 2
          have := (hasDerivAt_const x (2 : ℝ)).mul this
          convert this using 1
          simp only [Pi.sub_apply, Pi.pow_apply, id]; push_cast; ring
        convert h1.sub h2 using 1; ring
      rw [hd.deriv]
      have h_eq : -x⁻¹ + 4 * (1 - x) = -(2 * x - 1) ^ 2 / x := by
        field_simp; ring
      rw [h_eq]
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos_of_nonneg (sq_nonneg _)) (le_of_lt hx0)
  linarith [hk_anti (Set.left_mem_Icc.mpr (le_of_lt hq1))
    (Set.right_mem_Icc.mpr (le_of_lt hq1)) (le_of_lt hq1)]

/-- **Pinsker's inequality**: d_TV(P,Q)² ≤ KL(P‖Q) / 2.

This is stronger than d_TV² ≤ 2H² combined with H² ≤ KL.
We state it for finite distributions. -/
theorem klDiv_pinsker
    (P Q : FinDist H)
    (hQ_pos : ∀ h, 0 < Q.wt h) :
    ((1 / 2 : ℝ) * ∑ h, |P.wt h - Q.wt h|) ^ 2 ≤ klDiv P Q / 2 := by
  set S := Finset.univ.filter (fun h => Q.wt h ≤ P.wt h)
  set T := Finset.univ.filter (fun h => P.wt h < Q.wt h)
  set p := ∑ h ∈ S, P.wt h
  set q := ∑ h ∈ S, Q.wt h
  have hST : Finset.univ = S ∪ T := by
    ext h; simp [S, T]; exact le_or_gt (Q.wt h) (P.wt h)
  have hST_disj : Disjoint S T := by
    rw [Finset.disjoint_filter]
    intro h _ hle hlt; exact not_lt.mpr hle hlt
  have hp_eq : ∑ h ∈ T, P.wt h = 1 - p := by
    have := P.wt_sum_one
    rw [hST, Finset.sum_union hST_disj] at this; linarith
  have hq_eq : ∑ h ∈ T, Q.wt h = 1 - q := by
    have := Q.wt_sum_one
    rw [hST, Finset.sum_union hST_disj] at this; linarith
  have hp_pos : 0 ≤ p := Finset.sum_nonneg fun h _ => P.wt_nonneg h
  have hq_pos : 0 < q := by
    rcases isEmpty_or_nonempty H with h | hne
    · haveI := h; exact absurd Q.wt_sum_one (by simp)
    · haveI := hne
      rcases Finset.eq_empty_or_nonempty S with hS | hS
      · exfalso
        have hlt : ∀ h : H, P.wt h < Q.wt h := by
          intro h
          have : h ∉ S := by simp [hS]
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at this
          exact this
        have h0 : H := Classical.arbitrary H
        linarith [Finset.sum_lt_sum (fun h (_ : h ∈ Finset.univ) => le_of_lt (hlt h))
          ⟨h0, Finset.mem_univ h0, hlt h0⟩, P.wt_sum_one, Q.wt_sum_one]
      · exact Finset.sum_pos (fun h _ => hQ_pos h) hS
  have h1p_nonneg : 0 ≤ 1 - p := by
    have : 0 ≤ ∑ h ∈ T, P.wt h := Finset.sum_nonneg fun h _ => P.wt_nonneg h
    linarith [hp_eq]
  have h_pq : q ≤ p := by
    have : ∀ h ∈ S, Q.wt h ≤ P.wt h := fun h hh => (Finset.mem_filter.mp hh).2
    exact Finset.sum_le_sum this
  have h_tv_eq : (1 / 2 : ℝ) * ∑ h, |P.wt h - Q.wt h| = p - q := by
    rw [hST, Finset.sum_union hST_disj]
    have hS_abs : ∀ h ∈ S, |P.wt h - Q.wt h| = P.wt h - Q.wt h :=
      fun h hh => abs_of_nonneg (sub_nonneg.mpr (Finset.mem_filter.mp hh).2)
    have hT_abs : ∀ h ∈ T, |P.wt h - Q.wt h| = Q.wt h - P.wt h :=
      fun h hh => (abs_of_nonpos (sub_nonpos.mpr (le_of_lt (Finset.mem_filter.mp hh).2))).trans
        (neg_sub _ _)
    simp_rw [Finset.sum_congr rfl hS_abs, Finset.sum_congr rfl hT_abs,
      Finset.sum_sub_distrib, hp_eq, hq_eq]
    ring
  rw [h_tv_eq]
  suffices h : 2 * (p - q) ^ 2 ≤ klDiv P Q by linarith
  rcases lt_or_eq_of_le h_pq with hpq | hpq
  · have hT_ne : T.Nonempty := by
      by_contra hT_empty
      rw [Finset.not_nonempty_iff_eq_empty] at hT_empty
      have : 1 - q = 0 := by rw [← hq_eq]; simp [show T = ∅ from hT_empty]
      have : 1 - p = 0 := by rw [← hp_eq]; simp [show T = ∅ from hT_empty]
      linarith
    have h1q_pos : 0 < 1 - q := by
      rw [← hq_eq]; exact Finset.sum_pos (fun h _ => hQ_pos h) hT_ne
    have h_data : p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q)) ≤
        klDiv P Q := by
      simp only [klDiv]
      rw [hST, Finset.sum_union hST_disj]
      have hS := log_sum_le_sum_log S _ _ (fun x _ => P.wt_nonneg x)
        (fun x _ => hQ_pos x) hq_pos
      have hT := log_sum_le_sum_log T _ _ (fun x _ => P.wt_nonneg x)
        (fun x _ => hQ_pos x) (by rw [hq_eq]; exact h1q_pos)
      have hT' : (∑ x ∈ T, P.wt x) * Real.log ((∑ x ∈ T, P.wt x) / (∑ x ∈ T, Q.wt x)) =
          (1 - p) * Real.log ((1 - p) / (1 - q)) := by rw [hp_eq, hq_eq]
      linarith
    rcases lt_or_eq_of_le h1p_nonneg with h1p | h1p
    · have hp1 : p < 1 := by linarith
      have hq1 : q < 1 := lt_trans hpq hp1
      have hp0 : 0 < p := lt_trans hq_pos hpq
      linarith [binary_pinsker hp0 hp1 hq_pos hq1]
    · have hp1 : p = 1 := by linarith
      have hq_lt : q < 1 := by linarith
      have h_bp : 2 * (1 - q) ^ 2 ≤ -Real.log q :=
        neg_log_ge_two_sq hq_pos (le_of_lt hq_lt)
      have h_kl : -Real.log q ≤ klDiv P Q := by
        have h1 : p * Real.log (p / q) = -Real.log q := by
          rw [hp1, one_mul, one_div, Real.log_inv]
        have h2 : (1 - p) * Real.log ((1 - p) / (1 - q)) = 0 := by
          have : 1 - p = 0 := by linarith
          rw [this, zero_mul]
        linarith [h_data]
      have : p - q = 1 - q := by linarith
      rw [this]; linarith
  · have : 2 * (p - q) ^ 2 = 0 := by rw [hpq]; ring
    linarith [kl_div_nonneg P Q (fun h _ => hQ_pos h)]

end
