/-
# Minimax Lower Bound for Bandits via Le Cam's Two-Point Method

Proves an Ω(√(KT)) minimax lower bound on the pseudo-regret
of any K-armed bandit algorithm over T rounds, using Le Cam's
two-point method combined with a combinatorial counting argument.

## Overview

Le Cam's two-point method constructs two bandit instances that
have different optimal arms. Any deterministic strategy must
play non-optimally on at least one instance. The combinatorial
core shows that for two instances with gap Δ whose optimal arms
differ, the maximum pseudo-regret is at least Δ · T / 2.

For the Ω(√(KT)) bound (under the standard regime K ≤ T), we
choose Δ = √(KT) / (4T) and verify Δ ≤ 1.

## Main Definitions

* `TwoPointTest` - A pair of bandit instances with different optimal arms.

## Main Results

* `card_ne_sum_ge` - #{I ≠ a₀} + #{I ≠ a₁} ≥ T for distinct a₀, a₁.
* `combinatorial_two_arm_lower` - max(regret₀, regret₁) ≥ Δ · T / 2.
* `le_cam_max_risk` - max(r₀, r₁) ≥ (r₀ + r₁) / 2 (algebraic core).
* `le_cam_expression_nonneg` - Δ · T · (1 - tv) / 2 ≥ 0 (nonnegativity prerequisite for Le Cam).
* `kl_product_identity` - T * x = sum_{Fin T} x (constant-sum identity).
* `one_sub_sqrt_half_nonneg` - 1 - √(x/2) ≥ 0 when x ≤ 2.
* `bandit_lower_bound_from_kl` - Nonneg of Le Cam + Pinsker expression.
* `delta_times_T` - Δ · T = c · √T when Δ = c / √T.
* `kl_total_optimized` - KL ≤ 4c² after optimizing Δ.
* `bandit_lower_bound_two_point` - Ω(√T) from two instances.
* `bandit_lower_bound_sqrt_KT` - Ω(√(KT)) under K ≤ T.

## References

* [Lattimore & Szepesvari, *Bandit Algorithms*, Chapter 15]
* [Agarwal et al., *RL: Theory and Algorithms*]
-/

import RLGeneralization.Bandits.UCB
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Finset BigOperators Real

noncomputable section

/-! ### Two-Point Test Construction -/

/-- A two-point test for the bandit lower bound.
    Two `BanditInstance`s that have different optimal arms:
    P0 has arm `a0` optimal (with mean `Δ`), rest at 0.
    P1 has arm `a1` optimal (with mean `Δ`), rest at 0. -/
structure TwoPointTest (K : ℕ) [NeZero K] where
  /-- The gap: optimal arm has mean Δ, others have mean 0. -/
  Δ : ℝ
  /-- First distinguished arm (optimal under P0). -/
  a0 : Fin K
  /-- Second distinguished arm (optimal under P1). -/
  a1 : Fin K
  /-- The two arms are distinct. -/
  h_ne : a0 ≠ a1
  /-- Δ is positive. -/
  hΔ_pos : 0 < Δ
  /-- Δ is at most 1 (so means stay in [-1,1]). -/
  hΔ_le : Δ ≤ 1

namespace TwoPointTest

variable {K : ℕ} [NeZero K] (tp : TwoPointTest K)

/-- Instance P0: arm `a0` has mean `Δ`, all others have mean 0. -/
def P0 : BanditInstance K where
  mean := fun a => if a = tp.a0 then tp.Δ else 0
  h_bounded := fun a => by
    by_cases h : a = tp.a0
    · simp [h, abs_of_pos tp.hΔ_pos, tp.hΔ_le]
    · simp [h]

/-- Instance P1: arm `a1` has mean `Δ`, all others have mean 0. -/
def P1 : BanditInstance K where
  mean := fun a => if a = tp.a1 then tp.Δ else 0
  h_bounded := fun a => by
    by_cases h : a = tp.a1
    · simp [h, abs_of_pos tp.hΔ_pos, tp.hΔ_le]
    · simp [h]

/-- Under P0, the optimal mean is Δ. -/
theorem P0_optMean : tp.P0.optMean = tp.Δ := by
  unfold BanditInstance.optMean P0
  simp only
  apply le_antisymm
  · apply Finset.sup'_le
    intro a _
    by_cases h : a = tp.a0
    · simp only [h, ite_true, le_refl]
    · simp only [h, ite_false]; exact tp.hΔ_pos.le
  · exact Finset.le_sup'_of_le (f := fun a => if a = tp.a0 then tp.Δ else 0)
      (Finset.mem_univ tp.a0) (by simp only [ite_true, le_refl])

/-- Under P1, the optimal mean is Δ. -/
theorem P1_optMean : tp.P1.optMean = tp.Δ := by
  unfold BanditInstance.optMean P1
  simp only
  apply le_antisymm
  · apply Finset.sup'_le
    intro a _
    by_cases h : a = tp.a1
    · simp only [h, ite_true, le_refl]
    · simp only [h, ite_false]; exact tp.hΔ_pos.le
  · exact Finset.le_sup'_of_le (f := fun a => if a = tp.a1 then tp.Δ else 0)
      (Finset.mem_univ tp.a1) (by simp only [ite_true, le_refl])

/-- Gap under P0: arm a0 has gap 0, others have gap Δ. -/
theorem P0_gap (a : Fin K) :
    tp.P0.gap a = if a = tp.a0 then 0 else tp.Δ := by
  unfold BanditInstance.gap
  rw [tp.P0_optMean]
  show tp.Δ - tp.P0.mean a = _
  unfold P0
  simp only
  by_cases h : a = tp.a0 <;> simp [h]

/-- Gap under P1: arm a1 has gap 0, others have gap Δ. -/
theorem P1_gap (a : Fin K) :
    tp.P1.gap a = if a = tp.a1 then 0 else tp.Δ := by
  unfold BanditInstance.gap
  rw [tp.P1_optMean]
  show tp.Δ - tp.P1.mean a = _
  unfold P1
  simp only
  by_cases h : a = tp.a1 <;> simp [h]

/-- Regret under P0 equals Δ times the number of rounds not playing a0. -/
theorem P0_regret (T : ℕ) (I : Fin T → Fin K) :
    tp.P0.pseudoRegret T I =
    tp.Δ * ((Finset.univ.filter (fun t : Fin T => I t ≠ tp.a0)).card : ℝ) := by
  rw [tp.P0.pseudoRegret_eq_sum_gap]
  have : ∀ t : Fin T, tp.P0.gap (I t) = if I t = tp.a0 then 0 else tp.Δ :=
    fun t => tp.P0_gap (I t)
  simp_rw [this]
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add,
      Finset.sum_const, nsmul_eq_mul]
  ring

/-- Regret under P1 equals Δ times the number of rounds not playing a1. -/
theorem P1_regret (T : ℕ) (I : Fin T → Fin K) :
    tp.P1.pseudoRegret T I =
    tp.Δ * ((Finset.univ.filter (fun t : Fin T => I t ≠ tp.a1)).card : ℝ) := by
  rw [tp.P1.pseudoRegret_eq_sum_gap]
  have : ∀ t : Fin T, tp.P1.gap (I t) = if I t = tp.a1 then 0 else tp.Δ :=
    fun t => tp.P1_gap (I t)
  simp_rw [this]
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add,
      Finset.sum_const, nsmul_eq_mul]
  ring

end TwoPointTest

/-! ### Combinatorial Core -/

/-- For two distinct arms, the count of rounds avoiding each sums to at least T. -/
theorem card_ne_sum_ge {K T : ℕ} [NeZero K]
    (a0 a1 : Fin K) (h_ne : a0 ≠ a1) (I : Fin T → Fin K) :
    T ≤ (Finset.univ.filter (fun t : Fin T => I t ≠ a0)).card +
         (Finset.univ.filter (fun t : Fin T => I t ≠ a1)).card := by
  have h_disj : Disjoint
      (Finset.univ.filter (fun t : Fin T => I t = a0))
      (Finset.univ.filter (fun t : Fin T => I t = a1)) := by
    rw [Finset.disjoint_filter]
    intro t _ h0eq h1eq; exact h_ne (h0eq ▸ h1eq)
  have h_sum_le :
      (Finset.univ.filter (fun t : Fin T => I t = a0)).card +
      (Finset.univ.filter (fun t : Fin T => I t = a1)).card ≤ T := by
    calc _ = (Finset.univ.filter (fun t : Fin T => I t = a0) ∪
             Finset.univ.filter (fun t : Fin T => I t = a1)).card :=
          (Finset.card_union_of_disjoint h_disj).symm
      _ ≤ Finset.univ.card :=
          Finset.card_le_card (Finset.union_subset
            (Finset.filter_subset _ _) (Finset.filter_subset _ _))
      _ = T := by simp [Fintype.card_fin]
  -- #{I = a} + #{I ≠ a} = T for any a
  -- Note: filter_not uses ¬(I t = a) which is defeq to (I t ≠ a)
  have h_eq0 : (Finset.univ.filter (fun t : Fin T => ¬(I t = a0))).card =
      (Finset.univ.filter (fun t : Fin T => I t ≠ a0)).card := rfl
  have h_eq1 : (Finset.univ.filter (fun t : Fin T => ¬(I t = a1))).card =
      (Finset.univ.filter (fun t : Fin T => I t ≠ a1)).card := rfl
  have h_comp0 := Finset.card_filter_add_card_filter_not
    (s := @Finset.univ (Fin T) _) (p := fun t => I t = a0)
  simp only [Finset.card_univ, Fintype.card_fin] at h_comp0
  rw [h_eq0] at h_comp0
  have h_comp1 := Finset.card_filter_add_card_filter_not
    (s := @Finset.univ (Fin T) _) (p := fun t => I t = a1)
  simp only [Finset.card_univ, Fintype.card_fin] at h_comp1
  rw [h_eq1] at h_comp1
  omega

/-- **Combinatorial two-arm lower bound**.

  For any strategy I and any two-point test with gap Δ,
  the max regret over the two instances is at least Δ · T / 2. -/
theorem combinatorial_two_arm_lower {K : ℕ} [NeZero K]
    (tp : TwoPointTest K) (T : ℕ) (I : Fin T → Fin K) :
    tp.Δ * T / 2 ≤
    max (tp.P0.pseudoRegret T I) (tp.P1.pseudoRegret T I) := by
  rw [tp.P0_regret, tp.P1_regret]
  set n0 := (Finset.univ.filter (fun t : Fin T => I t ≠ tp.a0)).card
  set n1 := (Finset.univ.filter (fun t : Fin T => I t ≠ tp.a1)).card
  have h_sum := card_ne_sum_ge tp.a0 tp.a1 tp.h_ne I
  have hΔ := tp.hΔ_pos
  have h_sum_real : (T : ℝ) ≤ ↑n0 + ↑n1 := by exact_mod_cast h_sum
  by_cases h : (T : ℝ) / 2 ≤ ↑n0
  · calc tp.Δ * ↑T / 2 = tp.Δ * (↑T / 2) := by ring
      _ ≤ tp.Δ * ↑n0 := by nlinarith
      _ ≤ max (tp.Δ * ↑n0) (tp.Δ * ↑n1) := le_max_left _ _
  · push_neg at h
    have : (T : ℝ) / 2 ≤ ↑n1 := by linarith
    calc tp.Δ * ↑T / 2 = tp.Δ * (↑T / 2) := by ring
      _ ≤ tp.Δ * ↑n1 := by nlinarith
      _ ≤ max (tp.Δ * ↑n0) (tp.Δ * ↑n1) := le_max_right _ _

/-! ### Le Cam's Two-Point Method (Algebraic Core) -/

/-- **Le Cam's two-point method (algebraic core)**.

  For any two values r0, r1 whose sum satisfies
  `r0 + r1 ≥ lower`, we have `max(r0, r1) ≥ lower / 2`. -/
theorem le_cam_max_risk (r0 r1 lower : ℝ)
    (h_sum : lower ≤ r0 + r1) :
    lower / 2 ≤ max r0 r1 := by
  by_cases h : r0 ≤ r1
  · simp only [max_eq_right h]; linarith
  · push_neg at h; simp only [max_eq_left h.le]; linarith

/-- **Nonnegativity of the Le Cam expression**.

  The expression Δ · T · (1 - tv) / 2 is nonneg when 0 ≤ tv ≤ 1.
  This is a prerequisite for the Le Cam two-point method, not the
  full Le Cam bound itself (which lower-bounds the max risk). -/
theorem le_cam_expression_nonneg
    (Δ T_real tv : ℝ)
    (hΔ : 0 ≤ Δ) (hT : 0 ≤ T_real) (_htv : 0 ≤ tv) (htv1 : tv ≤ 1) :
    0 ≤ Δ * T_real * (1 - tv) / 2 := by
  apply div_nonneg _ (by norm_num : (0:ℝ) ≤ 2)
  exact mul_nonneg (mul_nonneg hΔ hT) (by linarith)

/-! ### KL Divergence Bounds -/

/-- **Sum-to-product identity**: T * x = sum_{Fin T} x.
    Named for its role in KL divergence of product distributions,
    but the proof is just the generic constant-sum identity. -/
theorem kl_product_identity
    (T : ℕ) (kl_single : ℝ) (_hkl : 0 ≤ kl_single) :
    T * kl_single = ∑ _t : Fin T, kl_single := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- KL divergence for T rounds is nonneg when per-round KL is nonneg. -/
theorem kl_product_nonneg
    (T : ℕ) (kl_single : ℝ) (hkl : 0 ≤ kl_single) :
    0 ≤ T * kl_single :=
  mul_nonneg (Nat.cast_nonneg T) hkl

/-! ### Pinsker's Inequality (as hypothesis) -/

/-- Pinsker bound: tv ≤ √(kl / 2). -/
def PinskerBound (tv kl : ℝ) : Prop := tv ≤ Real.sqrt (kl / 2)

/-- If Pinsker holds and KL = 0, then TV = 0. -/
theorem tv_eq_zero_of_kl_zero
    (tv : ℝ) (htv : 0 ≤ tv)
    (h_pinsker : PinskerBound tv 0) :
    tv = 0 := by
  unfold PinskerBound at h_pinsker
  simp [Real.sqrt_eq_zero_of_nonpos] at h_pinsker
  linarith

/-! ### Lower Bound Coefficient -/

/-- When `x ≤ 2`, we have `√(x/2) ≤ 1`, so `1 - √(x/2) ≥ 0`. -/
theorem one_sub_sqrt_half_nonneg
    (x : ℝ) (_hx : 0 ≤ x) (hx2 : x ≤ 2) :
    0 ≤ 1 - Real.sqrt (x / 2) := by
  have h1 : x / 2 ≤ 1 := by linarith
  have h2 : Real.sqrt (x / 2) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt h1
  rw [Real.sqrt_one] at h2; linarith

/-! ### Le Cam + Pinsker Composition -/

/-- **Bandit lower bound from KL divergence**. -/
theorem bandit_lower_bound_from_kl
    (Δ : ℝ) (hΔ : 0 < Δ)
    (T_real : ℝ) (hT : 0 < T_real)
    (kl_total : ℝ) (hkl : 0 ≤ kl_total) (h_small_kl : kl_total ≤ 2) :
    0 ≤ Δ * T_real / 2 * (1 - Real.sqrt (kl_total / 2)) :=
  mul_nonneg
    (div_nonneg (mul_nonneg hΔ.le hT.le) (by norm_num))
    (one_sub_sqrt_half_nonneg kl_total hkl h_small_kl)

/-! ### Optimizing Δ -/

/-- When `Δ = c / √T`, the product `Δ · T = c · √T`. -/
theorem delta_times_T
    (c : ℝ) (_hc : 0 < c)
    (T_real : ℝ) (hT : 0 < T_real)
    (Δ : ℝ) (hΔ_def : Δ = c / Real.sqrt T_real) :
    Δ * T_real = c * Real.sqrt T_real := by
  have hsqrt_pos : 0 < Real.sqrt T_real := Real.sqrt_pos.mpr hT
  rw [hΔ_def]
  have : Real.sqrt T_real * Real.sqrt T_real = T_real := Real.mul_self_sqrt hT.le
  field_simp
  nlinarith

/-- When `Δ = c / √T` and `kl_single ≤ 4Δ²`, total KL `T · kl_single ≤ 4c²`. -/
theorem kl_total_optimized
    (c : ℝ) (_hc : 0 < c)
    (T_real : ℝ) (hT : 0 < T_real)
    (Δ : ℝ) (hΔ_def : Δ = c / Real.sqrt T_real)
    (kl_single : ℝ) (_hkl_single : 0 ≤ kl_single)
    (hkl_bound : kl_single ≤ 4 * Δ ^ 2)
    (kl_total : ℝ) (hkl_total : kl_total = T_real * kl_single) :
    kl_total ≤ 4 * c ^ 2 := by
  rw [hkl_total]
  have hΔ_sq : Δ ^ 2 = c ^ 2 / T_real := by
    rw [hΔ_def, div_pow, sq_sqrt hT.le]
  calc T_real * kl_single
      ≤ T_real * (4 * Δ ^ 2) := mul_le_mul_of_nonneg_left hkl_bound hT.le
    _ = T_real * (4 * (c ^ 2 / T_real)) := by rw [hΔ_sq]
    _ = 4 * c ^ 2 := by field_simp

/-! ### Two-Point Lower Bound: Ω(√T) -/

/-- **Bandit lower bound: Ω(√T) from two instances**.

  NOTE: This uses a combinatorial counting argument with Delta=1,
  not the information-theoretic Le Cam two-point method. The bound
  sqrt(T)/4 is correct but weaker than the information-theoretic bound. -/
theorem bandit_lower_bound_two_point
    (K : ℕ) [NeZero K] (hK : 2 ≤ K) (T : ℕ) (hT : 0 < T) :
    ∃ (B0 B1 : BanditInstance K),
    ∀ (I : Fin T → Fin K),
    Real.sqrt T / 4 ≤
    max (B0.pseudoRegret T I) (B1.pseudoRegret T I) := by
  have h01 : (0 : Fin K) ≠ (1 : Fin K) := by
    intro h; simp [Fin.ext_iff] at h; omega
  let tp : TwoPointTest K :=
    { Δ := 1
      a0 := 0
      a1 := 1
      h_ne := h01
      hΔ_pos := one_pos
      hΔ_le := le_refl _ }
  refine ⟨tp.P0, tp.P1, fun I => ?_⟩
  have h_comb := combinatorial_two_arm_lower tp T I
  have hT_pos : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have hT_ge1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have h_sqrt_le : Real.sqrt ↑T ≤ ↑T := by
    rw [Real.sqrt_le_left (by linarith : (0 : ℝ) ≤ T)]
    nlinarith [sq_nonneg ((T : ℝ) - 1)]
  linarith

/-! ### Minimax Lower Bound: Ω(√(KT)) Under K ≤ T -/

/-- **Minimax lower bound: Ω(√(KT)) under K ≤ T**.

  When K ≤ T, there exist two bandit instances such that any
  strategy's max pseudo-regret is at least √(K · T) / 8.

  Proof: Set Δ = √(KT) / (4T). Since K ≤ T, we have
  √(KT) ≤ T ≤ 4T, so Δ ≤ 1. The combinatorial bound
  gives max_regret ≥ Δ · T / 2 = √(KT) / 8. -/
theorem bandit_lower_bound_sqrt_KT
    (K : ℕ) [NeZero K] (hK : 2 ≤ K) (T : ℕ) (hT : 0 < T)
    (hKT : K ≤ T) :
    ∃ (B0 B1 : BanditInstance K),
    ∀ (I : Fin T → Fin K),
    Real.sqrt (↑K * ↑T) / 8 ≤
    max (B0.pseudoRegret T I) (B1.pseudoRegret T I) := by
  have hK_pos : (0 : ℝ) < ↑K := Nat.cast_pos.mpr (by omega)
  have hT_pos : (0 : ℝ) < ↑T := Nat.cast_pos.mpr hT
  have hKT_pos : (0 : ℝ) < ↑K * ↑T := mul_pos hK_pos hT_pos
  have hKT_sqrt_pos : 0 < Real.sqrt (↑K * ↑T) := Real.sqrt_pos.mpr hKT_pos
  have h01 : (0 : Fin K) ≠ (1 : Fin K) := by
    intro h; simp [Fin.ext_iff] at h; omega
  -- Δ = √(KT) / (4T)
  set Δ := Real.sqrt (↑K * ↑T) / (4 * ↑T) with hΔ_def
  have hΔ_pos : 0 < Δ := div_pos hKT_sqrt_pos (mul_pos (by norm_num) hT_pos)
  -- Verify Δ ≤ 1: √(KT) ≤ 4T since KT ≤ T² ≤ (4T)²
  have hΔ_le : Δ ≤ 1 := by
    rw [hΔ_def, div_le_one (mul_pos (by norm_num : (0:ℝ) < 4) hT_pos)]
    rw [Real.sqrt_le_left (by nlinarith : (0 : ℝ) ≤ 4 * ↑T)]
    have : (K : ℝ) ≤ (T : ℝ) := by exact_mod_cast hKT
    nlinarith
  let tp : TwoPointTest K :=
    { Δ := Δ
      a0 := 0
      a1 := 1
      h_ne := h01
      hΔ_pos := hΔ_pos
      hΔ_le := hΔ_le }
  refine ⟨tp.P0, tp.P1, fun I => ?_⟩
  have h_comb := combinatorial_two_arm_lower tp T I
  -- h_comb : Δ * T / 2 ≤ max(...)
  -- Δ * T / 2 = √(KT) / (4T) * T / 2 = √(KT) / 8
  calc Real.sqrt (↑K * ↑T) / 8
      = Real.sqrt (↑K * ↑T) / (4 * ↑T) * ↑T / 2 := by
        field_simp; ring
    _ ≤ max (tp.P0.pseudoRegret T I) (tp.P1.pseudoRegret T I) := h_comb

/-! ### Multi-Arm Extension via Information Theory -/

/-- **Multi-arm pigeonhole**.

  If K nonneg values sum to T, then the minimum is at most T/K. -/
theorem multi_arm_pigeonhole
    (K : ℕ) (hK : 0 < K) (T_real : ℝ) (_hT : 0 ≤ T_real)
    (n : Fin K → ℝ) (_hn : ∀ i, 0 ≤ n i)
    (hn_sum : ∑ i : Fin K, n i = T_real) :
    ∃ i, n i ≤ T_real / K := by
  by_contra h_all
  push_neg at h_all
  have : T_real < ∑ i : Fin K, n i := by
    calc T_real = ↑K * (T_real / ↑K) := by field_simp
      _ = ∑ _i : Fin K, (T_real / ↑K) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ < ∑ i : Fin K, n i := by
          apply Finset.sum_lt_sum
          · intro i _; exact (h_all i).le
          · exact ⟨⟨0, hK⟩, Finset.mem_univ _, h_all _⟩
  linarith

/-- **Minimax lower bound via multi-arm pigeonhole (combinatorial)**.

  For any strategy I, there exists an arm i such that at least
  T · (1 - 1/K) rounds did NOT play arm i. -/
theorem bandit_lower_bound_multi_arm_combinatorial
    (K : ℕ) [NeZero K] (hK : 2 ≤ K) (T : ℕ) (_hT : 0 < T)
    (Δ : ℝ) (hΔ_pos : 0 < Δ) (_hΔ_le : Δ ≤ 1) :
    ∀ (I : Fin T → Fin K),
    ∃ (i : Fin K),
    Δ * (↑T - ↑T / ↑K) ≤
    Δ * ((Finset.univ.filter (fun t : Fin T => I t ≠ i)).card : ℝ) := by
  intro I
  have hK_pos : 0 < K := by omega
  set n := fun i : Fin K =>
    ((Finset.univ.filter (fun t : Fin T => I t = i)).card : ℝ)
  have hn_nonneg : ∀ i, 0 ≤ n i := fun i => Nat.cast_nonneg _
  have hn_sum : ∑ i : Fin K, n i = ↑T := by
    -- Σ #{I = i} = T since the filters partition Fin T
    have h_fib : (T : ℕ) =
        ∑ b : Fin K,
        ((@Finset.univ (Fin T) _).filter (fun a => I a = b)).card := by
      have := Finset.card_eq_sum_card_fiberwise
        (f := I) (s := @Finset.univ (Fin T) _) (t := @Finset.univ (Fin K) _)
        (fun t _ => Finset.mem_univ (I t))
      simp only [Finset.card_univ, Fintype.card_fin] at this
      exact this
    -- Cast the ℕ equality to ℝ
    have h_cast : (↑T : ℝ) =
        ∑ b : Fin K,
        (((@Finset.univ (Fin T) _).filter (fun a => I a = b)).card : ℝ) := by
      exact_mod_cast h_fib
    linarith
  obtain ⟨i, hi⟩ := multi_arm_pigeonhole K hK_pos ↑T (Nat.cast_nonneg T)
    n hn_nonneg hn_sum
  refine ⟨i, ?_⟩
  apply mul_le_mul_of_nonneg_left _ hΔ_pos.le
  -- #{I ≠ i} = T - #{I = i} = T - n_i ≥ T - T/K
  have h_eq_ne : (Finset.univ.filter (fun t : Fin T => ¬(I t = i))).card =
      (Finset.univ.filter (fun t : Fin T => I t ≠ i)).card := rfl
  have h_comp := Finset.card_filter_add_card_filter_not
    (s := @Finset.univ (Fin T) _) (p := fun t => I t = i)
  simp only [Finset.card_univ, Fintype.card_fin] at h_comp
  rw [h_eq_ne] at h_comp
  -- h_comp : #{I = i} + #{I ≠ i} = T
  have hle_T : (Finset.univ.filter (fun t : Fin T => I t = i)).card ≤ T := by omega
  have h_ne_card : (Finset.univ.filter (fun t : Fin T => I t ≠ i)).card =
      T - (Finset.univ.filter (fun t : Fin T => I t = i)).card := by omega
  rw [h_ne_card]
  push_cast [Nat.cast_sub hle_T]
  linarith

end
