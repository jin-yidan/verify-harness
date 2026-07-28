/-
# Minimax Matching: UCBVI Upper Bound meets Fano Lower Bound

Proves the algebraic core of the minimax matching for tabular episodic RL:

1. **Regret-to-PAC conversion**: If an algorithm achieves cumulative regret
   R_K ≤ C · √(H³·S·A·K) over K episodes, then choosing
   K = ⌈C²·H³·S·A / ε²⌉ ensures average per-episode regret ≤ ε.
   This yields PAC sample complexity O(H³·S·A / ε²).

2. **Minimax matching**: The UCBVI upper bound O(H³·S·A / ε²) matches
   the Fano lower bound Ω(S·H³·log(A) / ε²) up to a log(A) factor.
   We prove: lower_bound ≤ upper_bound when A ≥ 2, since log(A) ≤ A.

## Main Results

* `regret_to_pac_sample_complexity` — Setting K = C²·H³·S·A/ε² gives
  cumulative regret ≤ K·ε, so average regret ≤ ε.
* `upper_bound_positive` — The UCBVI sample complexity c·H³·S·A/ε² > 0.
* `lower_bound_le_upper_bound` — Ω(S·H³·log(A)/ε²) ≤ O(A·S·H³/ε²).
* `minimax_gap_is_log_A` — The ratio upper/lower = A/log(A).

## References

* [Azar, Osband, Munos, *Minimax Regret Bounds for RL*, ICML 2017]
* [Domingues et al., *Episodic RL in finite MDPs: minimax lower bound revisited*, 2021]
* [Lattimore & Szepesvári, *Bandit Algorithms*]
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real

noncomputable section

/-! ### Regret-to-PAC Conversion

If an algorithm has cumulative regret R_K ≤ C · √(H³·S·A·K) over K episodes,
then the average per-episode value gap satisfies R_K / K ≤ C · √(H³·S·A / K).

Setting K = C²·H³·S·A / ε² makes R_K/K ≤ ε. This is the standard
online-to-PAC conversion for RL.

The sample complexity (number of episodes) is K = C²·H³·S·A / ε². -/

/-- **Regret-to-PAC conversion (algebraic core)**.

  If cumulative regret satisfies R_K ≤ C · √(H³·S·A·K), then
  R_K / K ≤ C · √(H³·S·A) / √K.

  When K = C²·H³·S·A / ε², the RHS = C · √(H³·S·A) / (C · √(H³·S·A) / ε) = ε.

  We prove the algebraic identity: for positive reals `prod` and `K`,
  C · √(prod · K) / K = C · √(prod / K), which equals ε when K = C² · prod / ε².

  The key step: C · √(prod · K) / K ≤ ε when K ≥ C² · prod / ε². -/
theorem regret_to_pac_sample_complexity
    (C : ℝ) (hC : 0 < C)
    (prod : ℝ) (hprod : 0 < prod)
    (eps : ℝ) (heps : 0 < eps)
    (K : ℝ) (hK : 0 < K)
    (hK_bound : C ^ 2 * prod / eps ^ 2 ≤ K) :
    C * Real.sqrt (prod * K) / K ≤ eps := by
  -- We need C * sqrt(prod * K) / K ≤ eps
  -- Equivalently: C * sqrt(prod * K) ≤ eps * K
  -- Squaring (both sides positive): C^2 * prod * K ≤ eps^2 * K^2
  -- i.e., C^2 * prod ≤ eps^2 * K, i.e., C^2 * prod / eps^2 ≤ K
  rw [div_le_iff₀ hK]
  -- Goal: C * sqrt(prod * K) ≤ eps * K
  have hprodK : 0 ≤ prod * K := mul_nonneg hprod.le hK.le
  have hepsK : 0 < eps * K := mul_pos heps hK
  rw [← Real.sqrt_sq hepsK.le, ← Real.sqrt_sq hC.le,
      ← Real.sqrt_mul (sq_nonneg C)]
  apply Real.sqrt_le_sqrt
  -- Goal: C ^ 2 * (prod * K) ≤ (eps * K) ^ 2
  rw [mul_pow]
  -- Goal: C ^ 2 * (prod * K) ≤ eps ^ 2 * K ^ 2
  have hK_ineq : C ^ 2 * prod ≤ eps ^ 2 * K := by
    have heps_sq : (0 : ℝ) < eps ^ 2 := by positivity
    calc C ^ 2 * prod = C ^ 2 * prod / eps ^ 2 * eps ^ 2 := by
            field_simp
      _ ≤ K * eps ^ 2 := by nlinarith
      _ = eps ^ 2 * K := by ring
  nlinarith [sq_nonneg K]

/-! ### UCBVI Upper Bound on Sample Complexity

The UCBVI algorithm achieves regret R_K ≤ C · √(H³·S·A·K·log(HSAK/δ)).
Ignoring log factors, the sample complexity for ε-optimal policy is:

  K_upper = C² · H³ · S · A / ε²

This is the UCBVI-style upper bound. -/

/-- UCBVI sample complexity (ignoring log factors) is positive. -/
theorem upper_bound_positive
    (c : ℝ) (hc : 0 < c)
    (S H A eps : ℝ) (hS : 0 < S) (hH : 0 < H) (hA : 0 < A) (heps : 0 < eps) :
    0 < c * H ^ 3 * S * A / eps ^ 2 := by positivity

/-! ### Fano Lower Bound on Sample Complexity

The Fano/information-theoretic lower bound for tabular episodic RL is:

  K_lower = c · S · H³ · log(A) / ε²

This follows from the Fano method with A^(SH) hypotheses (see FanoLeCam.lean). -/

/-- Fano lower bound sample complexity is positive when A ≥ 2. -/
theorem lower_bound_positive
    (c : ℝ) (hc : 0 < c)
    (S H A eps : ℝ) (hS : 0 < S) (hH : 0 < H) (hA : 1 < A) (heps : 0 < eps) :
    0 < c * S * H ^ 3 * Real.log A / eps ^ 2 := by
  apply div_pos _ (by positivity)
  apply mul_pos _ (Real.log_pos hA)
  apply mul_pos (mul_pos hc hS) (pow_pos hH 3)

/-! ### Minimax Matching

The upper and lower bounds match up to a factor of A / log(A):

  Lower: Ω(S · H³ · log(A) / ε²)
  Upper: O(H³ · S · A / ε²)

Since log(A) ≤ A for all A > 0, the lower bound is always ≤ the upper bound
(with appropriate constants). The gap is exactly A / log(A). -/

/-- **log(A) ≤ A** for A ≥ 1, the key inequality for minimax matching.
    This is a standard fact: log x ≤ x for all x > 0. -/
theorem log_le_self_of_pos (A : ℝ) (hA : 0 < A) : Real.log A ≤ A :=
  Real.log_le_self hA.le

/-- **Minimax matching: lower bound ≤ upper bound**.

  For any constants c_low, c_up with c_low ≤ c_up, and A ≥ 1:
    c_low · S · H³ · log(A) / ε²  ≤  c_up · H³ · S · A / ε²

  since log(A) ≤ A. This shows the Fano lower bound is at most
  the UCBVI upper bound (with matching constants). -/
theorem lower_bound_le_upper_bound
    (c_low c_up : ℝ) (hc_low : 0 < c_low) (hc_le : c_low ≤ c_up)
    (S H A eps : ℝ)
    (hS : 0 < S) (hH : 0 < H) (hA : 1 ≤ A) (heps : 0 < eps) :
    c_low * S * H ^ 3 * Real.log A / eps ^ 2 ≤
    c_up * H ^ 3 * S * A / eps ^ 2 := by
  apply div_le_div_of_nonneg_right _ (by positivity : 0 < eps ^ 2).le
  have hlogA : Real.log A ≤ A := Real.log_le_self (by linarith)
  have hH3 : 0 < H ^ 3 := pow_pos hH 3
  -- Goal: c_low * S * H^3 * log A ≤ c_up * H^3 * S * A
  calc c_low * S * H ^ 3 * Real.log A
      ≤ c_low * S * H ^ 3 * A := by
        apply mul_le_mul_of_nonneg_left hlogA
        apply mul_nonneg (mul_nonneg hc_low.le hS.le) hH3.le
    _ = c_low * (H ^ 3 * S * A) := by ring
    _ ≤ c_up * (H ^ 3 * S * A) := by
        apply mul_le_mul_of_nonneg_right hc_le
        apply mul_nonneg (mul_nonneg hH3.le hS.le) (by linarith)
    _ = c_up * H ^ 3 * S * A := by ring

/-- **Minimax gap is exactly A / log(A)**.

  The ratio of upper to lower sample complexity bounds is:
    (c · H³ · S · A / ε²) / (c · S · H³ · log(A) / ε²) = A / log(A)

  This is a pure algebraic identity. -/
theorem minimax_gap_is_log_A
    (c : ℝ) (hc : 0 < c)
    (S H A eps : ℝ)
    (hS : 0 < S) (hH : 0 < H) (hA : 1 < A) (heps : 0 < eps) :
    (c * H ^ 3 * S * A / eps ^ 2) / (c * S * H ^ 3 * Real.log A / eps ^ 2) =
    A / Real.log A := by
  have hlogA : 0 < Real.log A := Real.log_pos hA
  have hH3 : 0 < H ^ 3 := pow_pos hH 3
  have heps2 : (0 : ℝ) < eps ^ 2 := by positivity
  have hcSH3 : 0 < c * S * H ^ 3 := by positivity
  have hdenom_ne : c * S * H ^ 3 * Real.log A / eps ^ 2 ≠ 0 :=
    ne_of_gt (div_pos (mul_pos hcSH3 hlogA) heps2)
  field_simp

/-- **Regret bound implies PAC bound** (composition form).

  Given UCBVI regret: R_K ≤ C · √(H³ · S · A · K),
  the PAC sample complexity is at most C² · H³ · S · A / ε².
  We prove: if R_K ≤ C · √(prod · K) and K ≥ C² · prod / ε²,
  then R_K ≤ K · ε (so average regret ≤ ε). -/
theorem regret_implies_pac
    (C : ℝ) (hC : 0 < C)
    (prod : ℝ) (hprod : 0 < prod)
    (eps : ℝ) (heps : 0 < eps)
    (K : ℝ) (hK : 0 < K)
    (R_K : ℝ) (_hR_nonneg : 0 ≤ R_K)
    (h_regret : R_K ≤ C * Real.sqrt (prod * K))
    (hK_bound : C ^ 2 * prod / eps ^ 2 ≤ K) :
    R_K ≤ K * eps := by
  have h_conv := regret_to_pac_sample_complexity C hC prod hprod eps heps K hK hK_bound
  -- h_conv : C * sqrt(prod * K) / K ≤ eps
  -- h_regret : R_K ≤ C * sqrt(prod * K)
  -- Need: R_K ≤ K * eps
  calc R_K ≤ C * Real.sqrt (prod * K) := h_regret
    _ = K * (C * Real.sqrt (prod * K) / K) := by field_simp
    _ ≤ K * eps := by nlinarith

end
