/-
# Self-Bounding Variance-Regret Argument

Formalizes the self-bounding technique used in variance-aware and
horizon-free RL analyses. The key pattern:

  If Regret ≤ C·√V and V ≤ a·Regret + b, then Regret ≤ C²a + C√b.

This eliminates the variance term V by substituting and solving
the resulting quadratic inequality.

## Main Results

* `self_bounding_quadratic` — the basic quadratic resolution
* `self_bounding_regret` — the standard variance-regret form

## References

* [Zanette et al., "Frequentist Regret Bounds for Randomized RL," AISTATS 2020]
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Real

noncomputable section

/-! ### Core Quadratic Resolution

Given R ≤ C·√V and V ≤ a·R + b with R, C, a, b ≥ 0:

1. R² ≤ C²·V ≤ C²·(a·R + b) = C²aR + C²b
2. R² - C²aR ≤ C²b
3. (R - C²a/2)² ≤ C²b + (C²a)²/4
4. R ≤ C²a/2 + √(C²b + C⁴a²/4)
5. Using √(x+y) ≤ √x + √y:  R ≤ C²a/2 + C√b + C²a/2 = C²a + C√b
-/

/-- **Quadratic self-bounding**: if R ≤ C√V and V ≤ aR + b, then R ≤ C²a + C√b.

This is the core lemma used in horizon-free and variance-aware RL analyses
to convert a regret bound involving the (unknown) total variance into a
variance-free bound. -/
theorem self_bounding_regret
    (R C V a b : ℝ)
    (hR_nonneg : 0 ≤ R)
    (hC_nonneg : 0 ≤ C)
    (ha_nonneg : 0 ≤ a)
    (hb_nonneg : 0 ≤ b)
    (hV_nonneg : 0 ≤ V)
    (h_regret : R ≤ C * √V)
    (h_var : V ≤ a * R + b) :
    R ≤ C ^ 2 * a + C * √b := by
  have hR_sq : R ^ 2 ≤ C ^ 2 * a * R + C ^ 2 * b := by
    calc R ^ 2 ≤ (C * √V) ^ 2 := sq_le_sq' (by linarith) h_regret
      _ = C ^ 2 * V := by rw [mul_pow, sq_sqrt hV_nonneg]
      _ ≤ C ^ 2 * (a * R + b) := by nlinarith [sq_nonneg C]
      _ = C ^ 2 * a * R + C ^ 2 * b := by ring
  by_cases h : R ≤ C ^ 2 * a
  · linarith [mul_nonneg hC_nonneg (sqrt_nonneg b)]
  · push_neg at h
    have h3 : 0 ≤ R - C ^ 2 * a := by linarith
    have h4 : 0 ≤ C * √b := mul_nonneg hC_nonneg (sqrt_nonneg b)
    have h_sq_bound : (R - C ^ 2 * a) ^ 2 ≤ (C * √b) ^ 2 := by
      rw [mul_pow, sq_sqrt hb_nonneg]
      nlinarith [mul_nonneg (mul_nonneg (sq_nonneg C) ha_nonneg) h3]
    calc R = (R - C ^ 2 * a) + C ^ 2 * a := by ring
      _ ≤ C * √b + C ^ 2 * a := by
          gcongr
          calc R - C ^ 2 * a
              = √((R - C ^ 2 * a) ^ 2) := (Real.sqrt_sq h3).symm
            _ ≤ √((C * √b) ^ 2) := Real.sqrt_le_sqrt h_sq_bound
            _ = C * √b := Real.sqrt_sq h4
      _ = C ^ 2 * a + C * √b := by ring

/-- **Self-bounding with explicit quadratic**: intermediate form showing
R² - C²aR ≤ C²b directly, useful for deriving tighter constants. -/
theorem self_bounding_quadratic
    (R C V a b : ℝ)
    (hR_nonneg : 0 ≤ R)
    (hC_nonneg : 0 ≤ C)
    (hV_nonneg : 0 ≤ V)
    (h_regret : R ≤ C * √V)
    (h_var : V ≤ a * R + b) :
    R ^ 2 ≤ C ^ 2 * a * R + C ^ 2 * b := by
  calc R ^ 2 ≤ (C * √V) ^ 2 := sq_le_sq' (by linarith) h_regret
    _ = C ^ 2 * V := by rw [mul_pow, sq_sqrt hV_nonneg]
    _ ≤ C ^ 2 * (a * R + b) := by nlinarith [sq_nonneg C]
    _ = C ^ 2 * a * R + C ^ 2 * b := by ring

/-- Variant with O-notation-style: if R ≤ C√(aR+b), then R ≤ C²a + C√b.
This is the form where the variance bound is substituted into the
regret bound directly. -/
theorem self_bounding_sqrt
    (R C a b : ℝ)
    (hR_nonneg : 0 ≤ R)
    (hC_nonneg : 0 ≤ C)
    (ha_nonneg : 0 ≤ a)
    (hb_nonneg : 0 ≤ b)
    (h_bound : R ≤ C * √(a * R + b)) :
    R ≤ C ^ 2 * a + C * √b :=
  self_bounding_regret R C (a * R + b) a b hR_nonneg hC_nonneg
    ha_nonneg hb_nonneg (by nlinarith) h_bound (le_refl _)

end
