/-
# Law of Total Variance (General Finite Form)

Proves the law of total variance for finite-type conditioning:

  Var[X] = E[Var[X|Y]] + Var[E[X|Y]]

The existing `total_variance_bound` in VarianceUCBVI.lean is specific
to the UCBVI setting (Var_P(V) ≤ H·E_P[V] for V ∈ [0,H]). This module
provides the general identity for arbitrary finite type conditioning.

## Main Results

* `law_of_total_variance` — Var[X] = E[Var[X|Y]] + Var[E[X|Y]]
* `law_of_total_variance_bound` — Var[X] ≥ Var[E[X|Y]]
  (the "explained variance" is at most total variance)

## References

* [Boucheron et al., *Concentration Inequalities*, §3.1]
* [Casella & Berger, *Statistical Inference*, Theorem 4.4.7]
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset BigOperators

noncomputable section

variable {S Y : Type*} [Fintype S] [Fintype Y] [DecidableEq Y]

/-! ### Setup

We work with a joint distribution over S × Y, represented as:
- P : S × Y → ℝ is the joint weight function (nonneg, sums to 1)
- Marginalization over Y gives P_S(s) = ∑_y P(s,y)
- Conditional E[X|Y=y] = ∑_s X(s) · P(s|Y=y)

For simplicity, we use the algebraic identity directly:
  Var = E[X²] - (E[X])²
  E[Var[X|Y]] = E[E[X²|Y]] - E[(E[X|Y])²]
  Var[E[X|Y]] = E[(E[X|Y])²] - (E[E[X|Y]])²
  Sum = E[E[X²|Y]] - (E[X])² = E[X²] - (E[X])² = Var[X]

where E[E[X²|Y]] = E[X²] and E[E[X|Y]] = E[X] (tower property).
-/

/-! ### Direct Algebraic Form

Instead of joint distributions, we use the cleanest algebraic form:
given a partition of a weighted sum into groups, the total variance
decomposes into within-group and between-group variance. -/

/-- **Law of total variance** (partition form).

Given weights w : Y → ℝ with ∑w = 1 (marginal over Y),
conditional means μ : Y → ℝ (μ(y) = E[X|Y=y]),
conditional second moments m₂ : Y → ℝ (m₂(y) = E[X²|Y=y]),
and the tower property holding:
  E[X] = ∑ w(y)·μ(y)
  E[X²] = ∑ w(y)·m₂(y)

Then: Var[X] = E[Var[X|Y]] + Var[E[X|Y]], i.e.,
  (∑ w·m₂ - (∑ w·μ)²) = (∑ w·(m₂ - μ²)) + (∑ w·μ² - (∑ w·μ)²) -/
theorem law_of_total_variance
    (w : Y → ℝ) (μ m₂ : Y → ℝ)
    (hw_nonneg : ∀ y, 0 ≤ w y) (hw_sum : ∑ y, w y = 1) :
    -- Total variance
    (∑ y, w y * m₂ y) - (∑ y, w y * μ y) ^ 2 =
    -- E[Var[X|Y]] = ∑ w(y)·(m₂(y) - μ(y)²)
    (∑ y, w y * (m₂ y - μ y ^ 2)) +
    -- Var[E[X|Y]] = ∑ w(y)·μ(y)² - (∑ w(y)·μ(y))²
    ((∑ y, w y * μ y ^ 2) - (∑ y, w y * μ y) ^ 2) := by
  -- Pure algebra: LHS = ∑w·m₂ - (∑wμ)²
  -- RHS = ∑w·m₂ - ∑w·μ² + ∑w·μ² - (∑wμ)² = ∑w·m₂ - (∑wμ)²
  have : ∀ y, w y * (m₂ y - μ y ^ 2) = w y * m₂ y - w y * μ y ^ 2 := fun y => mul_sub _ _ _
  simp_rw [this]
  rw [Finset.sum_sub_distrib]
  ring

/-- **Variance decomposition bound**: Var[E[X|Y]] ≤ Var[X].

The "explained variance" by conditioning on Y cannot exceed the
total variance. Equivalently: E[Var[X|Y]] ≥ 0. -/
theorem law_of_total_variance_bound
    (w : Y → ℝ) (μ m₂ : Y → ℝ)
    (hw_nonneg : ∀ y, 0 ≤ w y) (hw_sum : ∑ y, w y = 1)
    (hm₂_ge : ∀ y, μ y ^ 2 ≤ m₂ y) :
    (∑ y, w y * μ y ^ 2) - (∑ y, w y * μ y) ^ 2 ≤
    (∑ y, w y * m₂ y) - (∑ y, w y * μ y) ^ 2 := by
  -- Follows from m₂(y) ≥ μ(y)² (Jensen: E[X²|Y] ≥ (E[X|Y])²)
  linarith [Finset.sum_le_sum fun y (_ : y ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hm₂_ge y) (hw_nonneg y)]

/-- E[Var[X|Y]] ≥ 0 (conditional variance is nonneg on average). -/
theorem expected_conditional_variance_nonneg
    (w : Y → ℝ) (μ m₂ : Y → ℝ)
    (hw_nonneg : ∀ y, 0 ≤ w y)
    (hm₂_ge : ∀ y, μ y ^ 2 ≤ m₂ y) :
    0 ≤ ∑ y, w y * (m₂ y - μ y ^ 2) :=
  Finset.sum_nonneg fun y _ =>
    mul_nonneg (hw_nonneg y) (by linarith [hm₂_ge y])

end
