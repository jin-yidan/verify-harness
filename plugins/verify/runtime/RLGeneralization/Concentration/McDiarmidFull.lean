/-
# McDiarmid Variance Bound and Chebyshev Tail

This file proves the McDiarmid variance bound and Chebyshev-type tail
bound for functions of independent random variables with bounded
differences, building on:

1. **Efron-Stein** (SLT): `Var(f) ≤ ∑ᵢ E[(f - E^{(i)}f)²]`
2. **condDev_le_of_bounded_diff** (McDiarmid.lean): `|f(x) - E^{(i)}f(x)| ≤ cᵢ`
3. **Chebyshev** (Mathlib): `P(|X - E[X]| ≥ ε) ≤ Var(X)/ε²`

## Main results

* `mcdiarmid_variance_bound`: `Var(f) ≤ ∑ᵢ cᵢ²` (totalSensitivity)
* `mcdiarmid_chebyshev_tail`: `P(|f(X) - E[f]| ≥ ε) ≤ ∑cᵢ²/ε²`

## Proof chain

**Step 1** (variance bound): Efron-Stein gives `Var(f) ≤ ∑ᵢ E[(f - E^{(i)}f)²]`.
The pointwise bound `|f(x) - E^{(i)}f(x)| ≤ cᵢ` implies `(f(x) - E^{(i)}f(x))² ≤ cᵢ²`
pointwise. Integrating over the product space (a probability measure) gives
`E[(f - E^{(i)}f)²] ≤ cᵢ²`. Summing yields `Var(f) ≤ ∑ cᵢ²`.

**Step 2** (Chebyshev tail): By Chebyshev's inequality
(`meas_ge_le_variance_div_sq` from Mathlib),
`P(|f(X) - E[f]| ≥ ε) ≤ Var(f)/ε²`. Combined with Step 1, this gives the
polynomial tail bound `P(|f(X) - E[f]| ≥ ε) ≤ ∑cᵢ²/ε²`.

**Note**: The full exponential McDiarmid bound `exp(-2ε²/∑cᵢ²)` requires a
martingale filtration construction (Doob decomposition + Azuma-Hoeffding),
which is not proved here. The Chebyshev tail is weaker (polynomial vs
exponential) but is fully proved from existing infrastructure.

## References

* [Boucheron et al., *Concentration Inequalities*, Ch 3 & 6]
* [McDiarmid, *On the method of bounded differences*, 1989]
-/

import RLGeneralization.Concentration.McDiarmid
import Mathlib.Probability.Moments.Variance

open MeasureTheory ProbabilityTheory Real Finset BigOperators

noncomputable section

/-! ### Pointwise squared bound from bounded differences

The key algebraic step: if `|D(x)| ≤ c` pointwise, then `D(x)² ≤ c²`
pointwise. When `D(x) = f(x) - E^{(i)}f(x)` and `c = cᵢ`, integrating
over a probability measure gives `E[D²] ≤ cᵢ²`. -/

section VarianceBound

set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

variable {n : ℕ} {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
  [DiscreteMeasurableSpace Ω]
  {μs : Fin n → MeasureTheory.Measure Ω}
  [∀ i, MeasureTheory.IsProbabilityMeasure (μs i)]

local notation "μˢ" => MeasureTheory.Measure.pi μs

/-- If `|g(x)| ≤ c` for all `x`, then `∫ g(x)² dμ ≤ c²` for a
    probability measure `μ`. This is the key step connecting pointwise
    bounds to integral bounds. -/
theorem integral_sq_le_of_abs_le
    {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} [IsProbabilityMeasure μ]
    (g : α → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (h_bound : ∀ x, |g x| ≤ c) :
    ∫ x, g x ^ 2 ∂μ ≤ c ^ 2 := by
  calc ∫ x, g x ^ 2 ∂μ
      ≤ ∫ _x, c ^ 2 ∂μ := by
        apply MeasureTheory.integral_mono_of_nonneg
        · filter_upwards with x; exact sq_nonneg (g x)
        · exact MeasureTheory.integrable_const _
        · filter_upwards with x
          have habs := h_bound x
          nlinarith [sq_abs (g x), sq_abs c, sq_nonneg (g x), abs_nonneg (g x)]
    _ = c ^ 2 := by
        rw [MeasureTheory.integral_const]; simp

/-- **McDiarmid variance bound**: For a function `f` of `n` independent
    random variables, if `f` satisfies the bounded differences condition
    with constants `cᵢ` (i.e., changing coordinate `i` changes `f` by at
    most `cᵢ`), then `Var(f) ≤ ∑ᵢ cᵢ²`.

    Proof: Efron-Stein gives `Var(f) ≤ ∑ᵢ E[(f - E^{(i)}f)²]`.
    The bounded differences condition gives `|f(x) - E^{(i)}f(x)| ≤ cᵢ`
    pointwise (via `condDev_le_of_bounded_diff`), so `E[(f - E^{(i)}f)²] ≤ cᵢ²`.
    Summing yields `Var(f) ≤ ∑ᵢ cᵢ²`. -/
theorem mcdiarmid_variance_bound
    (f : (Fin n → Ω) → ℝ)
    (bd : BoundedDifferences n)
    (h_bd : ∀ i, ∀ x y : Fin n → Ω, (∀ j, j ≠ i → x j = y j) →
      |f x - f y| ≤ bd.bounds i) :
    ProbabilityTheory.variance f μˢ ≤ bd.totalSensitivity := by
  have hf : MeasureTheory.MemLp f 2 μˢ := MemLp.of_discrete
  calc ProbabilityTheory.variance f μˢ
      ≤ ∑ i : Fin n,
          ∫ x, (f x - condExpExceptCoord (μs := μs) i f x) ^ 2 ∂μˢ :=
        efron_stein_for_product f hf
    _ ≤ ∑ i : Fin n, bd.bounds i ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        apply integral_sq_le_of_abs_le _ (bd.bounds i) (bd.bounds_nonneg i)
        intro x
        exact condDev_le_of_bounded_diff f i (bd.bounds i) (bd.bounds_nonneg i)
          (h_bd i) x
    _ = bd.totalSensitivity := rfl

/-! ### Chebyshev tail bound from variance bound

Combining the McDiarmid variance bound with Chebyshev's inequality gives
a polynomial tail bound. While weaker than the exponential McDiarmid bound,
this is a genuine probability inequality proved entirely from existing
infrastructure. -/

/-- **McDiarmid-Chebyshev tail bound**: For a function `f` of `n` independent
    random variables satisfying the bounded differences condition with
    constants `cᵢ`:

      `P(|f(X) - E[f]| ≥ ε) ≤ ∑cᵢ² / ε²`

    This is a polynomial (Chebyshev-type) tail bound. It is weaker than the
    exponential McDiarmid bound `exp(-2ε²/∑cᵢ²)` but is fully proved from:
    - Efron-Stein inequality (SLT)
    - Bounded conditional deviations (McDiarmid.lean)
    - Chebyshev's inequality (Mathlib) -/
theorem mcdiarmid_chebyshev_tail
    (f : (Fin n → Ω) → ℝ)
    (bd : BoundedDifferences n)
    (h_bd : ∀ i, ∀ x y : Fin n → Ω, (∀ j, j ≠ i → x j = y j) →
      |f x - f y| ≤ bd.bounds i)
    {ε : ℝ} (hε : 0 < ε) :
    μˢ {ω | ε ≤ |f ω - μˢ[f]|} ≤
      ENNReal.ofReal (bd.totalSensitivity / ε ^ 2) := by
  have hf : MeasureTheory.MemLp f 2 μˢ := MemLp.of_discrete
  calc μˢ {ω | ε ≤ |f ω - μˢ[f]|}
      ≤ ENNReal.ofReal (ProbabilityTheory.variance f μˢ / ε ^ 2) :=
        meas_ge_le_variance_div_sq hf hε
    _ ≤ ENNReal.ofReal (bd.totalSensitivity / ε ^ 2) := by
        apply ENNReal.ofReal_le_ofReal
        apply div_le_div_of_nonneg_right
          (mcdiarmid_variance_bound f bd h_bd)
          (sq_nonneg ε)

/-- **Corollary for uniform bounded differences**: When all `n` coordinates
    have the same bound `c`, the Chebyshev tail becomes
    `P(|f(X) - E[f]| ≥ ε) ≤ n * c² / ε²`. -/
theorem mcdiarmid_chebyshev_tail_uniform
    (f : (Fin n → Ω) → ℝ)
    (c : ℝ) (hc : 0 ≤ c)
    (h_bd : ∀ i, ∀ x y : Fin n → Ω, (∀ j, j ≠ i → x j = y j) →
      |f x - f y| ≤ c)
    {ε : ℝ} (hε : 0 < ε) :
    μˢ {ω | ε ≤ |f ω - μˢ[f]|} ≤
      ENNReal.ofReal (n * c ^ 2 / ε ^ 2) := by
  have h := @mcdiarmid_chebyshev_tail n Ω _ _ _ μs _ f (uniformBD n c hc)
    (fun i => h_bd i) ε hε
  rwa [uniformBD_totalSensitivity] at h

/-- **Variance bound for uniform bounded differences**: When all `n`
    coordinates have the same bound `c`, `Var(f) ≤ n * c²`. -/
theorem mcdiarmid_variance_bound_uniform
    (f : (Fin n → Ω) → ℝ)
    (c : ℝ) (hc : 0 ≤ c)
    (h_bd : ∀ i, ∀ x y : Fin n → Ω, (∀ j, j ≠ i → x j = y j) →
      |f x - f y| ≤ c) :
    ProbabilityTheory.variance f μˢ ≤ n * c ^ 2 := by
  have h := @mcdiarmid_variance_bound n Ω _ _ _ μs _ f (uniformBD n c hc)
    (fun i => h_bd i)
  rwa [uniformBD_totalSensitivity] at h

/-- The McDiarmid-Chebyshev tail event has probability at most 1. This is
    the expected sanity check for any probability bound. -/
theorem mcdiarmid_chebyshev_tail_le_one
    (f : (Fin n → Ω) → ℝ)
    (bd : BoundedDifferences n)
    (_h_bd : ∀ i, ∀ x y : Fin n → Ω, (∀ j, j ≠ i → x j = y j) →
      |f x - f y| ≤ bd.bounds i)
    {ε : ℝ} :
    μˢ {ω | ε ≤ |f ω - μˢ[f]|} ≤ 1 := by
  exact prob_le_one

end VarianceBound

/-! ### Discussion: exponential vs polynomial tail bounds

The Chebyshev-based tail bound proved above gives:

  P(|f(X) - E[f]| ≥ ε) ≤ ∑cᵢ²/ε²

This is a *polynomial* decay in ε. The full McDiarmid inequality gives the
*exponential* tail bound:

  P(|f(X) - E[f]| ≥ ε) ≤ exp(-2ε²/∑cᵢ²)

The exponential bound is much tighter for large ε. To prove it, one needs:

1. **Doob martingale construction**: Define Mₖ = E[f | X₁,...,Xₖ] and show
   the differences Dₖ = Mₖ - Mₖ₋₁ satisfy |Dₖ| ≤ cₖ.
2. **Azuma-Hoeffding**: Apply the Azuma-Hoeffding inequality to the
   martingale (M₀, M₁, ..., Mₙ) with bounded differences.

The algebraic exponent and confidence-width results for the exponential
bound are proved in `McDiarmid.lean`. The missing piece is the measure-
theoretic construction of the Doob martingale and verification that it
satisfies the Azuma-Hoeffding hypotheses.

The polynomial Chebyshev tail bound proved here suffices for applications
where one only needs P(...) → 0 as n → ∞ (e.g., consistency results),
while the exponential bound is needed for finite-sample PAC-style
guarantees with explicit constants. -/

end
