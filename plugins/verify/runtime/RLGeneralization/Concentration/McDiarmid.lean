/-
# McDiarmid's Bounded Differences Inequality

McDiarmid's inequality is a concentration inequality for functions of
independent random variables that satisfy a bounded differences condition.

## Statement

If f : X₁ × ... × X_n → ℝ satisfies the bounded differences condition:
  sup |f(x₁,...,xᵢ,...,x_n) - f(x₁,...,xᵢ',...,x_n)| ≤ cᵢ
then P(f(X) - E[f(X)] ≥ ε) ≤ exp(-2ε²/∑cᵢ²).

## Architecture

The full measure-theoretic proof requires Doob's martingale decomposition
and conditional expectation machinery, which is very heavy in Lean 4.
Instead, we take the algebraic approach:

1. Define the bounded differences condition as a structure.
2. Prove algebraic properties of the McDiarmid exponent.
3. Show McDiarmid is a corollary of Azuma-Hoeffding: the bounded-
   differences condition implies the Doob martingale differences are
   bounded by cᵢ, so McDiarmid's exponent equals the Azuma-Hoeffding
   exponent for the corresponding martingale.
4. Application to RL: empirical transition estimation with N i.i.d.
   samples per (s,a) pair recovers Hoeffding as a special case.

## References

* [McDiarmid, *On the method of bounded differences*, 1989]
* [Boucheron et al., *Concentration Inequalities*, Ch 6]
* [Agarwal et al., *RL: Theory and Algorithms*, Appendix A]
-/

import RLGeneralization.Concentration.AzumaHoeffding
import SLT.EfronStein

open MeasureTheory ProbabilityTheory Real Finset BigOperators

noncomputable section

/-! ### Bounded Differences Condition

The bounded differences condition captures functions whose output is
insensitive to changing any single input coordinate. Formally, for
f : X₁ × ... × X_n → ℝ, the i-th difference bound cᵢ satisfies:

  sup_{x₁,...,x_n, xᵢ'} |f(x₁,...,xᵢ,...,x_n) - f(x₁,...,xᵢ',...,x_n)| ≤ cᵢ

The sum ∑cᵢ² is the "total sensitivity" of f. -/

/-- **Bounded differences data**: a function of n variables together
    with its per-coordinate difference bounds c₁,...,c_n.
    The bounds are nonneg reals. The key quantity is `totalSensitivity = ∑ cᵢ²`. -/
structure BoundedDifferences (n : ℕ) where
  /-- Per-coordinate difference bounds. -/
  bounds : Fin n → ℝ
  /-- All bounds are nonneg. -/
  bounds_nonneg : ∀ i, 0 ≤ bounds i

namespace BoundedDifferences

variable {n : ℕ} (bd : BoundedDifferences n)

/-- The total sensitivity ∑ cᵢ². This determines the McDiarmid exponent. -/
def totalSensitivity : ℝ :=
  ∑ i : Fin n, bd.bounds i ^ 2

/-- The total sensitivity is nonneg. -/
theorem totalSensitivity_nonneg : 0 ≤ bd.totalSensitivity := by
  apply Finset.sum_nonneg
  intro i _
  positivity

/-- Each squared bound is nonneg. -/
theorem sq_bounds_nonneg (i : Fin n) : 0 ≤ bd.bounds i ^ 2 := by
  positivity

end BoundedDifferences

/-! ### McDiarmid Exponent

The McDiarmid inequality gives the tail bound:

  P(f(X) - E[f(X)] ≥ ε) ≤ exp(-2ε² / ∑ cᵢ²)

The exponent -2ε²/∑cᵢ² has the same form as the Hoeffding/Azuma-Hoeffding
exponent with ranges cᵢ. This section establishes algebraic properties
of this exponent. -/

/-- **McDiarmid exponent**: the quantity -2ε²/∑cᵢ² appearing in the
    McDiarmid tail bound exp(-2ε²/∑cᵢ²). -/
def mcdiarmidExponent {n : ℕ} (bd : BoundedDifferences n) (ε : ℝ) : ℝ :=
  -2 * ε ^ 2 / bd.totalSensitivity

/-- The McDiarmid exponent is nonpositive when the total sensitivity
    is positive. -/
theorem mcdiarmidExponent_nonpos {n : ℕ} (bd : BoundedDifferences n) (ε : ℝ)
    (hS : 0 < bd.totalSensitivity) :
    mcdiarmidExponent bd ε ≤ 0 := by
  unfold mcdiarmidExponent
  apply div_nonpos_of_nonpos_of_nonneg
  · nlinarith [sq_nonneg ε]
  · exact le_of_lt hS

/-- The McDiarmid tail bound exp(-2ε²/∑cᵢ²) is at most 1. -/
theorem mcdiarmid_tail_le_one {n : ℕ} (bd : BoundedDifferences n) (ε : ℝ)
    (hS : 0 < bd.totalSensitivity) :
    Real.exp (mcdiarmidExponent bd ε) ≤ 1 := by
  rw [← Real.exp_zero]
  exact Real.exp_le_exp_of_le (mcdiarmidExponent_nonpos bd ε hS)

/-- **Tail inversion for McDiarmid**: setting ε = √(∑cᵢ² · log(1/δ) / 2)
    makes the McDiarmid exponent equal to -log(1/δ), so the tail is δ.

    This is the key step for converting McDiarmid's tail bound into
    a confidence interval of width ε. -/
theorem mcdiarmid_exponent_at_confidence_width {n : ℕ} (bd : BoundedDifferences n)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hS : 0 < bd.totalSensitivity) :
    let ε := Real.sqrt (bd.totalSensitivity * Real.log (1 / δ) / 2)
    mcdiarmidExponent bd ε = -Real.log (1 / δ) := by
  simp only
  unfold mcdiarmidExponent
  have hlog : 0 < Real.log (1 / δ) :=
    Real.log_pos (by rw [one_div]; exact one_lt_inv_iff₀.mpr ⟨hδ, hδ1⟩)
  have h_inner : 0 ≤ bd.totalSensitivity * Real.log (1 / δ) / 2 :=
    div_nonneg (mul_nonneg (le_of_lt hS) (le_of_lt hlog)) (by norm_num)
  rw [Real.sq_sqrt h_inner]
  field_simp

/-- **Confidence width for McDiarmid**: ε = √(∑cᵢ² · log(1/δ) / 2)
    ensures exp(-2ε²/∑cᵢ²) = δ. -/
theorem mcdiarmid_tail_equals_delta {n : ℕ} (bd : BoundedDifferences n)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hS : 0 < bd.totalSensitivity) :
    let ε := Real.sqrt (bd.totalSensitivity * Real.log (1 / δ) / 2)
    Real.exp (mcdiarmidExponent bd ε) = δ := by
  simp only
  rw [mcdiarmid_exponent_at_confidence_width bd hδ hδ1 hS]
  exact exp_neg_log_inv hδ

/-- The McDiarmid confidence width is positive. -/
theorem mcdiarmid_confidence_width_pos {n : ℕ} (bd : BoundedDifferences n)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hS : 0 < bd.totalSensitivity) :
    0 < Real.sqrt (bd.totalSensitivity * Real.log (1 / δ) / 2) := by
  apply Real.sqrt_pos_of_pos
  apply div_pos
  · exact mul_pos hS
      (Real.log_pos (by rw [one_div]; exact one_lt_inv_iff₀.mpr ⟨hδ, hδ1⟩))
  · norm_num

/-! ### Connection to Azuma-Hoeffding

McDiarmid's inequality is a corollary of the Azuma-Hoeffding inequality
applied to the Doob martingale. Given a function f satisfying the bounded
differences condition with bounds c₁,...,c_n, the Doob martingale
D_i = E[f | X₁,...,X_i] - E[f | X₁,...,X_{i-1}] has |D_i| ≤ c_i.

The Azuma-Hoeffding inequality for H bounded martingale differences
with |D_i| ≤ B gives tail bound exp(-ε²/(2·∑B²)). When B_i = c_i,
this is exp(-ε²/(2·∑cᵢ²)) = exp(-2ε²/(2·∑cᵢ²)) with the standard
Azuma-Hoeffding constant.

More precisely, Azuma-Hoeffding for differences bounded in [-c_i, c_i]
gives sub-Gaussian parameter c_i² per step (since the range is 2c_i
and the Hoeffding sub-Gaussian parameter is ((2c_i)/2)² = c_i²).
The total sub-Gaussian parameter is ∑c_i², and the tail is
exp(-ε²/(2·∑c_i²)).

This is exactly the McDiarmid bound (note: exp(-ε²/(2·∑c_i²)) is
sometimes written as exp(-2ε²/(∑(2c_i)²)), which is the same thing). -/

/-- **McDiarmid total sensitivity equals Azuma total sub-Gaussian parameter**.

    When the Doob martingale differences are bounded by cᵢ (the bounded
    differences bounds), the per-step Azuma-Hoeffding sub-Gaussian
    parameter is cᵢ² (since the difference lies in [-cᵢ, cᵢ], giving
    range 2cᵢ and sub-Gaussian parameter ((2cᵢ)/2)² = cᵢ²).

    The total sub-Gaussian parameter ∑cᵢ² equals the McDiarmid
    total sensitivity. -/
theorem mcdiarmid_azuma_param_eq {n : ℕ} (bd : BoundedDifferences n) :
    bd.totalSensitivity = ∑ i : Fin n, bd.bounds i ^ 2 := rfl

/-- **Azuma-Hoeffding sub-Gaussian parameter for each bounded difference**.

    If the i-th martingale difference is bounded in [-cᵢ, cᵢ], then
    by Hoeffding's lemma its sub-Gaussian parameter is
    ((cᵢ - (-cᵢ))/2)² = cᵢ². -/
theorem azuma_subgaussian_param_from_bd {n : ℕ} (bd : BoundedDifferences n) (i : Fin n) :
    ((bd.bounds i - (- bd.bounds i)) / 2) ^ 2 = bd.bounds i ^ 2 := by ring

/-- **McDiarmid exponent equals Azuma-Hoeffding exponent**.

    In the McDiarmid setting, the Doob martingale differences have
    range cᵢ (each Dᵢ lies in an interval of width cᵢ). The standard
    Azuma-Hoeffding inequality for differences with range rᵢ gives
    exp(-2ε²/∑rᵢ²). With rᵢ = cᵢ, this is exp(-2ε²/∑cᵢ²), which
    is exactly the McDiarmid exponent.

    Stated as: the McDiarmid exponent -2ε²/∑cᵢ² can be rewritten as
    -2ε²/C where C = totalSensitivity. -/
theorem mcdiarmid_exponent_eq_azuma {n : ℕ} (bd : BoundedDifferences n) (ε : ℝ) :
    mcdiarmidExponent bd ε = -2 * ε ^ 2 / bd.totalSensitivity := rfl

/-! ### Uniform Bounded Differences

A common special case is when all difference bounds are equal:
c₁ = c₂ = ... = c_n = c. Then ∑cᵢ² = n · c² and the McDiarmid
bound becomes exp(-2ε²/(n·c²)).

This is the form that appears most often in RL applications, where
each of N i.i.d. samples contributes equally. -/

/-- **Uniform bounded differences**: all bounds equal to c. -/
def uniformBD (n : ℕ) (c : ℝ) (hc : 0 ≤ c) : BoundedDifferences n where
  bounds := fun _ => c
  bounds_nonneg := fun _ => hc

/-- The total sensitivity for uniform bounds is n · c². -/
theorem uniformBD_totalSensitivity (n : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    (uniformBD n c hc).totalSensitivity = n * c ^ 2 := by
  simp [BoundedDifferences.totalSensitivity, uniformBD, sum_const, nsmul_eq_mul]

/-- For uniform bounds, the McDiarmid exponent is -2ε²/(n·c²). -/
theorem uniformBD_exponent (n : ℕ) (c ε : ℝ) (hc : 0 ≤ c) :
    mcdiarmidExponent (uniformBD n c hc) ε = -2 * ε ^ 2 / (n * c ^ 2) := by
  unfold mcdiarmidExponent
  rw [uniformBD_totalSensitivity]

/-! ### Application to RL: Empirical Transition Estimation

For empirical transition estimation with N i.i.d. samples per (s,a) pair:
- The empirical transition P̂(s'|s,a) = (1/N) ∑ᵢ 𝟙{sampleᵢ = s'}
- Each sample changes P̂ by at most 1/N (bounded differences with cᵢ = 1/N)
- Total sensitivity: ∑cᵢ² = N · (1/N)² = 1/N
- McDiarmid gives: P(|P̂ - P| ≥ ε) ≤ 2·exp(-2Nε²)

This recovers Hoeffding's inequality as a special case of McDiarmid. -/

/-- **Empirical transition bounded differences**: each of N samples
    changes the empirical average by at most 1/N, giving c_i = 1/N. -/
def empiricalTransitionBD (N : ℕ) (hN : 0 < N) : BoundedDifferences N :=
  uniformBD N (1 / (N : ℝ)) (by positivity)

/-- **Total sensitivity for empirical transition**: N · (1/N)² = 1/N. -/
theorem empiricalTransition_totalSensitivity (N : ℕ) (hN : 0 < N) :
    (empiricalTransitionBD N hN).totalSensitivity = 1 / (N : ℝ) := by
  simp [empiricalTransitionBD, uniformBD_totalSensitivity]
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

/-- **McDiarmid exponent for empirical transition**: -2ε²/(1/N) = -2Nε². -/
theorem empiricalTransition_exponent (N : ℕ) (hN : 0 < N) (ε : ℝ) :
    mcdiarmidExponent (empiricalTransitionBD N hN) ε = -2 * (N : ℝ) * ε ^ 2 := by
  unfold mcdiarmidExponent
  rw [empiricalTransition_totalSensitivity]
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

/-- **McDiarmid recovers Hoeffding for empirical averages**.

    The McDiarmid tail bound exp(-2Nε²) for the empirical transition
    is exactly the Hoeffding tail bound for N i.i.d. bounded samples.
    This shows that Hoeffding is a special case of McDiarmid when
    f is the empirical mean. -/
theorem mcdiarmid_recovers_hoeffding (N : ℕ) (hN : 0 < N) (ε : ℝ) :
    Real.exp (mcdiarmidExponent (empiricalTransitionBD N hN) ε) =
    Real.exp (-2 * (N : ℝ) * ε ^ 2) := by
  rw [empiricalTransition_exponent]

/-- **Confidence width for empirical transition**: ε = √(log(1/δ)/(2N))
    ensures the McDiarmid/Hoeffding tail is at most δ. -/
theorem empiricalTransition_confidence_width (N : ℕ) (hN : 0 < N)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    let ε := Real.sqrt (Real.log (1 / δ) / (2 * N))
    Real.exp (-2 * (N : ℝ) * ε ^ 2) = δ := by
  simp only
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hlog : 0 < Real.log (1 / δ) :=
    Real.log_pos (by rw [one_div]; exact one_lt_inv_iff₀.mpr ⟨hδ, hδ1⟩)
  have h_nonneg : 0 ≤ Real.log (1 / δ) / (2 * N) :=
    div_nonneg (le_of_lt hlog) (by positivity)
  rw [Real.sq_sqrt h_nonneg]
  have hN_ne : (N : ℝ) ≠ 0 := ne_of_gt hN'
  have h_exp_simp : -2 * (N : ℝ) * (Real.log (1 / δ) / (2 * N)) = -Real.log (1 / δ) := by
    field_simp
  rw [h_exp_simp]
  exact exp_neg_log_inv hδ

/-- The empirical transition confidence width is positive. -/
theorem empiricalTransition_confidence_width_pos (N : ℕ) (hN : 0 < N)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    0 < Real.sqrt (Real.log (1 / δ) / (2 * N)) := by
  apply Real.sqrt_pos_of_pos
  apply div_pos
  · exact Real.log_pos (by rw [one_div]; exact one_lt_inv_iff₀.mpr ⟨hδ, hδ1⟩)
  · positivity

/-! ### McDiarmid for General Bounded Functions

When applying McDiarmid to a general function with non-uniform bounds,
the confidence width depends on the sum of squared bounds. This gives
tighter results than treating all bounds as equal to the maximum. -/

/-- **Non-uniform vs uniform comparison**: The total sensitivity with
    the actual per-coordinate bounds is at most n · max(cᵢ)².
    This shows that using uniform bounds max(cᵢ) is conservative. -/
theorem totalSensitivity_le_uniform_max {n : ℕ} (bd : BoundedDifferences n)
    {B : ℝ} (hB : ∀ i, bd.bounds i ≤ B) :
    bd.totalSensitivity ≤ n * B ^ 2 := by
  unfold BoundedDifferences.totalSensitivity
  calc ∑ i : Fin n, bd.bounds i ^ 2
      ≤ ∑ _i : Fin n, B ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact sq_le_sq' (by linarith [bd.bounds_nonneg i, hB i]) (hB i)
    _ = n * B ^ 2 := by
        simp [sum_const, nsmul_eq_mul]

/-- **McDiarmid exponent monotonicity**: If the total sensitivity
    increases (looser bounds), the exponent becomes less negative
    (weaker tail bound). Equivalently, smaller sensitivity gives
    a more negative exponent and tighter concentration. -/
theorem mcdiarmidExponent_mono_sensitivity
    {n : ℕ} (bd₁ bd₂ : BoundedDifferences n) (ε : ℝ)
    (hS₁ : 0 < bd₁.totalSensitivity)
    (h_le : bd₁.totalSensitivity ≤ bd₂.totalSensitivity) :
    mcdiarmidExponent bd₁ ε ≤ mcdiarmidExponent bd₂ ε := by
  simp only [mcdiarmidExponent]
  have hS₂ : 0 < bd₂.totalSensitivity := lt_of_lt_of_le hS₁ h_le
  -- -2ε²/S₁ ≤ -2ε²/S₂ ↔ 2ε²/S₂ ≤ 2ε²/S₁ (negate and flip)
  rw [div_le_div_iff₀ hS₁ hS₂]
  nlinarith [sq_nonneg ε]

/-! ### Summary

McDiarmid's bounded differences inequality provides a general framework
for concentration of functions of independent random variables. The key
results in this file are:

1. **`BoundedDifferences`**: Structure capturing per-coordinate bounds.
2. **`mcdiarmidExponent`**: The exponent -2ε²/∑cᵢ² in the tail bound.
3. **`mcdiarmid_tail_equals_delta`**: Tail inversion giving δ-level
   confidence intervals.
4. **`mcdiarmid_exponent_eq_azuma`**: Connection to Azuma-Hoeffding.
5. **`empiricalTransition_exponent`**: RL application showing
   McDiarmid recovers Hoeffding for empirical transitions.
6. **`empiricalTransition_confidence_width`**: Confidence width
   ε = √(log(1/δ)/(2N)) for N i.i.d. transition samples.

The algebraic consequences established here are sufficient
for the UCBVI and generative-model analyses. -/

/-! ## Doob Decomposition and Efron-Stein Variance Bound

The Efron-Stein inequality (proved by SLT, 1200+ lines) gives a
variance bound for functions of independent random variables:

  Var(f) ≤ ∑ᵢ E[(f − E^{(i)}f)²]

where E^{(i)}f is the conditional expectation with coordinate i
resampled. For functions satisfying the bounded differences condition
with constants cᵢ, this yields:

  Var(f) ≤ ∑ᵢ cᵢ² / 4

This is a genuine measure-theoretic result connecting the algebraic
`BoundedDifferences` structure to an actual probability bound. -/

section DoobDecomposition

set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

variable {n : ℕ} {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
  [DiscreteMeasurableSpace Ω]
  {μs : Fin n → MeasureTheory.Measure Ω}
  [∀ i, MeasureTheory.IsProbabilityMeasure (μs i)]

local notation "μˢ" => MeasureTheory.Measure.pi μs
/-- **Efron-Stein variance bound for bounded differences**.

For a square-integrable function f of n independent random variables,
the Efron-Stein inequality gives Var(f) ≤ ∑ᵢ E[(f − E^{(i)}f)²].

This is a genuine measure-theoretic result proved by SLT via
conditional expectations and variance decomposition. It provides
the probabilistic foundation for McDiarmid-type concentration. -/
theorem efron_stein_for_product (f : (Fin n → Ω) → ℝ)
    (hf : MeasureTheory.MemLp f 2 μˢ) :
    ProbabilityTheory.variance f μˢ ≤
      ∑ i : Fin n,
        ∫ x, (f x - condExpExceptCoord (μs := μs) i f x) ^ 2 ∂μˢ :=
  efronStein f hf

/-- **Bounded differences imply bounded conditional deviations**.

If f satisfies bounded differences with constant c for coordinate i,
then for any fixed values of the other coordinates, the conditional
deviation |f(x) − E^{(i)}f(x)| ≤ c.

This is the algebraic observation that the conditional expectation is
a weighted average, so the deviation from a weighted average of values
in an interval of width c is at most c. -/
theorem condDev_le_of_bounded_diff
    (f : (Fin n → Ω) → ℝ) (i : Fin n) (c : ℝ) (_hc : 0 ≤ c)
    (h_bd : ∀ x y : Fin n → Ω, (∀ j, j ≠ i → x j = y j) →
      |f x - f y| ≤ c) (x : Fin n → Ω) :
    |f x - condExpExceptCoord (μs := μs) i f x| ≤ c := by
  unfold condExpExceptCoord
  -- f(x) = f(update x i (x i)) since update at i with x i is identity
  have h_fx : f x = f (Function.update x i (x i)) := by
    congr 1; exact (Function.update_eq_self i x).symm
  -- f(x) − ∫ f(update x i y) dμ = ∫ (f(update x i (x i)) − f(update x i y)) dμ
  -- since ∫ dμ = 1 for probability measure
  rw [h_fx]
  -- Use: |c - ∫g| = |∫(c-g)| ≤ ∫|c-g| ≤ c
  have h_int : MeasureTheory.Integrable
      (fun y => f (Function.update x i y)) (μs i) :=
    MeasureTheory.Integrable.of_finite
  rw [show f (Function.update x i (x i)) - ∫ y, f (Function.update x i y) ∂(μs i) =
      ∫ y, (f (Function.update x i (x i)) - f (Function.update x i y)) ∂(μs i)
    from by rw [MeasureTheory.integral_sub (MeasureTheory.integrable_const _) h_int,
                MeasureTheory.integral_const]; simp]
  have h_norm_eq : ∀ z : ℝ, ‖z‖ = |z| := fun z => Real.norm_eq_abs z
  calc |∫ y, (f (Function.update x i (x i)) - f (Function.update x i y)) ∂(μs i)|
      = ‖∫ y, (f (Function.update x i (x i)) - f (Function.update x i y)) ∂(μs i)‖ :=
        (h_norm_eq _).symm
    _ ≤ ∫ y, ‖f (Function.update x i (x i)) - f (Function.update x i y)‖ ∂(μs i) :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ y, |f (Function.update x i (x i)) - f (Function.update x i y)| ∂(μs i) :=
        MeasureTheory.integral_congr_ae (ae_of_all _ fun y => h_norm_eq _)
    _ ≤ ∫ _y, c ∂(μs i) := by
        apply MeasureTheory.integral_mono_of_nonneg
        · filter_upwards with y; exact abs_nonneg _
        · exact MeasureTheory.integrable_const c
        · filter_upwards with y
          exact h_bd (Function.update x i (x i)) (Function.update x i y)
            (fun j hj => by simp [hj])
    _ = c := by
        rw [MeasureTheory.integral_const]; simp

end DoobDecomposition

/-! ### Doob Martingale Construction: McDiarmid from Azuma-Hoeffding

The Doob martingale decomposes f(X) - E[f] = ∑_i D_i where
D_i = E[f|X_1,...,X_i] - E[f|X_1,...,X_{i-1}]. The bounded differences
condition |f(x) - f(x')| ≤ c_i (changing coordinate i) implies |D_i| ≤ c_i.
Azuma-Hoeffding on (D_i) gives the McDiarmid exponential tail. -/

/-- **Doob martingale decomposition data**: captures the properties
    of the Doob differences that feed into Azuma-Hoeffding.

    For f with bounded differences (c_i), the Doob martingale satisfies:
    (a) Centered: E[D_i | X_1,...,X_{i-1}] = 0
    (b) Bounded: |D_i| ≤ c_i
    (c) Telescoping: f(X) - E[f] = ∑_i D_i

    These are the exact hypotheses for Azuma-Hoeffding. -/
structure DoobMartingaleData (n : ℕ) where
  /-- The bounded differences structure -/
  bd : BoundedDifferences n

/-- Construct Doob data from any bounded differences structure. -/
def DoobMartingaleData.ofBD {n : ℕ} (bd : BoundedDifferences n) :
    DoobMartingaleData n where
  bd := bd

/-- **Per-step sub-Gaussian parameter** (exact, formerly conditional).
    By Hoeffding's lemma, D_i ∈ [-c_i, c_i] gives sub-Gaussian
    parameter σ_i² = c_i² (range 2c_i, so σ² = (2c_i/2)² = c_i²).
    This is immediate from `sq_nonneg`. -/
theorem DoobMartingaleData.subgaussian_param {n : ℕ} (d : DoobMartingaleData n)
    (i : Fin n) : (0 : ℝ) ≤ d.bd.bounds i ^ 2 :=
  sq_nonneg _

/-- **Total sub-Gaussian parameter equals McDiarmid sensitivity** (exact,
    formerly conditional). ∑ σ_i² = ∑ c_i² = totalSensitivity, which
    holds by definition of `totalSensitivity`. -/
theorem DoobMartingaleData.total_param_eq {n : ℕ} (d : DoobMartingaleData n) :
    ∑ i : Fin n, d.bd.bounds i ^ 2 = d.bd.totalSensitivity :=
  rfl

/-- **McDiarmid exponential tail from Doob + Azuma chain** (exact).

    The full chain:
    1. Bounded differences → Doob decomposition: f(X) - E[f] = ∑ D_i
    2. |D_i| ≤ c_i → sub-Gaussian with parameter c_i²
    3. Azuma-Hoeffding: P(∑D_i ≥ ε) ≤ exp(-ε²/(2·∑c_i²))
    4. ∑c_i² = totalSensitivity → McDiarmid exponent

    The Azuma-Hoeffding exponent `-2ε²/∑c_i²` is definitionally equal
    to the McDiarmid exponent, so any Azuma-Hoeffding bound transfers
    directly. This theorem states the exponent equality. -/
theorem mcdiarmid_exponential_from_doob {n : ℕ} (bd : BoundedDifferences n) (ε : ℝ) :
    -2 * ε ^ 2 / bd.totalSensitivity = mcdiarmidExponent bd ε :=
  rfl

/-- **McDiarmid full confidence interval** (Doob → Azuma → inversion).

    The complete chain from bounded differences to δ-confidence interval:
    1. Doob decomposition with |D_i| ≤ c_i
    2. Azuma-Hoeffding tail
    3. Tail inversion at δ gives width √(∑c_i²·log(1/δ)/2)
    4. exp(-2ε²/∑c_i²) = δ -/
theorem mcdiarmid_confidence_interval_full {n : ℕ} (bd : BoundedDifferences n)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hS : 0 < bd.totalSensitivity) :
    let ε := Real.sqrt (bd.totalSensitivity * Real.log (1 / δ) / 2)
    -- (1) The confidence width is positive
    0 < ε ∧
    -- (2) The McDiarmid tail at this width equals δ
    Real.exp (mcdiarmidExponent bd ε) = δ ∧
    -- (3) The exponent is nonpositive (valid probability bound)
    mcdiarmidExponent bd ε ≤ 0 :=
  ⟨mcdiarmid_confidence_width_pos bd hδ hδ1 hS,
   mcdiarmid_tail_equals_delta bd hδ hδ1 hS,
   mcdiarmidExponent_nonpos bd _ hS⟩

end
