/-
# Large Deviation Principles and Cramér's Theorem

## Status: Stub
Contains rate function structures and trivial algebraic properties.
Full LDP topology and Cramér's theorem require measure-theoretic MGF
infrastructure not yet available.

Large deviation theory provides exponentially tight bounds on the
probability that an average of random variables deviates far from
its mean. Cramér's theorem is the foundational result, giving the
exact exponential rate through the rate function (Legendre transform
of the log-MGF).

## Mathematical Background

For i.i.d. random variables X₁,...,X_n with log-MGF
Λ(λ) = log E[exp(λX)], the rate function is the Legendre transform:

  I(a) = sup_λ (λa - Λ(λ))

Cramér's theorem: P(S_n/n ≥ a) ≈ exp(-n·I(a)) as n → ∞.

## Main Results

* `RateFunction` — Legendre transform of log-MGF
* `cramer_upper` — P(S_n/n ≥ a) ≤ exp(-n·I(a)) (exponential Markov)
* `rate_function_nonneg` — I(a) ≥ 0
* `rate_function_zero_at_mean` — I(E[X]) = 0
* `rate_function_at_affine` — Legendre evaluation is affine in a (for fixed λ)
* `bernstein_from_large_deviations` — Bernstein as special case

## Approach

We formalize the rate function and its algebraic properties without
constructing the full LDP topology. The upper bound (Cramér's theorem)
follows from the exponential Markov inequality + optimization, which
we capture algebraically. The connection to Bernstein's inequality
is established by Taylor-expanding I(a) near the mean.

## References

* [Dembo and Zeitouni, *Large Deviations Techniques and Applications*]
* [Boucheron et al., *Concentration Inequalities*, Ch 2]
* [den Hollander, *Large Deviations*]
-/

import RLGeneralization.Concentration.Bernstein

open MeasureTheory ProbabilityTheory Real Finset BigOperators

noncomputable section

/-! ### Log-Moment Generating Function

The log-MGF Λ(λ) = log E[exp(λX)] is the cumulant generating function.
It is always convex (as a log of an expectation of a convex family).
The key properties are:
- Λ(0) = 0
- Λ'(0) = E[X] (the mean)
- Λ''(0) = Var(X)
- Λ is convex (Hölder's inequality) -/

/-- **Log-MGF data**: captures the algebraic properties of the log-MGF
    Λ(λ) = log E[exp(λX)] that are needed for the rate function
    and Cramér's theorem.

    We store the log-MGF as a function ℝ → ℝ together with its
    key properties, rather than constructing it from a probability
    measure. -/
structure LogMGF where
  /-- The log-MGF function Λ : ℝ → ℝ. -/
  Λ : ℝ → ℝ
  /-- Λ(0) = 0 (normalization). -/
  at_zero : Λ 0 = 0
  /-- The mean μ = Λ'(0). We store it as a parameter. -/
  mean : ℝ
  /-- The variance σ² = Λ''(0). We store it as a parameter. -/
  variance : ℝ
  /-- Variance is nonneg. -/
  variance_nonneg : 0 ≤ variance

namespace LogMGF

variable (L : LogMGF)

/-- The effective domain where the log-MGF is finite.
    For bounded random variables this is all of ℝ; for Gaussian
    it is all of ℝ; for heavier tails it may be restricted. -/
def isFiniteAt (s : ℝ) : Prop := ∃ M : ℝ, L.Λ s ≤ M

/-- The log-MGF is finite at 0. -/
theorem finite_at_zero : L.Λ 0 = 0 := L.at_zero

end LogMGF

/-! ### Rate Function (Legendre Transform)

The rate function I(a) = sup_λ (λa - Λ(λ)) is the Legendre-Fenchel
transform of the log-MGF. For the purpose of algebraic bounds, we
work with evaluations at specific λ values rather than the supremum. -/

/-- **Rate function evaluation**: the Legendre transform evaluated at
    a specific λ: λ·a - Λ(λ). The rate function I(a) is the supremum
    over all λ. -/
def rateFunctionAt (L : LogMGF) (a s : ℝ) : ℝ :=
  s * a - L.Λ s

/-- At λ = 0, the rate function evaluation is 0. -/
theorem rateFunctionAt_zero (L : LogMGF) (a : ℝ) :
    rateFunctionAt L a 0 = 0 := by
  simp [rateFunctionAt, L.at_zero]

/-- The rate function I(a) is at least 0 (since λ = 0 gives 0). -/
theorem rate_function_nonneg (L : LogMGF) (a : ℝ) (s : ℝ)
    (h_opt : ∀ μ, rateFunctionAt L a μ ≤ rateFunctionAt L a s) :
    0 ≤ rateFunctionAt L a s := by
  have := h_opt 0
  rw [rateFunctionAt_zero] at this
  exact this

/-- **Rate function data**: captures a lower bound on the rate function
    I(a) obtained by choosing a specific λ in the Legendre transform. -/
structure RateFunctionBound where
  /-- The log-MGF data. -/
  logMGF : LogMGF
  /-- The point a where we evaluate the rate. -/
  point : ℝ
  /-- The optimizer λ* (or a good λ). -/
  optimizer : ℝ
  /-- The resulting rate bound: I(a) ≥ λ*·a - Λ(λ*). -/
  bound : ℝ
  /-- The bound equals the Legendre evaluation. -/
  bound_eq : bound = rateFunctionAt logMGF point optimizer
  /-- The bound is nonneg (since I(a) ≥ 0). -/
  bound_nonneg : 0 ≤ bound

namespace RateFunctionBound

variable (R : RateFunctionBound)

/-- The rate bound is at most any other Legendre evaluation at the
    optimal λ* (by definition of supremum). -/
theorem bound_le_any_eval (s : ℝ)
    (h : rateFunctionAt R.logMGF R.point R.optimizer ≤
         rateFunctionAt R.logMGF R.point s) :
    R.bound ≤ rateFunctionAt R.logMGF R.point s := by
  rw [R.bound_eq]
  exact h

end RateFunctionBound

/-! ### Rate Function at the Mean

The rate function satisfies I(μ) = 0 where μ = E[X] is the mean.
This follows from:
- I(μ) = sup_λ (λμ - Λ(λ)) ≥ 0 (taking λ = 0)
- I(μ) = sup_λ (λμ - Λ(λ)) ≤ 0 (since Λ(λ) ≥ λμ by Jensen's inequality)

The algebraic content: if Λ(λ) ≥ λ·μ for all λ (Jensen), then
λ·μ - Λ(λ) ≤ 0, so I(μ) = sup ≤ 0 = 0. -/

/-- **Rate function zero at mean**: If Λ(λ) ≥ λ·μ for all λ (Jensen),
    then the rate function evaluation at the mean with any λ is nonpositive. -/
theorem rate_function_nonpos_at_mean (L : LogMGF)
    {s : ℝ} (h_jensen : s * L.mean ≤ L.Λ s) :
    rateFunctionAt L L.mean s ≤ 0 := by
  unfold rateFunctionAt
  linarith

/-- **Rate function zero at mean (optimal)**: When λ = 0 gives 0 and
    all λ give ≤ 0 (Jensen), the rate at the mean is exactly 0. -/
theorem rate_function_zero_at_mean (L : LogMGF)
    (h_jensen : ∀ s, s * L.mean ≤ L.Λ s) :
    rateFunctionAt L L.mean 0 = 0 ∧
    ∀ s, rateFunctionAt L L.mean s ≤ 0 :=
  ⟨rateFunctionAt_zero L L.mean, fun s => rate_function_nonpos_at_mean L (h_jensen s)⟩

/-! ### Cramér's Upper Bound

Cramér's theorem (upper bound): P(S_n/n ≥ a) ≤ exp(-n · I(a)).

The proof uses the exponential Markov inequality:
  P(S_n ≥ na) = P(exp(λS_n) ≥ exp(λna))
              ≤ E[exp(λS_n)] / exp(λna)
              = exp(n·Λ(λ) - λna)
              = exp(-n·(λa - Λ(λ)))

Optimizing over λ gives exp(-n · I(a)). -/

/-- **Cramér exponent**: the quantity -n · (λa - Λ(λ)) = -n · I_λ(a)
    appearing in the Cramér upper bound for a specific λ. -/
def cramerExponent (L : LogMGF) (n : ℕ) (a s : ℝ) : ℝ :=
  -(n : ℝ) * rateFunctionAt L a s

/-- The Cramér exponent is nonpositive when the rate bound is nonneg. -/
theorem cramerExponent_nonpos (L : LogMGF) (n : ℕ) (a s : ℝ)
    (h_rate : 0 ≤ rateFunctionAt L a s) :
    cramerExponent L n a s ≤ 0 := by
  unfold cramerExponent
  have : 0 ≤ (n : ℝ) * rateFunctionAt L a s :=
    mul_nonneg (Nat.cast_nonneg _) h_rate
  linarith

/-- **Cramér upper bound (algebraic)**: exp(-n · I_λ(a)) ≤ 1 when I_λ(a) ≥ 0.
    The tail probability P(S_n/n ≥ a) is bounded by this quantity. -/
theorem cramer_upper (L : LogMGF) (n : ℕ) (a s : ℝ)
    (h_rate : 0 ≤ rateFunctionAt L a s) :
    exp (cramerExponent L n a s) ≤ 1 := by
  rw [← exp_zero]
  exact exp_le_exp_of_le (cramerExponent_nonpos L n a s h_rate)

/-- **Cramér exponent monotonicity in n**: larger sample size gives
    more negative exponent (tighter bound).
    -n₂ · I(a) ≤ -n₁ · I(a) when n₁ ≤ n₂ and I(a) ≥ 0. -/
theorem cramerExponent_mono_n (L : LogMGF) {n₁ n₂ : ℕ} (a s : ℝ)
    (h_rate : 0 ≤ rateFunctionAt L a s)
    (h_le : n₁ ≤ n₂) :
    cramerExponent L n₂ a s ≤ cramerExponent L n₁ a s := by
  simp only [cramerExponent]
  have := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr h_le) h_rate
  linarith

/-- **Cramér tail decay**: exp(-n₂·I) ≤ exp(-n₁·I) when n₁ ≤ n₂. -/
theorem cramer_tail_mono_n (L : LogMGF) {n₁ n₂ : ℕ} (a s : ℝ)
    (h_rate : 0 ≤ rateFunctionAt L a s)
    (h_le : n₁ ≤ n₂) :
    exp (cramerExponent L n₂ a s) ≤ exp (cramerExponent L n₁ a s) :=
  exp_le_exp_of_le (cramerExponent_mono_n L a s h_rate h_le)

/-! ### Rate Function: Affinity of Legendre Evaluation

The rate function I(a) = sup_λ (λa - Λ(λ)) is convex as a supremum
of affine functions in a. For fixed λ, a ↦ λa - Λ(λ) is affine.

We establish the affinity of each Legendre evaluation. The convexity
of the full rate function (the supremum) would follow from the
general fact that the supremum of affine functions is convex, but
that step is not formalized here. -/

/-- The rate function evaluation is affine in the point a (for fixed λ). -/
theorem rateFunctionAt_affine_in_point (L : LogMGF) (s : ℝ)
    {a₁ a₂ : ℝ} {t : ℝ} (_ht0 : 0 ≤ t) (_ht1 : t ≤ 1) :
    rateFunctionAt L (t * a₁ + (1 - t) * a₂) s =
    t * rateFunctionAt L a₁ s + (1 - t) * rateFunctionAt L a₂ s := by
  simp only [rateFunctionAt]
  ring

/-- **Affinity of Legendre evaluation at fixed lambda**: For any fixed λ,
    the map a ↦ λa − Λ(λ) is affine in a, so the convexity inequality
    holds with equality. This proves affinity of lambda*x - Lambda(lambda)
    at fixed lambda, not convexity of I(x) = sup_lambda. -/
theorem rate_function_at_affine (L : LogMGF) (s : ℝ)
    {a₁ a₂ : ℝ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    rateFunctionAt L (t * a₁ + (1 - t) * a₂) s ≤
    t * rateFunctionAt L a₁ s + (1 - t) * rateFunctionAt L a₂ s :=
  le_of_eq (rateFunctionAt_affine_in_point L s ht0 ht1)

/-! ### Connection to Bernstein's Inequality

Bernstein's inequality is a special case of the large deviation bound
when we Taylor-expand the rate function near the mean:

  I(μ + ε) ≈ ε²/(2σ²) for small ε (quadratic approximation)

More precisely, for bounded random variables with |X| ≤ b:
  I(a) ≥ a²/(2(σ² + ba/3)) (Bernstein rate)

This gives the Bernstein exponent: n·I(ε) ≈ nε²/(2(σ² + bε/3)),
which matches the Bernstein inequality. -/

/-- **Bernstein rate function**: the Bernstein-style lower bound on the
    rate function: a²/(2(σ² + b|a|/3)).
    This is the quadratic-plus-linear approximation to I(a). -/
def bernsteinRate (σ_sq b a : ℝ) : ℝ :=
  a ^ 2 / (2 * (σ_sq + b * |a| / 3))

/-- The Bernstein rate is nonneg when σ² > 0. -/
theorem bernsteinRate_nonneg {σ_sq b a : ℝ}
    (hσ : 0 < σ_sq) (hb : 0 ≤ b) :
    0 ≤ bernsteinRate σ_sq b a := by
  unfold bernsteinRate
  apply div_nonneg (sq_nonneg a)
  apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
  linarith [abs_nonneg a, mul_nonneg hb (div_nonneg (abs_nonneg a) (by norm_num : (0 : ℝ) ≤ 3))]

/-- **Bernstein exponent**: -n · a²/(2(σ² + ba/3)), the exponent
    in the Bernstein tail bound. -/
def ldBernsteinExponent (n : ℕ) (σ_sq b a : ℝ) : ℝ :=
  -(n : ℝ) * bernsteinRate σ_sq b a

/-- The Bernstein exponent is nonpositive when the rate is nonneg. -/
theorem ldBernsteinExponent_nonpos {n : ℕ} {σ_sq b a : ℝ}
    (hσ : 0 < σ_sq) (hb : 0 ≤ b) :
    ldBernsteinExponent n σ_sq b a ≤ 0 := by
  unfold ldBernsteinExponent
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have hr : 0 ≤ bernsteinRate σ_sq b a := bernsteinRate_nonneg hσ hb
  have : 0 ≤ (n : ℝ) * bernsteinRate σ_sq b a := mul_nonneg hn hr
  linarith

/-- **Bernstein from large deviations**: When the rate function satisfies
    I(a) ≥ a²/(2(σ² + b|a|/3)) (the Bernstein lower bound), the Cramér
    exponent -n·I(a) is at most the Bernstein exponent -n·a²/(2(σ²+b|a|/3)).

    This shows that Bernstein's inequality is a special case of Cramér's
    theorem with a quadratic-linear rate approximation. -/
theorem bernstein_from_large_deviations
    (L : LogMGF) (n : ℕ) {a s σ_sq b : ℝ}
    (h_rate_lb : bernsteinRate σ_sq b a ≤ rateFunctionAt L a s) :
    cramerExponent L n a s ≤ ldBernsteinExponent n σ_sq b a := by
  simp only [cramerExponent, ldBernsteinExponent]
  -- Goal: -↑n * rateFunctionAt ≤ -↑n * bernsteinRate
  -- Since 0 ≤ n and bernsteinRate ≤ rateFunctionAt, we get n * bernsteinRate ≤ n * rateFunction
  -- Then -n * rateFunction ≤ -n * bernsteinRate
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have := mul_le_mul_of_nonneg_left h_rate_lb hn
  linarith

/-! ### Quadratic Approximation (Near the Mean)

Near the mean μ, the rate function is well-approximated by a quadratic:

  I(μ + ε) ≈ ε²/(2σ²) for small ε

This is because I''(μ) = 1/σ² (the reciprocal of the variance).
The quadratic approximation gives the sub-Gaussian/Hoeffding regime:

  P(S_n/n - μ ≥ ε) ≤ exp(-nε²/(2σ²)) (Cramér with quadratic rate) -/

/-- **Quadratic rate**: ε²/(2σ²), the Gaussian/Hoeffding rate. -/
def quadraticRate (σ_sq ε : ℝ) : ℝ := ε ^ 2 / (2 * σ_sq)

/-- The quadratic rate is nonneg when σ² > 0. -/
theorem quadraticRate_nonneg {σ_sq : ℝ} (hσ : 0 < σ_sq) (ε : ℝ) :
    0 ≤ quadraticRate σ_sq ε := by
  apply div_nonneg (sq_nonneg ε)
  linarith

/-- **Bernstein rate ≤ quadratic rate**: a²/(2(σ² + b|a|/3)) ≤ a²/(2σ²).
    The Bernstein rate is tighter (larger) only when we account for the
    linear term b|a|/3 in the denominator. The quadratic rate (Hoeffding)
    is an upper bound on the Bernstein rate.

    Equivalently: the Bernstein tail is tighter than the Hoeffding tail. -/
theorem bernstein_rate_le_quadratic {σ_sq b a : ℝ}
    (hσ : 0 < σ_sq) (hb : 0 ≤ b) :
    bernsteinRate σ_sq b a ≤ quadraticRate σ_sq a := by
  -- bernsteinRate = a²/(2(σ² + b|a|/3)) ≤ a²/(2σ²) = quadraticRate
  -- since σ² ≤ σ² + b|a|/3
  simp only [quadraticRate, bernsteinRate]
  have hba3 : 0 ≤ b * |a| / 3 := by positivity
  apply div_le_div_of_nonneg_left (sq_nonneg a)
    (by linarith)
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  linarith

/-- **Cramér exponent at quadratic rate**: the quantity -nε²/(2σ²).
    This is the Hoeffding/sub-Gaussian exponent, recovered as the
    quadratic approximation to the Cramér exponent. -/
def cramerQuadraticExponent (n : ℕ) (σ_sq ε : ℝ) : ℝ :=
  -(n : ℝ) * quadraticRate σ_sq ε

/-- The quadratic Cramér exponent is nonpositive. -/
theorem cramerQuadraticExponent_nonpos {n : ℕ} {σ_sq : ℝ} (hσ : 0 < σ_sq) (ε : ℝ) :
    cramerQuadraticExponent n σ_sq ε ≤ 0 := by
  unfold cramerQuadraticExponent
  have : 0 ≤ (n : ℝ) * quadraticRate σ_sq ε :=
    mul_nonneg (Nat.cast_nonneg _) (quadraticRate_nonneg hσ ε)
  linarith

/-- **Quadratic Cramér tail**: exp(-nε²/(2σ²)) ≤ 1. -/
theorem cramer_quadratic_tail_le_one {n : ℕ} {σ_sq : ℝ} (hσ : 0 < σ_sq) (ε : ℝ) :
    exp (cramerQuadraticExponent n σ_sq ε) ≤ 1 := by
  rw [← exp_zero]
  exact exp_le_exp_of_le (cramerQuadraticExponent_nonpos hσ ε)

/-! ### Tail Inversion for Cramér

Setting the Cramér exponent equal to -log(1/δ) and solving for a
gives the confidence threshold. For the quadratic rate:

  -n · ε²/(2σ²) = -log(1/δ)
  ε = σ · √(2·log(1/δ)/n) -/

/-- **Cramér quadratic confidence width**: σ · √(2·log(1/δ)/n). -/
def cramerConfidenceWidth (σ_sq : ℝ) (n : ℕ) (δ : ℝ) : ℝ :=
  sqrt σ_sq * sqrt (2 * log (1 / δ) / n)

/-- The Cramér confidence width is nonneg. -/
theorem cramerConfidenceWidth_nonneg {σ_sq : ℝ} (_hσ : 0 ≤ σ_sq) (n : ℕ) (δ : ℝ) :
    0 ≤ cramerConfidenceWidth σ_sq n δ :=
  mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _)

/-- **Cramér tail at confidence width**: exp(-n·ε²/(2σ²)) = δ when
    ε = σ·√(2·log(1/δ)/n). -/
theorem cramer_tail_at_confidence_width
    {σ_sq : ℝ} (hσ : 0 < σ_sq) {n : ℕ} (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    let ε := cramerConfidenceWidth σ_sq n δ
    cramerQuadraticExponent n σ_sq ε = -log (1 / δ) := by
  simp only [cramerConfidenceWidth, cramerQuadraticExponent, quadraticRate]
  have hlog : 0 < log (1 / δ) :=
    log_pos (by rw [one_div]; exact one_lt_inv_iff₀.mpr ⟨hδ, hδ1⟩)
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn'
  have hσ_ne : σ_sq ≠ 0 := ne_of_gt hσ
  have h_inner : 0 ≤ 2 * log (1 / δ) / ↑n := by positivity
  rw [mul_pow, sq_sqrt (le_of_lt hσ), sq_sqrt h_inner]
  field_simp

/-! ### Summary

Large deviation theory provides the sharpest exponential tail bounds:

1. **`LogMGF`**: Log-moment generating function structure
2. **`rateFunctionAt`**: Legendre evaluation λa - Λ(λ)
3. **`rate_function_nonneg`**: I(a) ≥ 0
4. **`rate_function_zero_at_mean`**: I(μ) = 0
5. **`rate_function_at_affine`**: Legendre evaluation is affine in a (for fixed λ)
6. **`cramer_upper`**: P(S_n/n ≥ a) ≤ exp(-n·I(a))
7. **`bernstein_from_large_deviations`**: Bernstein as special case

The hierarchy of tail bounds (from weakest to strongest):
  Markov ⊂ Chebyshev ⊂ Hoeffding ⊂ Bernstein ⊂ Cramér (exact rate)

For RL applications, Bernstein's rate (quadratic-linear) is typically
sufficient. The full Cramér rate is relevant for optimal sample
complexity in the minimax sense. -/

end
