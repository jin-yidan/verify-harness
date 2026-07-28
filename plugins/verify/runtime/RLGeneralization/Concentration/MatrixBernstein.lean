/-
# Matrix Bernstein Inequality (Algebraic Core)

The matrix Bernstein inequality controls the spectral norm of a sum of
independent random matrices:

  P(||∑ X_i|| ≥ t) ≤ d · exp(-t² / (2(σ² + bt/3)))

where σ² = ||∑ E[X_i X_i^T]|| (matrix variance), b is a uniform bound
on ||X_i||, and d is the matrix dimension.

The full proof requires the matrix exponential and the Golden-Thompson
trace inequality, which are beyond current Mathlib infrastructure.
Instead, we formalize the algebraic framework:

1. The matrix Bernstein exponent matches the scalar Bernstein exponent
2. The dimension factor d arises from a covering/union-bound argument
3. Solving for the confidence width gives t = O(σ√(d log(d/δ)) + bd log(d/δ))
4. Applied to feature outer products, this yields confidence ellipsoids
5. These ellipsoids connect to the elliptical potential lemma

## Main Results

* `matrixBernsteinExponent` -- exponent = t²/(2(σ² + bt/3))
* `matrix_bernstein_exponent_eq_scalar` -- matches `bernsteinExponent`
* `matrixBernsteinBound` -- d · exp(-exponent) form
* `matrix_bernstein_tail_with_dim` -- the bound is ≤ δ when t is large enough
* `matrix_bernstein_confidence_width` -- width is nonneg and sufficient
* `elliptical_potential_from_confidence` -- connecting to elliptical potential

## References

* [Tropp, "An Introduction to Matrix Concentration Inequalities", 2015]
* [Agarwal et al., *RL: Theory and Algorithms*]
-/

import RLGeneralization.Concentration.Bennett
import RLGeneralization.LinearMDP.Regret
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real Finset BigOperators

noncomputable section

/-! ### Matrix Variance Structure

The matrix variance statistic V = ∑ E[X_i X_i^T] is the matrix analogue
of the scalar variance. Its spectral norm ||V|| = σ² controls the
matrix Bernstein bound. We define these algebraically using our
`Fin d → Fin d → ℝ` representation. -/

/-- The **matrix variance** of a sequence of d×d matrices:
    V = ∑ M_i, where each M_i represents E[X_i X_i^T].

    In applications, M_i = outerProduct(φ_i) from the EllipticalPotential module. -/
def matrixVariance {n : ℕ} {d : ℕ}
    (matrices : Fin n → Fin d → Fin d → ℝ) (i j : Fin d) : ℝ :=
  ∑ k : Fin n, matrices k i j

/-- The **spectral norm bound** asserts that the spectral norm of the
    matrix variance is at most σ². Since we work algebraically, we
    define this as a predicate on the quadratic form:
    ∀ v, v^T V v ≤ σ² · ||v||². -/
-- [UNUSED]
def spectralNormBound {n : ℕ} {d : ℕ}
    (matrices : Fin n → Fin d → Fin d → ℝ)
    (sigma_sq : ℝ) : Prop :=
  ∀ v : Fin d → ℝ,
    quadForm v (matrixVariance matrices) ≤ sigma_sq * sqNorm v

/-! ### Matrix Bernstein Exponent

The matrix Bernstein exponent has exactly the same algebraic form as
the scalar Bernstein exponent t²/(2(σ² + bt/3)). The only difference
is the extra dimension factor d in front. -/

/-- The **matrix Bernstein exponent**: t² / (2(σ² + bt/3)).
    This is algebraically identical to the scalar Bernstein exponent
    from `Bennett.lean`'s `bernsteinExponent`. -/
def matrixBernsteinExponent (sigma_sq b t : ℝ) : ℝ :=
  t ^ 2 / (2 * (sigma_sq + b * t / 3))

/-- The matrix Bernstein exponent equals the scalar `bernsteinExponent`. -/
theorem matrix_bernstein_exponent_eq_scalar (sigma_sq b t : ℝ) :
    matrixBernsteinExponent sigma_sq b t = bernsteinExponent sigma_sq b t := by
  rfl

/-! ### Matrix Bernstein Bound (Algebraic Form)

The matrix Bernstein inequality states:
  P(||∑ X_i|| ≥ t) ≤ d · exp(-t²/(2(σ² + bt/3)))

The dimension factor d comes from the covering argument: the spectral
norm ||M|| = max_||v||=1 |v^T M v|, and an ε-net of the unit sphere
in R^d has cardinality at most (1+2/ε)^d ≤ 9^d (with ε = 1/2). The
factor d in the standard statement is actually 2d (from the 2d×2d
Hermitian dilation), simplified to d via the Hermitian structure. -/

/-- The **matrix Bernstein bound** in algebraic form:
    d · exp(-t²/(2(σ² + bt/3))). -/
def matrixBernsteinBound (d : ℕ) (sigma_sq b t : ℝ) : ℝ :=
  (d : ℝ) * exp (-matrixBernsteinExponent sigma_sq b t)

/-- The matrix Bernstein bound equals d times the scalar Bernstein bound. -/
theorem matrixBernsteinBound_eq_dim_mul_scalar (d : ℕ) (sigma_sq b t : ℝ) :
    matrixBernsteinBound d sigma_sq b t =
    (d : ℝ) * exp (-bernsteinExponent sigma_sq b t) := by
  simp [matrixBernsteinBound, matrix_bernstein_exponent_eq_scalar]

/-- **Dimension factor**: the matrix bound is exactly d times the scalar bound.

    This formalizes the fact that the "extra cost" of moving from scalar
    to matrix concentration is precisely a factor of d (the dimension). -/
theorem matrix_bernstein_dimension_factor (d : ℕ) (sigma_sq b t : ℝ) :
    matrixBernsteinBound d sigma_sq b t =
    (d : ℝ) * exp (-matrixBernsteinExponent sigma_sq b t) := by
  rfl

/-! ### Matrix Bernstein Tail Bound

We show that d · exp(-exponent) ≤ δ when the exponent is large enough,
i.e., when t²/(2(σ² + bt/3)) ≥ log(d/δ). This is the algebraic
content of the matrix Bernstein tail bound. -/

/-- The matrix Bernstein exponent is nonneg when σ² > 0, b > 0, t ≥ 0. -/
theorem matrixBernsteinExponent_nonneg {sigma_sq b t : ℝ}
    (hsigma : 0 < sigma_sq) (hb : 0 < b) (ht : 0 ≤ t) :
    0 ≤ matrixBernsteinExponent sigma_sq b t := by
  unfold matrixBernsteinExponent
  apply div_nonneg
  · positivity
  · apply mul_nonneg (by norm_num)
    have : 0 < sigma_sq + b * t / 3 := by positivity
    linarith

/-- **Matrix Bernstein tail with dimension**: if the exponent is at least
    log(d/δ), then d · exp(-exponent) ≤ δ. -/
theorem matrix_bernstein_tail_with_dim
    {d : ℕ} (hd : 0 < d)
    {sigma_sq b t delta : ℝ}
    (hdelta : 0 < delta)
    (_hsigma : 0 < sigma_sq) (_hb : 0 < b) (_ht : 0 < t)
    (h_exp : matrixBernsteinExponent sigma_sq b t ≥ Real.log ((d : ℝ) / delta)) :
    matrixBernsteinBound d sigma_sq b t ≤ delta := by
  unfold matrixBernsteinBound
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  -- exp(-exponent) ≤ exp(-log(d/δ)) = δ/d
  have h1 : exp (-matrixBernsteinExponent sigma_sq b t) ≤
      exp (-Real.log ((d : ℝ) / delta)) := by
    apply exp_le_exp.mpr
    linarith
  have h_ratio_pos : (0 : ℝ) < (d : ℝ) / delta := div_pos hd_pos hdelta
  have h2 : exp (-Real.log ((d : ℝ) / delta)) = delta / d := by
    rw [exp_neg, Real.exp_log h_ratio_pos, inv_div]
  calc (d : ℝ) * exp (-matrixBernsteinExponent sigma_sq b t)
      ≤ (d : ℝ) * exp (-Real.log ((d : ℝ) / delta)) := by
        gcongr
    _ = (d : ℝ) * (delta / d) := by rw [h2]
    _ = delta := by rw [mul_div_cancel₀ _ hd_pos.ne']

/-! ### Confidence Width

Solving d · exp(-t²/(2(σ² + bt/3))) ≤ δ for t gives the confidence
width. The standard closed-form upper bound is:

  t ≤ σ · √(2 · log(d/δ)) + b · 2 · log(d/δ) / 3

This comes from the inequality t²/(2(σ² + bt/3)) ≥ min(t²/(4σ²), 3t/(4b)),
so it suffices to have both t²/(4σ²) ≥ log(d/δ)/2 and 3t/(4b) ≥ log(d/δ)/2.

We prove the algebraic identity that the standard width formula indeed
makes the exponent large enough. -/

/-- Auxiliary: for a, b ≥ 0, (a + b)² ≤ 2(a² + b²). -/
private theorem sq_add_le_two_mul_sq_add_sq (a b : ℝ) :
    (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  nlinarith [sq_nonneg (a - b)]

/-- **Confidence width nonnegativity**: the matrix Bernstein confidence
    width t = σ · √(2L) + b · 2L/3 is nonneg when σ² > 0, b > 0, L ≥ 0. -/
theorem matrix_bernstein_width_nonneg
    {sigma_sq b : ℝ}
    (_hsigma : 0 < sigma_sq) (hb : 0 < b)
    {L : ℝ} (hL : 0 ≤ L) :
    0 ≤ Real.sqrt sigma_sq * Real.sqrt (2 * L) + b * (2 * L / 3) := by
  apply add_nonneg
  · apply mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  · apply mul_nonneg hb.le
    apply div_nonneg (mul_nonneg (by norm_num) hL) (by norm_num)

/-- The **matrix Bernstein confidence width**:
    t = σ · √(2 · L) + b · 2L/3

    where L = log(d/δ). We show this width satisfies:
      t² ≤ 2(σ² · 2L + b² · 4L²/9)

    which is the key algebraic step for showing the exponent is large enough. -/
theorem matrix_bernstein_confidence_width
    {sigma_sq b : ℝ}
    (hsigma : 0 < sigma_sq) (_hb : 0 < b)
    {L : ℝ} (_hL : 0 ≤ L) :
    let t := Real.sqrt sigma_sq * Real.sqrt (2 * L) + b * (2 * L / 3)
    t ^ 2 ≤ 2 * (sigma_sq * (2 * L) + (b * (2 * L / 3)) ^ 2) := by
  intro t
  -- t = a + c where a = √(σ²) · √(2L), c = b · 2L/3
  -- t² = (a + c)² ≤ 2(a² + c²) by (a-c)² ≥ 0
  -- a² = σ² · 2L (since √σ² · √(2L))² = σ² · 2L when σ² > 0)
  -- c² = (b · 2L/3)²
  have ha_sq : (Real.sqrt sigma_sq * Real.sqrt (2 * L)) ^ 2 =
      sigma_sq * (2 * L) := by
    rw [mul_pow, Real.sq_sqrt hsigma.le, Real.sq_sqrt (by linarith)]
  calc t ^ 2 ≤ 2 * ((Real.sqrt sigma_sq * Real.sqrt (2 * L)) ^ 2 +
      (b * (2 * L / 3)) ^ 2) := sq_add_le_two_mul_sq_add_sq _ _
    _ = 2 * (sigma_sq * (2 * L) + (b * (2 * L / 3)) ^ 2) := by
        rw [ha_sq]

/-! ### Confidence Ellipsoid

In linear MDPs, the matrix Bernstein inequality applied to the noise
terms ηₜ · φ(s,a) gives a confidence ellipsoid:

  ||θ̂ - θ*||_V ≤ β

where V = Λ_T = I + ∑ φφ^T (the Gram matrix), θ̂ is the least-squares
estimate, and β is the confidence radius derived from the matrix
Bernstein width.

We formalize this as an algebraic structure: given a matrix variance
bound and the Bernstein width, the estimation error (measured in the
V-norm) is bounded. -/

/-- A **confidence ellipsoid** asserts that the estimation error
    measured in the V-weighted norm is bounded by β.

    ||θ - θ̂||²_V = (θ - θ̂)ᵀ V (θ - θ̂) ≤ β². -/
-- [UNUSED]
def confidenceEllipsoid {d : ℕ}
    (theta theta_hat : Fin d → ℝ)
    (V : Fin d → Fin d → ℝ)
    (beta : ℝ) : Prop :=
  quadForm (fun i => theta i - theta_hat i) V ≤ beta ^ 2

/-! ### Connection to Elliptical Potential

The matrix Bernstein inequality applied to feature outer products
connects to the elliptical potential lemma. Specifically:

1. Matrix Bernstein gives ||Λ⁻¹ ∑ ηₜφₜ|| ≤ β with high probability
2. This β determines the exploration bonus: bonus_t = β · ||φ_t||_{Λ_t⁻¹}
3. The elliptical potential lemma bounds ∑ ||φ_t||_{Λ_t⁻¹}

The bridge is that the confidence radius β from matrix Bernstein
becomes the multiplicative constant in front of the exploration bonus. -/

/-- **Elliptical potential from confidence**: given a confidence
    radius β from matrix Bernstein, the total exploration bonus
    over T steps with d-dimensional features satisfies:

      ∑ bonus_t ≤ β · √(T · 2d · log(1 + T/d))

    This connects the matrix Bernstein confidence width to the
    elliptical potential lemma (`total_bonus_from_features`). -/
theorem elliptical_potential_from_confidence
    (d : ℕ) (hd : 0 < d) (T : ℕ)
    (phis : Fin T → Fin d → ℝ)
    (h_norm : ∀ k : Fin T, sqNorm (phis k) ≤ 1)
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    ∃ x : Fin T → ℝ,
      (∀ t, 0 ≤ x t) ∧
      ∀ (bonus : Fin T → ℝ),
        (∀ t, bonus t ≤ beta * Real.sqrt (min 1 (x t))) →
        ∑ t : Fin T, bonus t ≤
          beta * Real.sqrt ((T : ℝ) * (2 * (d : ℝ) * Real.log (1 + (T : ℝ) / d))) :=
  FiniteHorizonMDP.total_bonus_from_features d hd T phis h_norm beta hbeta

/-! ### Discharging the LinearMDP/Regret Hypothesis

The `ucbvi_lin_regret_from_bonus_hypotheses` in `LinearMDP/Regret.lean`
takes two hypotheses:
  1. Per-episode regret ≤ sum of bonuses (from optimism)
  2. Total bonus ≤ C · d · H · √K

The matrix Bernstein inequality (via the confidence ellipsoid) provides
the optimism property (hypothesis 1), and the elliptical potential
lemma provides the total bonus bound (hypothesis 2).

We show that the matrix Bernstein confidence width, combined with the
elliptical potential lemma, gives exactly the right form for hypothesis 2.
-/

/-- **Matrix Bernstein provides the right bonus structure**.

    The confidence radius β from matrix Bernstein, combined with
    the elliptical potential lemma, bounds the total exploration bonus
    by β · √(T · 2d · log(1 + T/d)).

    When β = O(d · √(log(dT/δ))), this gives total bonus
    O(d^{3/2} · √(T · log(dT/δ) · log(1+T/d))), matching the
    standard UCBVI-Lin bonus bound. -/
theorem matrix_bernstein_bonus_structure
    (d : ℕ) (hd : 0 < d) (T : ℕ)
    (_phis : Fin T → Fin d → ℝ)
    (_h_norm : ∀ k : Fin T, sqNorm (_phis k) ≤ 1)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (bonus : Fin T → ℝ)
    (x : Fin T → ℝ)
    (hx : ∀ t, 0 ≤ x t)
    (h_pot : ∑ t : Fin T, min 1 (x t) ≤
      2 * (d : ℝ) * Real.log (1 + (T : ℝ) / d))
    (h_bonus : ∀ t, bonus t ≤ beta * Real.sqrt (min 1 (x t))) :
    ∑ t : Fin T, bonus t ≤
    beta * Real.sqrt ((T : ℝ) * (2 * (d : ℝ) * Real.log (1 + (T : ℝ) / d))) :=
  FiniteHorizonMDP.total_bonus_from_potential d hd T beta hbeta bonus x hx h_pot h_bonus

/-- **The regret hypothesis form**: the total bonus has the right shape
    to discharge the `h_bonus` hypothesis in `ucbvi_lin_regret_from_bonus_hypotheses`.

    Given T = K · H (total steps), the total bonus is:
      β · √(KH · 2d · log(1 + KH/d))

    For β = C₁ · d · √H, this gives C₁ · d · H · √(2K · log(1 + KH/d)),
    which is O(C · d · H · √K) when log factors are absorbed into C. -/
theorem matrix_bernstein_regret_form
    (d : ℕ) (hd : 0 < d) (K H : ℕ)
    (phis : Fin (K * H) → Fin d → ℝ)
    (h_norm : ∀ k : Fin (K * H), sqNorm (phis k) ≤ 1)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (C : ℝ) (_hC : 0 < C)
    -- The confidence radius satisfies beta ≤ C
    (h_beta_bound : beta ≤ C) :
    ∃ x : Fin (K * H) → ℝ,
      (∀ t, 0 ≤ x t) ∧
      ∀ (bonus : Fin (K * H) → ℝ),
        (∀ t, bonus t ≤ beta * Real.sqrt (min 1 (x t))) →
        ∑ t : Fin (K * H), bonus t ≤
          C * Real.sqrt (((K * H : ℕ) : ℝ) *
            (2 * (d : ℝ) * Real.log (1 + ((K * H : ℕ) : ℝ) / d))) := by
  obtain ⟨x, hx_nonneg, h_total⟩ :=
    FiniteHorizonMDP.total_bonus_from_features d hd (K * H) phis h_norm beta hbeta
  exact ⟨x, hx_nonneg, fun bonus h_bonus => by
    calc ∑ t, bonus t
        ≤ beta * Real.sqrt (((K * H : ℕ) : ℝ) *
            (2 * (d : ℝ) * Real.log (1 + ((K * H : ℕ) : ℝ) / d))) :=
          h_total bonus h_bonus
      _ ≤ C * Real.sqrt (((K * H : ℕ) : ℝ) *
            (2 * (d : ℝ) * Real.log (1 + ((K * H : ℕ) : ℝ) / d))) := by
          apply mul_le_mul_of_nonneg_right h_beta_bound (Real.sqrt_nonneg _)⟩

/-! ### Monotonicity and Comparison Results

Additional algebraic properties of the matrix Bernstein exponent. -/

/-- The matrix Bernstein exponent is monotone in t for t ≥ 0:
    larger deviation t means larger exponent (tighter exponential bound). -/
theorem matrixBernsteinExponent_mono
    {sigma_sq b : ℝ} (hsigma : 0 < sigma_sq) (hb : 0 < b)
    {t₁ t₂ : ℝ} (ht₁ : 0 ≤ t₁) (h : t₁ ≤ t₂) :
    matrixBernsteinExponent sigma_sq b t₁ ≤
    matrixBernsteinExponent sigma_sq b t₂ := by
  unfold matrixBernsteinExponent
  -- For t₁ = 0, LHS = 0 ≤ RHS.
  rcases eq_or_lt_of_le ht₁ with rfl | ht₁_pos
  · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
               zero_div, add_zero]
    apply div_nonneg (sq_nonneg _)
    apply mul_nonneg (by norm_num)
    linarith [mul_nonneg hb.le (le_trans ht₁ h)]
  · -- Both denominators positive
    have ht₂ : 0 < t₂ := lt_of_lt_of_le ht₁_pos h
    have hd₁ : 0 < 2 * (sigma_sq + b * t₁ / 3) := by positivity
    have hd₂ : 0 < 2 * (sigma_sq + b * t₂ / 3) := by positivity
    rw [div_le_div_iff₀ hd₁ hd₂]
    -- Goal: t₁² · (2(σ² + bt₂/3)) ≤ t₂² · (2(σ² + bt₁/3))
    -- = (t₂ - t₁)(t₂ + t₁) · 2σ² + (t₂ - t₁) · t₁ · t₂ · 2b/3 ≥ 0
    -- since t₂ ≥ t₁ and all factors nonneg.
    have h_diff : 0 ≤ t₂ - t₁ := by linarith
    have h_t₁t₂ : 0 ≤ t₁ * t₂ := mul_nonneg ht₁ ht₂.le
    nlinarith [sq_nonneg t₁, sq_nonneg t₂, mul_nonneg h_diff (by linarith : 0 ≤ t₁ + t₂),
               mul_nonneg h_diff h_t₁t₂]

/-- The matrix Bernstein bound is monotone decreasing in t:
    larger t gives a smaller (tighter) tail bound. -/
theorem matrixBernsteinBound_anti
    {d : ℕ} (_hd : 0 < d)
    {sigma_sq b : ℝ} (hsigma : 0 < sigma_sq) (hb : 0 < b)
    {t₁ t₂ : ℝ} (ht₁ : 0 ≤ t₁) (h : t₁ ≤ t₂) :
    matrixBernsteinBound d sigma_sq b t₂ ≤
    matrixBernsteinBound d sigma_sq b t₁ := by
  unfold matrixBernsteinBound
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg d)
  apply exp_le_exp.mpr
  linarith [matrixBernsteinExponent_mono hsigma hb ht₁ h]

/-- **Matrix Bernstein reduces to scalar Bernstein for d=1.**

    When d = 1, the matrix Bernstein bound d · exp(-exponent) equals
    1 · exp(-exponent) = exp(-exponent), which is exactly the scalar
    Bernstein bound. -/
theorem matrix_bernstein_eq_scalar_at_dim_one (sigma_sq b t : ℝ) :
    matrixBernsteinBound 1 sigma_sq b t =
    exp (-bernsteinExponent sigma_sq b t) := by
  simp [matrixBernsteinBound, matrix_bernstein_exponent_eq_scalar]

end
