/-
# Regression Bridge for LSVI

Connects LSVI to the Statistical Learning Theory library
(Zhang, Lee, Liu 2026) for linear regression error bounds.

## Architecture

The SLT library provides (now on Lean 4.28.0 / Mathlib v4.28.0):
- `LeastSquares.RegressionModel`: y_i = f*(x_i) + σw_i
- `LeastSquares.isLeastSquaresEstimator`: f̂ minimizes empirical squared error
- `LeastSquares.linear_minimax_rate`: ‖f̂ - f*‖²_n ≤ O(σ²d/n) w.h.p.
- `LeastSquares.empiricalNorm`: empirical L2 norm √(n⁻¹ Σ fᵢ²)
- `LeastSquares.linearPredictorClass`: the class of linear functions ⟨θ, ·⟩

This file re-exports the SLT definitions needed by our LSVI formalization
and provides a simplified interface (`HasLinearRegressionRate`) for use
in the regret bound proofs.

## References

* [Zhang, Lee, Liu. *Statistical Learning Theory in Lean 4*.
  arXiv:2602.02285, 2026]
-/

import RLGeneralization.LinearFeatures.LSVI
import SLT.LeastSquares.LinearRegression.MinimaxRate
import SLT.LeastSquares.Defs

open Finset BigOperators MeasureTheory GaussianMeasure

noncomputable section

/-! ### Re-exported SLT Definitions

The following are available via the SLT imports:
- `LeastSquares.RegressionModel` -- the regression model y_i = f*(x_i) + σw_i
- `LeastSquares.empiricalNorm` -- √(n⁻¹ Σ fᵢ²)
- `LeastSquares.isLeastSquaresEstimator` -- minimizer of empirical error
- `LeastSquares.linearPredictorClass` -- {f : x ↦ ⟨θ, x⟩ | θ ∈ ℝ^d}
- `LeastSquares.linear_minimax_rate` -- the O(σ²d/n) bound with high probability
-/

/-! ### Simplified Interface for LSVI -/

/-- A fixed-design regression model (simplified wrapper around SLT).

  y_i = f*(x_i) + noise_i for i = 1,...,n

  In the LSVI context:
  - x_i = φ(s_i, a_i) (feature vector)
  - f* = θ*ᵀφ (true regression function, under Bellman completeness)
  - y_i = r_h(s_i,a_i) + V̂_{h+1}(s'_i) (Bellman target)
  - noise = y_i - f*(x_i) (Bellman residual) -/
structure RegressionSetup (d n : ℕ) where
  /-- Feature vectors (design points) -/
  features : Fin n → Fin d → ℝ
  /-- Responses -/
  responses : Fin n → ℝ
  /-- True parameter -/
  theta_star : Fin d → ℝ
  /-- Noise scale -/
  sigma : ℝ
  hsigma : 0 < sigma

/-- The predicted value at design point i under parameter θ. -/
def RegressionSetup.predict {d n : ℕ}
    (reg : RegressionSetup d n) (theta : Fin d → ℝ)
    (i : Fin n) : ℝ :=
  ∑ j, reg.features i j * theta j

/-- Empirical squared error: (1/n) ∑ (ŷ_i - y_i)². -/
def RegressionSetup.empiricalError {d n : ℕ}
    (reg : RegressionSetup d n) (theta : Fin d → ℝ) : ℝ :=
  (∑ i, (reg.predict theta i - reg.responses i)^2) / n

/-- The least squares estimator minimizes empirical error. -/
def RegressionSetup.isLSE {d n : ℕ}
    (reg : RegressionSetup d n) (theta_hat : Fin d → ℝ) : Prop :=
  ∀ theta : Fin d → ℝ,
    reg.empiricalError theta_hat ≤ reg.empiricalError theta

/-! ### Linear Regression Rate (from SLT library) -/

/-- **Linear regression minimax rate** (simplified statement).

  For a linear regression model with d-dimensional features and
  n ≥ d data points, the LSE satisfies with high probability:

    (1/n) ∑ (f̂(x_i) - f*(x_i))² ≤ C · σ² · d / n

  The full probabilistic version is `LeastSquares.linear_minimax_rate`
  from the SLT library. This simplified deterministic version is used
  as a hypothesis in the LSVI regret bound. -/
def HasLinearRegressionRate (d n : ℕ) (C sigma_sq : ℝ) : Prop :=
  ∀ (reg : RegressionSetup d n) (theta_hat : Fin d → ℝ),
    reg.isLSE theta_hat →
    reg.empiricalError theta_hat ≤ C * sigma_sq * d / n

/-! ### LSVI-SLT Bridge: Type Adapters

The SLT library operates on `EuclideanSpace ℝ (Fin d)` (= `WithLp 2 (Fin d → ℝ)`),
while LSVI uses plain `Fin d → ℝ`. The adapter lifts feature vectors via
`(WithLp.equiv).symm`. -/

/-- Lift a plain `Fin d → ℝ` vector to `EuclideanSpace ℝ (Fin d)`.
    Computationally the identity; only changes the type wrapper. -/
def liftToEuclidean {d : ℕ} (v : Fin d → ℝ) : EuclideanSpace ℝ (Fin d) :=
  (WithLp.equiv 2 (Fin d → ℝ)).symm v

/-- Convert an `EuclideanSpace ℝ (Fin d)` vector back to `Fin d → ℝ`. -/
def fromEuclidean {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) : Fin d → ℝ :=
  (WithLp.equiv 2 (Fin d → ℝ)) v

@[simp] lemma fromEuclidean_liftToEuclidean {d : ℕ} (v : Fin d → ℝ) :
    fromEuclidean (liftToEuclidean v) = v := by
  simp [fromEuclidean, liftToEuclidean]

@[simp] lemma liftToEuclidean_fromEuclidean {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) :
    liftToEuclidean (fromEuclidean v) = v := by
  simp [fromEuclidean, liftToEuclidean]

lemma liftToEuclidean_apply {d : ℕ} (v : Fin d → ℝ) (j : Fin d) :
    (liftToEuclidean v) j = v j := rfl

/-- The inner product of EuclideanSpace vectors equals the dot product. -/
lemma inner_liftToEuclidean {d : ℕ} (θ v : Fin d → ℝ) :
    @inner ℝ _ _ (liftToEuclidean θ) (liftToEuclidean v) = ∑ j, θ j * v j := by
  simp only [liftToEuclidean, EuclideanSpace.inner_eq_star_dotProduct]
  simp [star_trivial, dotProduct, mul_comm]

/-! ### Per-Stage Regression Model Construction -/

/-- Construct an SLT `RegressionModel` from LSVI per-stage data.
    Lifts feature vectors to `EuclideanSpace` and sets the true
    regression function to `f*(x) = inner(theta_star, x)`. -/
def lsviStageRegressionModel {d n : ℕ}
    (features : Fin n → Fin d → ℝ)
    (theta_star : Fin d → ℝ)
    (sigma : ℝ) (hsigma : 0 < sigma) :
    LeastSquares.RegressionModel n (EuclideanSpace ℝ (Fin d)) where
  x := fun i => liftToEuclidean (features i)
  f_star := fun v => @inner ℝ _ _ (liftToEuclidean theta_star) v
  σ := sigma
  hσ_pos := hsigma

/-- The f_star of the LSVI regression model is a linear predictor. -/
lemma lsviStageRegressionModel_f_star_mem {d n : ℕ}
    (features : Fin n → Fin d → ℝ)
    (theta_star : Fin d → ℝ)
    (sigma : ℝ) (hsigma : 0 < sigma) :
    (lsviStageRegressionModel features theta_star sigma hsigma).f_star ∈
      LeastSquares.linearPredictorClass d :=
  ⟨liftToEuclidean theta_star, rfl⟩

/-- The predicted value equals `theta_star^T phi_i` (the dot product). -/
lemma lsviStageRegressionModel_predict {d n : ℕ}
    (features : Fin n → Fin d → ℝ)
    (theta_star : Fin d → ℝ)
    (sigma : ℝ) (hsigma : 0 < sigma) (i : Fin n) :
    (lsviStageRegressionModel features theta_star sigma hsigma).f_star
      ((lsviStageRegressionModel features theta_star sigma hsigma).x i) =
    ∑ j, theta_star j * features i j := by
  simp only [lsviStageRegressionModel]
  rw [inner_liftToEuclidean]

/-! ### LSVI Sample Complexity -/

open FiniteHorizonMDP in
/-- **LSVI policy gap with a supplied regression rate**.

  Under Bellman completeness with d-dimensional linear features
  and n samples per stage, if the per-stage Bellman residual
  satisfies eta^2 <= C*sigma^2*d/n (from the linear minimax
  rate), then the policy gap satisfies:

    V*_H(s) - V^{pi_hat}_H(s) <= 2H^2 * sqrt(C * sigma^2 * d / n)

  The proof uses eta <= sqrt(C*sigma^2*d/n) combined with
  `policy_value_gap`.

  **Caveat**: The hypothesis eta^2 <= C*sigma^2*d/n is taken
  directly rather than derived from `LeastSquares.linear_minimax_rate`.
  The full probabilistic chain (with confidence delta) would
  require measure-theoretic plumbing. -/
theorem lsvi_sample_complexity_rate
    (M : FiniteHorizonMDP)
    (approx : M.ApproxBackwardQ)
    (C_reg : ℝ) (sigma_sq : ℝ) (d n : ℕ)
    (_hC : 0 ≤ C_reg) (_hsigma : 0 ≤ sigma_sq)
    (_hn : (0 : ℝ) < n)
    -- The regression rate bounds the per-stage residual:
    -- η² ≤ C·σ²·d/n (from SLT's linear_minimax_rate)
    (h_rate : approx.η ^ 2 ≤ C_reg * sigma_sq * d / n)
    (s : M.S) :
    M.optimalValueFn M.H le_rfl s -
    M.greedyValueFn approx M.H le_rfl s ≤
      2 * (M.H : ℝ) ^ 2 * Real.sqrt (C_reg * sigma_sq * d / n) := by
  have h_core := M.policy_value_gap approx s
  have hη := approx.hη
  -- η ≤ √(C·σ²·d/n) since η ≥ 0 and η² ≤ C·σ²·d/n
  have h_eta_le : approx.η ≤ Real.sqrt (C_reg * sigma_sq * d / n) := by
    rw [← Real.sqrt_sq hη]
    exact Real.sqrt_le_sqrt h_rate
  have hH2 : (0 : ℝ) ≤ 2 * (M.H : ℝ) ^ 2 := by positivity
  linarith [mul_le_mul_of_nonneg_left h_eta_le hH2]

open FiniteHorizonMDP in
/-- **LSVI sample complexity, inverse form**.

  To achieve V*_H(s) - V^{π̂}_H(s) ≤ ε, it suffices to have
  per-stage Bellman residual η ≤ ε / (2H²).

  Combined with the regression rate η² ≤ C·σ²·d/n, this yields
  the sample complexity:
    n ≥ 4·C·H⁴·σ²·d / ε²

  This theorem states the inverse form: given a target accuracy ε > 0
  and per-stage residual η ≤ ε / (2H²), the policy gap is at most ε. -/
theorem lsvi_sample_complexity_inverse
    (M : FiniteHorizonMDP)
    (approx : M.ApproxBackwardQ)
    (ε : ℝ) (hε : 0 < ε)
    (hH : 0 < M.H)
    -- Per-stage residual is small enough
    (h_eta_small : approx.η ≤ ε / (2 * (M.H : ℝ) ^ 2))
    (s : M.S) :
    M.optimalValueFn M.H le_rfl s -
    M.greedyValueFn approx M.H le_rfl s ≤ ε := by
  have h_core := M.policy_value_gap approx s
  have hH2_pos : (0 : ℝ) < 2 * (M.H : ℝ) ^ 2 := by positivity
  calc M.optimalValueFn M.H le_rfl s -
        M.greedyValueFn approx M.H le_rfl s
      ≤ 2 * (M.H : ℝ) ^ 2 * approx.η := h_core
    _ ≤ 2 * (M.H : ℝ) ^ 2 * (ε / (2 * (M.H : ℝ) ^ 2)) := by
        apply mul_le_mul_of_nonneg_left h_eta_small (le_of_lt hH2_pos)
    _ = ε := by field_simp

open FiniteHorizonMDP in
/-- **Deterministic LSVI sample-complexity reduction**.

  If the per-stage Bellman residual satisfies η² ≤ C·σ²·d/n and
  the sample size satisfies n ≥ 4CH⁴σ²d/ε², then:
    V*_H(s) - V^π̂_H(s) ≤ ε

  **Caveat**: This is purely DETERMINISTIC. The hypothesis
  `h_rate : approx.η² ≤ Cσ²d/n` is taken directly — it is not
  derived from a probability space via `HasLinearRegressionRate`
  or the SLT library. The full probabilistic statement would
  additionally need a probability space and high-probability event. -/
theorem lsvi_sample_complexity
    (M : FiniteHorizonMDP)
    (approx : M.ApproxBackwardQ)
    (C_reg : ℝ) (sigma_sq : ℝ) (d n : ℕ)
    (ε : ℝ)
    (hε : 0 < ε)
    (_hC : 0 < C_reg) (_hsigma : 0 ≤ sigma_sq)
    (hH : 0 < M.H)
    (hn : (0 : ℝ) < n)
    -- The regression rate bounds the per-stage residual
    (h_rate : approx.η ^ 2 ≤ C_reg * sigma_sq * d / n)
    -- The sample size is large enough
    (h_n_large : 4 * C_reg * (M.H : ℝ) ^ 4 * sigma_sq * d / ε ^ 2 ≤ n)
    (s : M.S) :
    M.optimalValueFn M.H le_rfl s -
    M.greedyValueFn approx M.H le_rfl s ≤ ε := by
  -- Step 1: From h_n_large, derive C·σ²·d/n ≤ ε²/(4H⁴)
  -- Step 2: From h_rate, derive η² ≤ ε²/(4H⁴)
  -- Step 3: Therefore η ≤ ε/(2H²) (taking square roots)
  -- Step 4: Apply lsvi_sample_complexity_inverse
  apply lsvi_sample_complexity_inverse M approx ε hε hH _ s
  -- Need to show: approx.η ≤ ε / (2 * ↑M.H ^ 2)
  have hH2_pos : (0 : ℝ) < 2 * (M.H : ℝ) ^ 2 := by positivity
  have hη := approx.hη
  -- Strategy: show η² ≤ (ε/(2H²))², then take sqrt
  have h_rate_ub : C_reg * sigma_sq * ↑d / ↑n ≤
      ε ^ 2 / (4 * (↑M.H) ^ 4) := by
    -- From h_n_large: 4CH⁴σ²d/ε² ≤ n
    -- Multiply both sides by ε²/(n·4H⁴): Cσ²d/n ≤ ε²/(4H⁴)
    have h4H4_pos : (0 : ℝ) < 4 * (↑M.H) ^ 4 := by positivity
    rw [div_le_div_iff₀ hn h4H4_pos]
    -- Goal: C_reg * sigma_sq * ↑d * (4 * ↑M.H ^ 4) ≤ ε ^ 2 * ↑n
    -- From h_n_large: 4 * C_reg * ↑M.H ^ 4 * sigma_sq * ↑d / ε ^ 2 ≤ ↑n
    have hε2 : (0 : ℝ) < ε ^ 2 := by positivity
    have h1 : 4 * C_reg * (↑M.H) ^ 4 * sigma_sq * ↑d ≤ ↑n * ε ^ 2 := by
      rw [div_le_iff₀ hε2] at h_n_large
      linarith
    nlinarith
  have h_target_sq : approx.η ^ 2 ≤ (ε / (2 * (M.H : ℝ) ^ 2)) ^ 2 := by
    calc approx.η ^ 2 ≤ C_reg * sigma_sq * ↑d / ↑n := h_rate
      _ ≤ ε ^ 2 / (4 * (↑M.H) ^ 4) := h_rate_ub
      _ = (ε / (2 * (↑M.H) ^ 2)) ^ 2 := by
          rw [div_pow]; ring_nf
  -- η ≤ ε/(2H²) from η² ≤ target² and target ≥ 0
  have h_target_nonneg : 0 ≤ ε / (2 * (M.H : ℝ) ^ 2) := by positivity
  exact le_of_sq_le_sq h_target_sq h_target_nonneg

/-! ### LSVI Linear Setup -/

/-- **LSVI Linear Setup** -- bundles the structural assumptions used
    in the LSVI PAC argument into a single structure. -/
structure LSVILinearSetup (M : FiniteHorizonMDP) where
  /-- Feature dimension -/
  d : ℕ
  /-- Feature map: phi(s,a) is a d-dimensional vector -/
  phi : M.S → M.A → Fin d → ℝ
  /-- Feature vectors are bounded -/
  phi_bound : ℝ
  h_phi_bound_pos : 0 < phi_bound
  h_phi_bounded : ∀ (s : M.S) (a : M.A) (j : Fin d),
    |phi s a j| ≤ phi_bound
  /-- **Bellman completeness** for the linear feature class. -/
  bellman_complete :
    ∀ (h : Fin M.H) (theta : Fin d → ℝ),
    ∃ theta' : Fin d → ℝ, ∀ (s : M.S) (a : M.A),
      M.r h s a + ∑ s', M.P h s a s' *
        Finset.univ.sup' Finset.univ_nonempty
          (fun a' => ∑ j, theta (j) * phi s' a' j) =
      ∑ j, theta' j * phi s a j
  /-- Regression constant from SLT minimax rate (C > 0) -/
  C_reg : ℝ
  hC_reg : 0 < C_reg
  /-- Noise variance bound (sigma^2 >= 0) -/
  sigma_sq : ℝ
  hsigma_sq : 0 ≤ sigma_sq

/-! ### LSVI-SLT Bridge: Connecting linear_minimax_rate to LSVI -/

open LeastSquares in
/-- **SLT probabilistic guarantee applied to an LSVI stage** (model form).

This is the direct application of the SLT library's `linear_minimax_rate`
to a regression model. The user constructs the model from LSVI per-stage
data (possibly via `lsviStageRegressionModel`) and provides it here.

Output: exists C_1 C_2 > 0 such that with probability >= 1 - exp(-C_2*d),
the squared empirical prediction error is <= C_1*sigma^2*d/n. -/
theorem lsvi_stage_slt_bound {d n : ℕ} (hn : 0 < n) (hd : 0 < d)
    (M : RegressionModel n (EuclideanSpace ℝ (Fin d)))
    (hf_star : M.f_star ∈ linearPredictorClass d)
    (hinj : Function.Injective (designMatrixMul M.x))
    (f_hat : (Fin n → ℝ) → (EuclideanSpace ℝ (Fin d) → ℝ))
    (hf_hat : ∀ w, isLeastSquaresEstimator
      (M.response w) (linearPredictorClass d) M.x (f_hat w)) :
    ∃ C₁ C₂ : ℝ, C₁ > 0 ∧ C₂ > 0 ∧
      (stdGaussianPi n
        {w | (empiricalNorm n
          (fun i => f_hat w (M.x i) - M.f_star (M.x i)))^2 ≤
          C₁ * M.σ ^ 2 * d / n}).toReal ≥
        1 - Real.exp (-C₂ * d) :=
  linear_minimax_rate hn hd M hf_star hinj f_hat hf_hat

end
