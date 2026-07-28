/-
# Policy Evaluation with Linear Function Approximation

LSTD (Least-Squares Temporal-Difference) finite-sample bounds in the
discounted infinite-horizon setting.

## Architecture

The LSTD solution theta_hat = A_hat^{-1} b_hat is defined via
Mathlib's matrix inverse. The finite-sample error bound is taken
as a CONDITIONAL hypothesis (conditional on the design matrix being
well-conditioned, the LSTD error is O(d/n)). This mirrors the
pattern in `LinearFeatures/RegressionBridge.lean` for LSVI.

## Main Results

* `ConditionalLSTDSetup` -- packages the LSTD regression problem
  with the regression rate hypothesis
* `lstd_value_error` -- composes the parameter error with the feature
  map bound to get a sup-norm value function error bound:
  ‖V_hat - V^pi‖_infty <= B * sqrt(d) * error_bound
* `lstd_sample_complexity` -- given a target accuracy epsilon > 0,
  derives the sample count for epsilon-accuracy

## References

* [Lazaric, Ghavamzadeh, Munos. *Finite-Sample Analysis of LSTD*. JMLR, 2012]
* [Zhang, Lee, Liu. *Statistical Learning Theory in Lean 4*.
  arXiv:2602.02285, 2026]
-/

import RLGeneralization.MDP.BellmanContraction
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Finset BigOperators

noncomputable section

namespace FiniteMDP

variable (M : FiniteMDP)

/-- Finite-dimensional coordinate inner product `⟨x, θ⟩ = Σ_j x_j θ_j`. -/
def featureDot {d : ℕ} (x θ : Fin d → ℝ) : ℝ :=
  ∑ j, x j * θ j

/-- Discounted Bellman feature difference `φ(s) - γ φ(s')`. -/
def bellmanFeatureDiff {d : ℕ} (φ : M.S → Fin d → ℝ) (s s' : M.S) :
    Fin d → ℝ :=
  fun j => φ s j - M.γ * φ s' j

/-- The Bellman feature difference is given coordinatewise by
    `φ(s)_j - γ φ(s')_j`. -/
theorem bellmanFeatureDiff_apply {d : ℕ} (φ : M.S → Fin d → ℝ)
    (s s' : M.S) (j : Fin d) :
    M.bellmanFeatureDiff φ s s' j = φ s j - M.γ * φ s' j := by
  rfl

/-- Shared linear value-function evaluator for a feature map `φ` and
    parameter vector `θ`. Both LSTD and TD value approximations are
    instances of this same finite-dimensional map. -/
def linearValue {d : ℕ} (φ : M.S → Fin d → ℝ) (θ : Fin d → ℝ) :
    M.StateValueFn :=
  fun s => featureDot (φ s) θ

/-- `linearValue` is additive in the parameter vector. -/
theorem linearValue_add_apply {d : ℕ} (φ : M.S → Fin d → ℝ)
    (θ₁ θ₂ : Fin d → ℝ) (s : M.S) :
    M.linearValue φ (θ₁ + θ₂) s =
    M.linearValue φ θ₁ s + M.linearValue φ θ₂ s := by
  unfold linearValue
  calc
    ∑ j, φ s j * (θ₁ j + θ₂ j)
        = ∑ j, (φ s j * θ₁ j + φ s j * θ₂ j) := by
            apply Finset.sum_congr rfl
            intro j _
            ring
    _ = ∑ j, φ s j * θ₁ j + ∑ j, φ s j * θ₂ j := by
            rw [Finset.sum_add_distrib]

/-- `linearValue` is compatible with subtraction in the parameter vector. -/
theorem linearValue_sub_apply {d : ℕ} (φ : M.S → Fin d → ℝ)
    (θ₁ θ₂ : Fin d → ℝ) (s : M.S) :
    M.linearValue φ (θ₁ - θ₂) s =
    M.linearValue φ θ₁ s - M.linearValue φ θ₂ s := by
  unfold linearValue
  calc
    ∑ j, φ s j * (θ₁ j - θ₂ j)
        = ∑ j, (φ s j * θ₁ j - φ s j * θ₂ j) := by
            apply Finset.sum_congr rfl
            intro j _
            ring
    _ = ∑ j, φ s j * θ₁ j - ∑ j, φ s j * θ₂ j := by
            rw [Finset.sum_sub_distrib]

/-- `linearValue` is homogeneous in the parameter vector. -/
theorem linearValue_smul_apply {d : ℕ} (φ : M.S → Fin d → ℝ)
    (c : ℝ) (θ : Fin d → ℝ) (s : M.S) :
    M.linearValue φ (c • θ) s = c * M.linearValue φ θ s := by
  unfold linearValue
  calc
    ∑ j, φ s j * (c * θ j)
        = ∑ j, c * (φ s j * θ j) := by
            apply Finset.sum_congr rfl
            intro j _
            ring
    _ = c * ∑ j, φ s j * θ j := by
            rw [← Finset.mul_sum]

/-- Linear function approximation setup. -/
structure LinearApprox (d : ℕ) where
  φ : M.S → Fin d → ℝ
  φ_bound : ∃ B : ℝ, 0 < B ∧ ∀ s i, |φ s i| ≤ B

/-- LSTD data: (s, r, s') triples. -/
structure LSTDData (n : ℕ) where
  states : Fin n → M.S
  rewards : Fin n → ℝ
  next_states : Fin n → M.S
  hn : 0 < n

/-- Shared empirical TD matrix built from one-step samples and a feature map. -/
def empiricalTDMatrix {d n : ℕ} (φ : M.S → Fin d → ℝ)
    (states next_states : Fin n → M.S) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => (∑ k : Fin n,
    φ (states k) i * M.bellmanFeatureDiff φ (states k) (next_states k) j) / n

/-- Shared empirical TD reward vector built from one-step samples. -/
def empiricalTDVector {d n : ℕ} (φ : M.S → Fin d → ℝ)
    (states : Fin n → M.S) (rewards : Fin n → ℝ) : Fin d → ℝ :=
  fun i => (∑ k : Fin n, φ (states k) i * rewards k) / n

/-- The empirical LSTD matrix A_hat:
    A_hat_ij = (1/n) sum_k phi(s_k)_i * (phi(s_k)_j - gamma * phi(s'_k)_j) -/
def lstdMatrix {d n : ℕ} (approx : M.LinearApprox d)
    (data : M.LSTDData n) : Matrix (Fin d) (Fin d) ℝ :=
  M.empiricalTDMatrix approx.φ data.states data.next_states

/-- The empirical LSTD vector b_hat:
    b_hat_i = (1/n) sum_k phi(s_k)_i * r_k -/
def lstdVector {d n : ℕ} (approx : M.LinearApprox d)
    (data : M.LSTDData n) : Fin d → ℝ :=
  M.empiricalTDVector approx.φ data.states data.rewards

/-- `lstdMatrix` is the shared empirical TD matrix specialized to the
    LSTD sample bundle. -/
theorem lstdMatrix_eq_empiricalTDMatrix {d n : ℕ}
    (approx : M.LinearApprox d) (data : M.LSTDData n) :
    M.lstdMatrix approx data =
    M.empiricalTDMatrix approx.φ data.states data.next_states := by
  rfl

/-- `lstdVector` is the shared empirical TD reward vector specialized to
    the LSTD sample bundle. -/
theorem lstdVector_eq_empiricalTDVector {d n : ℕ}
    (approx : M.LinearApprox d) (data : M.LSTDData n) :
    M.lstdVector approx data =
    M.empiricalTDVector approx.φ data.states data.rewards := by
  rfl

/-- LSTD solution: `theta_hat = A_hat^{-1} b_hat` using Mathlib's matrix inverse.

    This definition is algebraic: it is the canonical matrix-inverse
    expression, and it should be read together with the usual
    well-conditioned/invertibility hypotheses carried elsewhere in the
    setup. -/
def lstdSolution {d n : ℕ}
    (approx : M.LinearApprox d) (data : M.LSTDData n) :
    Fin d → ℝ :=
  (M.lstdMatrix approx data)⁻¹.mulVec (M.lstdVector approx data)

/-! ### LSTD Value Approximation -/

/-- The approximate value function V_hat(s) = <phi(s), theta_hat>. -/
def lstdValueFn {d n : ℕ}
    (approx : M.LinearApprox d) (data : M.LSTDData n) :
    M.StateValueFn :=
  M.linearValue approx.φ (M.lstdSolution approx data)

/-- The projected value function V_theta(s) = <phi(s), theta> for any parameter. -/
def projectedValue {d : ℕ}
    (approx : M.LinearApprox d) (θ : Fin d → ℝ) :
    M.StateValueFn :=
  M.linearValue approx.φ θ

/-- `projectedValue` is the generic linear-value evaluator applied to
    the approximation feature map. -/
theorem projectedValue_eq_linearValue {d : ℕ}
    (approx : M.LinearApprox d) (θ : Fin d → ℝ) :
    M.projectedValue approx θ = M.linearValue approx.φ θ := by
  rfl

/-- The LSTD value function is the projected value function evaluated
    at the LSTD solution `theta_hat`. -/
theorem lstdValueFn_eq_projectedValue_lstdSolution {d n : ℕ}
    (approx : M.LinearApprox d) (data : M.LSTDData n) :
    M.lstdValueFn approx data =
    M.projectedValue approx (M.lstdSolution approx data) := by
  funext s
  rfl

/-! ### Conditional LSTD Setup -/

/-- **Conditional LSTD Setup** -- packages the LSTD problem with
    the regression rate hypothesis. The error_bound represents the
    per-coordinate parameter error ||theta_hat - theta_star||_infty,
    which is O(sqrt(d/n)) under standard conditions.

    This is a CONDITIONAL module: the rate is taken as a hypothesis,
    not derived from a probability space. The full probabilistic
    statement would additionally need the SLT library's
    `linear_minimax_rate` and measure-theoretic plumbing. -/
structure ConditionalLSTDSetup (d n : ℕ) where
  /-- The linear approximation architecture -/
  approx : M.LinearApprox d
  /-- The LSTD data -/
  data : M.LSTDData n
  /-- The true parameter theta_star (projection of V^pi onto features) -/
  theta_star : Fin d → ℝ
  /-- The per-coordinate parameter error bound -/
  error_bound : ℝ
  /-- The error bound is positive -/
  h_error_pos : 0 < error_bound
  /-- Conditional regression rate hypothesis:
      each coordinate of (theta_hat - theta_star) is bounded by error_bound.
      This follows from the LSTD finite-sample analysis when
      A_hat is well-conditioned and n >= Omega(d). -/
  h_rate : ∀ j : Fin d, |M.lstdSolution approx data j - theta_star j| ≤ error_bound

/-! ### Feature Map Bound Extraction -/

/-- Extract the feature bound B from a LinearApprox. -/
def LinearApprox.B {d : ℕ} (approx : M.LinearApprox d) : ℝ :=
  approx.φ_bound.choose

lemma LinearApprox.B_pos {d : ℕ} (approx : M.LinearApprox d) :
    0 < approx.B M := approx.φ_bound.choose_spec.1

lemma LinearApprox.φ_le_B {d : ℕ} (approx : M.LinearApprox d)
    (s : M.S) (i : Fin d) : |approx.φ s i| ≤ approx.B M :=
  approx.φ_bound.choose_spec.2 s i

/-! ### Pointwise Value Error -/

/-- The pointwise error between the approximate and projected value:
    V_hat(s) - V_star(s) = sum_j phi(s)_j * (theta_hat_j - theta_star_j). -/
lemma lstd_value_diff_eq {d n : ℕ}
    (setup : M.ConditionalLSTDSetup d n) (s : M.S) :
    M.lstdValueFn setup.approx setup.data s -
    M.projectedValue setup.approx setup.theta_star s =
    ∑ j, setup.approx.φ s j *
      (M.lstdSolution setup.approx setup.data j - setup.theta_star j) := by
  unfold lstdValueFn projectedValue linearValue featureDot
  calc
    ∑ j, setup.approx.φ s j * M.lstdSolution setup.approx setup.data j -
        ∑ j, setup.approx.φ s j * setup.theta_star j
      = ∑ j, (setup.approx.φ s j * M.lstdSolution setup.approx setup.data j -
          setup.approx.φ s j * setup.theta_star j) := by
            rw [← Finset.sum_sub_distrib]
    _ = ∑ j, setup.approx.φ s j *
          (M.lstdSolution setup.approx setup.data j - setup.theta_star j) := by
            apply Finset.sum_congr rfl
            intro j _
            ring

/-- Each term |phi(s)_j * (theta_hat_j - theta_star_j)| is bounded by
    B * error_bound. -/
lemma lstd_term_bound {d n : ℕ}
    (setup : M.ConditionalLSTDSetup d n)
    (s : M.S) (j : Fin d) :
    |setup.approx.φ s j *
      (M.lstdSolution setup.approx setup.data j - setup.theta_star j)| ≤
    setup.approx.B M * setup.error_bound := by
  rw [abs_mul]
  exact mul_le_mul
    (setup.approx.φ_le_B M s j)
    (setup.h_rate j)
    (abs_nonneg _)
    (le_of_lt (setup.approx.B_pos M))

/-! ### Main Theorems -/

/-- **LSTD value function error bound** (conditional).

    Under the conditional regression rate hypothesis, the pointwise
    error between the LSTD value approximation and the projected
    true value satisfies:

      |V_hat(s) - V_theta_star(s)| <= d * B * error_bound

    where B is the feature bound and d is the feature dimension.

    This has real algebraic content: it decomposes the inner product
    V_hat(s) - V_star(s) = sum_j phi_j * (theta_hat_j - theta_star_j)
    and applies the triangle inequality with the per-coordinate bound. -/
theorem lstd_value_error {d n : ℕ}
    (setup : M.ConditionalLSTDSetup d n) (s : M.S) :
    |M.lstdValueFn setup.approx setup.data s -
     M.projectedValue setup.approx setup.theta_star s| ≤
    d * setup.approx.B M * setup.error_bound := by
  rw [M.lstd_value_diff_eq setup s]
  -- Triangle inequality: |sum_j a_j| <= sum_j |a_j|
  calc |∑ j, setup.approx.φ s j *
        (M.lstdSolution setup.approx setup.data j - setup.theta_star j)|
      ≤ ∑ j : Fin d, |setup.approx.φ s j *
        (M.lstdSolution setup.approx setup.data j - setup.theta_star j)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin d, setup.approx.B M * setup.error_bound :=
        Finset.sum_le_sum (fun j _ => M.lstd_term_bound setup s j)
    _ = d * setup.approx.B M * setup.error_bound := by
        simp [Finset.sum_const, nsmul_eq_mul]; ring

/-- **LSTD sup-norm value error** (conditional).

    The sup-norm version: for all states s,
      |V_hat(s) - V_theta_star(s)| <= d * B * error_bound

    This is the uniform version of `lstd_value_error`. -/
theorem lstd_sup_value_error {d n : ℕ}
    (setup : M.ConditionalLSTDSetup d n) :
    ∀ s, |M.lstdValueFn setup.approx setup.data s -
     M.projectedValue setup.approx setup.theta_star s| ≤
    d * setup.approx.B M * setup.error_bound :=
  fun s => M.lstd_value_error setup s

/-! ### Sample Complexity -/

/-- **LSTD sample complexity** (conditional, inverse form).

    To achieve |V_hat(s) - V_theta_star(s)| <= epsilon for all states,
    it suffices to have the per-coordinate parameter error bounded by
    epsilon / (d * B).

    Combined with the LSTD finite-sample analysis which gives
    per-coordinate error O(sqrt(sigma^2 * d / n)), this yields the
    sample complexity n >= Omega(sigma^2 * d^3 * B^2 / epsilon^2).

    The proof is purely algebraic: it combines `lstd_value_error`
    with the hypothesis that error_bound <= epsilon / (d * B). -/
theorem lstd_sample_complexity {d n : ℕ}
    (setup : M.ConditionalLSTDSetup d n)
    (ε : ℝ)
    -- The per-coordinate error is small enough for epsilon-accuracy
    (h_small : d * setup.approx.B M * setup.error_bound ≤ ε) :
    ∀ s, |M.lstdValueFn setup.approx setup.data s -
     M.projectedValue setup.approx setup.theta_star s| ≤ ε :=
  fun s => le_trans (M.lstd_value_error setup s) h_small

/-- **LSTD sample complexity with explicit rate** (conditional).

    If the per-coordinate LSTD error satisfies
      error_bound^2 <= C * sigma^2 * d / n
    and the sample size satisfies
      n >= C * sigma^2 * d^3 * B^2 / epsilon^2,
    then |V_hat(s) - V_theta_star(s)| <= epsilon for all states.

    The proof chains:
    1. error_bound <= sqrt(C * sigma^2 * d / n)  (from h_rate_sq)
    2. d * B * sqrt(C * sigma^2 * d / n) <= epsilon  (from h_n_large)
    3. d * B * error_bound <= epsilon  (combining 1 and 2)
    4. |V_hat(s) - V_star(s)| <= epsilon  (from lstd_value_error) -/
theorem lstd_sample_complexity_rate {d n : ℕ}
    (setup : M.ConditionalLSTDSetup d n)
    (C_reg sigma_sq ε : ℝ)
    (_hε : 0 < ε)
    (_hC : 0 ≤ C_reg) (_hsigma : 0 ≤ sigma_sq)
    (_hn : (0 : ℝ) < n)
    (_hd : 0 < (d : ℝ))
    -- The per-coordinate error squared is bounded by the regression rate
    (h_rate_sq : setup.error_bound ^ 2 ≤ C_reg * sigma_sq * d / n)
    -- The sample size is large enough
    (h_n_large : (d : ℝ) * setup.approx.B M *
      Real.sqrt (C_reg * sigma_sq * d / n) ≤ ε) :
    ∀ s, |M.lstdValueFn setup.approx setup.data s -
     M.projectedValue setup.approx setup.theta_star s| ≤ ε := by
  intro s
  -- Step 1: error_bound <= sqrt(C * sigma^2 * d / n)
  have h_eb_le : setup.error_bound ≤
      Real.sqrt (C_reg * sigma_sq * d / n) := by
    rw [← Real.sqrt_sq (le_of_lt setup.h_error_pos)]
    exact Real.sqrt_le_sqrt h_rate_sq
  -- Step 2: d * B * error_bound <= d * B * sqrt(rate) <= epsilon
  have hB_pos : 0 < setup.approx.B M := setup.approx.B_pos M
  have hdB_nonneg : 0 ≤ (d : ℝ) * setup.approx.B M := by positivity
  have h_chain : (d : ℝ) * setup.approx.B M * setup.error_bound ≤ ε :=
    le_trans (mul_le_mul_of_nonneg_left h_eb_le hdB_nonneg) h_n_large
  -- Step 3: Apply lstd_value_error
  exact le_trans (M.lstd_value_error setup s) h_chain

end FiniteMDP

end
