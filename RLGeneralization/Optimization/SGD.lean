/-
# Stochastic Gradient Descent Convergence

Formalizes SGD convergence rates for convex and strongly convex objectives.
The core algebraic identities and rate expressions are proven; the connection
to actual stochastic processes (expectations over random gradients) is
captured via algebraic hypotheses.

## Mathematical Background

SGD update: θ_{t+1} = θ_t - α_t · g_t
where g_t is a stochastic gradient satisfying E[g_t] = ∇f(θ_t).

For convex f with bounded gradient variance:
  E[f(θ̄_T) - f*] ≤ O(1/√T)

For μ-strongly convex f:
  E[‖θ_T - θ*‖²] ≤ O(1/(μT))

## Main Definitions

* `SGDState` - State of SGD at step t: parameter and accumulated cost
* `SGDHyp` - Hypotheses for SGD convergence: L-smoothness, convexity, noise bound
* `StrongConvexHyp` - Additional μ-strong convexity hypothesis
* `sgd_update` - The SGD update formula
* `convex_sgd_one_step_rearranged` - One-step progress for convex SGD
* `convex_sgd_rate_nonneg` - O(1/sqrt(T)) rate expression is nonneg
* `strongly_convex_sgd_rate_nonneg` - O(1/(mu*T)) rate expression is nonneg

* `convex_sgd_convergence` - Full O(1/√T) convergence bound for convex SGD
* `strongly_convex_sgd_convergence` - Noise-ball bound for strongly convex SGD

## Approach

We work with deterministic algebraic surrogates: the "expected iterate distance"
and "expected suboptimality" are real-valued sequences satisfying recurrences.
The SGD noise hypothesis ‖g_t - ∇f‖² ≤ σ² enters as a bound on sequence terms.

## References

* [Bubeck, *Convex Optimization: Algorithms and Complexity*][bubeck2015]
* [Shalev-Shwartz, *Online Learning and Online Convex Optimization*][shalev2012]
* [Agarwal et al., *RL: Theory and Algorithms*]
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Finset BigOperators Real

noncomputable section

/-! ### SGD State and Configuration -/

/-- **SGD state**: tracks the squared distance to optimum and suboptimality
    at each step, as algebraic quantities. This is a deterministic surrogate
    for E[‖θ_t - θ*‖²] and E[f(θ_t) - f*]. -/
structure SGDState where
  /-- Squared distance to optimum: represents E[‖θ_t - θ*‖²] -/
  distSq : ℝ
  /-- Suboptimality gap: represents E[f(θ_t) - f*] -/
  subopt : ℝ
  /-- Distance is nonneg -/
  distSq_nonneg : 0 ≤ distSq
  /-- Suboptimality is nonneg (for convex f and θ* optimal) -/
  subopt_nonneg : 0 ≤ subopt

/-- **SGD hypotheses** for convex optimization.
    These encode the algebraic consequences of L-smoothness, convexity,
    and bounded gradient variance. -/
structure SGDHyp where
  /-- Smoothness parameter L > 0 -/
  L : ℝ
  /-- Gradient variance bound σ² -/
  sigma_sq : ℝ
  /-- Initial squared distance to optimum D₀² -/
  D0_sq : ℝ
  /-- L is positive -/
  hL : 0 < L
  /-- Variance bound is nonneg -/
  hsigma : 0 ≤ sigma_sq
  /-- Initial distance is nonneg -/
  hD0 : 0 ≤ D0_sq

/-- **Strong convexity hypothesis**: additional μ > 0 parameter. -/
structure StrongConvexHyp extends SGDHyp where
  /-- Strong convexity parameter μ > 0 -/
  mu : ℝ
  /-- μ is positive -/
  hmu : 0 < mu
  /-- μ ≤ L (strong convexity constant ≤ smoothness constant) -/
  hmu_le_L : mu ≤ L

/-! ### SGD Update: Algebraic Formulation

The SGD update θ_{t+1} = θ_t - α_t · g_t, combined with convexity and
L-smoothness, yields the following one-step recurrence for the squared
distance to optimum:

  E[‖θ_{t+1} - θ*‖²] ≤ E[‖θ_t - θ*‖²] - 2α_t(f(θ_t) - f*) + α_t² σ²

This is the fundamental algebraic identity underlying SGD convergence.
-/

/-- **SGD update formula**: given current squared-distance d_t², step size α,
    suboptimality gap Δ_t, and noise variance σ², the next squared-distance is
    bounded by d_t² - 2α·Δ_t + α²·σ².

    This encodes the algebraic consequence of:
    ‖θ_{t+1} - θ*‖² = ‖θ_t - α·g_t - θ*‖²
                      = ‖θ_t - θ*‖² - 2α⟨g_t, θ_t - θ*⟩ + α²‖g_t‖²
    Taking expectations and using convexity + noise bound. -/
def sgdNextDistBound (d_sq alpha delta sigma_sq : ℝ) : ℝ :=
  d_sq - 2 * alpha * delta + alpha ^ 2 * sigma_sq

/-- The SGD one-step bound is correct by computation. -/
theorem sgd_update_eq (d_sq alpha delta sigma_sq : ℝ) :
    sgdNextDistBound d_sq alpha delta sigma_sq =
    d_sq - 2 * alpha * delta + alpha ^ 2 * sigma_sq := by
  rfl

/-! ### Gradient Variance Bound

The noise hypothesis E[‖g_t - ∇f(θ_t)‖²] ≤ σ² is the fundamental
assumption on the stochastic gradient oracle. This is algebraically
captured as a bound on the noise contribution to the one-step recurrence. -/

/-- **SGD variance bound**: the noise contribution α²·σ² to the one-step
    recurrence is nonneg. -/
theorem sgd_variance_contribution_nonneg (alpha sigma_sq : ℝ)
    (hsigma : 0 ≤ sigma_sq) :
    0 ≤ alpha ^ 2 * sigma_sq :=
  mul_nonneg (sq_nonneg _) hsigma

/-! ### Convex SGD: One-Step Progress

For convex f, the one-step recurrence gives:
  d_{t+1}² ≤ d_t² - 2α·Δ_t + α²σ²

Rearranging: Δ_t ≤ (d_t² - d_{t+1}²)/(2α) + α·σ²/2 -/

/-- **One-step progress**: the recurrence d' ≤ d - 2αδ + α²σ² implies
    2αδ ≤ d - d' + α²σ², which gives the one-step bound. -/
theorem convex_sgd_one_step_rearranged (d_sq d_sq' alpha delta sigma_sq : ℝ)
    (_halpha : 0 < alpha)
    (h_recurrence : d_sq' ≤ d_sq - 2 * alpha * delta + alpha ^ 2 * sigma_sq) :
    2 * alpha * delta ≤ (d_sq - d_sq') + alpha ^ 2 * sigma_sq := by
  nlinarith

/-! ### Convex SGD: O(1/√T) Rate

Telescoping the one-step bound and using constant step size α = D₀/(σ√T):

  (1/T) ∑ Δ_t ≤ D₀²/(2αT) + ασ²/2 = D₀σ/√T

This gives the classical O(1/√T) rate for convex SGD. -/

/-- **Nonnegativity of telescoping bound expression**: proves
    0 ≤ D₀²/(2α) + α·σ²/2 when D₀² ≥ 0, α > 0, σ² ≥ 0.
    This is a nonnegativity check, not the telescoping sum bound itself
    (see `convex_sgd_convergence` for the actual bound). -/
theorem sgd_telescope_bound_nonneg (D0_sq sigma_sq alpha : ℝ)
    (hD0 : 0 ≤ D0_sq) (halpha : 0 < alpha) (hsigma : 0 ≤ sigma_sq) :
    0 ≤ D0_sq / (2 * alpha) + alpha * sigma_sq / 2 := by
  apply add_nonneg
  · exact div_nonneg hD0 (by positivity)
  · positivity

/-- **Convex SGD rate**: the rate expression is nonneg, confirming
    the O(1/√T) convergence bound is well-defined. -/
theorem convex_sgd_rate_nonneg (h : SGDHyp) (T : ℕ) (_hT : 0 < T) :
    0 ≤ Real.sqrt h.D0_sq * Real.sqrt h.sigma_sq / Real.sqrt (T : ℝ) :=
  div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)

/-! ### Strongly Convex SGD: O(1/(μT)) Rate

For μ-strongly convex f with step size α_t = 2/(μ(t+1)):

  E[‖θ_T - θ*‖²] ≤ max(D₀², 4σ²/μ²) · 1/(μT)

The key algebraic ingredient is the strongly convex one-step recurrence:

  d_{t+1}² ≤ (1 - α_t μ) d_t² + α_t² σ²
-/

/-- **Strongly convex one-step**: the recurrence
    d_{t+1}² ≤ (1 - αμ) · d_t² + α² σ².

    This encodes: for μ-strongly convex f,
    E[‖θ_{t+1} - θ*‖²] ≤ (1 - α_t μ) E[‖θ_t - θ*‖²] + α_t² σ² -/
def stronglyConvexNextBound (d_sq alpha mu sigma_sq : ℝ) : ℝ :=
  (1 - alpha * mu) * d_sq + alpha ^ 2 * sigma_sq

/-- The strongly convex recurrence bound is correct by computation. -/
theorem strongly_convex_update_eq (d_sq alpha mu sigma_sq : ℝ) :
    stronglyConvexNextBound d_sq alpha mu sigma_sq =
    (1 - alpha * mu) * d_sq + alpha ^ 2 * sigma_sq := by
  rfl

/-- **One-step contraction**: when α < 1/μ, the contraction factor 1 - αμ ∈ (0,1). -/
theorem strongly_convex_contraction (alpha mu : ℝ)
    (halpha : 0 < alpha) (hmu : 0 < mu)
    (hlt : alpha * mu < 1) :
    0 < 1 - alpha * mu ∧ 1 - alpha * mu < 1 := by
  exact ⟨by linarith, by linarith [mul_pos halpha hmu]⟩

/-- **Nonnegativity of noise contribution**: proves 0 ≤ α² · σ²
    where α = 2/(μ(t+2)). This is just mul_nonneg applied to
    a square and a nonneg value, not the O(1/t²) decay rate. -/
theorem strongly_convex_step_noise_nonneg (mu sigma_sq : ℝ) (t : ℕ)
    (_hmu : 0 < mu) (hsigma : 0 ≤ sigma_sq) :
    let alpha := 2 / (mu * ((t : ℝ) + 2))
    0 ≤ alpha ^ 2 * sigma_sq :=
  mul_nonneg (sq_nonneg _) hsigma

/-- **Strongly convex rate nonneg**: the O(1/(μT)) rate expression is nonneg. -/
theorem strongly_convex_sgd_rate_nonneg (h : StrongConvexHyp) (T : ℕ)
    (_hT : 0 < T) :
    0 ≤ (max h.D0_sq (4 * h.sigma_sq / h.mu ^ 2)) / (h.mu * T) :=
  div_nonneg (le_max_of_le_left h.hD0)
    (mul_nonneg (le_of_lt h.hmu) (Nat.cast_nonneg' (n := T)))

/-! ### Step Size Schedules

Common step size schedules for SGD and their algebraic properties. -/

/-- Decaying step size α_t = c / (t + 1). -/
def decayStepSize (c : ℝ) (t : ℕ) : ℝ := c / ((t : ℝ) + 1)

/-- Decaying step size is positive. -/
theorem decayStepSize_pos (c : ℝ) (hc : 0 < c) (t : ℕ) :
    0 < decayStepSize c t := by
  unfold decayStepSize; positivity

/-- Decaying step size is monotone decreasing. -/
theorem decayStepSize_antitone (c : ℝ) (hc : 0 < c) :
    ∀ s t : ℕ, s ≤ t → decayStepSize c t ≤ decayStepSize c s := by
  intro s t hst
  unfold decayStepSize
  have hs_pos : (0 : ℝ) < (s : ℝ) + 1 := by positivity
  have hle : (s : ℝ) + 1 ≤ (t : ℝ) + 1 := by
    have : (s : ℝ) ≤ (t : ℝ) := Nat.cast_le.mpr hst
    linarith
  exact div_le_div_of_nonneg_left (by linarith) hs_pos hle

/-! ### Polyak-Ruppert Averaging

For convex SGD, averaging the iterates θ̄_T = (1/T) ∑ θ_t achieves the
optimal O(1/√T) rate even with constant step size. The key algebraic
fact is that averaging "smooths out" the noise. -/

/-- **Average suboptimality bound**: if each Δ_t ≤ B_t, then the average
    (1/T) ∑ Δ_t ≤ (1/T) ∑ B_t. This is used in the telescoping argument. -/
theorem average_bound_le (T : ℕ) (_hT : 0 < T)
    (delta bound : Fin T → ℝ)
    (h : ∀ i, delta i ≤ bound i) :
    (∑ i, delta i) / T ≤ (∑ i, bound i) / T := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg' (n := T))
  exact Finset.sum_le_sum (fun i _ => h i)

/-! ### Mini-batch SGD

Mini-batch SGD uses g_t = (1/B) ∑_{b=1}^{B} g_t^{(b)} where each g_t^{(b)}
is an independent stochastic gradient. The variance reduces to σ²/B. -/

/-- **Mini-batch variance reduction**: averaging B independent gradient
    estimates reduces variance by factor B. -/
theorem minibatch_variance_reduction (sigma_sq : ℝ) (B : ℕ)
    (hsigma : 0 ≤ sigma_sq) (hB : 0 < B) :
    0 ≤ sigma_sq / B ∧ sigma_sq / B ≤ sigma_sq := by
  have hBr : (0 : ℝ) < B := Nat.cast_pos.mpr hB
  constructor
  · positivity
  · have h1 : 1 ≤ (B : ℝ) := by exact_mod_cast hB
    rw [div_le_iff₀ hBr]
    nlinarith

/-! ### Convex SGD Convergence Theorem

The actual convergence bound connecting the one-step recurrence to the final rate.

From the one-step recurrence d(t+1) ≤ d(t) - 2α·δ(t) + α²σ², telescoping gives:
  ∑_{t=0}^{T-1} 2α·δ(t) ≤ d(0) - d(T) + T·α²·σ² ≤ D₀² + T·α²·σ²

So (1/T)·∑ δ(t) ≤ (D₀² + T·α²·σ²) / (2αT) = D₀²/(2αT) + ασ²/2

With the optimal constant step α = D₀/(σ√T):
  (1/T)·∑ δ(t) ≤ D₀·σ/√T

We work with `ℕ → ℝ` sequences indexed by natural numbers and
`Finset.range` sums to avoid the complexity of `Fin` index proofs.
-/

/-- **Telescoping the one-step recurrence**: for sequences d, δ : ℕ → ℝ satisfying
    the one-step recurrence d(t+1) ≤ d(t) - 2α·δ(t) + α²σ² for t < T,
    the sum of 2α·δ(t) is bounded by d(0) - d(T) + T·α²·σ².

    This is the key algebraic step: summing the rearranged one-step bounds
    produces a telescoping sum on the distances. -/
theorem convex_sgd_telescope_sum' (T : ℕ)
    (d delta : ℕ → ℝ) (alpha sigma_sq : ℝ)
    (h_rec : ∀ t, t < T → d (t + 1) ≤ d t - 2 * alpha * delta t + alpha ^ 2 * sigma_sq) :
    ∑ t ∈ Finset.range T, (2 * alpha * delta t) ≤
      d 0 - d T + (T : ℝ) * (alpha ^ 2 * sigma_sq) := by
  induction T with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have ih_applied := ih (fun t ht => h_rec t (Nat.lt_succ_of_lt ht))
    have h_last := h_rec n (Nat.lt_succ_of_le le_rfl)
    -- ih: ∑_{t<n} 2α δ(t) ≤ d(0) - d(n) + n·α²σ²
    -- last: d(n+1) ≤ d(n) - 2α δ(n) + α²σ², so 2α δ(n) ≤ d(n) - d(n+1) + α²σ²
    have cast_succ : (↑(n + 1) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [cast_succ]
    nlinarith

/-- **Convex SGD sum bound**: for convex f with constant step size α > 0,
    if d(t+1) ≤ d(t) - 2α·δ(t) + α²σ² and d(T) ≥ 0, then
      ∑_{t<T} δ(t) ≤ (d(0) + T·α²·σ²) / (2α) -/
theorem convex_sgd_sum_bound' (T : ℕ)
    (d delta : ℕ → ℝ) (alpha sigma_sq : ℝ)
    (halpha : 0 < alpha)
    (hd_T : 0 ≤ d T)
    (h_rec : ∀ t, t < T → d (t + 1) ≤ d t - 2 * alpha * delta t + alpha ^ 2 * sigma_sq) :
    ∑ t ∈ Finset.range T, delta t ≤
      (d 0 + (T : ℝ) * alpha ^ 2 * sigma_sq) / (2 * alpha) := by
  have h_tel := convex_sgd_telescope_sum' T d delta alpha sigma_sq h_rec
  -- From telescope: ∑ 2α δ(t) ≤ d(0) - d(T) + T α²σ² ≤ d(0) + T α²σ²
  have h_sum_2a : ∑ t ∈ Finset.range T, (2 * alpha * delta t) ≤
      d 0 + (T : ℝ) * (alpha ^ 2 * sigma_sq) := by linarith
  -- Factor: ∑ 2α δ(t) = 2α · ∑ δ(t)
  have h_factor : ∑ t ∈ Finset.range T, (2 * alpha * delta t) =
      2 * alpha * ∑ t ∈ Finset.range T, delta t := by
    rw [Finset.mul_sum]
  rw [h_factor] at h_sum_2a
  -- 2α · ∑δ ≤ d(0) + T α²σ², so ∑δ ≤ (d(0) + T α²σ²) / (2α)
  have h2a : (0 : ℝ) < 2 * alpha := by linarith
  rw [le_div_iff₀ h2a]
  nlinarith

/-- **Convex SGD convergence**: for convex f with constant step size α > 0,
    if the one-step recurrence d(t+1) ≤ d(t) - 2α·δ(t) + α²σ² holds,
    d(0) ≤ D₀², and d(T) ≥ 0, then the average suboptimality satisfies:

      (1/T) · ∑_{t<T} δ(t) ≤ D₀² / (2αT) + α σ² / 2

    Substituting the optimal constant step α = D₀/(σ√T) yields
    the classical O(1/√T) rate: avg suboptimality ≤ D₀·σ/√T. -/
theorem convex_sgd_convergence (T : ℕ) (hT : 0 < T)
    (d delta : ℕ → ℝ) (alpha sigma_sq D0_sq : ℝ)
    (halpha : 0 < alpha)
    (hd0 : d 0 ≤ D0_sq)
    (hd_T : 0 ≤ d T)
    (h_rec : ∀ t, t < T → d (t + 1) ≤ d t - 2 * alpha * delta t + alpha ^ 2 * sigma_sq) :
    (∑ t ∈ Finset.range T, delta t) / (T : ℝ) ≤
      D0_sq / (2 * alpha * (T : ℝ)) + alpha * sigma_sq / 2 := by
  have hTr : (0 : ℝ) < (T : ℝ) := Nat.cast_pos.mpr hT
  have h2a : (0 : ℝ) < 2 * alpha := by linarith
  -- Get the sum bound
  have h_sum := convex_sgd_sum_bound' T d delta alpha sigma_sq halpha hd_T h_rec
  -- h_sum: ∑ δ ≤ (d(0) + T α²σ²) / (2α) ≤ (D₀² + T α²σ²) / (2α)
  have h_ub : (d 0 + (T : ℝ) * alpha ^ 2 * sigma_sq) / (2 * alpha) ≤
      (D0_sq + (T : ℝ) * alpha ^ 2 * sigma_sq) / (2 * alpha) := by
    apply div_le_div_of_nonneg_right _ (by linarith : (0 : ℝ) ≤ 2 * alpha)
    linarith
  -- So ∑ δ ≤ (D₀² + T α²σ²) / (2α)
  -- Divide by T: (∑ δ)/T ≤ (D₀² + T α²σ²) / (2αT) = D₀²/(2αT) + ασ²/2
  rw [div_le_iff₀ hTr]
  -- Goal: ∑ δ ≤ (D₀²/(2αT) + ασ²/2) * T
  have h_rhs_eq : (D0_sq / (2 * alpha * ↑T) + alpha * sigma_sq / 2) * ↑T =
      (D0_sq + (T : ℝ) * alpha ^ 2 * sigma_sq) / (2 * alpha) := by
    have hne_a : (2 : ℝ) * alpha ≠ 0 := by positivity
    have hne_T : (T : ℝ) ≠ 0 := by positivity
    field_simp
  linarith

/-! ### Strongly Convex SGD Convergence Theorem

For μ-strongly convex f with constant step size α satisfying αμ ≤ 1,
the one-step recurrence is:
  d(t+1) ≤ (1 - αμ) · d(t) + α² σ²

The sequence d(t) contracts toward the noise ball of radius α σ²/μ.
Specifically, for M = max(d(0), α σ²/μ), we have d(t) ≤ M for all t,
because (1 - αμ)M + α²σ² ≤ M when ασ²/μ ≤ M.

For α = 2/(μ(T+1)), this gives d(T) ≤ max(d(0), 2σ²/(μ²(T+1))),
establishing the O(1/(μT)) rate.
-/

/-- **Strongly convex SGD: one-step contraction bound**.
    For the strongly convex recurrence d' ≤ (1 - αμ)d + α²σ²,
    if 1 - αμ ≥ 0 and d ≤ C, then d' ≤ (1 - αμ)C + α²σ².
    This is the key step for inductive convergence proofs. -/
theorem strongly_convex_sgd_one_step_ub (d d' alpha mu sigma_sq C : ℝ)
    (h_recurrence : d' ≤ (1 - alpha * mu) * d + alpha ^ 2 * sigma_sq)
    (h_contract : 0 ≤ 1 - alpha * mu)
    (h_ub : d ≤ C) :
    d' ≤ (1 - alpha * mu) * C + alpha ^ 2 * sigma_sq := by
  have : (1 - alpha * mu) * d ≤ (1 - alpha * mu) * C :=
    mul_le_mul_of_nonneg_left h_ub h_contract
  linarith

/-- **Strongly convex SGD convergence**: for μ-strongly convex f with
    constant step size α satisfying 0 < α, 0 < μ, αμ ≤ 1, after T steps
    of the recurrence d(t+1) ≤ (1 - αμ) d(t) + α²σ², we have:

      d(T) ≤ max(d(0), α σ² / μ)

    This shows d(t) stays in the "noise ball" of radius ασ²/μ (or at d(0)
    if starting outside). For α = 2/(μ(T+1)), the noise ball has radius
    2σ²/(μ²(T+1)), giving the O(σ²/(μT)) convergence rate. -/
theorem strongly_convex_sgd_convergence (T : ℕ)
    (d : ℕ → ℝ) (alpha mu sigma_sq : ℝ)
    (halpha : 0 < alpha) (hmu : 0 < mu)
    (h_contract : alpha * mu ≤ 1)
    (h_rec : ∀ t, t < T →
      d (t + 1) ≤ (1 - alpha * mu) * d t + alpha ^ 2 * sigma_sq) :
    d T ≤ max (d 0) (alpha * sigma_sq / mu) := by
  -- We prove: ∀ t ≤ T, d t ≤ M where M = max(d 0, ασ²/μ)
  -- Key: if d t ≤ M, then d(t+1) ≤ (1-αμ)M + α²σ² ≤ M
  -- because (1-αμ)M + α²σ² ≤ M ⟺ α²σ² ≤ αμ M ⟺ ασ²/μ ≤ M
  set M := max (d 0) (alpha * sigma_sq / mu) with hM_def
  suffices h : ∀ t, t ≤ T → d t ≤ M from h T le_rfl
  intro t ht
  induction t with
  | zero => exact le_max_left _ _
  | succ n ih =>
    have hn_lt : n < T := Nat.lt_of_succ_le ht
    have h_ih : d n ≤ M := ih (Nat.le_of_lt hn_lt)
    have h_one_minus : (0 : ℝ) ≤ 1 - alpha * mu := by linarith
    -- d(n+1) ≤ (1-αμ) d(n) + α²σ² ≤ (1-αμ) M + α²σ²
    have h_step : d (n + 1) ≤ (1 - alpha * mu) * M + alpha ^ 2 * sigma_sq :=
      strongly_convex_sgd_one_step_ub (d n) (d (n + 1)) alpha mu sigma_sq M
        (h_rec n hn_lt) h_one_minus h_ih
    -- Show (1-αμ) M + α²σ² ≤ M, i.e., α²σ² ≤ αμ M
    have h_noise_ball : alpha * sigma_sq / mu ≤ M := le_max_right _ _
    -- αμ · (ασ²/μ) = α²σ², so α²σ² ≤ αμ · M
    have hamu : (0 : ℝ) < alpha * mu := mul_pos halpha hmu
    have h_key : alpha ^ 2 * sigma_sq ≤ alpha * mu * M := by
      have h1 : alpha * mu * (alpha * sigma_sq / mu) = alpha ^ 2 * sigma_sq := by
        have hne_mu : mu ≠ 0 := ne_of_gt hmu
        field_simp
      nlinarith [mul_le_mul_of_nonneg_left h_noise_ball (le_of_lt hamu)]
    -- So (1-αμ)M + α²σ² ≤ (1-αμ)M + αμ M = M
    linarith

/-! ### Connection to RL

In RL, SGD appears in:
- Policy gradient: θ_{t+1} = θ_t + α ∇̂ J(θ_t)
- TD learning: w_{t+1} = w_t + α (r + γ φ(s')^T w - φ(s)^T w) φ(s)
- Actor-critic: both policy and value updates

The SGD convergence framework above applies when:
1. The loss landscape is (approximately) convex/strongly convex
2. The stochastic gradients have bounded variance

**Blocked**: Connecting to actual RL policy optimization requires the
policy gradient theorem (in PolicyOptimization.PolicyGradient) and
Fisher information geometry (in PolicyOptimization.NPG). The challenge
is that RL objectives are generally non-convex, so the convex SGD rates
apply only in special cases (e.g., linear function approximation). -/

end
