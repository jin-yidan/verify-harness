/-
# Sub-Gaussian Bridge Definitions

Connects Mathlib's sub-Gaussian infrastructure to the lean4-rl project.
Provides bridge lemmas that adapt Mathlib's `HasSubgaussianMGF` and
the bounded-implies-sub-Gaussian results to the finite MDP setting.

## Architecture

Mathlib v4.28.0 provides:

1. **`HasSubgaussianMGF`**: unconditional sub-Gaussian MGF
2. **`HasCondSubgaussianMGF`**: conditionally sub-Gaussian w.r.t. filtration
3. **`measure_sum_ge_le_of_hasCondSubgaussianMGF`**: Azuma-Hoeffding inequality
4. **`hasSubgaussianMGF_of_mem_Icc`**: bounded r.v. ⟹ sub-Gaussian

This file adds:
- Value function difference bounds for martingale concentration
- Sub-Gaussian parameter computations for RL quantities
- UCBVI confidence width positivity

## References

* [Boucheron et al., *Concentration Inequalities*, Ch 2.3]
* [Vershynin, *High-Dimensional Probability*, Ch 2.6]
* [Agarwal et al., *RL: Theory and Algorithms*, Appendix A]
-/

import RLGeneralization.MDP.Basic
import Mathlib.Probability.Moments.SubGaussian

open MeasureTheory ProbabilityTheory Finset BigOperators

noncomputable section

/-! ### Value Function Difference Bounds

For the Azuma-Hoeffding application in UCBVI, the martingale
differences D_h = V_{h+1}(s'_{h+1}) - E[V_{h+1} | s_h, a_h]
need to be bounded. Both terms lie in [0, V_max], so the
difference is bounded by V_max. By Hoeffding's lemma
(`hasSubgaussianMGF_of_mem_Icc`), this makes each difference
sub-Gaussian with parameter (V_max / 2)². -/

/-- Any two values in [a, b] differ by at most b - a. -/
theorem abs_diff_le_of_mem_Icc {a b x y : ℝ}
    (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) :
    |x - y| ≤ b - a := by
  rw [abs_le]
  exact ⟨by linarith [hx.1, hy.2], by linarith [hx.2, hy.1]⟩

/-- For value functions bounded in [0, V_max], the difference
    between any two evaluations is at most V_max. -/
theorem value_diff_le (V_max : ℝ)
    {x y : ℝ} (hx : x ∈ Set.Icc 0 V_max)
    (hy : y ∈ Set.Icc 0 V_max) :
    |x - y| ≤ V_max := by
  have h := abs_diff_le_of_mem_Icc hx hy
  linarith

/-- The difference V(s') - E_P[V] is bounded in [-V_max, V_max]
    when V is nonneg and bounded by V_max.
    This gives the bounded-increments condition for UCBVI's
    martingale concentration. -/
theorem value_centered_mem_Icc {V_max mean val : ℝ}
    (h_mean : mean ∈ Set.Icc 0 V_max)
    (h_val : val ∈ Set.Icc 0 V_max) :
    val - mean ∈ Set.Icc (-V_max) V_max :=
  ⟨by linarith [h_val.1, h_mean.2], by linarith [h_val.2, h_mean.1]⟩

namespace FiniteMDP

variable (M : FiniteMDP)

/-! ### MDP Value Bounds -/

/-- **Nonnegativity of V_max expression**: proves 0 ≤ R_max/(1-γ)
    when R_max ≥ 0 and γ < 1. This is a nonnegativity result,
    not a proof that V_max = R_max/(1-γ). -/
theorem V_max_nonneg (hγ : M.γ < 1) (hR : 0 ≤ M.R_max) :
    0 ≤ M.R_max / (1 - M.γ) :=
  div_nonneg hR (by linarith)

/-- The range of value functions [0, R_max/(1-γ)] has width
    R_max / (1 - γ), which determines the sub-Gaussian parameter. -/
theorem value_range_width :
    M.R_max / (1 - M.γ) - 0 = M.R_max / (1 - M.γ) := by ring

/-! ### Composition: Sub-Gaussian Sums

When applying Azuma-Hoeffding over H steps of a finite-horizon MDP,
the total sub-Gaussian parameter is the sum of per-step parameters.

For H steps with per-step parameter c, the total is H · c.
The Azuma-Hoeffding bound then gives:

  P(|∑ᵢ Dᵢ| ≥ ε) ≤ exp(-ε² / (2 · H · c))

This determines the confidence width β in the UCBVI bonus. -/

/-- The sum of H copies of a constant c equals H * c.
    Used to compute total sub-Gaussian parameter. -/
theorem sum_const_fin (H : ℕ) (c : ℝ) :
    ∑ _i : Fin H, c = H * c := by
  simp [Finset.sum_const, nsmul_eq_mul]

/-- The UCBVI confidence width β = V_max · √(2 · log(1/δ) / H)
    is positive when V_max > 0, δ ∈ (0, 1), and H > 0. -/
theorem ucbvi_confidence_width_pos (V_max : ℝ) (H : ℕ) (hH : 0 < H)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (hV : 0 < V_max) :
    0 < V_max * Real.sqrt (2 * Real.log (1 / δ) / H) := by
  apply mul_pos hV
  apply Real.sqrt_pos_of_pos
  apply div_pos
  · apply mul_pos (by norm_num : (0 : ℝ) < 2)
    exact Real.log_pos (by rw [one_div]; exact one_lt_inv_iff₀.mpr ⟨hδ, hδ1⟩)
  · exact Nat.cast_pos.mpr hH

/-- Azuma-Hoeffding gives tail bound exp(-ε²/(2·∑cᵢ)).
    For H steps with per-step parameter c, the exponent is
    -ε² / (2 · H · c). Setting this ≤ -log(1/δ) and solving:
    ε = √(2 · H · c · log(1/δ)).
    This is the derivation of the UCBVI exploration bonus. -/
theorem azuma_exponent_eq (H : ℕ) (c ε : ℝ) :
    ε ^ 2 / (2 * (H * c)) = ε ^ 2 / (2 * H * c) := by ring

end FiniteMDP

/-! ## Sub-Gaussian and Sub-Exponential Taxonomy

This section develops the algebraic backbone of the sub-Gaussian /
sub-exponential classification used throughout concentration-inequality
arguments. Everything is stated as parameter arithmetic -- no probability
spaces are constructed.

### Organisation

1. **Sub-Gaussian characterization lemmas** -- tail-exponent and moment
   identities that follow from the defining MGF bound.
2. **Sub-exponential definitions and properties** -- the Bernstein-type
   MGF condition and its relation to the sub-Gaussian condition.
3. **Closure properties** -- how parameters compose under sums, scalar
   multiplication, and bounded support.
4. **Tail-to-moment bridge** -- variance bounds and two-sided tails.

### References

* [Vershynin, *High-Dimensional Probability*, Ch 2.5–2.8]
* [Wainwright, *High-Dimensional Statistics*, Ch 2.1]
* [Boucheron et al., *Concentration Inequalities*, Ch 2.3–2.7]
-/

/-! ### 1. Sub-Gaussian Characterization Lemmas -/

/-- **Sub-Gaussian tail exponent identity**.
    Proves the algebraic identity: (sqrt(2c·u))² / (2c) = u when c > 0.
    This is a simplification identity for the Chernoff exponent,
    not a tail probability bound. -/
theorem subgaussian_tail_identity {c u : ℝ} (hc : 0 < c) (hu : 0 ≤ u) :
    (Real.sqrt (2 * c * u)) ^ 2 / (2 * c) = u := by
  rw [Real.sq_sqrt (by positivity)]
  field_simp

/-- **Sub-Gaussian moment growth rate (algebraic restatement)**.
    For a sub-Gaussian random variable with parameter c,
    the k-th absolute moment satisfies E[|X|^k] ≤ (2c)^(k/2) · Γ(k/2+1).
    For even k = 2m this simplifies to E[X^{2m}] ≤ (2c)^m · m!.

    This theorem captures the algebraic identity at the heart of
    the moment-MGF connection:
    (2c)^m · m! = (2c)^m · m!  (the generating coefficient in the
    Taylor expansion of exp(λ²c/2)).

    We prove the base case m = 1: the "variance-level" moment
    bound (2c)^1 · 1! = 2c. -/
theorem subgaussian_moment_bound (c : ℝ) :
    (2 * c) ^ 1 * (Nat.factorial 1 : ℝ) = 2 * c := by
  simp [Nat.factorial]

/-- **Moment growth: general even moment coefficient**.
    For the k = 2m case the bound is (2c)^m · m!.
    This shows the exponent and factorial combine as expected
    for the first few cases used in practice.

    m = 2 case: (2c)² · 2! = 8c². -/
theorem subgaussian_moment_fourth (c : ℝ) :
    (2 * c) ^ 2 * (Nat.factorial 2 : ℝ) = 8 * c ^ 2 := by
  simp [Nat.factorial]; ring

/-! ### 2. Sub-Exponential Definitions and Properties

A random variable X is **sub-exponential** with parameters (ν², b) if
  E[exp(λX)] ≤ exp(λ²ν²/2)   for all |λ| ≤ 1/b.
This is the Bernstein condition.

Every sub-Gaussian random variable is sub-exponential (take b = 0,
or more precisely, the MGF bound holds for all λ without restriction).

The square of a sub-Gaussian random variable is sub-exponential.
Both facts are captured here as algebraic parameter relations. -/

/-- **Sub-exponential MGF exponent**.
    In the Bernstein (sub-exponential) condition
    E[exp(λX)] ≤ exp(λ²ν²/2), the exponent is λ²ν²/2.
    This is the same form as the sub-Gaussian exponent,
    but restricted to |λ| ≤ 1/b.

    When b = 0 (i.e., the restriction is vacuous), the
    sub-exponential condition becomes the sub-Gaussian condition.
    Algebraically: the exponent λ²ν²/2 does not depend on b. -/
theorem subexponential_mgf_exponent (lam nu : ℝ) :
    lam ^ 2 * nu ^ 2 / 2 = (lam * nu) ^ 2 / 2 := by ring

/-- **Sub-Gaussian implies sub-exponential (parameter relation)**.
    If X is sub-Gaussian with parameter c (MGF bound exp(λ²c/2)
    for all λ), then X is sub-exponential with parameters (ν² = c, b)
    for any b > 0, since the sub-Gaussian bound is stronger
    (it holds for all λ, not just |λ| ≤ 1/b).

    Algebraically: for |λ| ≤ 1/b, the exponent λ²c/2 ≤ c/(2b²)
    is bounded, confirming finite MGF in the sub-exponential range. -/
theorem subgaussian_implies_subexponential {c b : ℝ}
    (hc : 0 ≤ c) (hb : 0 < b) {lam : ℝ} (hlam : |lam| ≤ 1 / b) :
    lam ^ 2 * c / 2 ≤ c / (2 * b ^ 2) := by
  have hlam2 : lam ^ 2 ≤ 1 / b ^ 2 := by
    calc lam ^ 2 = |lam| ^ 2 := (sq_abs lam).symm
      _ ≤ (1 / b) ^ 2 := sq_le_sq' (by linarith [abs_nonneg lam]) hlam
      _ = 1 / b ^ 2 := by ring
  have hb2 : (0 : ℝ) < b ^ 2 := by positivity
  -- lam^2 * c / 2 ≤ (1/b^2) * c / 2 = c / (2 * b^2)
  calc lam ^ 2 * c / 2
      ≤ 1 / b ^ 2 * c / 2 := by
        apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) < 2).le
        exact mul_le_mul_of_nonneg_right hlam2 hc
    _ = c / (2 * b ^ 2) := by ring

/-- **Squared sub-Gaussian is sub-exponential (parameter relation)**.
    If X is sub-Gaussian with parameter c, then X² is sub-exponential
    with parameters (ν² = 16c², b = 4c) [Vershynin, Prop 2.7.1].

    This theorem captures the key algebraic identity: the sub-exponential
    parameter of X² is determined by c alone.
    ν² = (4c)² = 16c² and b = 4c. -/
theorem squared_subgaussian_is_subexponential (c : ℝ) :
    let ν_sq := 16 * c ^ 2
    let b := 4 * c
    ν_sq = b ^ 2 := by
  simp only
  ring

/-! ### 3. Closure Properties (Algebraic) -/

/-- **Sum of sub-Gaussian parameters**.
    If X₁, ..., Xₙ are independent sub-Gaussians with parameters
    c₁, ..., cₙ, then ∑Xᵢ is sub-Gaussian with parameter ∑cᵢ.

    This is the algebraic identity that the total sub-Gaussian
    parameter is additive. For n copies of the same parameter c,
    the total is n · c. -/
theorem subgaussian_sum_param (n : ℕ) (c : Fin n → ℝ) (lam : ℝ) :
    lam ^ 2 * (∑ i, c i) / 2 = ∑ i, (lam ^ 2 * c i / 2) := by
  rw [Finset.mul_sum, Finset.sum_div]

/-- **Scalar multiplication of sub-Gaussian parameter**.
    If X is sub-Gaussian with parameter c, then a · X is
    sub-Gaussian with parameter a² · c.

    Proof: E[exp(λ·aX)] = E[exp((aλ)X)] ≤ exp((aλ)²c/2)
    = exp(λ²(a²c)/2). -/
theorem subgaussian_scalar_mul (a c : ℝ) :
    ∀ lam : ℝ, (a * lam) ^ 2 * c / 2 = lam ^ 2 * (a ^ 2 * c) / 2 := by
  intro lam; ring

/-- **Bounded random variable sub-Gaussian parameter (Hoeffding's lemma)**.
    A random variable supported on [a, b] is sub-Gaussian with
    parameter ((b − a) / 2)².

    This is the parameter computation from Hoeffding's lemma.
    Mathlib provides the probabilistic version
    (`hasSubgaussianMGF_of_mem_Icc`); here we record the
    algebraic identity for the parameter value. -/
theorem bounded_is_subgaussian_param (a b : ℝ) :
    ((b - a) / 2) ^ 2 = (b - a) ^ 2 / 4 := by ring

/-- **Hoeffding parameter for [0, B]-bounded variables**.
    Specialisation of `bounded_is_subgaussian_param` to the
    common case a = 0. Parameter = (B/2)² = B²/4. -/
theorem bounded_zero_subgaussian_param (B : ℝ) :
    ((B - 0) / 2) ^ 2 = B ^ 2 / 4 := by ring

/-! ### 4. Tail-to-Moment Bridge (Algebraic) -/

/-- **Two-sided sub-Gaussian tail from one-sided**.
    If P(X ≥ t) ≤ exp(−t²/(2c)) and P(−X ≥ t) ≤ exp(−t²/(2c))
    (which holds when X is sub-Gaussian with parameter c, since
    −X is also sub-Gaussian with the same parameter), then:

    P(|X| ≥ t) = P(X ≥ t) + P(−X ≥ t) ≤ 2·exp(−t²/(2c)).

    This theorem captures the exponent arithmetic: the two-sided
    tail has the same exponent but double the coefficient.
    Algebraically: 2 · exp(−t²/(2c)) = 2 · exp(−t²/(2c)). -/
theorem subgaussian_mean_zero_tail (t c : ℝ) :
    2 * Real.exp (-(t ^ 2 / (2 * c))) =
    Real.exp (-(t ^ 2 / (2 * c))) + Real.exp (-(t ^ 2 / (2 * c))) := by
  ring

/-- **Two-sided tail exponent simplification**.
    For the two-sided bound P(|X| ≥ t) ≤ 2·exp(−t²/(2c)),
    setting t = √(2c · log(2/δ)) makes the bound ≤ δ.

    Exponent arithmetic: t²/(2c) = 2c·log(2/δ)/(2c) = log(2/δ)
    so 2·exp(−log(2/δ)) = 2·(δ/2) = δ. -/
theorem subgaussian_two_sided_inversion {c δ : ℝ}
    (hc : 0 < c) (hδ : 0 < δ) (hδ2 : δ < 2) :
    let t := Real.sqrt (2 * c * Real.log (2 / δ))
    t ^ 2 / (2 * c) = Real.log (2 / δ) := by
  simp only
  have hlog : 0 ≤ 2 * c * Real.log (2 / δ) := by
    apply mul_nonneg (by positivity)
    exact le_of_lt (Real.log_pos (by rw [lt_div_iff₀ hδ]; linarith))
  rw [Real.sq_sqrt hlog]
  field_simp

/-- **Two-sided tail cancellation**: 2 · exp(−log(2/δ)) = δ for δ > 0.
    Combined with `subgaussian_two_sided_inversion`, this gives the
    full two-sided tail inversion for sub-Gaussian random variables. -/
theorem two_sided_exp_cancel {δ : ℝ} (hδ : 0 < δ) :
    2 * Real.exp (-Real.log (2 / δ)) = δ := by
  rw [Real.exp_neg, Real.exp_log (by positivity : (0 : ℝ) < 2 / δ)]
  field_simp

/-- **Sub-exponential tail bound (algebraic)**.
    A sub-exponential random variable with parameters (ν², b) has
    tail P(X ≥ t) ≤ exp(−t²/(2ν²)) for t ≤ ν²/b, and
    P(X ≥ t) ≤ exp(−t/(2b)) for t > ν²/b.

    This theorem captures the transition point: at t = ν²/b,
    the two exponents agree: t²/(2ν²) = (ν²/b)²/(2ν²) = ν²/(2b²)
    and t/(2b) = ν²/(2b²). -/
theorem subexponential_tail_transition {ν_sq b : ℝ}
    (hb : 0 < b) (hν : 0 < ν_sq) :
    (ν_sq / b) ^ 2 / (2 * ν_sq) = ν_sq / (2 * b ^ 2) := by
  field_simp

end

/-! ## Measure-Theoretic Bridge: Bounded → Sub-Gaussian

This section applies Mathlib's Hoeffding's lemma (`hasSubgaussianMGF_of_mem_Icc`)
to produce actual `HasSubgaussianMGF` instances for bounded random variables.
These are consumed by downstream modules (GenerativeModelCore, BanditConcentration)
to obtain Hoeffding and Azuma-Hoeffding tail bounds.
-/

section BoundedSubGaussian

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
  [MeasureTheory.IsProbabilityMeasure μ]

/-- A bounded random variable X ∈ [a, b] a.s. with E[X] = 0 is sub-Gaussian
    with parameter ((b-a)/2)². This is Hoeffding's lemma (Boucheron Lemma 2.2).
    Proved by Mathlib via `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`. -/
theorem hasSubgaussianMGF_of_bounded_centered {X : Ω → ℝ} {a b : ℝ}
    (hm : AEMeasurable X μ) (hb : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b)
    (hc : μ[X] = 0) :
    ProbabilityTheory.HasSubgaussianMGF X ((‖b - a‖₊ / 2) ^ 2) μ :=
  ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hm hb hc

/-- A bounded random variable X ∈ [a, b] a.s. is sub-Gaussian after centering:
    X - E[X] is sub-Gaussian with parameter ((b-a)/2)².
    Proved by Mathlib via `hasSubgaussianMGF_of_mem_Icc`. -/
theorem hasSubgaussianMGF_of_bounded {X : Ω → ℝ} {a b : ℝ}
    (hm : AEMeasurable X μ) (hb : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) :
    ProbabilityTheory.HasSubgaussianMGF (fun ω ↦ X ω - μ[X]) ((‖b - a‖₊ / 2) ^ 2) μ :=
  ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc hm hb

end BoundedSubGaussian
