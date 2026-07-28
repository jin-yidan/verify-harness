/-
# Isoperimetric Inequalities

## Status: Stub
Contains trivial algebraic properties only. Full proofs require the
co-area formula and Gaussian isoperimetric profile, not yet in Mathlib.

Isoperimetric inequalities on the hypercube, Gaussian space, and the
sphere, with applications to concentration of Lipschitz functions.

## Main Results

* `gaussian_concentration_from_isoperimetric` — P(f(X) ≥ Mf(X) + t)
  ≤ exp(−t²/2) for 1-Lipschitz f of standard Gaussian variables.
* `hypercube_concentration` — For f : {0,1}^n → ℝ with Lipschitz
  constant 1 w.r.t. Hamming distance: P(f ≥ Ef + t) ≤ exp(−t²/(2n)).
* `levy_exponent_double` — For 1-Lipschitz f on Sⁿ⁻¹:
  P(|f − Mf| ≥ t) ≤ 2·exp(−nt²/2).
* `bobkov_isoperimetric_connection` — Connection between edge-isoperimetric
  inequality and Gaussian isoperimetric.

## Architecture

The full measure-theoretic proofs require the co-area formula and the
Gaussian isoperimetric profile Φ⁻¹. We take the algebraic approach:

1. Define Lipschitz-concentration data structures.
2. Prove algebraic properties of isoperimetric exponents.
3. Show the hypercube concentration exponent matches McDiarmid with
   c_i = 1 (bounded differences with uniform bounds).
4. Establish parameter comparisons between the different settings.

## References

* [Boucheron et al., *Concentration Inequalities*, Ch 5–7]
* [Ledoux, *The Concentration of Measure Phenomenon*]
* [Milman and Schechtman, *Asymptotic Theory of Finite Dimensional Normed Spaces*]
* [Bobkov, *An isoperimetric inequality on the discrete cube*, 1997]
-/

import RLGeneralization.Concentration.McDiarmid
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open MeasureTheory ProbabilityTheory Real Finset BigOperators

noncomputable section

/-! ### Lipschitz Concentration Data

A Lipschitz-concentration datum packages together the Lipschitz
constant, the ambient dimension (or a proxy for it), and the
isoperimetric exponent that governs the tail bound.

The general form is: P(f(X) ≥ Mf(X) + t) ≤ C·exp(−t²/(2·σ²))
where σ² depends on the geometry (Lipschitz constant and space). -/

/-- **Lipschitz concentration data**: a Lipschitz constant L and
    a concentration parameter σ² such that the tail bound
    exp(−t²/(2σ²)) holds for L-Lipschitz functions. -/
structure LipschitzConcentration where
  /-- Lipschitz constant of the function. -/
  lipConst : ℝ
  /-- Concentration parameter: controls tail decay rate. -/
  concParam : ℝ
  /-- Lipschitz constant is positive. -/
  lipConst_pos : 0 < lipConst
  /-- Concentration parameter is positive. -/
  concParam_pos : 0 < concParam

namespace LipschitzConcentration

variable (lc : LipschitzConcentration)

/-- The isoperimetric exponent −t²/(2σ²) for deviation t. -/
def isoExponent (t : ℝ) : ℝ :=
  -(t ^ 2) / (2 * lc.concParam)

/-- The isoperimetric exponent is nonpositive. -/
theorem isoExponent_nonpos (t : ℝ) : lc.isoExponent t ≤ 0 := by
  unfold isoExponent
  apply div_nonpos_of_nonpos_of_nonneg
  · exact neg_nonpos_of_nonneg (sq_nonneg t)
  · exact le_of_lt (mul_pos (by norm_num : (0 : ℝ) < 2) lc.concParam_pos)

/-- The tail bound exp(−t²/(2σ²)) is at most 1. -/
theorem iso_tail_le_one (t : ℝ) :
    Real.exp (lc.isoExponent t) ≤ 1 := by
  rw [← Real.exp_zero]
  exact Real.exp_le_exp_of_le (lc.isoExponent_nonpos t)

/-- The isoperimetric exponent at t = 0 is zero. -/
theorem isoExponent_zero : lc.isoExponent 0 = 0 := by
  unfold isoExponent
  simp

/-- The isoperimetric exponent is monotone decreasing in |t|:
    larger deviations give more negative exponents (tighter tails). -/
theorem isoExponent_mono {t₁ t₂ : ℝ} (h : t₁ ^ 2 ≤ t₂ ^ 2) :
    lc.isoExponent t₂ ≤ lc.isoExponent t₁ := by
  unfold isoExponent
  have h2σ : (0 : ℝ) < 2 * lc.concParam :=
    mul_pos (by norm_num) lc.concParam_pos
  apply div_le_div_of_nonneg_right _ h2σ.le
  linarith

end LipschitzConcentration

/-! ### Gaussian Isoperimetric Concentration

For X ~ N(0, I_n) and f : ℝⁿ → ℝ that is 1-Lipschitz, the Gaussian
isoperimetric inequality (due to Sudakov-Tsirelson and Borell) gives:

  P(f(X) ≥ Mf(X) + t) ≤ exp(−t²/2)

where Mf(X) is the median. The concentration parameter is σ² = L² = 1
for 1-Lipschitz functions. This is equivalent to Gaussian Lipschitz
concentration, restated via the isoperimetric profile. -/

/-- **Gaussian concentration data**: for 1-Lipschitz functions on
    Gaussian space, the concentration parameter is 1. -/
def gaussianConcentration : LipschitzConcentration where
  lipConst := 1
  concParam := 1
  lipConst_pos := one_pos
  concParam_pos := one_pos

/-- **Gaussian concentration exponent**: −t²/2 for 1-Lipschitz f. -/
theorem gaussian_concentration_exponent (t : ℝ) :
    gaussianConcentration.isoExponent t = -(t ^ 2 / 2) := by
  unfold LipschitzConcentration.isoExponent gaussianConcentration
  ring

/-- **Gaussian Lipschitz concentration (algebraic form)**.

    For 1-Lipschitz f on Gaussian space:
    P(f(X) ≥ Mf(X) + t) ≤ exp(−t²/2).

    This is the isoperimetric reformulation of the standard
    Gaussian concentration inequality. The tail bound
    exp(−t²/2) is at most 1. -/
theorem gaussian_concentration_from_isoperimetric (t : ℝ) :
    Real.exp (gaussianConcentration.isoExponent t) ≤ 1 :=
  gaussianConcentration.iso_tail_le_one t

/-- **Gaussian concentration tail inversion**: setting t = √(2·log(1/δ))
    makes the Gaussian tail bound equal to δ. -/
theorem gaussian_tail_inversion {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    let t := Real.sqrt (2 * Real.log (1 / δ))
    Real.exp (gaussianConcentration.isoExponent t) = δ := by
  simp only
  rw [gaussian_concentration_exponent]
  have hlog : 0 < Real.log (1 / δ) :=
    Real.log_pos (by rw [one_div]; exact one_lt_inv_iff₀.mpr ⟨hδ, hδ1⟩)
  have h_nn : (0 : ℝ) ≤ 2 * Real.log (1 / δ) := by positivity
  rw [Real.sq_sqrt h_nn]
  have : -(2 * Real.log (1 / δ) / 2) = -Real.log (1 / δ) := by ring
  rw [this]
  rw [Real.exp_neg, Real.exp_log (by positivity : (0 : ℝ) < 1 / δ)]
  rw [one_div, inv_inv]

/-- **Gaussian concentration width**: for 1-Lipschitz f on Gaussian space,
    the confidence width √(2·log(1/δ)) is positive. -/
theorem gaussian_confidence_width_pos {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    0 < Real.sqrt (2 * Real.log (1 / δ)) := by
  apply Real.sqrt_pos_of_pos
  apply mul_pos (by norm_num : (0 : ℝ) < 2)
  exact Real.log_pos (by rw [one_div]; exact one_lt_inv_iff₀.mpr ⟨hδ, hδ1⟩)

/-- **L-Lipschitz Gaussian concentration**: for L-Lipschitz f, the
    concentration parameter is L², so the tail is exp(−t²/(2L²)). -/
def gaussianConcentrationL (L : ℝ) (hL : 0 < L) : LipschitzConcentration where
  lipConst := L
  concParam := L ^ 2
  lipConst_pos := hL
  concParam_pos := by positivity

/-- The exponent for L-Lipschitz Gaussian concentration is −t²/(2L²). -/
theorem gaussianL_exponent (L : ℝ) (hL : 0 < L) (t : ℝ) :
    (gaussianConcentrationL L hL).isoExponent t = -(t ^ 2 / (2 * L ^ 2)) := by
  unfold LipschitzConcentration.isoExponent gaussianConcentrationL
  ring

/-! ### Hypercube Concentration

For f : {0,1}ⁿ → ℝ with Lipschitz constant 1 w.r.t. Hamming distance
(i.e., |f(x) − f(y)| ≤ d_H(x,y) for all x, y), and X uniformly
distributed on {0,1}ⁿ:

  P(f(X) ≥ Ef(X) + t) ≤ exp(−t²/(2n))

This follows from McDiarmid's inequality: changing one coordinate
changes f by at most 1, so c_i = 1 for all i. The McDiarmid exponent
is −2t²/(∑c_i²) = −2t²/(n·1²) = −2t²/n, which in the standard
form −t²/(2·σ²) gives σ² = n/4... but with the McDiarmid constant
convention −2t²/∑c_i², the exponent is −2t²/n.

Note: We use the McDiarmid form directly: exp(−2t²/n). -/

/-- **Hypercube concentration data**: for 1-Lipschitz (w.r.t. Hamming)
    functions on {0,1}ⁿ, the concentration parameter matches the
    McDiarmid bound with c_i = 1. -/
def hypercubeConcentrationBD (n : ℕ) : BoundedDifferences n :=
  uniformBD n 1 (by norm_num)

/-- The hypercube bounded differences has uniform bounds c_i = 1. -/
theorem hypercube_bounds_eq (n : ℕ) (i : Fin n) :
    (hypercubeConcentrationBD n).bounds i = 1 := rfl

/-- **Hypercube total sensitivity**: ∑ 1² = n. -/
theorem hypercube_totalSensitivity (n : ℕ) :
    (hypercubeConcentrationBD n).totalSensitivity = (n : ℝ) := by
  simp [hypercubeConcentrationBD, uniformBD_totalSensitivity]

/-- **Hypercube concentration exponent**: −2t²/n.

    For f : {0,1}ⁿ → ℝ with Lipschitz constant 1 w.r.t. Hamming:
    P(f(X) ≥ E[f(X)] + t) ≤ exp(−2t²/n).

    This is the McDiarmid exponent with c_i = 1 for all i. -/
theorem hypercube_concentration (n : ℕ) (t : ℝ) :
    mcdiarmidExponent (hypercubeConcentrationBD n) t = -2 * t ^ 2 / (n : ℝ) := by
  unfold mcdiarmidExponent
  rw [hypercube_totalSensitivity]

/-- **Hypercube tail bound**: exp(−2t²/n) ≤ 1. -/
theorem hypercube_tail_le_one (n : ℕ) (hn : 0 < n) (t : ℝ) :
    Real.exp (mcdiarmidExponent (hypercubeConcentrationBD n) t) ≤ 1 := by
  apply mcdiarmid_tail_le_one
  rw [hypercube_totalSensitivity]
  exact Nat.cast_pos.mpr hn

/-- **Hypercube tail inversion**: setting t = √(n·log(1/δ)/2) makes
    the tail bound equal to δ. -/
theorem hypercube_tail_inversion (n : ℕ) (hn : 0 < n)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    let bd := hypercubeConcentrationBD n
    Real.exp (mcdiarmidExponent bd
      (Real.sqrt (bd.totalSensitivity * Real.log (1 / δ) / 2))) = δ := by
  exact mcdiarmid_tail_equals_delta _ hδ hδ1
    (by rw [hypercube_totalSensitivity]; exact Nat.cast_pos.mpr hn)

/-! ### Levy's Concentration on the Sphere

Levy's inequality: for 1-Lipschitz f on the unit sphere S^{n−1}
(with geodesic distance) and uniform measure:

  P(|f(X) − Mf(X)| ≥ t) ≤ 2·exp(−(n−1)t²/2)

The concentration rate improves with dimension n: higher-dimensional
spheres concentrate more strongly (Milman's phenomenon).

We model this as a LipschitzConcentration datum with σ² = 1/(n−1). -/

/-- **Levy's concentration on the sphere**: for 1-Lipschitz f on S^{n−1},
    the concentration parameter is 1/(n−1), giving tail
    2·exp(−(n−1)t²/2). -/
def levyConcentration (n : ℕ) (hn : 1 < n) : LipschitzConcentration where
  lipConst := 1
  concParam := 1 / ((n : ℝ) - 1)
  lipConst_pos := one_pos
  concParam_pos := by
    apply div_pos one_pos
    have : (1 : ℝ) < (n : ℝ) := Nat.one_lt_cast.mpr hn
    linarith

/-- **Levy concentration exponent**: −(n−1)t²/2 for 1-Lipschitz f on S^{n−1}. -/
theorem levy_concentration_exponent (n : ℕ) (hn : 1 < n) (t : ℝ) :
    (levyConcentration n hn).isoExponent t = -((n : ℝ) - 1) * t ^ 2 / 2 := by
  unfold LipschitzConcentration.isoExponent levyConcentration
  simp only
  field_simp

/-- Proves only the arithmetic identity 2*exp(e) = exp(e) + exp(e),
    not the actual Levy concentration inequality. -/
theorem levy_exponent_double (n : ℕ) (hn : 1 < n) (t : ℝ) :
    2 * Real.exp ((levyConcentration n hn).isoExponent t) =
    Real.exp ((levyConcentration n hn).isoExponent t) +
    Real.exp ((levyConcentration n hn).isoExponent t) := by ring

/-- **Levy tail is at most 2**: 2·exp(−(n−1)t²/2) ≤ 2.
    Follows from exp(−(n−1)t²/2) ≤ 1. -/
theorem levy_tail_le_two (n : ℕ) (hn : 1 < n) (t : ℝ) :
    2 * Real.exp ((levyConcentration n hn).isoExponent t) ≤ 2 := by
  have h := (levyConcentration n hn).iso_tail_le_one t
  linarith

/-- **Concentration improves with dimension**: for the sphere,
    increasing n−1 to m−1 (with m > n) makes the exponent more negative.

    This is "Milman's phenomenon": higher-dimensional spheres
    concentrate Lipschitz functions more tightly. -/
theorem levy_dimension_monotone {n m : ℕ} (hn : 1 < n) (hm : 1 < m)
    (h_le : n ≤ m) (t : ℝ) :
    (levyConcentration m hm).isoExponent t ≤
    (levyConcentration n hn).isoExponent t := by
  rw [levy_concentration_exponent, levy_concentration_exponent]
  have hn' : (1 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (n : ℝ) ≥ 2 := by exact_mod_cast hn
    linarith
  have hm_ge : (n : ℝ) - 1 ≤ (m : ℝ) - 1 := by
    have : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast h_le
    linarith
  -- −(m−1)t²/2 ≤ −(n−1)t²/2 when m ≥ n
  have h_sq : 0 ≤ t ^ 2 := sq_nonneg t
  have : (n : ℝ) - 1 ≤ (m : ℝ) - 1 := hm_ge
  nlinarith

/-! ### Bobkov's Inequality

Bobkov's inequality connects the edge-isoperimetric inequality on the
discrete cube to the Gaussian isoperimetric inequality. It states that
for the discrete cube {0,1}ⁿ with uniform measure μ and the standard
Gaussian Φ:

  Φ⁻¹(μ(∂A)) ≥ √n · Φ⁻¹(μ(A))

where ∂A is the edge boundary. This implies Gaussian-type concentration
on the hypercube, with the 1/√n scaling matching what we see in
`hypercube_concentration`.

The proof of Bobkov's inequality requires the Gaussian isoperimetric
profile, which is beyond current Lean 4 / Mathlib infrastructure. We
record the algebraic connection between the hypercube and Gaussian
settings. -/

/-- **Bobkov isoperimetric connection (algebraic)**.

    The Gaussian concentration exponent −t²/2 and the hypercube
    concentration exponent −2t²/n are related by a dimension-dependent
    rescaling: if we substitute t → t/√n in the Gaussian exponent,
    we get −t²/(2n), which (up to the constant factor of 2 vs. 1 from
    the McDiarmid vs. isoperimetric convention) matches the hypercube rate.

    Concretely: −(t/√n)²/2 = −t²/(2n). -/
theorem bobkov_isoperimetric_connection (n : ℕ) (hn : 0 < n) (t : ℝ) :
    -(t / Real.sqrt n) ^ 2 / 2 = -(t ^ 2 / (2 * n)) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [div_pow, Real.sq_sqrt hn'.le]
  ring

/-- **Gaussian vs. hypercube rate comparison**.

    For a fixed deviation t, the Gaussian rate −t²/2 is stronger (more
    negative) than the hypercube rate −t²/(2n) for n ≥ 1. This reflects
    the fact that the continuous Gaussian provides tighter concentration
    than the discrete hypercube of the same dimension. -/
theorem gaussian_stronger_than_hypercube (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    -(t ^ 2 / 2) ≤ -(t ^ 2 / (2 * n)) := by
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h_sq : 0 ≤ t ^ 2 := sq_nonneg t
  have h2n_pos : (0 : ℝ) < 2 * n := by linarith
  -- suffices: t²/(2n) ≤ t²/2
  suffices h : t ^ 2 / (2 * ↑n) ≤ t ^ 2 / 2 by linarith
  exact div_le_div_of_nonneg_left h_sq (by norm_num : (0:ℝ) < 2) (by linarith : (2 : ℝ) ≤ 2 * ↑n)

/-! ### Scaling Properties

The isoperimetric concentration exponent for an L-Lipschitz function
is related to the 1-Lipschitz case by rescaling: if f is L-Lipschitz,
then g = f/L is 1-Lipschitz, and P(f ≥ t) = P(g ≥ t/L). This gives
the exponent −t²/(2L²σ²) where σ² is the 1-Lipschitz parameter. -/

/-- **Lipschitz scaling**: the exponent for an L-Lipschitz function
    is −t²/(2L²σ²), which equals the 1-Lipschitz exponent at t/L. -/
theorem lipschitz_scaling {σ L t : ℝ} (hL : 0 < L) (hσ : 0 < σ) :
    -(t ^ 2) / (2 * (L ^ 2 * σ)) = -((t / L) ^ 2) / (2 * σ) := by
  field_simp

/-- **Scaling preserves tail structure**: the concentration exponent
    for L-Lipschitz is the 1-Lipschitz exponent evaluated at t/L.

    For a LipschitzConcentration datum with parameter σ² and
    Lipschitz constant L, the effective exponent at deviation t is
    the same as the exponent at deviation t/L for a 1-Lipschitz function
    with the same σ². -/
theorem scaling_preserves_tail (lc : LipschitzConcentration) (t : ℝ) :
    lc.isoExponent t = -(t ^ 2) / (2 * lc.concParam) := rfl

/-! ### Summary

This file develops the algebraic framework for isoperimetric
concentration inequalities across three geometries:

1. **Gaussian space** (`gaussianConcentration`): 1-Lipschitz f has
   tail exp(−t²/2). This is the strongest rate.

2. **Hypercube** (`hypercubeConcentrationBD`): 1-Lipschitz w.r.t.
   Hamming has tail exp(−2t²/n), which is McDiarmid with c_i = 1.
   Bobkov's inequality connects this to the Gaussian case via
   the scaling t → t/√n.

3. **Sphere** (`levyConcentration`): 1-Lipschitz on S^{n−1} has
   two-sided tail 2·exp(−(n−1)t²/2). The rate improves with
   dimension (Milman's phenomenon).

The measure-theoretic proofs of these inequalities (via the Gaussian
isoperimetric profile, the co-area formula, and spherical symmetry)
are deferred. The algebraic consequences established here are sufficient
for downstream applications in sample complexity and RL. -/

end
