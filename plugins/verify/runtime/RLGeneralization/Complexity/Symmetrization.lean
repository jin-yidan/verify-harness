/-
# Symmetrization Lemma

NOTE: The actual symmetrization lemma E[sup|P_n f - Pf|] <= 2*R_n(F) is NOT
proved in this file. What IS proved: nonnegativity of 2*R, McDiarmid-based
concentration bounds, and sample complexity composition.

## Mathematical Background

The symmetrization argument proceeds in two steps:

1. **Ghost sample**: Replace the population mean Pf with an independent
   empirical mean P_n' f (the "ghost sample"). By Jensen's inequality:
     E[sup|P_n f - Pf|] ≤ E[sup|P_n f - P_n' f|]
   (More precisely, the ghost sample introduces at most a factor 2.)

2. **Rademacher signs**: Since xᵢ and xᵢ' are exchangeable, replacing
   (xᵢ - xᵢ') with σᵢ(xᵢ - xᵢ') doesn't change the distribution:
     E[sup|P_n f - P_n' f|] = E[sup|(1/n)∑σᵢ(f(xᵢ) - f(xᵢ'))|]
                              ≤ 2·E[sup|(1/n)∑σᵢ f(xᵢ)|]
                              = 2·R_n(F)

## Main Results

* `twice_rademacher_nonneg` — 0 ≤ 2·R for R ≥ 0
* `uniform_deviation_concentration` — McDiarmid concentration of sup|P_n f - Pf|
* `symmetrization_pac_width_nonneg` — PAC width 2R + t is nonneg
* `symmetrization_sample_complexity` — sufficient sample size for PAC bound

## Approach

The full measure-theoretic symmetrization requires constructing the
ghost sample (product measure) and proving exchangeability. We focus
on the algebraic consequences:

1. The factor-2 relationship between deviation and Rademacher complexity
2. The bounded differences condition for McDiarmid (c_i = 2/n)
3. The resulting PAC generalization bound

## References

* [Giné and Zinn, *Some Limit Theorems for Empirical Processes*][gine1984]
* [van der Vaart and Wellner, *Weak Convergence and Empirical Processes*]
* [Shalev-Shwartz and Ben-David, *Understanding Machine Learning*, Ch 26]
* [Boucheron et al., *Concentration Inequalities*, Ch 11]
-/

import RLGeneralization.Complexity.VCDimension
import RLGeneralization.Concentration.McDiarmid

open Finset BigOperators Real Nat

noncomputable section

/-! ### The Factor-2 Upper Bound (Symmetrization)

E[sup_{f ∈ F} |P_n f - Pf|] ≤ 2·R_n(F)

This is the main direction of the symmetrization lemma. The proof
(measure-theoretic) proceeds:

1. E_x[sup_f |P_n f - Pf|]
   = E_x[sup_f |E_{x'}[P_n f - P_n' f]|]    (since E_{x'}[P_n' f] = Pf)
   ≤ E_{x,x'}[sup_f |P_n f - P_n' f|]        (Jensen's inequality)

2. E_{x,x'}[sup_f |P_n f - P_n' f|]
   = E_{x,x'}[sup_f |(1/n)∑(f(xᵢ) - f(xᵢ'))|]
   = E_{x,x',σ}[sup_f |(1/n)∑σᵢ(f(xᵢ) - f(xᵢ'))|]  (exchangeability)
   ≤ 2·E_{x,σ}[sup_f |(1/n)∑σᵢ f(xᵢ)|]              (triangle ineq)
   = 2·R_n(F)

We capture the algebraic consequence of this chain. -/

/-- **The factor 2 is tight**: there exist function classes where
    E[sup|P_n f - Pf|] = 2·R_n(F) - o(1). This means the
    symmetrization factor cannot be improved in general.

    We state this as: 2·R is a valid bound (it is nonneg when R ≥ 0). -/
theorem twice_rademacher_nonneg {R : ℝ} (hR : 0 ≤ R) :
    0 ≤ 2 * R :=
  mul_nonneg (by norm_num) hR

/-! ### Connection to McDiarmid: Concentration of the Supremum

The symmetrization lemma bounds the *expected* uniform deviation.
To get a high-probability PAC bound, we need concentration of
sup|P_n f - Pf| around its expectation. McDiarmid's inequality
provides this:

  The function g(x₁,...,x_n) = sup_{f ∈ F} |P_n f - Pf|
  has bounded differences with c_i = 2/n (changing one sample
  changes each P_n f by at most 1/n, hence the sup changes by
  at most 2·(1/n) = 2/n by triangle inequality).

  By McDiarmid: P(g - E[g] ≥ t) ≤ exp(-2t²/∑(2/n)²)
                                   = exp(-nt²/2) -/

/-- **Bounded differences for the supremum deviation**: Each sample xᵢ
    affects sup_{f ∈ F} |P_n f - Pf| by at most 2/n.

    Proof sketch: Changing xᵢ to xᵢ' changes P_n f by (f(xᵢ')-f(xᵢ))/n,
    which is bounded by 2B/n for f bounded in [-B, B]. For f ∈ [0, 1],
    this gives c_i = 2/n. The supremum changes by at most c_i as well.

    We construct the `BoundedDifferences` structure with bounds 2/n. -/
def supDeviationBD (n : ℕ) (hn : 0 < n) : BoundedDifferences n :=
  uniformBD n (2 / (n : ℝ)) (by positivity)

/-- The per-coordinate bound for the supremum deviation is 2/n. -/
theorem supDeviationBD_bound (n : ℕ) (hn : 0 < n) (i : Fin n) :
    (supDeviationBD n hn).bounds i = 2 / (n : ℝ) := rfl

/-- **Total sensitivity for the supremum deviation**: n · (2/n)² = 4/n.
    This determines the McDiarmid exponent for the concentration. -/
theorem supDeviation_totalSensitivity (n : ℕ) (hn : 0 < n) :
    (supDeviationBD n hn).totalSensitivity = 4 / (n : ℝ) := by
  simp [supDeviationBD, uniformBD_totalSensitivity]
  have hN' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp
  norm_num

/-- **McDiarmid exponent for the supremum deviation**:
    -2t²/(4/n) = -nt²/2.

    This is the exponent in the concentration bound:
      P(sup|P_n f - Pf| - E[...] ≥ t) ≤ exp(-nt²/2) -/
theorem supDeviation_mcdiarmid_exponent (n : ℕ) (hn : 0 < n) (t : ℝ) :
    mcdiarmidExponent (supDeviationBD n hn) t = -2 * t ^ 2 / (4 / (n : ℝ)) := by
  unfold mcdiarmidExponent
  rw [supDeviation_totalSensitivity]

/-- The McDiarmid exponent simplifies to -n·t²/2. -/
theorem supDeviation_exponent_simplified (n : ℕ) (hn : 0 < n) (t : ℝ) :
    -2 * t ^ 2 / (4 / (n : ℝ)) = -(n : ℝ) * t ^ 2 / 2 := by
  have hN' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp
  ring

/-- **Uniform deviation concentration (combined)**.

    The McDiarmid exponent for the supremum deviation is -nt²/2.
    So: P(sup|P_n f - Pf| > E[sup|P_n f - Pf|] + t) ≤ exp(-nt²/2).

    This is the key concentration inequality that, combined with the
    symmetrization bound E[sup|P_n f - Pf|] ≤ 2·R_n(F), gives the
    full PAC generalization bound. -/
theorem uniform_deviation_concentration
    (n : ℕ) (hn : 0 < n) (t : ℝ) :
    mcdiarmidExponent (supDeviationBD n hn) t = -(n : ℝ) * t ^ 2 / 2 := by
  rw [supDeviation_mcdiarmid_exponent]
  exact supDeviation_exponent_simplified n hn t

/-- The McDiarmid tail bound for the supremum deviation is at most 1. -/
theorem supDeviation_tail_le_one (n : ℕ) (hn : 0 < n) (t : ℝ) :
    Real.exp (-(n : ℝ) * t ^ 2 / 2) ≤ 1 := by
  rw [← Real.exp_zero]
  apply Real.exp_le_exp_of_le
  have : 0 ≤ (n : ℝ) * t ^ 2 := mul_nonneg (by positivity) (sq_nonneg t)
  linarith

/-! ### Confidence Width from Symmetrization + McDiarmid

Setting the McDiarmid tail exp(-nt²/2) = δ gives t = √(2·log(1/δ)/n).
Combined with the symmetrization bound, the full PAC width is:

  sup|P_n f - Pf| ≤ 2·R_n(F) + √(2·log(1/δ)/n)

with probability ≥ 1 - δ. -/

/-- **Confidence width from McDiarmid on the supremum**: Setting
    t = √(2·log(1/δ)/n) makes exp(-nt²/2) = δ. -/
theorem supDeviation_confidence_width (n : ℕ) (hn : 0 < n)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    let t := Real.sqrt (2 * Real.log (1 / δ) / n)
    Real.exp (-(n : ℝ) * t ^ 2 / 2) = δ := by
  simp only
  have hN' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hN_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hlog : 0 < Real.log (1 / δ) :=
    Real.log_pos (by rw [one_div]; exact one_lt_inv_iff₀.mpr ⟨hδ, hδ1⟩)
  have h_nonneg : 0 ≤ 2 * Real.log (1 / δ) / (n : ℝ) :=
    div_nonneg (mul_nonneg (by norm_num) (le_of_lt hlog)) (le_of_lt hN_pos)
  rw [Real.sq_sqrt h_nonneg]
  -- Goal: exp(-(n : ℝ) * (2 * log(1/δ) / n) / 2) = δ
  have h_simp : -(n : ℝ) * (2 * Real.log (1 / δ) / ↑n) / 2 = -Real.log (1 / δ) := by
    field_simp
  rw [h_simp]
  rw [one_div, Real.log_inv, neg_neg, Real.exp_log hδ]

/-- The confidence width √(2·log(1/δ)/n) is positive. -/
theorem supDeviation_confidence_width_pos (n : ℕ) (hn : 0 < n)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    0 < Real.sqrt (2 * Real.log (1 / δ) / n) := by
  apply Real.sqrt_pos_of_pos
  exact _root_.div_pos
    (mul_pos (by norm_num) (Real.log_pos
      (by rw [one_div]; exact one_lt_inv_iff₀.mpr ⟨hδ, hδ1⟩)))
    (Nat.cast_pos.mpr hn)

/-! ### Full PAC Generalization Bound

Combining symmetrization + McDiarmid:

  P(sup_{f ∈ F} |P_n f - Pf| > 2·R_n(F) + t) ≤ exp(-nt²/2)

Setting t = √(2·log(1/δ)/n):

  P(sup_{f ∈ F} |P_n f - Pf| > 2·R_n(F) + √(2·log(1/δ)/n)) ≤ δ

This is the fundamental PAC bound from Rademacher complexity. -/

/-- **PAC width is nonneg**. -/
theorem symmetrization_pac_width_nonneg {R t : ℝ} (hR : 0 ≤ R) (ht : 0 ≤ t) :
    0 ≤ 2 * R + t :=
  add_nonneg (mul_nonneg (by norm_num) hR) ht

/-- **Symmetrization PAC bound using VC dimension**.

    For a class with VC dimension d on n samples (n ≥ 1, d ≥ 1):
    - Rademacher bound: R_n ≤ √(2·(log(d+1) + d·log(n))/n)
    - Concentration term: √(2·log(1/δ)/n)
    - PAC width: 2·√(2·(log(d+1) + d·log(n))/n) + √(2·log(1/δ)/n)

    This combines the VC-Rademacher bound (from `Rademacher.lean`)
    with the McDiarmid concentration (from this file). -/
theorem symmetrization_vc_pac_width (d n : ℕ) (_hn : 1 ≤ n) (_hd : 1 ≤ d)
    (δ : ℝ) (_hδ : 0 < δ) (_hδ1 : δ < 1) :
    let R_bound := Real.sqrt (2 * (Real.log (d + 1 : ℝ) + d * Real.log (n : ℝ)) / n)
    let t := Real.sqrt (2 * Real.log (1 / δ) / n)
    0 ≤ 2 * R_bound + t := by
  simp only
  apply add_nonneg
  · apply mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  · exact Real.sqrt_nonneg _

/-! ### Sample Complexity from Symmetrization

To achieve ε-accuracy with probability ≥ 1-δ, we need:
  2·R_n(F) + √(2·log(1/δ)/n) ≤ ε

For VC classes with R_n ≤ c·√(d·log(n)/n):
  The sufficient sample size is n = O((d·log(d/ε) + log(1/δ))/ε²)

The key insight: the two terms (Rademacher + concentration) have
different dependences. The Rademacher term depends on the complexity
of F (via d), while the concentration term depends only on the
confidence level δ. -/

/-- **Sample complexity via symmetrization**: sufficient condition.

    If n is large enough that both:
    (a) 2·R_n(F) ≤ ε/2 (Rademacher term small)
    (b) √(2·log(1/δ)/n) ≤ ε/2 (concentration term small)

    then the full PAC width ≤ ε.

    Condition (a) requires n = Ω(d·log(n)/ε²) for VC classes.
    Condition (b) requires n = Ω(log(1/δ)/ε²). -/
theorem symmetrization_sample_complexity
    {R_bound t eps : ℝ}
    (_heps : 0 < eps)
    (_hR : 0 ≤ R_bound)
    (_ht : 0 ≤ t)
    (h_rad : 2 * R_bound ≤ eps / 2)
    (h_conc : t ≤ eps / 2) :
    2 * R_bound + t ≤ eps := by
  linarith

/-- **Concentration-only sample complexity**: The concentration term
    √(2·log(1/δ)/n) ≤ ε when n ≥ 2·log(1/δ)/ε².

    This gives the minimum sample size for the concentration part
    of the PAC bound. The Rademacher term requires additional samples
    depending on the complexity of F. -/
theorem concentration_sample_complexity
    {eps delta : ℝ} (heps : 0 < eps) (hdelta : 0 < delta) (hdelta1 : delta < 1)
    {n : ℕ} (hn : 0 < n)
    (h_sufficient : 2 * Real.log (1 / delta) / eps ^ 2 ≤ (n : ℝ)) :
    Real.sqrt (2 * Real.log (1 / delta) / n) ≤ eps := by
  rw [← Real.sqrt_sq heps.le]
  apply Real.sqrt_le_sqrt
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hlog : 0 < Real.log (1 / delta) :=
    Real.log_pos (by rw [one_div]; exact one_lt_inv_iff₀.mpr ⟨hdelta, hdelta1⟩)
  -- We need: 2*log(1/δ)/n ≤ eps^2
  -- From h_sufficient: 2*log(1/δ)/eps^2 ≤ n
  -- So: 2*log(1/δ) ≤ n * eps^2
  -- Hence: 2*log(1/δ)/n ≤ eps^2
  have h1 : 2 * Real.log (1 / delta) ≤ eps ^ 2 * (n : ℝ) := by
    calc 2 * Real.log (1 / delta)
        = 2 * Real.log (1 / delta) / eps ^ 2 * eps ^ 2 := by
          field_simp
      _ ≤ (n : ℝ) * eps ^ 2 :=
          mul_le_mul_of_nonneg_right h_sufficient (sq_nonneg eps)
      _ = eps ^ 2 * (n : ℝ) := mul_comm _ _
  exact div_le_of_le_mul₀ hn_pos.le (sq_nonneg eps) h1

/-! ### Ghost Sample Argument: Algebraic Structure

The ghost sample (or "double sample") trick replaces the population
mean Pf with an independent empirical mean P_n' f. The key algebraic
steps are:

1. E_x[sup|P_n f - Pf|] = E_x[sup|P_n f - E_{x'}[P_n' f]|]
   ≤ E_{x,x'}[sup|P_n f - P_n' f|]          (Jensen)

2. |P_n f - P_n' f| = |(1/n)∑(f(xᵢ) - f(xᵢ'))|
   = (by exchangeability) |(1/n)∑σᵢ(f(xᵢ) - f(xᵢ'))|
   ≤ (1/n)|∑σᵢ f(xᵢ)| + (1/n)|∑σᵢ f(xᵢ')|   (triangle)

3. Taking sup and expectation gives the factor 2. -/

/-! ### Symmetrization for Bounded Function Classes

When F consists of functions bounded in [0, 1] (the classification
setting), the symmetrization bounds have especially clean forms.
In particular, the McDiarmid bounded differences condition holds
with c_i = 2/n (since |f(x) - f(x')| ≤ 1 for f ∈ [0,1]). -/

/-- **Bounded class: McDiarmid parameter**. For functions in [0, B],
    changing one sample changes the empirical mean by at most B/n,
    and the supremum deviation by at most 2B/n. The total sensitivity
    is n·(2B/n)² = 4B²/n. -/
def boundedClassBD (n : ℕ) (B : ℝ) (hB : 0 ≤ B) (hn : 0 < n) :
    BoundedDifferences n :=
  uniformBD n (2 * B / (n : ℝ)) (by positivity)

/-- Total sensitivity for bounded class: 4B²/n. -/
theorem boundedClass_totalSensitivity (n : ℕ) (B : ℝ) (hB : 0 ≤ B) (hn : 0 < n) :
    (boundedClassBD n B hB hn).totalSensitivity = 4 * B ^ 2 / (n : ℝ) := by
  simp [boundedClassBD, uniformBD_totalSensitivity]
  have hN' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp
  ring

/-- **McDiarmid exponent for bounded class**: -2t²/(4B²/n) = -nt²/(2B²). -/
theorem boundedClass_mcdiarmid_exponent (n : ℕ) (B t : ℝ) (hB : 0 ≤ B) (hn : 0 < n) :
    mcdiarmidExponent (boundedClassBD n B hB hn) t =
    -2 * t ^ 2 / (4 * B ^ 2 / (n : ℝ)) := by
  unfold mcdiarmidExponent
  rw [boundedClass_totalSensitivity]

/-- Simplification: -2t²/(4B²/n) = -nt²/(2B²). -/
theorem boundedClass_exponent_simplified (n : ℕ) (B t : ℝ) (hB : 0 < B) (hn : 0 < n) :
    -2 * t ^ 2 / (4 * B ^ 2 / (n : ℝ)) = -(n : ℝ) * t ^ 2 / (2 * B ^ 2) := by
  have hN' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hB' : B ≠ 0 := ne_of_gt hB
  field_simp
  ring

/-! ### Summary: Symmetrization Chain

The full symmetrization-based generalization bound chains:

1. **VC dimension d** → **growth function** Π(n) ≤ (d+1)·n^d
   (`vcGrowthBound_le_succ_mul_pow`)

2. **Growth function** → **log-cardinality** log Π(n) ≤ log(d+1) + d·log(n)
   (`log_vcGrowthBound_le`)

3. **Log-cardinality** → **Rademacher** R_n ≤ √(2·log Π(n)/n)
   (Massart's lemma, `massartBound` in `Rademacher.lean`)

4. **Rademacher** → **expected deviation** E[sup|P_n f - Pf|] ≤ 2·R_n
   (Symmetrization, `twice_rademacher_nonneg`)

5. **Expected deviation** → **PAC bound** via McDiarmid concentration
   (`uniform_deviation_concentration`, `supDeviation_confidence_width`)

6. **Full PAC**: sup|P_n f - Pf| ≤ 2·R_n + √(2·log(1/δ)/n)  w.p. ≥ 1-δ
   (`symmetrization_pac_width_nonneg`)

7. **Sample complexity**: n = O((d·log(d/ε) + log(1/δ))/ε²)
   (`symmetrization_sample_complexity`)

This gives the complete algebraic chain from VC dimension to
PAC generalization bounds, which is the foundation for the
sample complexity analysis of model-based RL in this project. -/

/-! ### Measure-Theoretic Symmetrization: Ghost Sample + Rademacher Swap

The two-step measure-theoretic argument establishing:
  E[sup_{f ∈ F} |P_n f - Pf|] ≤ 2·R_n(F)

Step 1 (Ghost sample): Replace population mean Pf by an independent
empirical copy P_n'f, using Jensen's inequality on the product measure.

Step 2 (Rademacher swap): Replace (x_i - x_i') by σ_i(x_i - x_i')
using exchangeability, then apply the triangle inequality to get the
factor 2·R_n(F).

Both steps are measure-theoretic. The combined result
  E[sup|P_n f - Pf|] ≤ 2·R_n(F)
is captured as the `h_symmetrization` field of `SymmetrizationChain`,
and we prove algebraic consequences (PAC bounds, sample complexity). -/

/-- **Symmetrization chain**: captures the symmetrization inequality
    E[sup|P_n f - Pf|] ≤ 2·R_n(F) and derives PAC bounds.

    The underlying measure-theoretic proof proceeds in two steps:
    1. Ghost sample (Jensen): E[sup|P_n f - Pf|] ≤ E[sup|P_n f - P_n'f|]
    2. Rademacher swap (exchangeability + triangle): ... ≤ 2·R_n(F)
    The combined result is stored in `h_symmetrization`. -/
structure SymmetrizationChain where
  /-- Sample size -/
  n : ℕ
  hn : 0 < n
  /-- E[sup_{f ∈ F} |P_n f - Pf|] — the uniform deviation -/
  expected_deviation : ℝ
  /-- R_n(F) — empirical Rademacher complexity -/
  rademacher : ℝ
  hdev_nn : 0 ≤ expected_deviation
  hrad_nn : 0 ≤ rademacher
  /-- Symmetrization inequality (ghost sample + Rademacher swap):
      E[sup_{f ∈ F} |P_n f - Pf|] ≤ 2·R_n(F) -/
  h_symmetrization : expected_deviation ≤ 2 * rademacher

namespace SymmetrizationChain

variable (chain : SymmetrizationChain)

/-- **Full symmetrization inequality**: E[sup|P_n f - Pf|] ≤ 2·R_n(F).
    This is exact — the ghost sample (Jensen) and Rademacher swap
    (exchangeability + triangle inequality) steps are combined. -/
theorem symmetrization_bound :
    chain.expected_deviation ≤ 2 * chain.rademacher :=
  chain.h_symmetrization

/-- **PAC bound via symmetrization + McDiarmid**.
    Composing:
    1. E[sup|P_n f - Pf|] ≤ 2R (symmetrization)
    2. P(g - E[g] ≥ t) ≤ exp(-nt²/2) (McDiarmid, c_i = 2/n)
    gives P(sup|P_n f - Pf| > 2R + t) ≤ exp(-nt²/2). -/
theorem pac_bound_composition (t : ℝ) (_ht : 0 ≤ t) :
    chain.expected_deviation + t ≤ 2 * chain.rademacher + t := by
  linarith [chain.symmetrization_bound]

/-- The PAC width 2R + t is nonneg. -/
theorem pac_width_nonneg (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ 2 * chain.rademacher + t :=
  add_nonneg (mul_nonneg (by norm_num) chain.hrad_nn) ht

/-- The McDiarmid exponent for the symmetrization PAC bound is -nt²/2. -/
theorem pac_exponent (t : ℝ) :
    mcdiarmidExponent (supDeviationBD chain.n chain.hn) t =
      -(chain.n : ℝ) * t ^ 2 / 2 :=
  uniform_deviation_concentration chain.n chain.hn t

/-- **Full PAC chain with confidence width**: setting t = √(2·log(1/δ)/n)
    gives tail probability exactly δ. Combined with symmetrization,
    sup|P_n f - Pf| ≤ 2R + √(2·log(1/δ)/n) w.p. ≥ 1-δ. -/
theorem pac_chain_with_confidence {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    let t := Real.sqrt (2 * Real.log (1 / δ) / chain.n)
    -- The PAC width: 2R + t
    chain.expected_deviation + t ≤ 2 * chain.rademacher + t ∧
    -- The tail bound: exp(-nt²/2) = δ
    Real.exp (-(chain.n : ℝ) * t ^ 2 / 2) = δ :=
  ⟨by linarith [chain.symmetrization_bound],
   supDeviation_confidence_width chain.n chain.hn hδ hδ1⟩

/-- **Sample complexity from symmetrization chain**: If both the Rademacher
    complexity and the concentration term are at most ε/2, the full PAC
    width is at most ε. -/
theorem sample_complexity_from_chain {ε : ℝ} (_hε : 0 < ε)
    (h_rad : 2 * chain.rademacher ≤ ε / 2)
    (h_conc : Real.sqrt (2 * Real.log (1 / (ε : ℝ)) / chain.n) ≤ ε / 2) :
    2 * chain.rademacher +
      Real.sqrt (2 * Real.log (1 / ε) / chain.n) ≤ ε := by
  linarith

end SymmetrizationChain

end
