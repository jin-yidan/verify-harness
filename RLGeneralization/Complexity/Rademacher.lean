/-
# Rademacher Complexity Bounds

Rademacher complexity measures the richness of a function class by its
correlation with random sign vectors. It provides distribution-dependent
generalization bounds that are tighter than VC-based bounds when the
function class has favorable structure.

## Mathematical Background

The empirical Rademacher complexity of a function class F on a sample
x₁, ..., x_n is:

  R̂_n(F) = E_σ[sup_{f ∈ F} (1/n) ∑ σᵢ f(xᵢ)]

where σ₁, ..., σ_n are i.i.d. Rademacher (±1 with equal probability).
The Rademacher complexity R_n(F) = E_x[R̂_n(F)] averages over samples.

## Main Results

* `RademacherBound` — Structure for algebraic Rademacher complexity bounds
* `rademacher_finite_class` — R_n ≤ √(2·log|F|/n) for finite F (Massart)
* `vcRademacherBound` — R_n ≤ √(2·(log(d+1) + d·log(n))/n) when VCDim = d
* `RademacherBound.contract` — R_n(φ∘F) ≤ L·R_n(F) for L-Lipschitz φ
* `rademacher_pac_bound` — PAC generalization bound from Rademacher + McDiarmid
* `rademacherSampleComplexity` — n = O(d·log(d/ε)/ε²) for ε-accuracy

## Approach

We work with algebraic bounds on the Rademacher complexity, avoiding
the measure-theoretic construction of Rademacher random variables.
The key algebraic ingredients are:
1. Massart's lemma (finite class bound via log-cardinality)
2. VC growth function bound → Rademacher via Massart
3. Contraction inequality (Lipschitz composition)
4. Symmetrization connecting Rademacher to generalization

## References

* [Bartlett and Mendelson, *Rademacher and Gaussian Complexities*][bartlett2002]
* [Shalev-Shwartz and Ben-David, *Understanding Machine Learning*][shalev2014]
* [Mohri et al., *Foundations of Machine Learning*][mohri2018]
* [Agarwal et al., *RL: Theory and Algorithms*]
-/

import RLGeneralization.Complexity.VCDimension
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open Finset BigOperators Real Nat

noncomputable section

/-! ### Rademacher Complexity: Definitions and Basic Structure -/

/-- **Rademacher complexity bound**: An algebraic upper bound on the
    empirical Rademacher complexity R̂_n(F) for a function class.

    The Rademacher complexity depends on:
    - `n`: sample size
    - `bound`: the upper bound value R such that R̂_n(F) ≤ R

    We work with bounds rather than the complexity itself, since
    computing R̂_n(F) requires the measure-theoretic Rademacher
    construction. -/
structure RademacherBound where
  /-- Sample size -/
  n : ℕ
  /-- The upper bound on Rademacher complexity -/
  bound : ℝ
  /-- Sample size is positive -/
  hn : 0 < n
  /-- The bound is nonneg (Rademacher complexity is nonneg) -/
  hbound : 0 ≤ bound

namespace RademacherBound

variable (R : RademacherBound)

/-- The sample size as a positive real number. -/
def nReal : ℝ := (R.n : ℝ)

/-- The sample size is positive as a real number. -/
theorem nReal_pos : 0 < R.nReal :=
  Nat.cast_pos.mpr R.hn

/-- The sample size is nonzero as a real number. -/
theorem nReal_ne_zero : R.nReal ≠ 0 :=
  ne_of_gt R.nReal_pos

end RademacherBound

/-! ### Massart's Lemma: Finite Class Bound

Massart's lemma gives the fundamental bound for finite function classes:

  R̂_n(F) ≤ √(2·log|F|/n)

This is the starting point for all Rademacher complexity bounds. The
proof (in the measure-theoretic setting) uses the sub-Gaussian maximal
inequality: the maximum of |F| sub-Gaussian random variables with
parameter 1/n has expectation ≤ √(2·log|F|/n).

Here we establish the algebraic properties of this bound. -/

/-- **Massart's finite-class bound (value)**: √(2·log|F|/n).
    This is the upper bound on R̂_n(F) for a class of cardinality |F|. -/
def massartBound (cardF : ℕ) (n : ℕ) : ℝ :=
  Real.sqrt (2 * Real.log (cardF : ℝ) / n)

/-- Massart's bound is nonneg. -/
theorem massartBound_nonneg (cardF : ℕ) (n : ℕ) (_hF : 1 ≤ cardF) (_hn : 0 < n) :
    0 ≤ massartBound cardF n := by
  apply Real.sqrt_nonneg

/-- Massart's bound is positive when |F| ≥ 2. -/
theorem massartBound_pos (cardF : ℕ) (n : ℕ) (hF : 2 ≤ cardF) (hn : 0 < n) :
    0 < massartBound cardF n := by
  apply Real.sqrt_pos_of_pos
  apply _root_.div_pos
  · apply mul_pos (by norm_num : (0 : ℝ) < 2)
    exact Real.log_pos (by exact_mod_cast (show 1 < cardF by omega))
  · exact Nat.cast_pos.mpr hn

/-- Massart's bound squared: (√(2·log|F|/n))² = 2·log|F|/n. -/
theorem massartBound_sq (cardF : ℕ) (n : ℕ) (hF : 1 ≤ cardF) (hn : 0 < n) :
    massartBound cardF n ^ 2 = 2 * Real.log (cardF : ℝ) / n := by
  unfold massartBound
  rw [Real.sq_sqrt]
  apply div_nonneg
  · apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    exact Real.log_nonneg (by exact_mod_cast hF)
  · positivity

/-- **Massart's lemma (algebraic)**: For a finite function class F with
    |F| hypotheses, the Rademacher complexity bound satisfies:

      R_n(F) ≤ √(2·log|F|/n)

    This constructs the `RademacherBound` structure from the class
    cardinality and sample size. -/
def rademacher_finite_class (cardF : ℕ) (n : ℕ) (hF : 1 ≤ cardF) (hn : 0 < n) :
    RademacherBound where
  n := n
  bound := massartBound cardF n
  hn := hn
  hbound := massartBound_nonneg cardF n hF hn

/-! ### Monotonicity Properties of Massart's Bound -/

/-- Massart's bound increases with class size: if |F₁| ≤ |F₂| then
    √(2·log|F₁|/n) ≤ √(2·log|F₂|/n). -/
theorem massartBound_mono_cardF {cardF₁ cardF₂ : ℕ} (n : ℕ)
    (hF₁ : 1 ≤ cardF₁) (h : cardF₁ ≤ cardF₂) (hn : 0 < n) :
    massartBound cardF₁ n ≤ massartBound cardF₂ n := by
  unfold massartBound
  apply Real.sqrt_le_sqrt
  apply div_le_div_of_nonneg_right _ (by positivity : 0 < (n : ℝ)).le
  apply mul_le_mul_of_nonneg_left
  · exact Real.log_le_log (by exact_mod_cast hF₁) (by exact_mod_cast h)
  · norm_num

/-- Massart's bound decreases with sample size: if n₁ ≤ n₂ then
    √(2·log|F|/n₂) ≤ √(2·log|F|/n₁). -/
theorem massartBound_mono_n (cardF : ℕ) {n₁ n₂ : ℕ}
    (hF : 2 ≤ cardF) (hn₁ : 0 < n₁) (h : n₁ ≤ n₂) :
    massartBound cardF n₂ ≤ massartBound cardF n₁ := by
  unfold massartBound
  apply Real.sqrt_le_sqrt
  apply div_le_div_of_nonneg_left
  · apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    apply Real.log_nonneg
    have h1 : 1 ≤ cardF := by omega
    exact_mod_cast h1
  · exact Nat.cast_pos.mpr hn₁
  · exact_mod_cast h

/-! ### Rademacher from VC Dimension

When a function class has VC dimension d, the growth function bound gives
|F restricted to n points| ≤ (d+1)·n^d ≤ (en/d)^d for n ≥ d. Applying
Massart's lemma to this effective cardinality:

  R_n(F) ≤ √(2·log((d+1)·n^d)/n)
         ≤ √(2·(log(d+1) + d·log(n))/n)
         = O(√(d·log(n)/n))

This is the fundamental rate for VC classes. -/

/-- **VC-based Rademacher bound (value)**: √(2·(log(d+1) + d·log(n))/n).
    This bounds the Rademacher complexity of a class with VC dimension d
    on n samples. -/
def vcRademacherBound (d : ℕ) (n : ℕ) : ℝ :=
  Real.sqrt (2 * (Real.log (d + 1 : ℝ) + d * Real.log (n : ℝ)) / n)

/-- The VC-based Rademacher bound is nonneg. -/
theorem vcRademacherBound_nonneg (d : ℕ) (n : ℕ) (_hn : 1 ≤ n) (_hd : 1 ≤ d) :
    0 ≤ vcRademacherBound d n :=
  Real.sqrt_nonneg _

/-- **Massart subsumes VC**: The Massart bound with effective cardinality
    (d+1)·n^d dominates the VC-based Rademacher bound.
    Specifically: √(2·log((d+1)·n^d)/n) ≥ √(2·(log(d+1)+d·log(n))/n)
    since log((d+1)·n^d) = log(d+1) + d·log(n) when both are positive. -/
theorem massart_from_vc_growth (d : ℕ) (n : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d) :
    vcRademacherBound d n ≤
      massartBound ((d + 1) * n ^ d) n := by
  unfold vcRademacherBound massartBound
  apply Real.sqrt_le_sqrt
  apply div_le_div_of_nonneg_right _ (by positivity : 0 < (n : ℝ)).le
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  -- log(d+1) + d*log(n) ≤ log((d+1)*n^d) when both factors are positive
  have hd1 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have hn' : (0 : ℝ) < (n : ℝ) := by positivity
  have hnd : (0 : ℝ) < (n : ℝ) ^ d := by positivity
  have : ((((d + 1) * n ^ d : ℕ) : ℝ)) = ((d : ℝ) + 1) * (n : ℝ) ^ d := by
    push_cast; ring
  rw [this, Real.log_mul (ne_of_gt hd1) (ne_of_gt hnd), Real.log_pow]

/-- The VC-Rademacher bound constructs a `RademacherBound`. -/
def rademacher_from_vc_bound (d : ℕ) (n : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d) :
    RademacherBound where
  n := n
  bound := vcRademacherBound d n
  hn := by omega
  hbound := vcRademacherBound_nonneg d n hn hd

/-! ### Contraction Inequality

The Rademacher contraction (Talagrand-Ledoux) inequality states that
for a Lipschitz function φ with constant L:

  R_n(φ ∘ F) ≤ L · R_n(F)

where φ ∘ F = {φ ∘ f : f ∈ F}. This is crucial for deriving bounds
on classification loss classes from bounds on the underlying function
class.

We state this as an algebraic consequence: if R is a bound on
R_n(F), then L·R is a bound on R_n(φ∘F). -/

/-- Contraction preserves the `RademacherBound` structure. -/
def RademacherBound.contract (R : RademacherBound) (L : ℝ) (hL : 0 ≤ L) :
    RademacherBound where
  n := R.n
  bound := L * R.bound
  hn := R.hn
  hbound := mul_nonneg hL R.hbound

/-- The contracted bound has the expected value. -/
theorem RademacherBound.contract_bound (R : RademacherBound) (L : ℝ) (hL : 0 ≤ L) :
    (R.contract L hL).bound = L * R.bound := rfl

/-- Contraction with L = 1 preserves the bound. -/
theorem RademacherBound.contract_one (R : RademacherBound) :
    (R.contract 1 (le_refl 0 |>.trans one_pos.le)).bound = R.bound := by
  simp [contract_bound]

/-- Contraction composes: contracting by L₁ then L₂ gives L₂·L₁·R. -/
theorem RademacherBound.contract_compose (R : RademacherBound)
    (L₁ L₂ : ℝ) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) :
    ((R.contract L₁ hL₁).contract L₂ hL₂).bound = L₂ * L₁ * R.bound := by
  simp [contract_bound, mul_assoc]

/-! ### Generalization Bound from Rademacher Complexity

The symmetrization argument (see `Symmetrization.lean`) gives:

  E[sup_{f ∈ F} |P_n f - Pf|] ≤ 2·R_n(F)

where P_n f = (1/n)∑f(xᵢ) is the empirical mean and Pf = E[f(X)] is the
true mean. Combined with McDiarmid's inequality for concentration of
the supremum around its expectation, this gives the PAC bound:

  P(sup|P_n f - Pf| > 2·R_n + ε) ≤ exp(-nε²/2)

Equivalently, with probability ≥ 1-δ:

  sup|P_n f - Pf| ≤ 2·R_n + √(2·log(1/δ)/n) -/

/-- The generalization bound from a `RademacherBound` structure. -/
def RademacherBound.generalizationBound (R : RademacherBound) : ℝ :=
  2 * R.bound

/-- The generalization bound is nonneg. -/
theorem RademacherBound.generalizationBound_nonneg (R : RademacherBound) :
    0 ≤ R.generalizationBound :=
  mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) R.hbound

/-- **Rademacher PAC generalization bound (algebraic)**.
    [WRAPPER: Pure le_trans of deviation and combined bound hypotheses.
    Blocked on symmetrization (Rademacher ↔ uniform deviation) and
    McDiarmid's inequality, both requiring measure-theoretic integration.]

    With probability ≥ 1-δ over the sample:

      sup_{f ∈ F} |P_n f - Pf| ≤ 2·R_n(F) + √(2·log(1/δ)/n)

    Both the deviation bound and the combined bound are taken as
    hypotheses; the body is le_trans. -/
theorem rademacher_pac_bound
    {R_n_bound mcdiarmid_term eps : ℝ}
    (_hR : 0 ≤ R_n_bound)
    (_hM : 0 ≤ mcdiarmid_term)
    (h_combined : 2 * R_n_bound + mcdiarmid_term ≤ eps)
    {deviation : ℝ}
    (h_dev : deviation ≤ 2 * R_n_bound + mcdiarmid_term) :
    deviation ≤ eps :=
  le_trans h_dev h_combined

/-- **The McDiarmid concentration term**: √(2·log(1/δ)/n). -/
def mcdiarmidConcentrationTerm (n : ℕ) (δ : ℝ) : ℝ :=
  Real.sqrt (2 * Real.log (1 / δ) / n)

/-- The McDiarmid concentration term is nonneg. -/
theorem mcdiarmidConcentrationTerm_nonneg (n : ℕ) (δ : ℝ)
    (_hn : 0 < n) (_hδ : 0 < δ) (_hδ1 : δ < 1) :
    0 ≤ mcdiarmidConcentrationTerm n δ := by
  apply Real.sqrt_nonneg

/-- The McDiarmid concentration term is positive when δ ∈ (0,1). -/
theorem mcdiarmidConcentrationTerm_pos (n : ℕ) (δ : ℝ)
    (hn : 0 < n) (hδ : 0 < δ) (hδ1 : δ < 1) :
    0 < mcdiarmidConcentrationTerm n δ := by
  unfold mcdiarmidConcentrationTerm
  apply Real.sqrt_pos_of_pos
  exact _root_.div_pos
    (mul_pos (by norm_num : (0 : ℝ) < 2)
      (Real.log_pos (by rw [one_div]; exact one_lt_inv_iff₀.mpr ⟨hδ, hδ1⟩)))
    (Nat.cast_pos.mpr hn)

/-- **Full PAC bound**: 2·R_n + √(2·log(1/δ)/n) is the total PAC width. -/
def rademacherPACWidth (R : RademacherBound) (δ : ℝ) : ℝ :=
  R.generalizationBound + mcdiarmidConcentrationTerm R.n δ

/-- The full PAC width is nonneg. -/
theorem rademacherPACWidth_nonneg (R : RademacherBound) (δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    0 ≤ rademacherPACWidth R δ :=
  add_nonneg R.generalizationBound_nonneg
    (mcdiarmidConcentrationTerm_nonneg R.n δ R.hn hδ hδ1)

/-! ### Sample Complexity from Rademacher Bounds

To achieve ε-accuracy with probability ≥ 1-δ, we need:

  2·R_n(F) + √(2·log(1/δ)/n) ≤ ε

For the VC case where R_n ≤ √(2d·log(n)/n):
  2·√(2d·log(n)/n) + √(2·log(1/δ)/n) ≤ ε

The dominant term is O(√(d·log(n)/n)), giving n = O(d·log(n)/ε²).
By the self-referential bound log(n) ≤ log(d/ε²) + log log(...),
this simplifies to n = O((d·log(d/ε) + log(1/δ))/ε²). -/

/-- **Rademacher sample complexity formula**: The number of samples
    sufficient for ε-accurate uniform convergence using Rademacher
    complexity bounds.

    n_R(R, ε, δ) = (2R + √(2·log(1/δ)/n))² / ε²

    In practice, for VC classes with R_n ≤ √(2d·log(n)/n),
    the sufficient sample size is n = O((d·log(d/ε) + log(1/δ))/ε²). -/
def rademacherSampleComplexity (d : ℕ) (eps delta : ℝ) : ℝ :=
  (d * Real.log (d / eps) + Real.log (1 / delta)) / eps ^ 2

/-! ### Comparison: Rademacher vs VC vs PAC-Bayes

The three main approaches to generalization give different sample
complexity scalings:

1. **VC dimension**: n = O(d·log(d/ε)/ε²) — depends on d = VCDim
2. **Rademacher**: n = O(R_n²/ε² + log(1/δ)/ε²) — distribution-dependent
3. **PAC-Bayes**: n = O(KL(Q||P)/ε²) — depends on posterior concentration

The Rademacher approach interpolates: for worst-case distributions it
recovers the VC bound, but for favorable distributions it can be
much tighter (e.g., when F has small effective dimension). -/

/-! ### Rademacher for Specific Function Classes -/

/-- **Linear function class**: For a class of linear functions
    f(x) = ⟨w, x⟩ with ‖w‖ ≤ W and ‖x‖ ≤ X, the Rademacher
    complexity is R_n ≤ WX/√n.

    This is better than the VC bound of O(√(d/n)) when the norms
    are controlled and d is large. -/
def linearRademacherBound (W X : ℝ) (n : ℕ) : ℝ :=
  W * X / Real.sqrt (n : ℝ)

/-- The linear Rademacher bound is nonneg when W, X ≥ 0. -/
theorem linearRademacherBound_nonneg {W X : ℝ} {n : ℕ}
    (hW : 0 ≤ W) (hX : 0 ≤ X) (_hn : 0 < n) :
    0 ≤ linearRademacherBound W X n := by
  unfold linearRademacherBound
  apply div_nonneg (mul_nonneg hW hX)
  exact Real.sqrt_nonneg _

/-- The linear Rademacher bound decreases with sample size. -/
theorem linearRademacherBound_anti {W X : ℝ} {n₁ n₂ : ℕ}
    (hW : 0 < W) (hX : 0 < X) (hn₁ : 0 < n₁) (h : n₁ ≤ n₂) :
    linearRademacherBound W X n₂ ≤ linearRademacherBound W X n₁ := by
  unfold linearRademacherBound
  apply div_le_div_of_nonneg_left (mul_pos hW hX).le
  · exact Real.sqrt_pos_of_pos (by positivity)
  · exact Real.sqrt_le_sqrt (by exact_mod_cast h)

/-! ### Summary: Key Rademacher Complexity Results

1. **`massartBound`**: √(2·log|F|/n) — finite class bound
2. **`vcRademacherBound`**: √(2·(log(d+1) + d·log(n))/n) — VC-based bound
3. **`RademacherBound.contract`**: L·R bound for L-Lipschitz composition
4. **`rademacherPACWidth`**: 2·R + √(2·log(1/δ)/n) — full PAC width
5. **`rademacherSampleComplexity`**: O(d·log(d/ε)/ε²) — sufficient samples

The algebraic chain is:
  VC dim → growth function → log-cardinality → Massart → Rademacher →
  symmetrization (×2) → McDiarmid concentration → PAC generalization bound.

The measure-theoretic ingredients (Rademacher r.v. construction,
symmetrization proof, McDiarmid application) are deferred. The
algebraic consequences established here are sufficient for the
sample complexity analysis in the RL setting. -/

end
