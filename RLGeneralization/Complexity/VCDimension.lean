/-
# VC Dimension Theory and Sauer-Shelah Lemma

Formalizes VC dimension theory for hypothesis classes, the Sauer-Shelah
growth function bound, and sample complexity results for uniform convergence.

## Mathematical Background

The VC dimension of a hypothesis class H over domain X is the largest m
such that some subset of X of size m is shattered by H. The Sauer-Shelah
lemma bounds the growth function (number of distinct labelings on n points):

  Π_H(n) ≤ ∑_{i=0}^{d} C(n,i)

where d = VCDim(H). For n ≥ d, this yields Π_H(n) ≤ (en/d)^d.

## Main Results

* `vcGrowthBound` -- growth function bound: ∑_{i=0}^{d} C(n,i)
* `sauer_shelah_family` -- Sauer-Shelah for set families (from Mathlib)
* `vcGrowthBound_le_two_pow` -- growth bound ≤ 2^n
* `vcGrowthBound_le_succ_mul_pow` -- growth bound ≤ (d+1)*n^d
* `vc_dimension_summary` -- combined chain: |𝒜| ≤ (d+1)*n^d
* `vc_vs_pac_bayes` -- comparison: VC O(d*log/ε²) vs PAC-Bayes O(KL/ε²)

## Approach

We build on Mathlib's `Finset.Shatters`, `Finset.vcDim`, and the
Sauer-Shelah lemma `Finset.card_shatterer_le_sum_vcDim` from
`Mathlib.Combinatorics.SetFamily.Shatter`. We define algebraic growth
function bounds and derive sample complexity formulas.

## References

* [Vapnik and Chervonenkis, *On the Uniform Convergence of Relative
  Frequencies of Events to Their Probabilities*][vapnik1971]
* [Sauer, *On the Density of Families of Sets*][sauer1972]
* [Shelah, *A Combinatorial Problem*][shelah1972]
* [Agarwal et al., *RL: Theory and Algorithms*]
-/

import Mathlib.Combinatorics.SetFamily.Shatter
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset BigOperators Real Nat

noncomputable section

/-! ### Growth Function Bound -/

/-- The Sauer-Shelah growth function bound: ∑_{i=0}^{d} C(n,i).
    This is the combinatorial upper bound on the number of distinct
    labelings that a hypothesis class of VC dimension d can induce
    on n points. -/
def vcGrowthBound (n d : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (d + 1), n.choose i

/-! ### Sauer-Shelah Lemma (from Mathlib) -/

/-- **Sauer-Shelah lemma for set families**: The cardinality of a set family
    is bounded by the growth function evaluated at the VC dimension.

    This combines Mathlib's `card_le_card_shatterer` (Pajor's variant)
    with `card_shatterer_le_sum_vcDim`. -/
theorem sauer_shelah_family {α : Type*} [DecidableEq α] [Fintype α]
    (𝒜 : Finset (Finset α)) :
    #𝒜 ≤ vcGrowthBound (Fintype.card α) 𝒜.vcDim := by
  unfold vcGrowthBound
  have h := (Finset.card_le_card_shatterer 𝒜).trans
    (Finset.card_shatterer_le_sum_vcDim (𝒜 := 𝒜))
  simp only [← Nat.range_succ_eq_Iic] at h
  exact h

/-! ### Growth Bound: Basic Properties -/

/-- The growth bound is at least 1 (via the C(n,0) = 1 term). -/
lemma one_le_vcGrowthBound (n d : ℕ) : 1 ≤ vcGrowthBound n d := by
  unfold vcGrowthBound
  calc 1 = n.choose 0 := by simp
    _ ≤ ∑ i ∈ Finset.range (d + 1), n.choose i :=
        Finset.single_le_sum (fun i _ => Nat.zero_le _)
          (Finset.mem_range.mpr (by omega))

/-- Growth bound is monotone in the VC dimension parameter. -/
lemma vcGrowthBound_mono_right (n : ℕ) {d₁ d₂ : ℕ} (h : d₁ ≤ d₂) :
    vcGrowthBound n d₁ ≤ vcGrowthBound n d₂ := by
  unfold vcGrowthBound
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (by omega))
    (fun i _ _ => Nat.zero_le _)

/-- Growth bound is monotone in n. -/
lemma vcGrowthBound_mono_left {n₁ n₂ : ℕ} (h : n₁ ≤ n₂) (d : ℕ) :
    vcGrowthBound n₁ d ≤ vcGrowthBound n₂ d := by
  unfold vcGrowthBound
  exact Finset.sum_le_sum (fun i _ => Nat.choose_le_choose i h)

/-! ### Growth Bound: Upper Bounds -/

/-- The growth bound is at most 2^n (since it's a partial sum of row n
    of Pascal's triangle, and the full sum is 2^n). -/
theorem vcGrowthBound_le_two_pow (n d : ℕ) :
    vcGrowthBound n d ≤ 2 ^ n := by
  unfold vcGrowthBound
  induction d with
  | zero =>
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, Nat.choose_zero_right]
    exact Nat.one_le_two_pow
  | succ d ih =>
    rw [Finset.sum_range_succ]
    by_cases hle : d + 1 ≤ n
    · -- d + 1 ≤ n, so d + 2 ≤ n + 1
      -- Use that partial sum ≤ full sum since all terms are nonneg
      calc ∑ i ∈ Finset.range (d + 1), n.choose i + n.choose (d + 1)
          ≤ ∑ i ∈ Finset.range (n + 1), n.choose i := by
            rw [← Finset.sum_range_succ]
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.range_mono (by omega))
              (fun i _ _ => Nat.zero_le _)
        _ = 2 ^ n := Nat.sum_range_choose n
    · push_neg at hle
      rw [Nat.choose_eq_zero_of_lt hle, add_zero]
      exact ih

/-- Each binomial coefficient C(n,i) ≤ n^d when i ≤ d and 1 ≤ n,
    using C(n,i) ≤ n^i ≤ n^d. -/
private lemma choose_le_pow_of_le (n : ℕ) {d i : ℕ}
    (hi : i ≤ d) (hn : 1 ≤ n) :
    n.choose i ≤ n ^ d :=
  (Nat.choose_le_pow n i).trans (Nat.pow_le_pow_right hn hi)

/-- The growth bound satisfies ∑_{i=0}^d C(n,i) ≤ (d+1) * n^d when n ≥ 1.
    This is the polynomial upper bound on the Sauer-Shelah growth function. -/
theorem vcGrowthBound_le_succ_mul_pow (n : ℕ) {d : ℕ} (hn : 1 ≤ n) :
    vcGrowthBound n d ≤ (d + 1) * n ^ d := by
  unfold vcGrowthBound
  calc ∑ i ∈ Finset.range (d + 1), n.choose i
      ≤ ∑ _i ∈ Finset.range (d + 1), n ^ d := by
        exact Finset.sum_le_sum (fun i hi => by
          have : i < d + 1 := Finset.mem_range.mp hi
          exact choose_le_pow_of_le n (by omega) hn)
    _ = (d + 1) * n ^ d := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-! ### Finite Hypothesis Class Bound -/

/-- **Finite class bound**: A finite set family over a type with n elements
    has at most 2^n elements. This is a direct consequence of Sauer-Shelah. -/
theorem card_le_two_pow_card {α : Type*} [Fintype α]
    (𝒜 : Finset (Finset α)) :
    #𝒜 ≤ 2 ^ Fintype.card α := by
  classical
  exact (sauer_shelah_family 𝒜).trans (vcGrowthBound_le_two_pow _ _)

/-! ### VC Dimension for Abstract Hypothesis Classes -/

/-- A hypothesis class represented as a finite collection of functions
    from a finite domain X to Bool (binary classification). -/
structure HypothesisClass (X : Type*) [Fintype X] [DecidableEq X] where
  /-- Number of hypotheses -/
  size : ℕ
  hsize : 0 < size
  /-- The hypotheses: functions from X to Bool -/
  hypotheses : Fin size → (X → Bool)

namespace HypothesisClass

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Convert a hypothesis class to a set family over X.
    Each hypothesis h : X → Bool induces the set {x | h(x) = true}. -/
def toSetFamily (H : HypothesisClass X) : Finset (Finset X) :=
  (Finset.univ : Finset (Fin H.size)).image
    (fun i => Finset.univ.filter (fun x => H.hypotheses i x = true))

/-- The VC dimension of a hypothesis class, via the set family representation. -/
def vcDimension (H : HypothesisClass X) : ℕ :=
  H.toSetFamily.vcDim

/-- The growth function: number of distinct labelings on n points.
    Bounded by the growth function bound via Sauer-Shelah. -/
theorem growth_function_bound (H : HypothesisClass X) :
    #H.toSetFamily ≤ vcGrowthBound (Fintype.card X) H.vcDimension :=
  sauer_shelah_family H.toSetFamily

/-- Size of hypothesis class is at most 2^|X|. -/
theorem size_le_two_pow_card (H : HypothesisClass X) :
    #H.toSetFamily ≤ 2 ^ Fintype.card X :=
  card_le_two_pow_card H.toSetFamily

end HypothesisClass

/-! ### Real-Valued Growth Function Bounds -/

/-- The growth function bound cast to ℝ. -/
def vcGrowthBoundReal (n d : ℕ) : ℝ := (vcGrowthBound n d : ℝ)

/-- Growth bound is at least 1 as a real number. -/
lemma one_le_vcGrowthBoundReal (n d : ℕ) : (1 : ℝ) ≤ vcGrowthBoundReal n d :=
  Nat.one_le_cast.mpr (one_le_vcGrowthBound n d)

/-- Growth bound is positive as a real number. -/
lemma vcGrowthBoundReal_pos (n d : ℕ) : 0 < vcGrowthBoundReal n d :=
  lt_of_lt_of_le one_pos (one_le_vcGrowthBoundReal n d)

/-- The log of the growth bound is nonneg. -/
lemma log_vcGrowthBoundReal_nonneg (n d : ℕ) :
    0 ≤ Real.log (vcGrowthBoundReal n d) :=
  Real.log_nonneg (one_le_vcGrowthBoundReal n d)

/-- **Polynomial growth bound (real-valued)**: the growth function
    satisfies Π(n,d) ≤ (d+1) * n^d for n ≥ 1. -/
theorem vcGrowthBoundReal_le_succ_mul_pow (n : ℕ) {d : ℕ} (hn : 1 ≤ n) :
    vcGrowthBoundReal n d ≤ (d + 1 : ℝ) * (n : ℝ) ^ d := by
  unfold vcGrowthBoundReal
  exact_mod_cast vcGrowthBound_le_succ_mul_pow n hn

/-- **Log of growth bound**: log(Π(n,d)) ≤ log(d+1) + d*log(n) for n ≥ 1.
    This is the key estimate for sample complexity analysis:
    the effective log-cardinality of the hypothesis class restricted
    to n points grows as d*log(n). -/
theorem log_vcGrowthBound_le (n : ℕ) {d : ℕ} (hn : 1 ≤ n) (hd : 1 ≤ d) :
    Real.log (vcGrowthBoundReal n d) ≤
      Real.log (d + 1 : ℝ) + d * Real.log (n : ℝ) := by
  calc Real.log (vcGrowthBoundReal n d)
      ≤ Real.log ((d + 1 : ℝ) * (n : ℝ) ^ d) := by
        apply Real.log_le_log (vcGrowthBoundReal_pos n d)
        exact vcGrowthBoundReal_le_succ_mul_pow n hn
    _ = Real.log (d + 1 : ℝ) + Real.log ((n : ℝ) ^ d) := by
        rw [Real.log_mul (by positivity) (by positivity)]
    _ = Real.log (d + 1 : ℝ) + d * Real.log (n : ℝ) := by
        rw [Real.log_pow]

/-! ### Growth Bound: Special Values -/

/-- The growth function bound with d = 0 is 1 (only C(n,0) = 1). -/
@[simp]
lemma vcGrowthBound_zero_right (n : ℕ) : vcGrowthBound n 0 = 1 := by
  simp [vcGrowthBound]

/-- The growth function bound at d = 1 is n+1. -/
lemma vcGrowthBound_one (n : ℕ) : vcGrowthBound n 1 = n + 1 := by
  simp [vcGrowthBound, Finset.sum_range_succ]
  omega

/-! ### VC-Based Sample Complexity: Algebraic Core -/

/-- **VC sample complexity formula**: The number of samples sufficient for
    ε-accurate uniform convergence with a hypothesis class of VC dimension d.

    n_VC(d, ε, δ) = d * (log(d/ε) + log(1/δ)) / ε²

    This definition captures the well-known sample complexity scaling. -/
def vcSampleComplexity (d : ℕ) (eps delta : ℝ) : ℝ :=
  (d * (Real.log (d / eps) + Real.log (1 / delta))) / eps ^ 2

/-- **PAC-Bayes sample complexity formula** (for comparison).

    n_PB(KL, ε, δ) = (KL + log(1/δ)) / (2 * ε²)

    where KL = KL(Q||P) is the KL divergence between posterior and prior. -/
def pacBayesSampleComplexity (kl eps delta : ℝ) : ℝ :=
  (kl + Real.log (1 / delta)) / (2 * eps ^ 2)

/-! ### Comparison: VC Dimension vs PAC-Bayes -/

/-- **VC vs PAC-Bayes sample complexity comparison**.

    For a finite hypothesis class, the VC sample complexity uses
    d * log(d/ε) / ε², where d = VCDim(H). The PAC-Bayes sample
    complexity with uniform prior uses log|H| / ε². Since d ≤ log|H|,
    the VC complexity is at most log|H| * (log-terms) / ε².

    When d << log|H|, VC gives a tighter bound because it exploits
    the geometric structure (shattering) rather than just counting. -/
theorem vc_vs_pac_bayes
    {d : ℕ} {logH eps delta : ℝ}
    (_heps : 0 < eps) (_hdelta : 0 < delta)
    (_hlogH : 0 ≤ logH)
    (hd_le : (d : ℝ) ≤ logH)
    (hlog_nonneg : 0 ≤ Real.log (d / eps) + Real.log (1 / delta)) :
    vcSampleComplexity d eps delta ≤
      logH * (Real.log (d / eps) + Real.log (1 / delta)) / eps ^ 2 := by
  unfold vcSampleComplexity
  apply div_le_div_of_nonneg_right _ (by positivity : 0 < eps ^ 2).le
  exact mul_le_mul_of_nonneg_right hd_le hlog_nonneg

/-- **When PAC-Bayes beats VC**: If the KL divergence KL(Q||P)
    is much smaller than d * log(d/ε), then PAC-Bayes sample
    complexity is smaller. This is the case when the posterior
    is concentrated near the prior.

    Formally: if KL ≤ d * log(d/ε) and d * log(d/ε) > 0,
    then n_PB ≤ n_VC (up to the factor of 2). -/
theorem pac_bayes_beats_vc_when_kl_small
    {d : ℕ} {kl eps delta : ℝ}
    (_heps : 0 < eps) (_hdelta : 0 < delta)
    (hkl_nonneg : 0 ≤ kl + Real.log (1 / delta))
    (hkl_small : kl + Real.log (1 / delta) ≤
      d * (Real.log (d / eps) + Real.log (1 / delta))) :
    pacBayesSampleComplexity kl eps delta ≤
      vcSampleComplexity d eps delta := by
  unfold pacBayesSampleComplexity vcSampleComplexity
  -- (kl+log)/(2ε²) ≤ d*L/ε² ⟺ (kl+log)/2 ≤ d*L ⟺ kl+log ≤ 2*d*L
  -- From hkl_small and hkl_nonneg: d*L ≥ kl+log ≥ 0, so 2*d*L ≥ d*L ≥ kl+log
  have hL_nonneg : 0 ≤ d * (Real.log (d / eps) + Real.log (1 / delta)) :=
    le_trans hkl_nonneg hkl_small
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * eps ^ 2)
    (by positivity : (0 : ℝ) < eps ^ 2)]
  nlinarith [sq_nonneg eps]

/-! ### Summary: Key VC Dimension Facts -/

/-- **Summary theorem**: For a set family 𝒜 over a finite type with n elements
    and VC dimension d (where n ≥ 1):

    (1) |𝒜| ≤ ∑_{i=0}^d C(n,i)    [Sauer-Shelah]
    (2) ∑_{i=0}^d C(n,i) ≤ 2^n     [trivial bound]
    (3) ∑_{i=0}^d C(n,i) ≤ (d+1)*n^d  [polynomial bound]

    This gives the chain: |𝒜| ≤ (d+1)*n^d, so that
    log|𝒜| ≤ log(d+1) + d*log(n), which is the growth rate used
    in uniform convergence bounds. -/
theorem vc_dimension_summary {α : Type*} [DecidableEq α] [Fintype α]
    (𝒜 : Finset (Finset α))
    (hn : 1 ≤ Fintype.card α) :
    (#𝒜 : ℝ) ≤ (𝒜.vcDim + 1 : ℝ) * (Fintype.card α : ℝ) ^ 𝒜.vcDim := by
  have h1 := sauer_shelah_family 𝒜
  have h2 := vcGrowthBound_le_succ_mul_pow (Fintype.card α) (d := 𝒜.vcDim) hn
  exact_mod_cast h1.trans h2

/-- **Log-form summary**: log|𝒜| ≤ log(d+1) + d*log(n) where d = vcDim(𝒜)
    and n = |α|. This is the effective sample complexity scaling. -/
theorem vc_dimension_log_summary {α : Type*} [DecidableEq α] [Fintype α]
    (𝒜 : Finset (Finset α))
    (hn : 1 ≤ Fintype.card α) (hd : 1 ≤ 𝒜.vcDim)
    (h𝒜 : 𝒜.Nonempty) :
    Real.log (#𝒜 : ℝ) ≤
      Real.log (𝒜.vcDim + 1 : ℝ) + 𝒜.vcDim * Real.log (Fintype.card α : ℝ) := by
  have h_card_pos : (0 : ℝ) < #𝒜 := Nat.cast_pos.mpr h𝒜.card_pos
  calc Real.log (#𝒜 : ℝ)
      ≤ Real.log (vcGrowthBoundReal (Fintype.card α) 𝒜.vcDim) := by
        apply Real.log_le_log h_card_pos
        unfold vcGrowthBoundReal
        exact Nat.cast_le.mpr (sauer_shelah_family 𝒜)
    _ ≤ Real.log (𝒜.vcDim + 1 : ℝ) + 𝒜.vcDim * Real.log (Fintype.card α : ℝ) :=
        log_vcGrowthBound_le (Fintype.card α) hn hd

end
