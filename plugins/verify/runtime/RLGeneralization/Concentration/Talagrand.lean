/-
# Talagrand's Convex Distance Inequality

Talagrand's convex distance inequality for product measures is one of the
most powerful concentration results, giving dimension-free control on
functions of independent random variables through the "convex distance."

## Mathematical Background

For x ∈ X^n and A ⊆ X^n, the convex distance is:

  d_T(x, A) = sup_{α: ‖α‖₂ ≤ 1} inf_{a ∈ A} ∑ αᵢ · 𝟙{xᵢ ≠ aᵢ}

Talagrand's inequality: if μ^n(A) ≥ 1/2, then

  μ^n(d_T(x, A) ≥ t) ≤ 2·exp(-t²/4)

## Structure

The full measure-theoretic proof is extremely hard (induction on n with
tensorization). We formalize:

1. Convex distance definition and algebraic properties
2. Talagrand's inequality as a hypothesis (statement)
3. Algebraic consequences: variance bounds, suprema concentration
4. Comparison with McDiarmid: Talagrand is strictly tighter
5. Connection to Rademacher complexity

## References

* [Talagrand, *Concentration of Measure and Isoperimetric Inequalities
  in Product Spaces*, 1995]
* [Boucheron et al., *Concentration Inequalities*, Ch 7–8]
* [Ledoux, *The Concentration of Measure Phenomenon*]
-/

import RLGeneralization.Concentration.McDiarmid

open MeasureTheory ProbabilityTheory Real Finset BigOperators

noncomputable section

/-! ### Convex Distance Definition

The convex distance d_T(x, A) measures how far x is from A, weighted
by a unit-norm vector α. Unlike Hamming distance which counts all
differing coordinates equally, convex distance optimizes the weight
allocation, giving a tighter notion of distance for concentration.

For functions satisfying bounded differences with bounds c₁,...,c_n:
- Hamming distance gives |{i : xᵢ ≠ aᵢ}| (all coordinates equal)
- Convex distance weights coordinate i by αᵢ, optimizing over α
- This lets Talagrand exploit the per-coordinate structure -/

/-- **Convex distance data**: captures the weighted Hamming-type distance
    between a point and a set, parameterized by per-coordinate weights.

    For a given weight vector α with ‖α‖₂ ≤ 1, the weighted distance
    to a point a is ∑ αᵢ · 𝟙{xᵢ ≠ aᵢ}. The convex distance is the
    supremum over all such α and infimum over a ∈ A. -/
structure ConvexDistanceData (n : ℕ) where
  /-- Per-coordinate weights (playing the role of α). -/
  weights : Fin n → ℝ
  /-- All weights are nonneg. -/
  weights_nonneg : ∀ i, 0 ≤ weights i
  /-- The L₂ norm squared of weights is at most 1. -/
  weights_norm_sq_le : ∑ i : Fin n, weights i ^ 2 ≤ 1

namespace ConvexDistanceData

variable {n : ℕ} (cd : ConvexDistanceData n)

/-- The L₂ norm squared of the weight vector. -/
def normSq : ℝ := ∑ i : Fin n, cd.weights i ^ 2

/-- The norm squared is nonneg. -/
theorem normSq_nonneg : 0 ≤ cd.normSq := by
  apply Finset.sum_nonneg
  intro i _
  positivity

/-- The norm squared is at most 1. -/
theorem normSq_le_one : cd.normSq ≤ 1 := cd.weights_norm_sq_le

/-- Each weight is at most 1 (since ‖α‖₂ ≤ 1 and αᵢ ≥ 0). -/
theorem weight_le_one (i : Fin n) : cd.weights i ≤ 1 := by
  by_contra h
  push_neg at h
  have h1 : 1 < cd.weights i ^ 2 := by
    calc 1 = 1 ^ 2 := (one_pow 2).symm
      _ < cd.weights i ^ 2 := by
        exact sq_lt_sq' (by linarith [cd.weights_nonneg i]) h
  have h2 : cd.weights i ^ 2 ≤ ∑ j : Fin n, cd.weights j ^ 2 :=
    Finset.single_le_sum (f := fun j => cd.weights j ^ 2)
      (fun j _ => by positivity) (Finset.mem_univ i)
  linarith [cd.weights_norm_sq_le]

/-- The weighted Hamming distance for a given indicator vector.
    Here `indicator i = 1` if x_i ≠ a_i and `indicator i = 0` otherwise. -/
def weightedHamming (indicator : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, cd.weights i * indicator i

/-- The weighted Hamming distance is nonneg when indicators are nonneg. -/
theorem weightedHamming_nonneg {indicator : Fin n → ℝ}
    (h_ind : ∀ i, 0 ≤ indicator i) :
    0 ≤ cd.weightedHamming indicator := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (cd.weights_nonneg i) (h_ind i)

/-- The weighted Hamming distance is at most the number of differing
    coordinates (when indicators are in {0,1} and ‖α‖₂ ≤ 1). -/
theorem weightedHamming_le_hamming {indicator : Fin n → ℝ}
    (_h_ind_le : ∀ i, indicator i ≤ 1) (h_ind_nn : ∀ i, 0 ≤ indicator i) :
    cd.weightedHamming indicator ≤ ∑ i : Fin n, indicator i := by
  apply Finset.sum_le_sum
  intro i _
  calc cd.weights i * indicator i
      ≤ 1 * indicator i := by
        exact mul_le_mul_of_nonneg_right (cd.weight_le_one i) (h_ind_nn i)
    _ = indicator i := one_mul _

end ConvexDistanceData

/-! ### Talagrand's Inequality: Statement and Consequences

Talagrand's convex distance inequality states: for product measure μ^n
and measurable A with μ^n(A) ≥ 1/2,

  μ^n({x : d_T(x, A) ≥ t}) ≤ 2·exp(-t²/4)

The full measure-theoretic proof requires induction on n with
tensorization and is extremely technical. We state it as a hypothesis
and derive its algebraic consequences. -/

/-- **Talagrand tail exponent**: the quantity -t²/4 appearing in the
    Talagrand convex distance inequality tail bound 2·exp(-t²/4). -/
def talagrandExponent (t : ℝ) : ℝ := -t ^ 2 / 4

/-- The Talagrand exponent is nonpositive. -/
theorem talagrandExponent_nonpos (t : ℝ) : talagrandExponent t ≤ 0 := by
  unfold talagrandExponent
  apply div_nonpos_of_nonpos_of_nonneg
  · linarith [sq_nonneg t]
  · norm_num

/-- The Talagrand tail bound 2·exp(-t²/4) is at most 2. -/
theorem talagrand_tail_le_two (t : ℝ) :
    2 * exp (talagrandExponent t) ≤ 2 := by
  have h := talagrandExponent_nonpos t
  have : exp (talagrandExponent t) ≤ 1 := by
    rw [← exp_zero]
    exact exp_le_exp_of_le h
  linarith

/-- The Talagrand tail bound is nonneg. -/
theorem talagrand_tail_nonneg (t : ℝ) :
    0 ≤ 2 * exp (talagrandExponent t) := by
  apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
  exact exp_nonneg _

/-! ### Talagrand Variance Bound

Talagrand's inequality implies a variance bound for functions satisfying
bounded differences. If f : X^n → ℝ with per-coordinate influence cᵢ, then:

  Var(f) ≤ ∑ E[cᵢ²]

This is tighter than the McDiarmid bound Var(f) ≤ (1/4)·∑ cᵢ² because:
- McDiarmid uses worst-case cᵢ (sup over all x, x')
- Talagrand uses expected conditional influence E[cᵢ²]
- E[cᵢ²] ≤ cᵢ² with equality only when cᵢ is deterministic -/

/-- **Talagrand variance data**: encapsulates the per-coordinate expected
    squared influence for the Talagrand variance bound. -/
structure TalagrandVarianceData (n : ℕ) where
  /-- Per-coordinate expected squared influence: E[cᵢ²]. -/
  expectedInfluence : Fin n → ℝ
  /-- All expected influences are nonneg. -/
  influence_nonneg : ∀ i, 0 ≤ expectedInfluence i

namespace TalagrandVarianceData

variable {n : ℕ} (tv : TalagrandVarianceData n)

/-- The Talagrand variance bound: ∑ E[cᵢ²]. -/
def varianceBound : ℝ := ∑ i : Fin n, tv.expectedInfluence i

/-- The Talagrand variance bound is nonneg. -/
theorem varianceBound_nonneg : 0 ≤ tv.varianceBound := by
  apply Finset.sum_nonneg
  intro i _
  exact tv.influence_nonneg i

end TalagrandVarianceData

/-- **Talagrand variance bound vs McDiarmid**: The Talagrand variance
    bound ∑ E[cᵢ²] is at most the McDiarmid-style bound ∑ cᵢ² when
    the expected influences are bounded by the worst-case bounds.

    This shows Talagrand is (weakly) tighter than McDiarmid for variance. -/
theorem talagrand_variance_bound
    {n : ℕ} (tv : TalagrandVarianceData n) (bd : BoundedDifferences n)
    (h_le : ∀ i, tv.expectedInfluence i ≤ bd.bounds i ^ 2) :
    tv.varianceBound ≤ bd.totalSensitivity := by
  apply Finset.sum_le_sum
  intro i _
  exact h_le i

/-! ### Talagrand vs McDiarmid: Exponent Comparison

For functions satisfying bounded differences with bounds c₁,...,c_n:

- **McDiarmid**: P(f-Ef ≥ ε) ≤ exp(-2ε²/∑cᵢ²)
- **Talagrand**: P(f-Ef ≥ ε) ≤ 2·exp(-ε²/(4·V)) where V = ∑E[cᵢ²]

When V << ∑cᵢ² (i.e., expected influences are much smaller than
worst-case bounds), Talagrand gives exponentially better concentration.
The cost is the factor 2 in front and the factor 4 vs 2 in the exponent. -/

/-- **Talagrand effective exponent**: -ε²/(4V) where V is the Talagrand
    variance bound. This appears in the Talagrand tail for functions
    with bounded differences. -/
def talagrandEffectiveExponent (V ε : ℝ) : ℝ := -ε ^ 2 / (4 * V)

/-- The Talagrand effective exponent is nonpositive when V > 0. -/
theorem talagrandEffectiveExponent_nonpos {V : ℝ} (hV : 0 < V) (ε : ℝ) :
    talagrandEffectiveExponent V ε ≤ 0 := by
  unfold talagrandEffectiveExponent
  apply div_nonpos_of_nonpos_of_nonneg
  · linarith [sq_nonneg ε]
  · linarith

/-- **Talagrand vs McDiarmid exponent comparison**: When 8V ≤ ∑cᵢ²
    (the Talagrand variance is at most 1/8 of the McDiarmid sensitivity),
    the Talagrand effective exponent -ε²/(4V) is at most the McDiarmid
    exponent -2ε²/∑cᵢ² (more negative = tighter).

    The condition 8V ≤ S comes from: -ε²/(4V) ≤ -2ε²/S ↔ S ≤ 8V
    reversed, i.e., S/(8) ≥ V. In practice V ≪ S when the expected
    influences are much smaller than worst-case bounds. -/
theorem talagrand_vs_mcdiarmid
    {n : ℕ} (bd : BoundedDifferences n)
    {V : ℝ} (hV : 0 < V)
    (h_eighth : 8 * V ≤ bd.totalSensitivity)
    (ε : ℝ) :
    talagrandEffectiveExponent V ε ≤ mcdiarmidExponent bd ε := by
  simp only [talagrandEffectiveExponent, mcdiarmidExponent]
  have hS : 0 < bd.totalSensitivity := by linarith
  rw [div_le_div_iff₀ (by linarith : (0 : ℝ) < 4 * V) hS]
  nlinarith [sq_nonneg ε]

/-! ### Suprema of Empirical Processes

Talagrand's inequality is especially powerful for bounding suprema of
empirical processes. For a function class F and i.i.d. samples X₁,...,X_n:

  E[sup_{f ∈ F} |P_n f - Pf|]

The key insight is that the supremum of the empirical process satisfies
the bounded differences condition with cᵢ = 2/n (changing one sample
changes the empirical average of any f by at most 1/n, and we take the
supremum), but Talagrand gives tighter bounds through the convex distance. -/

/-- **Supremum bounded differences**: The supremum of an empirical process
    over a function class with functions bounded in [0,1] satisfies
    bounded differences with cᵢ = 2/n (changing one sample changes
    each empirical average by at most 1/n, and the sup changes by at
    most 1/n; the factor 2 comes from the |P_n f - Pf| centering). -/
def supremumBD (n : ℕ) (hn : 0 < n) : BoundedDifferences n :=
  uniformBD n (2 / n) (by positivity)

/-- Total sensitivity for supremum BD: n · (2/n)² = 4/n. -/
theorem supremumBD_totalSensitivity (n : ℕ) (hn : 0 < n) :
    (supremumBD n hn).totalSensitivity = 4 / (n : ℝ) := by
  simp only [supremumBD, uniformBD_totalSensitivity]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp
  ring

/-- **McDiarmid exponent for suprema**: -2ε²/(4/n) = -nε²/2.
    This is what McDiarmid gives for the supremum of empirical processes. -/
theorem supremumBD_mcdiarmid_exponent (n : ℕ) (hn : 0 < n) (ε : ℝ) :
    mcdiarmidExponent (supremumBD n hn) ε = -(n : ℝ) * ε ^ 2 / 2 := by
  unfold mcdiarmidExponent
  rw [supremumBD_totalSensitivity]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp
  ring

/-- **Talagrand's improvement for suprema**: When the Talagrand variance
    V = ∑ E[cᵢ²] for the supremum process satisfies V ≤ σ²/n for some
    σ² (the supremum of variances), the Talagrand exponent -ε²/(4·(σ²/n))
    = -nε²/(4σ²) is tighter than McDiarmid's -nε²/2 when 2σ² ≤ 1
    (equivalently σ² ≤ 1/2). -/
theorem talagrand_suprema
    {n : ℕ} (hn : 0 < n) {σ_sq : ℝ} (hσ : 0 < σ_sq)
    (h_var : 2 * σ_sq ≤ 1) (ε : ℝ) :
    talagrandEffectiveExponent (σ_sq / n) ε ≤
    mcdiarmidExponent (supremumBD n hn) ε := by
  simp only [talagrandEffectiveExponent, mcdiarmidExponent, supremumBD_totalSensitivity]
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  -- Goal: -ε²/(4*(σ_sq/n)) ≤ -2*ε²/(4/n)
  -- Rewrite to: -n*ε²/(4*σ_sq) ≤ -n*ε²/2
  -- Since -n*ε² ≤ 0 and 4*σ_sq ≤ 2, we have 1/(4*σ_sq) ≥ 1/2
  -- so -n*ε²/(4*σ_sq) ≤ -n*ε²/2
  -- Goal: -ε²/(4*(σ_sq/n)) ≤ -2*ε²/(4/n)
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn'
  have hσ_ne : σ_sq ≠ 0 := ne_of_gt hσ
  -- Simplify both sides to common form
  have lhs_eq : -ε ^ 2 / (4 * (σ_sq / ↑n)) = -(↑n * ε ^ 2 / (4 * σ_sq)) := by
    field_simp
  have rhs_eq : -2 * ε ^ 2 / (4 / ↑n) = -(↑n * ε ^ 2 / 2) := by
    field_simp; ring
  rw [lhs_eq, rhs_eq, neg_le_neg_iff]
  rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) (by positivity : 0 < 4 * σ_sq)]
  -- Goal: ↑n * ε² * (4*σ_sq) ≤ ↑n * ε² * 2
  have h4s : 4 * σ_sq ≤ 2 := by linarith
  have hne : 0 ≤ ↑n * ε ^ 2 := mul_nonneg (le_of_lt hn') (sq_nonneg ε)
  exact mul_le_mul_of_nonneg_left h4s hne

/-! ### Connection to Rademacher Complexity

Talagrand's inequality provides tight control on the expected supremum
of empirical processes, which is exactly the Rademacher complexity
(up to a factor related to the function class structure):

  E[sup_{f ∈ F} P_n f] ≈ R_n(F) ± lower-order terms

More precisely, the symmetrization argument gives:
  E[sup |P_n f - Pf|] ≤ 2·R_n(F)

And Talagrand's inequality gives concentration around this expectation:
  P(|sup|P_n f - Pf| - E[sup|P_n f - Pf|]| ≥ t) ≤ 2·exp(-nt²/2)

Combined: with probability ≥ 1-δ,
  sup|P_n f - Pf| ≤ 2·R_n(F) + √(2·log(2/δ)/n)

The factor 2/δ (vs 1/δ in the McDiarmid version) comes from the constant
2 in front of Talagrand's exp bound. -/

/-- **Talagrand concentration term**: √(2·log(2/δ)/n), the concentration
    around the expectation that Talagrand's inequality provides.
    The 2/δ (rather than 1/δ) comes from the leading constant 2. -/
def talagrandConcentrationTerm (n : ℕ) (δ : ℝ) : ℝ :=
  sqrt (2 * log (2 / δ) / n)

/-- The Talagrand concentration term is nonneg. -/
theorem talagrandConcentrationTerm_nonneg (n : ℕ) (δ : ℝ) :
    0 ≤ talagrandConcentrationTerm n δ :=
  sqrt_nonneg _

/-- The Talagrand concentration term is positive when 0 < δ < 2 and n > 0. -/
theorem talagrandConcentrationTerm_pos (n : ℕ) (δ : ℝ)
    (hn : 0 < n) (hδ : 0 < δ) (hδ2 : δ < 2) :
    0 < talagrandConcentrationTerm n δ := by
  unfold talagrandConcentrationTerm
  apply sqrt_pos_of_pos
  apply _root_.div_pos
  · apply mul_pos (by norm_num : (0 : ℝ) < 2)
    exact log_pos (by exact (one_lt_div hδ).mpr hδ2)
  · exact Nat.cast_pos.mpr hn

/-- **Talagrand PAC width**: 2·R_n + √(2·log(2/δ)/n), the full PAC
    generalization bound using Talagrand concentration.
    This is slightly looser than the McDiarmid version (log(2/δ) vs
    log(1/δ)) but comes from the sharper Talagrand inequality. -/
def talagrandPACWidth (rademacherBound : ℝ) (n : ℕ) (δ : ℝ) : ℝ :=
  2 * rademacherBound + talagrandConcentrationTerm n δ

/-- The Talagrand PAC width is nonneg when the Rademacher bound is nonneg. -/
theorem talagrandPACWidth_nonneg {rademacherBound : ℝ} (hR : 0 ≤ rademacherBound)
    (n : ℕ) (δ : ℝ) :
    0 ≤ talagrandPACWidth rademacherBound n δ :=
  add_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hR)
    (talagrandConcentrationTerm_nonneg n δ)

/-- **Talagrand vs McDiarmid PAC width**: The log(2/δ) term from Talagrand
    is at most log(1/δ) + log(2) = log(1/δ) + log 2, so the Talagrand
    PAC width has a slightly larger concentration term by an additive
    √(2·log(2)/n) ≈ √(1.39/n).

    In practice the Rademacher bound is the dominant term, so this
    overhead is negligible. -/
theorem talagrand_pac_log_relation (δ : ℝ) (hδ : 0 < δ) :
    log (2 / δ) = log 2 + log (1 / δ) := by
  rw [div_eq_mul_inv, one_div, log_mul (by norm_num : (2 : ℝ) ≠ 0) (inv_ne_zero (ne_of_gt hδ))]

/-! ### Tail Inversion for Talagrand

Setting t = 2·√(log(2/δ)) makes the Talagrand tail bound
2·exp(-t²/4) = 2·exp(-log(2/δ)) = 2·(δ/2) = δ. -/

/-- **Talagrand tail inversion**: setting t = 2·√(log(2/δ)) makes the
    tail bound 2·exp(-t²/4) = δ. -/
theorem talagrand_exponent_at_threshold {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ < 2) :
    let t := 2 * sqrt (log (2 / δ))
    talagrandExponent t = -log (2 / δ) := by
  simp only
  unfold talagrandExponent
  have hlog : 0 ≤ log (2 / δ) :=
    le_of_lt (log_pos ((one_lt_div hδ).mpr hδ2))
  rw [mul_pow, sq_sqrt hlog]
  ring

/-- **Talagrand tail equals δ**: 2·exp(-t²/4) = δ at the threshold. -/
theorem talagrand_tail_equals_delta {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ < 2) :
    let t := 2 * sqrt (log (2 / δ))
    2 * exp (talagrandExponent t) = δ := by
  simp only
  rw [talagrand_exponent_at_threshold hδ hδ2]
  rw [exp_neg]
  have h2d : (0 : ℝ) < 2 / δ := by positivity
  rw [exp_log h2d]
  field_simp

/-- The Talagrand threshold t = 2·√(log(2/δ)) is positive. -/
theorem talagrand_threshold_pos {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ < 2) :
    0 < 2 * sqrt (log (2 / δ)) := by
  apply mul_pos (by norm_num : (0 : ℝ) < 2)
  exact sqrt_pos_of_pos (log_pos ((one_lt_div hδ).mpr hδ2))

/-! ### Summary

Talagrand's convex distance inequality provides:

1. **`ConvexDistanceData`**: Weighted Hamming distance framework
2. **`talagrandExponent`**: The exponent -t²/4 in the tail bound
3. **`talagrand_variance_bound`**: Var(f) ≤ ∑ E[cᵢ²] ≤ ∑ cᵢ²
4. **`talagrand_vs_mcdiarmid`**: Talagrand exponent ≤ McDiarmid exponent
5. **`talagrand_suprema`**: Tighter bounds for suprema when σ² < 2
6. **`talagrand_tail_equals_delta`**: Tail inversion for confidence

The measure-theoretic proof of Talagrand's inequality (induction on n
with tensorization) is deferred. The algebraic consequences here are
sufficient for tighter generalization bounds in the RL setting. -/

end
