/-
# Generative Model Core

Trusted probability-space infrastructure for the generative model:
the product measure over independent transition samples, the empirical
transition random variable, and the PAC concentration theorem for the
empirical kernel.

## Main Results

* `transitionPMF` - P(.|s,a) as a PMF
* `generativeModelMeasure` - full product over all (s,a,i) triples
* `samples_iIndepFun` - samples are independent (from `iIndepFun_pi`)
* `sampleCoords_iIndepFun` - fixed-(s,a) coordinates are independent
* `indicator_expectation` - E[1{X = s'}] = P(s'|s,a)
* `coordinate_indicator_expectation` - product-space version of the same fact
* `empirical_transition_entry_concentration` - two-sided per-entry concentration
* `generative_model_pac` - union-bound PAC event for the full empirical kernel

## References

* [Azar, Munos, Kappen, *Minimax PAC bounds on the sample complexity
  of RL with a generative model*][azar2013]
* [Agarwal et al., *RL: Theory and Algorithms*]
-/

import RLGeneralization.Concentration.Hoeffding
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Independence.Basic

open Finset BigOperators MeasureTheory ProbabilityTheory ENNReal

noncomputable section

namespace FiniteMDP

variable (M : FiniteMDP)

/-! ### Measurable spaces on finite state/action spaces -/

/-- Discrete measurable space on S: every subset is measurable. -/
instance measurableSpaceS : MeasurableSpace M.S := ⊤

/-- Discrete measurable space on A: every subset is measurable. -/
instance measurableSpaceA : MeasurableSpace M.A := ⊤

/-- S has discrete measurable space. -/
instance discreteMeasurableSpaceS : DiscreteMeasurableSpace M.S where
  forall_measurableSet _ := MeasurableSpace.measurableSet_top

/-- A has discrete measurable space. -/
instance discreteMeasurableSpaceA : DiscreteMeasurableSpace M.A where
  forall_measurableSet _ := MeasurableSpace.measurableSet_top

/-! ### Transition kernel as a product measure -/

/-- The transition kernel P(.|s,a) viewed as a PMF on the finite state space. -/
def transitionPMF (s : M.S) (a : M.A) : PMF M.S :=
  PMF.ofFintype (fun s' => ENNReal.ofReal (M.P s a s'))
    (by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun s' _ => M.P_nonneg s a s')]
      simp [M.P_sum_one s a])

/-- The PMF assigns the correct probability to each state. -/
lemma transitionPMF_apply (s : M.S) (a : M.A) (s' : M.S) :
    M.transitionPMF s a s' = ENNReal.ofReal (M.P s a s') := by
  simp [transitionPMF, PMF.ofFintype_apply]

/-- Measure on a single sample: P(.|s,a) as a probability measure on S. -/
def singleSampleMeasure (s : M.S) (a : M.A) : Measure M.S :=
  (M.transitionPMF s a).toMeasure

/-- Each single-sample measure is a probability measure. -/
instance singleSampleMeasure_prob (s : M.S) (a : M.A) :
    IsProbabilityMeasure (M.singleSampleMeasure s a) :=
  PMF.toMeasure.isProbabilityMeasure _

/-- Index type for the generative model sample space. -/
abbrev SampleIndex (N : ℕ) := M.S × M.A × Fin N

/-- The full generative model measure: product of independent
categorical samples P(.|s,a) for each (s,a,i) triple. -/
def generativeModelMeasure (N : ℕ) :
    Measure (M.SampleIndex N → M.S) :=
  Measure.pi (fun idx => M.singleSampleMeasure idx.1 idx.2.1)

/-- The generative model measure is a probability measure. -/
instance generativeModelMeasure_prob {N : ℕ} [NeZero N] :
    IsProbabilityMeasure (M.generativeModelMeasure N) := by
  unfold generativeModelMeasure
  infer_instance

/-! ### Independence and empirical transitions -/

/-- The coordinate projections from the generative model space are independent. -/
theorem samples_iIndepFun (N : ℕ) :
    iIndepFun (m := fun (_ : M.SampleIndex N) => M.measurableSpaceS)
      (fun idx (ω : M.SampleIndex N → M.S) => ω idx)
      (M.generativeModelMeasure N) := by
  unfold generativeModelMeasure
  exact iIndepFun_pi (fun _ => aemeasurable_id)

/-- The empirical transition kernel constructed from a point in the generative-model
sample space. -/
def empiricalTransitionRV {N : ℕ} (hN : 0 < N)
    (ω : M.SampleIndex N → M.S) :
    M.S → M.A → M.S → ℝ :=
  fun s a s' => M.empiricalTransition hN (fun s a i => ω (s, a, i)) s a s'

/-- The coordinate samples for a fixed state-action pair form an independent family. -/
theorem sampleCoords_iIndepFun {N : ℕ} (s : M.S) (a : M.A) :
    iIndepFun (fun i : Fin N => fun ω : M.SampleIndex N → M.S => ω (s, a, i))
      (M.generativeModelMeasure N) := by
  exact (M.samples_iIndepFun N).precomp (fun {_ _} h => by simpa using h)

/-- The empirical transition entry is measurable as a function of the generative-model
sample point. -/
theorem empiricalTransitionRV_measurable {N : ℕ} (hN : 0 < N)
    (s : M.S) (a : M.A) (s' : M.S) :
    Measurable (fun ω : M.SampleIndex N → M.S => M.empiricalTransitionRV hN ω s a s') := by
  rw [show (fun ω : M.SampleIndex N → M.S => M.empiricalTransitionRV hN ω s a s') =
      fun ω => (∑ i : Fin N, M.transitionIndicator s' (ω (s, a, i))) / N by
        funext ω
        simpa [empiricalTransitionRV] using
          M.empirical_as_indicator_sum hN (fun s a i => ω (s, a, i)) s a s']
  refine Measurable.div_const ?_ (N : ℝ)
  exact Finset.measurable_sum Finset.univ (fun i _ => by
    exact (Measurable.of_discrete (f := M.transitionIndicator s')).comp
      (measurable_pi_apply (s, a, i)))

/-- The empirical transition kernel extracted from a generative-model sample point
is pointwise nonnegative. -/
lemma empiricalTransitionRV_nonneg {N : ℕ} (hN : 0 < N)
    (ω : M.SampleIndex N → M.S) (s : M.S) (a : M.A) (s' : M.S) :
    0 ≤ M.empiricalTransitionRV hN ω s a s' := by
  simpa [empiricalTransitionRV] using
    M.empiricalTransition_nonneg hN (fun s a i => ω (s, a, i)) s a s'

/-- The empirical transition kernel extracted from a generative-model sample point
sums to one for every state-action pair. -/
lemma empiricalTransitionRV_sum_one {N : ℕ} (hN : 0 < N)
    (ω : M.SampleIndex N → M.S) (s : M.S) (a : M.A) :
    ∑ s', M.empiricalTransitionRV hN ω s a s' = 1 := by
  simpa [empiricalTransitionRV] using
    M.empiricalTransition_sum_one hN (fun s a i => ω (s, a, i)) s a

/-! ### Indicator expectations -/

/-- E[1{X = s'}] = P(s'|s,a) under the single-sample measure. -/
theorem indicator_expectation (s : M.S) (a : M.A) (s' : M.S) :
    ∫ x, M.transitionIndicator s' x ∂(M.singleSampleMeasure s a) =
    M.P s a s' := by
  simp only [singleSampleMeasure]
  rw [PMF.integral_eq_sum]
  simp only [transitionIndicator, M.transitionPMF_apply]
  simp only [ENNReal.toReal_ofReal (M.P_nonneg s a _)]
  conv_lhs => arg 2; ext x; rw [show (if x = s' then (1 : ℝ) else 0) =
    if x = s' then 1 else 0 from rfl]
  simp [Finset.sum_ite_eq', Finset.mem_univ]

/-- E[1{X = s'}²] = E[1{X = s'}], since the indicator is idempotent. -/
lemma indicator_sq_eq (s' x : M.S) :
    (M.transitionIndicator s' x) ^ 2 = M.transitionIndicator s' x := by
  simp only [transitionIndicator]
  split_ifs <;> norm_num

/-- Variance of the raw indicator is trivially bounded by one. -/
theorem indicator_second_moment_le (s : M.S) (a : M.A) (s' : M.S) :
    ∫ x, (M.transitionIndicator s' x) ^ 2 ∂(M.singleSampleMeasure s a) ≤ 1 := by
  have h_sq : ∫ x, (M.transitionIndicator s' x) ^ 2
      ∂(M.singleSampleMeasure s a) =
      ∫ x, M.transitionIndicator s' x ∂(M.singleSampleMeasure s a) := by
    congr 1
    ext x
    exact M.indicator_sq_eq s' x
  rw [h_sq, M.indicator_expectation s a s']
  calc
    M.P s a s'
      ≤ ∑ s'', M.P s a s'' :=
        Finset.single_le_sum (fun s'' _ => M.P_nonneg s a s'') (Finset.mem_univ s')
    _ = 1 := M.P_sum_one s a

/-- The expectation of an indicator evaluated at a fixed coordinate of the generative-model
product space matches the underlying transition probability. -/
theorem coordinate_indicator_expectation {N : ℕ} [NeZero N]
    (s : M.S) (a : M.A) (i : Fin N) (s' : M.S) :
    ∫ ω : M.SampleIndex N → M.S, M.transitionIndicator s' (ω (s, a, i))
      ∂(M.generativeModelMeasure N) = M.P s a s' := by
  have h_eval :
      ∫ ω : M.SampleIndex N → M.S, M.transitionIndicator s' (ω (s, a, i))
        ∂(M.generativeModelMeasure N) =
      ∫ x : M.S, M.transitionIndicator s' x ∂(M.singleSampleMeasure s a) := by
    simpa [generativeModelMeasure] using
      (MeasureTheory.integral_comp_eval
        (μ := fun idx : M.SampleIndex N => M.singleSampleMeasure idx.1 idx.2.1)
        (i := (s, a, i))
        (f := M.transitionIndicator s')
        ((Measurable.of_discrete (f := M.transitionIndicator s')).aestronglyMeasurable))
  exact h_eval.trans (M.indicator_expectation s a s')

/-! ### Empirical transition concentration -/

/-- Two-sided Hoeffding bound for one empirical transition entry under the generative-model
product measure. -/
theorem empirical_transition_entry_concentration
    {N : ℕ} (hN : 0 < N)
    (s : M.S) (a : M.A) (s' : M.S)
    (eps_0 : ℝ) (heps_0 : 0 < eps_0) :
    (M.generativeModelMeasure N).real
      {ω | eps_0 ≤ |M.P s a s' - M.empiricalTransitionRV hN ω s a s'|} ≤
      2 * Real.exp (-2 * (N : ℝ) * eps_0 ^ 2) := by
  let _ : NeZero N := ⟨Nat.ne_of_gt hN⟩
  let p : ℝ := M.P s a s'
  let csg : NNReal := (1 / 4 : NNReal)
  let Y : Fin N → (M.SampleIndex N → M.S) → ℝ :=
    fun i ω => M.transitionIndicator s' (ω (s, a, i))
  let X : Fin N → (M.SampleIndex N → M.S) → ℝ :=
    fun i ω => Y i ω - p
  have h_indep_Y :
      iIndepFun Y (M.generativeModelMeasure N) := by
    simpa [Y] using
      (M.sampleCoords_iIndepFun (N := N) s a).comp
        (g := fun (_ : Fin N) (x : M.S) => M.transitionIndicator s' x)
        (fun _ => Measurable.of_discrete)
  have h_indep_X :
      iIndepFun X (M.generativeModelMeasure N) := by
    simpa [X, Y] using h_indep_Y.comp
      (g := fun (_ : Fin N) (x : ℝ) => x - p)
      (fun _ => measurable_id.sub measurable_const)
  have h_indep_negX :
      iIndepFun (fun i ω => - X i ω) (M.generativeModelMeasure N) := by
    simpa using h_indep_X.comp
      (g := fun (_ : Fin N) (x : ℝ) => -x)
      (fun _ => measurable_neg)
  have h_subG_X : ∀ i ∈ (Finset.univ : Finset (Fin N)),
      HasSubgaussianMGF (X i) csg (M.generativeModelMeasure N) := by
    intro i _
    have h_meas_Yi : Measurable (Y i) := by
      simpa [Y] using
        ((Measurable.of_discrete (f := M.transitionIndicator s')).comp
          (measurable_pi_apply (s, a, i)))
    have h_raw :=
      hasSubgaussianMGF_of_mem_Icc (μ := M.generativeModelMeasure N) h_meas_Yi.aemeasurable
        (by
          filter_upwards with ω
          exact M.transitionIndicator_mem_Icc s' (ω (s, a, i)))
    have h_int : ∫ ω, Y i ω ∂(M.generativeModelMeasure N) = p := by
      simpa [Y, p] using M.coordinate_indicator_expectation (N := N) s a i s'
    convert h_raw using 1
    · simp [X, Y, p, h_int]
    · norm_num [csg]
  have h_subG_neg : ∀ i ∈ (Finset.univ : Finset (Fin N)),
      HasSubgaussianMGF (fun ω => - X i ω) csg (M.generativeModelMeasure N) := by
    intro i hi
    exact (h_subG_X i hi).neg
  have h_upper :
      (M.generativeModelMeasure N).real
        {ω | (N : ℝ) * eps_0 ≤ ∑ i : Fin N, X i ω} ≤
      Real.exp (-2 * (N : ℝ) * eps_0 ^ 2) := by
    have h_main := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun h_indep_X h_subG_X
      (ε := (N : ℝ) * eps_0) (by positivity)
    have hN_ne : (N : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hN)
    have h_sum_csg : ↑(∑ i : Fin N, csg) = (N : ℝ) * (1 / 4 : ℝ) := by
      simp [csg, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have h_exp_arg :
        -((N : ℝ) * eps_0) ^ 2 / (2 * ↑(∑ i : Fin N, csg)) =
          -2 * (N : ℝ) * eps_0 ^ 2 := by
      rw [h_sum_csg]
      field_simp [hN_ne]
      ring
    have h_exp :
        Real.exp (-((N : ℝ) * eps_0) ^ 2 / (2 * ↑(∑ i : Fin N, csg))) =
          Real.exp (-2 * (N : ℝ) * eps_0 ^ 2) := by
      rw [h_exp_arg]
    simpa [X, hN, p, csg, mul_assoc, div_eq_mul_inv, pow_two] using h_main.trans_eq h_exp
  have h_lower :
      (M.generativeModelMeasure N).real
        {ω | (N : ℝ) * eps_0 ≤ ∑ i : Fin N, - X i ω} ≤
      Real.exp (-2 * (N : ℝ) * eps_0 ^ 2) := by
    have h_main := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun h_indep_negX h_subG_neg
      (ε := (N : ℝ) * eps_0) (by positivity)
    have hN_ne : (N : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hN)
    have h_sum_csg : ↑(∑ i : Fin N, csg) = (N : ℝ) * (1 / 4 : ℝ) := by
      simp [csg, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have h_exp_arg :
        -((N : ℝ) * eps_0) ^ 2 / (2 * ↑(∑ i : Fin N, csg)) =
          -2 * (N : ℝ) * eps_0 ^ 2 := by
      rw [h_sum_csg]
      field_simp [hN_ne]
      ring
    have h_exp :
        Real.exp (-((N : ℝ) * eps_0) ^ 2 / (2 * ↑(∑ i : Fin N, csg))) =
          Real.exp (-2 * (N : ℝ) * eps_0 ^ 2) := by
      rw [h_exp_arg]
    simpa [mul_assoc, div_eq_mul_inv, pow_two, csg] using h_main.trans_eq h_exp
  have h_upper_subset :
      {ω | eps_0 ≤ M.empiricalTransitionRV hN ω s a s' - p} ⊆
        {ω | (N : ℝ) * eps_0 ≤ ∑ i : Fin N, X i ω} := by
    intro ω hω
    have h_emp : M.empiricalTransitionRV hN ω s a s' =
        (∑ i : Fin N, Y i ω) / N := by
      simpa [empiricalTransitionRV, Y] using
        M.empirical_as_indicator_sum hN (fun s a i => ω (s, a, i)) s a s'
    have hω' : eps_0 ≤ (∑ i : Fin N, Y i ω) / N - p := by
      simpa [h_emp] using hω
    have hN_real : (0 : ℝ) < N := by
      exact_mod_cast hN
    have h1 : eps_0 + p ≤ (∑ i : Fin N, Y i ω) / N := by
      linarith
    have h2 : (eps_0 + p) * (N : ℝ) ≤ ∑ i : Fin N, Y i ω := by
      rwa [le_div_iff₀ hN_real] at h1
    have hsum : ∑ i : Fin N, X i ω = ∑ i : Fin N, Y i ω - (N : ℝ) * p := by
      simp [X, Y, Finset.sum_sub_distrib]
    have htarget : (N : ℝ) * eps_0 ≤ ∑ i : Fin N, Y i ω - (N : ℝ) * p := by
      nlinarith
    simpa [hsum] using htarget
  have h_lower_subset :
      {ω | eps_0 ≤ p - M.empiricalTransitionRV hN ω s a s'} ⊆
        {ω | (N : ℝ) * eps_0 ≤ ∑ i : Fin N, - X i ω} := by
    intro ω hω
    have h_emp : M.empiricalTransitionRV hN ω s a s' =
        (∑ i : Fin N, Y i ω) / N := by
      simpa [empiricalTransitionRV, Y] using
        M.empirical_as_indicator_sum hN (fun s a i => ω (s, a, i)) s a s'
    have hω' : eps_0 ≤ p - (∑ i : Fin N, Y i ω) / N := by
      simpa [h_emp] using hω
    have hN_real : (0 : ℝ) < N := by
      exact_mod_cast hN
    have h1 : eps_0 + (∑ i : Fin N, Y i ω) / N ≤ p := by
      linarith
    have h2 : (eps_0 + (∑ i : Fin N, Y i ω) / N) * (N : ℝ) ≤ p * (N : ℝ) := by
      exact mul_le_mul_of_nonneg_right h1 hN_real.le
    have hN_ne : (N : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hN)
    have h2' : eps_0 * (N : ℝ) + ∑ i : Fin N, Y i ω ≤ p * (N : ℝ) := by
      have h_expand :
          (eps_0 + (∑ i : Fin N, Y i ω) / N) * (N : ℝ) =
            eps_0 * (N : ℝ) + ∑ i : Fin N, Y i ω := by
        field_simp [hN_ne]
      rwa [h_expand] at h2
    have hsum : -(∑ i : Fin N, X i ω) = (N : ℝ) * p - ∑ i : Fin N, Y i ω := by
      simp [X, Y, Finset.sum_sub_distrib]
    have htarget : (N : ℝ) * eps_0 ≤ (N : ℝ) * p - ∑ i : Fin N, Y i ω := by
      linarith
    simpa [Finset.sum_neg_distrib, hsum] using htarget
  have h_abs_subset :
      {ω | eps_0 ≤ |p - M.empiricalTransitionRV hN ω s a s'|} ⊆
        {ω | (N : ℝ) * eps_0 ≤ ∑ i : Fin N, X i ω} ∪
        {ω | (N : ℝ) * eps_0 ≤ ∑ i : Fin N, - X i ω} := by
    intro ω hω
    have hω' : eps_0 ≤ |p - M.empiricalTransitionRV hN ω s a s'| := hω
    by_cases hsign : 0 ≤ p - M.empiricalTransitionRV hN ω s a s'
    · have hcase : eps_0 ≤ p - M.empiricalTransitionRV hN ω s a s' := by
        rwa [abs_of_nonneg hsign] at hω'
      exact Or.inr (h_lower_subset hcase)
    · have hcase : eps_0 ≤ M.empiricalTransitionRV hN ω s a s' - p := by
        rw [abs_of_neg (by linarith)] at hω'
        linarith
      exact Or.inl (h_upper_subset hcase)
  calc
    (M.generativeModelMeasure N).real
        {ω | eps_0 ≤ |M.P s a s' - M.empiricalTransitionRV hN ω s a s'|}
      = (M.generativeModelMeasure N).real
          {ω | eps_0 ≤ |p - M.empiricalTransitionRV hN ω s a s'|} := by
            simp [p]
    _ ≤ (M.generativeModelMeasure N).real
          ({ω | (N : ℝ) * eps_0 ≤ ∑ i : Fin N, X i ω} ∪
            {ω | (N : ℝ) * eps_0 ≤ ∑ i : Fin N, - X i ω}) :=
          measureReal_mono h_abs_subset (by finiteness)
    _ ≤ (M.generativeModelMeasure N).real
          {ω | (N : ℝ) * eps_0 ≤ ∑ i : Fin N, X i ω} +
        (M.generativeModelMeasure N).real
          {ω | (N : ℝ) * eps_0 ≤ ∑ i : Fin N, - X i ω} :=
          measureReal_union_le _ _
    _ ≤ Real.exp (-2 * (N : ℝ) * eps_0 ^ 2) +
        Real.exp (-2 * (N : ℝ) * eps_0 ^ 2) := by
          gcongr
    _ = 2 * Real.exp (-2 * (N : ℝ) * eps_0 ^ 2) := by
      ring

/-- Full PAC bound for the generative model. -/
theorem generative_model_pac
    {N : ℕ} (hN : 0 < N)
    (eps_0 : ℝ) (heps_0 : 0 < eps_0) :
    (M.generativeModelMeasure N).real
      {ω | ∀ s a s',
        |M.P s a s' - M.empiricalTransitionRV hN ω s a s'| < eps_0} ≥
      1 - Fintype.card M.S * Fintype.card M.S *
        Fintype.card M.A * (2 * Real.exp (-2 * (N : ℝ) * eps_0 ^ 2)) := by
  let _ : NeZero N := ⟨Nat.ne_of_gt hN⟩
  have h_meas_good :
      MeasurableSet
        {ω | ∀ s a s',
          |M.P s a s' - M.empiricalTransitionRV hN ω s a s'| < eps_0} := by
    classical
    let goodEntry : M.S × M.A × M.S → Set (M.SampleIndex N → M.S) :=
      fun p => {ω |
        |M.P p.1 p.2.1 p.2.2 - M.empiricalTransitionRV hN ω p.1 p.2.1 p.2.2| < eps_0}
    have h_entry : ∀ p, MeasurableSet (goodEntry p) := by
      intro p
      exact measurableSet_lt
        (measurable_const.sub
          (M.empiricalTransitionRV_measurable hN p.1 p.2.1 p.2.2)).abs
        measurable_const
    have h_eq :
        {ω | ∀ s a s',
          |M.P s a s' - M.empiricalTransitionRV hN ω s a s'| < eps_0} =
        ⋂ p : M.S × M.A × M.S, goodEntry p := by
      ext ω
      simp [goodEntry]
    rw [h_eq]
    exact MeasurableSet.iInter fun p : M.S × M.A × M.S => h_entry p
  simpa using M.pac_from_concentration (M.empiricalTransitionRV hN)
    eps_0 (2 * Real.exp (-2 * (N : ℝ) * eps_0 ^ 2))
    heps_0.le (by positivity)
    (fun s a s' => M.empirical_transition_entry_concentration hN s a s' eps_0 heps_0)
    h_meas_good

end FiniteMDP

end
