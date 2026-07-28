/-
# Bandit Probability Space and Concentration

Constructs the probability space for a K-armed bandit with Bernoulli
rewards and proves Hoeffding concentration for empirical arm means.

## Architecture

1. Each arm `a` has Bernoulli(p_a) rewards.
2. The sample space is `Fin K × Fin N → Bool` with product measure.
3. Coordinate projections are independent (by `iIndepFun_pi`).

This mirrors GenerativeModelCore.lean but for the simpler bandit setting.

## References

* [Agarwal et al., *RL: Theory and Algorithms*]
-/

import RLGeneralization.Bandits.UCB
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals

open Finset BigOperators MeasureTheory ProbabilityTheory

noncomputable section

/-! ### Bandit Reward Distribution -/

/-- The probability parameter for arm `a`'s Bernoulli reward.
    Maps `mean ∈ [-1,1]` to `p ∈ [0,1]` via `p = (1 + mean) / 2`. -/
def banditArmProb {K : ℕ} [NeZero K] (B : BanditInstance K) (a : Fin K) : NNReal :=
  ⟨(1 + B.mean a) / 2, by
    have h := B.h_bounded a; rw [abs_le] at h; linarith⟩

lemma banditArmProb_val_le_one {K : ℕ} [NeZero K] (B : BanditInstance K) (a : Fin K) :
    (banditArmProb B a : ℝ) ≤ 1 := by
  simp only [banditArmProb, NNReal.coe_mk]
  have h := B.h_bounded a; rw [abs_le] at h; linarith

lemma banditArmProb_le_one {K : ℕ} [NeZero K] (B : BanditInstance K) (a : Fin K) :
    banditArmProb B a ≤ 1 := by
  rw [← NNReal.coe_le_coe, NNReal.coe_one]
  exact banditArmProb_val_le_one B a

/-- Bernoulli PMF for arm `a`'s reward. -/
def banditArmPMF {K : ℕ} [NeZero K] (B : BanditInstance K) (a : Fin K) : PMF Bool :=
  PMF.bernoulli (banditArmProb B a) (banditArmProb_le_one B a)

/-- Measure for a single arm's reward sample. -/
def banditArmMeasure {K : ℕ} [NeZero K] (B : BanditInstance K) (a : Fin K) : Measure Bool :=
  (banditArmPMF B a).toMeasure

instance banditArmMeasure_prob {K : ℕ} [NeZero K] (B : BanditInstance K) (a : Fin K) :
    IsProbabilityMeasure (banditArmMeasure B a) :=
  PMF.toMeasure.isProbabilityMeasure _

/-! ### Product Probability Space -/

/-- Index type for bandit samples: (arm, sample number). -/
abbrev BanditSampleIndex (K N : ℕ) := Fin K × Fin N

/-- The full bandit product measure: independent Bernoulli samples
    for each (arm, sample) pair. -/
def banditMeasure {K : ℕ} [NeZero K] (B : BanditInstance K) (N : ℕ) :
    Measure (BanditSampleIndex K N → Bool) :=
  Measure.pi (fun idx => banditArmMeasure B idx.1)

instance banditMeasure_prob {K : ℕ} [NeZero K] (B : BanditInstance K)
    (N : ℕ) [NeZero N] :
    IsProbabilityMeasure (banditMeasure B N) := by
  unfold banditMeasure; infer_instance

/-! ### Independence -/

/-- Coordinate projections from the bandit sample space are independent. -/
theorem banditSamples_iIndepFun {K : ℕ} [NeZero K] (B : BanditInstance K) (N : ℕ) :
    iIndepFun (m := fun _ : BanditSampleIndex K N => Bool.instMeasurableSpace)
      (fun idx (ω : BanditSampleIndex K N → Bool) => ω idx)
      (banditMeasure B N) := by
  unfold banditMeasure
  exact iIndepFun_pi (fun _ => aemeasurable_id)

/-! ### Empirical Arm Mean -/

/-- The reward indicator: converts Bool to {0, 1} ⊂ ℝ. -/
def rewardOf : Bool → ℝ
  | true => 1
  | false => 0

lemma rewardOf_nonneg (b : Bool) : 0 ≤ rewardOf b := by cases b <;> simp [rewardOf]
lemma rewardOf_le_one (b : Bool) : rewardOf b ≤ 1 := by cases b <;> simp [rewardOf]
lemma rewardOf_mem_Icc (b : Bool) : rewardOf b ∈ Set.Icc 0 1 :=
  ⟨rewardOf_nonneg b, rewardOf_le_one b⟩

/-- The empirical mean for arm `a` from N samples. -/
def empiricalArmMean {K : ℕ} [NeZero K] {N : ℕ} (_hN : 0 < N)
    (ω : BanditSampleIndex K N → Bool) (a : Fin K) : ℝ :=
  (∑ i : Fin N, rewardOf (ω (a, i))) / N

/-- The true expected reward for arm `a` under the Bernoulli model. -/
def trueArmReward {K : ℕ} [NeZero K] (B : BanditInstance K) (a : Fin K) : ℝ :=
  (banditArmProb B a : ℝ)

/-- Samples for a fixed arm form an independent family. -/
theorem armSamples_iIndepFun {K : ℕ} [NeZero K]
    (B : BanditInstance K) {N : ℕ} (a : Fin K) :
    iIndepFun (fun i : Fin N => fun ω : BanditSampleIndex K N → Bool => ω (a, i))
      (banditMeasure B N) :=
  (banditSamples_iIndepFun B N).precomp (fun {_ _} h => by simpa using h)

/-! ### Coordinate Expectation -/

/-- The expectation of rewardOf at a fixed coordinate equals the arm probability. -/
theorem coordinate_reward_expectation {K : ℕ} [NeZero K]
    (B : BanditInstance K) {N : ℕ} [NeZero N]
    (a : Fin K) (i : Fin N) :
    ∫ ω : BanditSampleIndex K N → Bool, rewardOf (ω (a, i))
      ∂(banditMeasure B N) = trueArmReward B a := by
  -- Step 1: Project from product measure to single-arm measure
  have h_proj : ∫ ω : BanditSampleIndex K N → Bool,
      rewardOf (ω (a, i)) ∂(banditMeasure B N) =
      ∫ b : Bool, rewardOf b ∂(banditArmMeasure B a) := by
    change ∫ ω, (rewardOf ∘ fun ω' => ω' (a, i)) ω ∂(banditMeasure B N) = _
    rw [show banditMeasure B N =
      Measure.pi (fun idx : BanditSampleIndex K N => banditArmMeasure B idx.1)
      from rfl]
    exact MeasureTheory.integral_comp_eval
      (μ := fun idx : BanditSampleIndex K N => banditArmMeasure B idx.1)
      (i := (a, i)) (f := rewardOf)
      ((Measurable.of_discrete (f := rewardOf)).aestronglyMeasurable)
  rw [h_proj]
  -- Step 2: Compute Bernoulli integral
  simp only [banditArmMeasure, trueArmReward, banditArmPMF]
  rw [PMF.integral_eq_sum]
  -- ∑ b : Bool, ↑(bernoulli p · b) · rewardOf b = p
  simp [PMF.bernoulli_apply, rewardOf, banditArmProb]

/-! ### Hoeffding Concentration for Arm Means -/

/-- **Hoeffding concentration for a single arm's empirical mean.**

  P(|μ̂_a - p_a| ≥ ε) ≤ 2·exp(-2Nε²)

  Proof follows the same sub-Gaussian pattern as
  empirical_transition_entry_concentration in GenerativeModelCore. -/
theorem arm_mean_concentration {K : ℕ} [NeZero K]
    (B : BanditInstance K) {N : ℕ} (hN : 0 < N)
    (a : Fin K) (ε : ℝ) (hε : 0 < ε) :
    (banditMeasure B N).real
      {ω | ε ≤ |trueArmReward B a - empiricalArmMean hN ω a|} ≤
      2 * Real.exp (-2 * (N : ℝ) * ε ^ 2) := by
  let _ : NeZero N := ⟨Nat.ne_of_gt hN⟩
  let μ := banditMeasure B N
  let p := trueArmReward B a
  let csg : NNReal := (1 / 4 : NNReal)
  let Y : Fin N → (BanditSampleIndex K N → Bool) → ℝ :=
    fun i ω => rewardOf (ω (a, i))
  let X : Fin N → (BanditSampleIndex K N → Bool) → ℝ :=
    fun i ω => Y i ω - p
  -- Step 1: Independence of X_i
  -- Step 1: Independence
  have h_indep_Y : iIndepFun Y μ := by
    simpa [Y, μ] using
      (armSamples_iIndepFun B a (N := N)).comp
        (g := fun (_ : Fin N) (b : Bool) => rewardOf b)
        (fun _ => Measurable.of_discrete)
  have h_indep_X : iIndepFun X μ := by
    simpa [X] using h_indep_Y.comp
      (g := fun (_ : Fin N) (x : ℝ) => x - p)
      (fun _ => measurable_id.sub measurable_const)
  have h_indep_negX : iIndepFun (fun i ω => - X i ω) μ := by
    simpa using h_indep_X.comp
      (g := fun (_ : Fin N) (x : ℝ) => -x)
      (fun _ => measurable_neg)
  -- Step 2: Sub-Gaussian property
  have h_subG_X : ∀ i ∈ (Finset.univ : Finset (Fin N)),
      HasSubgaussianMGF (X i) csg μ := by
    intro i _
    have h_meas_Yi : Measurable (Y i) := by
      simpa [Y] using
        (Measurable.of_discrete (f := rewardOf)).comp
          (measurable_pi_apply (a, i))
    have h_raw := hasSubgaussianMGF_of_mem_Icc (μ := μ) h_meas_Yi.aemeasurable
      (by filter_upwards with ω; exact rewardOf_mem_Icc (ω (a, i)))
    have h_int : ∫ ω, Y i ω ∂μ = p := by
      simpa [Y, p, μ] using coordinate_reward_expectation B a i
    convert h_raw using 1
    · simp [X, Y, p, h_int]
    · norm_num [csg]
  have h_subG_neg : ∀ i ∈ (Finset.univ : Finset (Fin N)),
      HasSubgaussianMGF (fun ω => - X i ω) csg μ := by
    intro i hi; exact (h_subG_X i hi).neg
  -- Step 3: Upper tail
  have h_upper : μ.real {ω | (N : ℝ) * ε ≤ ∑ i : Fin N, X i ω} ≤
      Real.exp (-2 * (N : ℝ) * ε ^ 2) := by
    have h_main := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
      h_indep_X h_subG_X (ε := (N : ℝ) * ε) (by positivity)
    have hN_ne : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
    have h_sum_csg : ↑(∑ i : Fin N, csg) = (N : ℝ) * (1 / 4 : ℝ) := by
      simp [csg, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have h_exp_arg :
        -((N : ℝ) * ε) ^ 2 / (2 * ↑(∑ i : Fin N, csg)) =
          -2 * (N : ℝ) * ε ^ 2 := by
      rw [h_sum_csg]; field_simp [hN_ne]; ring
    calc μ.real {ω | (N : ℝ) * ε ≤ ∑ i : Fin N, X i ω}
        ≤ Real.exp (-((N : ℝ) * ε) ^ 2 / (2 * ↑(∑ i : Fin N, csg))) := h_main
      _ = Real.exp (-2 * (N : ℝ) * ε ^ 2) := by rw [h_exp_arg]
  -- Step 4: Lower tail
  have h_lower : μ.real {ω | (N : ℝ) * ε ≤ ∑ i : Fin N, - X i ω} ≤
      Real.exp (-2 * (N : ℝ) * ε ^ 2) := by
    have h_main := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
      h_indep_negX h_subG_neg (ε := (N : ℝ) * ε) (by positivity)
    have hN_ne : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
    have h_sum_csg : ↑(∑ i : Fin N, csg) = (N : ℝ) * (1 / 4 : ℝ) := by
      simp [csg, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have h_exp_arg :
        -((N : ℝ) * ε) ^ 2 / (2 * ↑(∑ i : Fin N, csg)) =
          -2 * (N : ℝ) * ε ^ 2 := by
      rw [h_sum_csg]; field_simp [hN_ne]; ring
    calc μ.real {ω | (N : ℝ) * ε ≤ ∑ i : Fin N, - X i ω}
        ≤ Real.exp (-((N : ℝ) * ε) ^ 2 / (2 * ↑(∑ i : Fin N, csg))) := h_main
      _ = Real.exp (-2 * (N : ℝ) * ε ^ 2) := by rw [h_exp_arg]
  -- Step 5: Connect |p - mean_hat| ≥ ε to the sum events
  have h_abs_subset :
      {ω | ε ≤ |p - empiricalArmMean hN ω a|} ⊆
        {ω | (N : ℝ) * ε ≤ ∑ i : Fin N, X i ω} ∪
        {ω | (N : ℝ) * ε ≤ ∑ i : Fin N, - X i ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    have h_emp : empiricalArmMean hN ω a = (∑ i : Fin N, Y i ω) / N := by
      simp [empiricalArmMean, Y]
    have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    -- ∑ X = ∑ (Y - p) = (∑ Y) - N·p
    have h_sum_X : ∑ i : Fin N, X i ω = (∑ i, Y i ω) - N * p := by
      simp [X, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
    have h_sum_negX : ∑ i : Fin N, - X i ω = N * p - ∑ i, Y i ω := by
      simp [X, Finset.sum_sub_distrib,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hN_ne : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
    by_cases hsign : 0 ≤ p - empiricalArmMean hN ω a
    · right
      change (N : ℝ) * ε ≤ ∑ i, - X i ω
      rw [h_sum_negX]; rw [h_emp] at hsign hω
      have h1 : ε ≤ p - (∑ i, Y i ω) / ↑N := by
        have := hω; rwa [abs_of_nonneg hsign] at this
      -- Multiply by N: N*ε ≤ N*p - ∑Y
      have h2 : ↑N * ε ≤ ↑N * p - ∑ i, Y i ω := by
        have := (div_le_iff₀ hN_pos).mp (by linarith : (∑ i, Y i ω) / ↑N ≤ p - ε)
        linarith
      linarith
    · left
      change (N : ℝ) * ε ≤ ∑ i, X i ω
      rw [h_sum_X]; rw [h_emp] at hsign hω
      push_neg at hsign
      have h1 : ε ≤ (∑ i, Y i ω) / ↑N - p := by
        have := hω
        rw [abs_of_neg (by linarith)] at this; linarith
      have h2 : ↑N * ε ≤ ∑ i, Y i ω - ↑N * p := by
        have := (le_div_iff₀ hN_pos).mp (by linarith : p + ε ≤ (∑ i, Y i ω) / ↑N)
        linarith
      linarith
  -- Step 6: Combine
  calc μ.real {ω | ε ≤ |trueArmReward B a - empiricalArmMean hN ω a|}
      = μ.real {ω | ε ≤ |p - empiricalArmMean hN ω a|} := by simp [p]
    _ ≤ μ.real ({ω | (N : ℝ) * ε ≤ ∑ i : Fin N, X i ω} ∪
          {ω | (N : ℝ) * ε ≤ ∑ i : Fin N, - X i ω}) := by
        exact measureReal_mono h_abs_subset (ne_of_lt (lt_of_le_of_lt
          (measure_mono (Set.subset_univ _)) (by simp [μ])))
    _ ≤ μ.real {ω | (N : ℝ) * ε ≤ ∑ i : Fin N, X i ω} +
        μ.real {ω | (N : ℝ) * ε ≤ ∑ i : Fin N, - X i ω} :=
        measureReal_union_le _ _
    _ ≤ Real.exp (-2 * (N : ℝ) * ε ^ 2) +
        Real.exp (-2 * (N : ℝ) * ε ^ 2) := by linarith [h_upper, h_lower]
    _ = 2 * Real.exp (-2 * (N : ℝ) * ε ^ 2) := by ring

/-- **Uniform concentration over all arms.**

  P(∃a, |μ̂_a - p_a| ≥ ε) ≤ 2K·exp(-2Nε²)

  Union bound over K arms. -/
theorem all_arms_concentration {K : ℕ} [NeZero K]
    (B : BanditInstance K) {N : ℕ} (hN : 0 < N)
    (ε : ℝ) (hε : 0 < ε) :
    (banditMeasure B N).real
      {ω | ∃ a, ε ≤ |trueArmReward B a - empiricalArmMean hN ω a|} ≤
      (Fintype.card (Fin K) : ℝ) * (2 * Real.exp (-2 * (N : ℝ) * ε ^ 2)) := by
  -- {∃a, bad_a} ⊆ ⋃_a {bad_a}
  have h_subset : {ω | ∃ a, ε ≤ |trueArmReward B a - empiricalArmMean hN ω a|} ⊆
      ⋃ a : Fin K, {ω | ε ≤ |trueArmReward B a - empiricalArmMean hN ω a|} := by
    intro ω ⟨a, ha⟩; exact Set.mem_iUnion.mpr ⟨a, ha⟩
  -- P(⋃_a bad_a) ≤ ∑_a P(bad_a) (sub-additivity)
  have _ : NeZero N := ⟨Nat.ne_of_gt hN⟩
  calc (banditMeasure B N).real
        {ω | ∃ a, ε ≤ |trueArmReward B a - empiricalArmMean hN ω a|}
      ≤ (banditMeasure B N).real
          (⋃ a : Fin K, {ω | ε ≤ |trueArmReward B a - empiricalArmMean hN ω a|}) :=
        measureReal_mono h_subset (ne_of_lt (lt_of_le_of_lt
          (measure_mono (Set.subset_univ _)) (by simp)))
    _ ≤ ∑ a : Fin K, (banditMeasure B N).real
          {ω | ε ≤ |trueArmReward B a - empiricalArmMean hN ω a|} :=
        measureReal_iUnion_fintype_le _
    _ ≤ ∑ _a : Fin K, (2 * Real.exp (-2 * (N : ℝ) * ε ^ 2)) := by
        apply Finset.sum_le_sum; intro a _
        exact arm_mean_concentration B hN a ε hε
    _ = ↑(Fintype.card (Fin K)) * (2 * Real.exp (-2 * (N : ℝ) * ε ^ 2)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-! ### Prefix Concentration for UCB

  The UCB analysis needs concentration at every prefix size 1..T
  simultaneously. We define `prefixArmMean` (mean of first n of T samples),
  prove it concentrates, and derive a uniform good event via union bound. -/

/-- Empirical mean of the first `n` of `T` samples for arm `a`. -/
def prefixArmMean {K : ℕ} [NeZero K] {T : ℕ}
    (ω : BanditSampleIndex K T → Bool) (a : Fin K)
    (n : ℕ) (hnT : n ≤ T) : ℝ :=
  (∑ i : Fin n, rewardOf (ω (a, Fin.castLE hnT i))) / n

/-- `prefixArmMean` doesn't depend on the proof of `n ≤ T` (by proof irrelevance). -/
@[simp] lemma prefixArmMean_proof_irrel {K : ℕ} [NeZero K] {T : ℕ}
    (ω : BanditSampleIndex K T → Bool) (a : Fin K) (n : ℕ)
    (h1 h2 : n ≤ T) :
    prefixArmMean ω a n h1 = prefixArmMean ω a n h2 := rfl

/-- Prefix samples for a fixed arm are independent under the product measure. -/
theorem prefixArmSamples_iIndepFun {K : ℕ} [NeZero K]
    (B : BanditInstance K) {T : ℕ} (a : Fin K)
    {n : ℕ} (hnT : n ≤ T) :
    iIndepFun
      (fun i : Fin n => fun ω : BanditSampleIndex K T → Bool =>
        ω (a, Fin.castLE hnT i))
      (banditMeasure B T) :=
  (armSamples_iIndepFun B a (N := T)).precomp
    (fun {i j} h => by
      have := congr_arg Fin.val h
      simp only [Fin.val_castLE] at this
      exact Fin.ext this)

/-- **Hoeffding concentration for a prefix of arm samples.**

  P(|p_a − prefixMean(ω,a,n)| ≥ ε) ≤ 2·exp(−2nε²)

  Proof mirrors `arm_mean_concentration` with `Fin n` indices
  accessing the first n of T samples via `Fin.castLE`. -/
theorem prefix_arm_mean_concentration {K : ℕ} [NeZero K]
    (B : BanditInstance K) {T : ℕ}
    (a : Fin K) {n : ℕ} (hn : 0 < n) (hnT : n ≤ T)
    (ε : ℝ) (hε : 0 < ε) :
    (banditMeasure B T).real
      {ω | ε ≤ |trueArmReward B a - prefixArmMean ω a n hnT|} ≤
      2 * Real.exp (-2 * (n : ℝ) * ε ^ 2) := by
  have _ : NeZero T := ⟨by omega⟩
  let μ := banditMeasure B T
  let p := trueArmReward B a
  let csg : NNReal := (1 / 4 : NNReal)
  let Y : Fin n → (BanditSampleIndex K T → Bool) → ℝ :=
    fun i ω => rewardOf (ω (a, Fin.castLE hnT i))
  let X : Fin n → (BanditSampleIndex K T → Bool) → ℝ :=
    fun i ω => Y i ω - p
  -- Independence
  have h_indep_Y : iIndepFun Y μ := by
    simpa [Y, μ] using
      (prefixArmSamples_iIndepFun B a hnT).comp
        (g := fun (_ : Fin n) (b : Bool) => rewardOf b)
        (fun _ => Measurable.of_discrete)
  have h_indep_X : iIndepFun X μ := by
    simpa [X] using h_indep_Y.comp
      (g := fun (_ : Fin n) (x : ℝ) => x - p)
      (fun _ => measurable_id.sub measurable_const)
  have h_indep_negX : iIndepFun (fun i ω => - X i ω) μ := by
    simpa using h_indep_X.comp
      (g := fun (_ : Fin n) (x : ℝ) => -x)
      (fun _ => measurable_neg)
  -- Sub-Gaussian property
  have h_subG_X : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      HasSubgaussianMGF (X i) csg μ := by
    intro i _
    have h_meas_Yi : Measurable (Y i) := by
      simpa [Y] using
        (Measurable.of_discrete (f := rewardOf)).comp
          (measurable_pi_apply (a, Fin.castLE hnT i))
    have h_raw := hasSubgaussianMGF_of_mem_Icc (μ := μ) h_meas_Yi.aemeasurable
      (by filter_upwards with ω; exact rewardOf_mem_Icc (ω (a, Fin.castLE hnT i)))
    have h_int : ∫ ω, Y i ω ∂μ = p := by
      simpa [Y, p, μ] using coordinate_reward_expectation B a (Fin.castLE hnT i)
    convert h_raw using 1
    · simp [X, Y, p, h_int]
    · norm_num [csg]
  have h_subG_neg : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      HasSubgaussianMGF (fun ω => - X i ω) csg μ := by
    intro i hi; exact (h_subG_X i hi).neg
  -- Upper tail
  have hN_ne : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have h_sum_csg : ↑(∑ i : Fin n, csg) = (n : ℝ) * (1 / 4 : ℝ) := by
    simp [csg, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h_exp_arg :
      -((n : ℝ) * ε) ^ 2 / (2 * ↑(∑ i : Fin n, csg)) =
        -2 * (n : ℝ) * ε ^ 2 := by
    rw [h_sum_csg]; field_simp [hN_ne]; ring
  have h_upper : μ.real {ω | (n : ℝ) * ε ≤ ∑ i : Fin n, X i ω} ≤
      Real.exp (-2 * (n : ℝ) * ε ^ 2) := by
    calc μ.real {ω | (n : ℝ) * ε ≤ ∑ i : Fin n, X i ω}
        ≤ Real.exp (-((n : ℝ) * ε) ^ 2 / (2 * ↑(∑ i : Fin n, csg))) :=
          HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
            h_indep_X h_subG_X (ε := (n : ℝ) * ε) (by positivity)
      _ = Real.exp (-2 * (n : ℝ) * ε ^ 2) := by rw [h_exp_arg]
  -- Lower tail
  have h_lower : μ.real {ω | (n : ℝ) * ε ≤ ∑ i : Fin n, - X i ω} ≤
      Real.exp (-2 * (n : ℝ) * ε ^ 2) := by
    calc μ.real {ω | (n : ℝ) * ε ≤ ∑ i : Fin n, - X i ω}
        ≤ Real.exp (-((n : ℝ) * ε) ^ 2 / (2 * ↑(∑ i : Fin n, csg))) :=
          HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
            h_indep_negX h_subG_neg (ε := (n : ℝ) * ε) (by positivity)
      _ = Real.exp (-2 * (n : ℝ) * ε ^ 2) := by rw [h_exp_arg]
  -- Connect |p - prefixMean| ≥ ε to sum events
  have hN_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have h_abs_subset :
      {ω | ε ≤ |p - prefixArmMean ω a n hnT|} ⊆
        {ω | (n : ℝ) * ε ≤ ∑ i : Fin n, X i ω} ∪
        {ω | (n : ℝ) * ε ≤ ∑ i : Fin n, - X i ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    have h_emp : prefixArmMean ω a n hnT = (∑ i : Fin n, Y i ω) / n := by
      simp [prefixArmMean, Y]
    have h_sum_X : ∑ i : Fin n, X i ω = (∑ i, Y i ω) - n * p := by
      simp [X, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have h_sum_negX : ∑ i : Fin n, - X i ω = n * p - ∑ i, Y i ω := by
      simp [X, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    by_cases hsign : 0 ≤ p - prefixArmMean ω a n hnT
    · right
      change (n : ℝ) * ε ≤ ∑ i, - X i ω
      rw [h_sum_negX]; rw [h_emp] at hsign hω
      have h1 : ε ≤ p - (∑ i, Y i ω) / ↑n := by
        have := hω; rwa [abs_of_nonneg hsign] at this
      have h2 : ↑n * ε ≤ ↑n * p - ∑ i, Y i ω := by
        have := (div_le_iff₀ hN_pos).mp (by linarith : (∑ i, Y i ω) / ↑n ≤ p - ε)
        linarith
      linarith
    · left
      change (n : ℝ) * ε ≤ ∑ i, X i ω
      rw [h_sum_X]; rw [h_emp] at hsign hω
      push_neg at hsign
      have h1 : ε ≤ (∑ i, Y i ω) / ↑n - p := by
        have := hω
        rw [abs_of_neg (by linarith)] at this; linarith
      have h2 : ↑n * ε ≤ ∑ i, Y i ω - ↑n * p := by
        have := (le_div_iff₀ hN_pos).mp (by linarith : p + ε ≤ (∑ i, Y i ω) / ↑n)
        linarith
      linarith
  -- Combine
  calc μ.real {ω | ε ≤ |trueArmReward B a - prefixArmMean ω a n hnT|}
      = μ.real {ω | ε ≤ |p - prefixArmMean ω a n hnT|} := by simp [p]
    _ ≤ μ.real ({ω | (n : ℝ) * ε ≤ ∑ i : Fin n, X i ω} ∪
          {ω | (n : ℝ) * ε ≤ ∑ i : Fin n, - X i ω}) :=
        measureReal_mono h_abs_subset (ne_of_lt (lt_of_le_of_lt
          (measure_mono (Set.subset_univ _)) (by simp [μ])))
    _ ≤ μ.real {ω | (n : ℝ) * ε ≤ ∑ i : Fin n, X i ω} +
        μ.real {ω | (n : ℝ) * ε ≤ ∑ i : Fin n, - X i ω} :=
        measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-2 * (n : ℝ) * ε ^ 2) := by linarith [h_upper, h_lower]

/-- Helper: prefix mean indexed by `Fin T` (avoids proof terms in set comprehensions). -/
private def prefixArmMean_at {K : ℕ} [NeZero K] {T : ℕ}
    (ω : BanditSampleIndex K T → Bool) (a : Fin K) (m : Fin T) : ℝ :=
  prefixArmMean ω a (m.val + 1) (Nat.succ_le_of_lt m.isLt)

/-- **Uniform concentration over all arms and all prefix sizes.**

  P(∃ a, ∃ m < T, |p_a − prefixMean(ω,a,m+1)| ≥ √(2L/(m+1))) ≤ 2KT·exp(−4L)

  Union bound over K arms × T prefix sizes. Each event contributes
  2·exp(−2(m+1)·(2L/(m+1))) = 2·exp(−4L). -/
theorem uniform_prefix_concentration {K : ℕ} [NeZero K]
    (B : BanditInstance K) {T : ℕ} (hT : 0 < T)
    (L : ℝ) (hL : 0 < L) :
    (banditMeasure B T).real
      {ω | ∃ a : Fin K, ∃ m : Fin T,
        Real.sqrt (2 * L / (↑m.val + 1)) ≤
          |trueArmReward B a - prefixArmMean_at ω a m|} ≤
      2 * (K : ℝ) * T * Real.exp (-4 * L) := by
  have hNeZeroT : NeZero T := ⟨by omega⟩
  -- Each bad(a,m) has probability ≤ 2·exp(-4L)
  have h_each : ∀ a : Fin K, ∀ m : Fin T,
      (banditMeasure B T).real
        {ω | Real.sqrt (2 * L / (↑m.val + 1)) ≤
          |trueArmReward B a - prefixArmMean_at ω a m|} ≤
        2 * Real.exp (-4 * L) := by
    intro a m
    have hm_pos : 0 < m.val + 1 := by omega
    have hε_pos : 0 < Real.sqrt (2 * L / (↑m.val + 1)) := by positivity
    have hm_le : m.val + 1 ≤ T := Nat.succ_le_of_lt m.isLt
    calc (banditMeasure B T).real
          {ω | Real.sqrt (2 * L / (↑m.val + 1)) ≤
            |trueArmReward B a - prefixArmMean_at ω a m|}
        ≤ 2 * Real.exp (-2 * (↑(m.val + 1)) *
            (Real.sqrt (2 * L / (↑m.val + 1))) ^ 2) := by
          change (banditMeasure B T).real
            {ω | Real.sqrt (2 * L / (↑m.val + 1)) ≤
              |trueArmReward B a - prefixArmMean ω a (m.val + 1) hm_le|} ≤ _
          exact prefix_arm_mean_concentration B a hm_pos hm_le _ hε_pos
      _ = 2 * Real.exp (-4 * L) := by
          push_cast
          have hpos : (0 : ℝ) < (m.val : ℝ) + 1 := by positivity
          have hne : (m.val : ℝ) + 1 ≠ 0 := ne_of_gt hpos
          congr 1
          rw [Real.sq_sqrt (show (0 : ℝ) ≤ 2 * L / ((m.val : ℝ) + 1) by positivity)]
          field_simp [hne]
          ring_nf
  -- Bad event ⊆ ⋃_a ⋃_m bad(a,m)
  have h_subset : {ω | ∃ a, ∃ m : Fin T,
      Real.sqrt (2 * L / (↑m.val + 1)) ≤
        |trueArmReward B a - prefixArmMean_at ω a m|} ⊆
      ⋃ a : Fin K, ⋃ m : Fin T,
        {ω | Real.sqrt (2 * L / (↑m.val + 1)) ≤
          |trueArmReward B a - prefixArmMean_at ω a m|} := by
    intro ω ⟨a, m, hm⟩; exact Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨m, hm⟩⟩
  -- Union bound: ≤ K·T·(2·exp(-4L))
  calc (banditMeasure B T).real
        {ω | ∃ a, ∃ m : Fin T,
          Real.sqrt (2 * L / (↑m.val + 1)) ≤
            |trueArmReward B a - prefixArmMean_at ω a m|}
      ≤ (banditMeasure B T).real
          (⋃ a : Fin K, ⋃ m : Fin T,
            {ω | Real.sqrt (2 * L / (↑m.val + 1)) ≤
              |trueArmReward B a - prefixArmMean_at ω a m|}) :=
        measureReal_mono h_subset (ne_of_lt (lt_of_le_of_lt
          (measure_mono (Set.subset_univ _)) (by simp)))
    _ ≤ ∑ a : Fin K, (banditMeasure B T).real
          (⋃ m : Fin T,
            {ω | Real.sqrt (2 * L / (↑m.val + 1)) ≤
              |trueArmReward B a - prefixArmMean_at ω a m|}) :=
        measureReal_iUnion_fintype_le _
    _ ≤ ∑ _a : Fin K, ∑ _m : Fin T, 2 * Real.exp (-4 * L) := by
        apply Finset.sum_le_sum; intro a _
        calc (banditMeasure B T).real
              (⋃ m : Fin T,
                {ω | Real.sqrt (2 * L / (↑m.val + 1)) ≤
                  |trueArmReward B a - prefixArmMean_at ω a m|})
            ≤ ∑ m : Fin T, (banditMeasure B T).real
                {ω | Real.sqrt (2 * L / (↑m.val + 1)) ≤
                  |trueArmReward B a - prefixArmMean_at ω a m|} :=
              measureReal_iUnion_fintype_le _
          _ ≤ ∑ m : Fin T, 2 * Real.exp (-4 * L) := by
              apply Finset.sum_le_sum; intro m _; exact h_each a m
    _ = 2 * (K : ℝ) * T * Real.exp (-4 * L) := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fin]; ring

/-! ### UCB Good-Event Probability

  Setting L = log(2KT/δ)/4, the uniform good event (all arms concentrated
  at all prefix sizes) fails with probability ≤ δ. Combined with the
  conditional UCB regret analysis, this gives the full probabilistic bound. -/

/-- **Probability of the UCB bad event.**

  With L = log(2KT/δ)/4, the probability that ANY arm at ANY prefix size
  has concentration error exceeding √(2L/n) is at most δ.

  This is the probability guarantee for the UCB good event.
  Setting `L_UCB = 4L = log(2KT/δ)`, the conditional regret bound
  from `ucb_gap_dependent_regret_presentation` gives:
    R_T ≤ ∑_{a:Δ>0} (8·log(2KT/δ)/Δ_a + 2Δ_a) -/
theorem ucb_concentration_event_probability {K : ℕ} [NeZero K]
    (B : BanditInstance K) {T : ℕ} (hT : 0 < T)
    (δ : ℝ) (hδ : 0 < δ) (hδ_small : δ < 2 * ↑K * ↑T) :
    let L := Real.log (2 * ↑K * ↑T / δ) / 4
    (banditMeasure B T).real
      {ω | ∃ a : Fin K, ∃ m : Fin T,
        Real.sqrt (2 * L / (↑m.val + 1)) ≤
          |trueArmReward B a - prefixArmMean_at ω a m|} ≤ δ := by
  intro L
  have hK_pos : (0 : ℝ) < ↑K := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne K))
  have hT_pos : (0 : ℝ) < ↑T := Nat.cast_pos.mpr hT
  have hKT_pos : (0 : ℝ) < 2 * ↑K * ↑T := by positivity
  have hfrac_pos : (0 : ℝ) < 2 * ↑K * ↑T / δ := by positivity
  have hfrac_gt : (1 : ℝ) < 2 * ↑K * ↑T / δ := by rw [lt_div_iff₀ hδ]; linarith
  have hL : 0 < L := div_pos (Real.log_pos hfrac_gt) (by norm_num : (0:ℝ) < 4)
  calc (banditMeasure B T).real
        {ω | ∃ a : Fin K, ∃ m : Fin T,
          Real.sqrt (2 * L / (↑m.val + 1)) ≤
            |trueArmReward B a - prefixArmMean_at ω a m|}
      ≤ 2 * ↑K * ↑T * Real.exp (-4 * L) :=
        uniform_prefix_concentration B hT L hL
    _ = 2 * ↑K * ↑T * Real.exp (-Real.log (2 * ↑K * ↑T / δ)) := by
        congr 1; congr 1
        change -4 * (Real.log (2 * ↑K * ↑T / δ) / 4) = -Real.log (2 * ↑K * ↑T / δ)
        ring
    _ = 2 * ↑K * ↑T * (2 * ↑K * ↑T / δ)⁻¹ := by
        rw [Real.exp_neg, Real.exp_log hfrac_pos]
    _ = δ := by field_simp [ne_of_gt hKT_pos, ne_of_gt hδ]

/-- **Reward-scale conversion for the UCB bridge.**

  The Bernoulli model has `trueArmReward B a = (1 + B.mean a) / 2`.
  The UCB analysis uses `B.mean a`. If the Bernoulli empirical mean
  has error ≤ ε, the UCB-scale empirical mean has error ≤ 2ε.

  Concretely: `|2·p̂ - 1 - μ_a| = 2·|p̂ - p_a|` where p_a = (1+μ_a)/2. -/
theorem bernoulli_to_ucb_error {K : ℕ} [NeZero K]
    (B : BanditInstance K) (a : Fin K)
    (p_hat : ℝ) :
    |2 * p_hat - 1 - B.mean a| = 2 * |p_hat - trueArmReward B a| := by
  have h_eq : 2 * p_hat - 1 - B.mean a =
      2 * (p_hat - trueArmReward B a) := by
    simp [trueArmReward, banditArmProb]; ring
  rw [h_eq, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]

/-- **UCB good event from Bernoulli concentration.**

  Under the Bernoulli good event (all prefix means concentrated),
  the UCB good event holds with parameter `L_UCB = 4 * L_Bernoulli`.

  This is the key bridge between the probability space (BanditConcentration)
  and the deterministic UCB analysis (UCB.lean).

  The `emp_errors` function converts from Bernoulli to UCB scale:
  `emp_errors a n = 2·prefixMean(a,n) − 1 − μ_a`.

  Under the Bernoulli good event: `|emp_errors a n| ≤ 2√(2L_B/n) = √(2·4L_B/n)`.
  So `ucbGoodEvent emp_errors (4·L_B)` holds. -/
theorem ucbGoodEvent_from_bernoulli_concentration {K : ℕ} [NeZero K]
    (B : BanditInstance K) {T : ℕ} (_hT : 0 < T)
    (L : ℝ) (_hL : 0 < L)
    (ω : BanditSampleIndex K T → Bool)
    -- Bernoulli good event: all prefix means concentrated
    (h_good : ∀ a : Fin K, ∀ m : Fin T,
      |trueArmReward B a - prefixArmMean_at ω a m| ≤
        Real.sqrt (2 * L / (↑m.val + 1))) :
    -- UCB good event holds with 4·L
    BanditInstance.ucbGoodEvent (K := K)
      (fun a n =>
        if h : 1 ≤ n ∧ n ≤ T then
          2 * prefixArmMean_at ω a ⟨n - 1, by omega⟩ - 1 - B.mean a
        else 0)
      (4 * L) := by
  intro a n hn
  by_cases hnT : n ≤ T
  · -- n ≤ T: use the Bernoulli good event
    have h_cond : 1 ≤ n ∧ n ≤ T := ⟨hn, hnT⟩
    change |dite (1 ≤ n ∧ n ≤ T) _ _| ≤ _
    rw [dif_pos h_cond]
    -- Get Bernoulli concentration
    have hm : n - 1 < T := by omega
    have h_raw := h_good a ⟨n - 1, hm⟩
    rw [abs_sub_comm] at h_raw
    -- Scale conversion: |2p̂ - 1 - μ| = 2|p̂ - p|
    have h_scale := bernoulli_to_ucb_error B a (prefixArmMean_at ω a ⟨n - 1, hm⟩)
    -- √4 = 2
    have h_sqrt4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
    -- Denominator: ↑(n-1) + 1 = ↑n
    have h_denom : (↑(⟨n-1, hm⟩ : Fin T).val + 1 : ℝ) = ↑n := by
      have : (⟨n-1, hm⟩ : Fin T).val = n - 1 := rfl
      rw [this]
      have : n - 1 + 1 = n := by omega
      exact_mod_cast this
    calc |2 * prefixArmMean_at ω a ⟨n - 1, hm⟩ - 1 - B.mean a|
        = 2 * |prefixArmMean_at ω a ⟨n - 1, hm⟩ - trueArmReward B a| := h_scale
      _ ≤ 2 * Real.sqrt (2 * L / (↑(⟨n-1, hm⟩ : Fin T).val + 1)) :=
          mul_le_mul_of_nonneg_left h_raw (by norm_num)
      _ = Real.sqrt 4 * Real.sqrt (2 * L / (↑(⟨n-1, hm⟩ : Fin T).val + 1)) := by
          rw [h_sqrt4]
      _ = Real.sqrt (4 * (2 * L / (↑(⟨n-1, hm⟩ : Fin T).val + 1))) :=
          (Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4) _).symm
      _ = Real.sqrt (2 * (4 * L) / (↑(⟨n-1, hm⟩ : Fin T).val + 1)) := by
          congr 1; ring
      _ = Real.sqrt (2 * (4 * L) / ↑n) := by rw [h_denom]
  · -- n > T: error is 0, bound is ≥ 0
    change |dite (1 ≤ n ∧ n ≤ T) _ _| ≤ _
    rw [dif_neg (by omega : ¬(1 ≤ n ∧ n ≤ T)), abs_zero]
    exact Real.sqrt_nonneg _

/-! ### Full Probabilistic UCB Regret Guarantee

  Composes the probabilistic concentration results above with the
  deterministic UCB analysis from `Bandits.UCB` to get the full
  probabilistic regret bound for the UCB algorithm:

    P(R_T ≤ ∑_{a:Δ>0} 8·L_UCB/Δ_a + 2Δ_a) ≥ 1 - δ

  where L_UCB = log(2KT/δ).

  The proof chains:
  1. `ucb_concentration_event_probability`: P(bad event) ≤ δ
  2. `ucbGoodEvent_from_bernoulli_concentration`: good event → ucbGoodEvent(4L)
  3. The deterministic UCB analysis under the good event

  **Reference**: Hoeffding's inequality (Boucheron et al. Ch. 2.6,
  intro survey Sec. 3.5) provides the per-arm concentration in step 1.
  The union bound over arms and prefix sizes (step 1) follows the
  standard sub-Gaussian analysis from Boucheron Ch. 2.3.
-/

/-- **Probabilistic UCB good event.**

  With probability ≥ 1 - δ over the random arm rewards, the Bernoulli
  concentration event holds with L = log(2KT/δ)/4. Under this event,
  `ucbGoodEvent_from_bernoulli_concentration` converts to the UCB good
  event with parameter 4L = log(2KT/δ), and then
  `ucb_gap_dependent_regret_presentation` gives:
    R_T ≤ ∑_{a:Δ>0} (8·log(2KT/δ)/Δ_a + 2Δ_a).

  This theorem provides the probability guarantee; the deterministic
  regret bound under the good event is in `UCB.lean`. -/
theorem ucb_high_probability_good_event {K : ℕ} [NeZero K]
    (B : BanditInstance K) {T : ℕ} (hT : 0 < T)
    (δ : ℝ) (hδ : 0 < δ) (hδ_small : δ < 2 * ↑K * ↑T) :
    let L := Real.log (2 * ↑K * ↑T / δ) / 4
    (banditMeasure B T).real
      {ω | ∀ a : Fin K, ∀ m : Fin T,
        |trueArmReward B a - prefixArmMean_at ω a m| ≤
          Real.sqrt (2 * L / (↑m.val + 1))} ≥ 1 - δ := by
  intro L
  have : NeZero T := ⟨by omega⟩
  -- P(bad) ≤ δ by ucb_concentration_event_probability
  have h_bad_prob := ucb_concentration_event_probability B hT δ hδ hδ_small
  -- The good event is the complement of the bad event
  -- good = {ω | ∀ a m, |error| ≤ √(2L/(m+1))}
  -- bad  = {ω | ∃ a m, √(2L/(m+1)) ≤ |error|}
  -- goodᶜ ⊆ bad (by negation of ∀ → ∃ with ¬≤ → <)
  -- So P(good) = 1 - P(goodᶜ) ≥ 1 - P(bad) ≥ 1 - δ
  set good : Set (BanditSampleIndex K T → Bool) :=
    {ω | ∀ a : Fin K, ∀ m : Fin T,
      |trueArmReward B a - prefixArmMean_at ω a m| ≤
        Real.sqrt (2 * L / (↑m.val + 1))} with good_def
  set bad : Set (BanditSampleIndex K T → Bool) :=
    {ω | ∃ a : Fin K, ∃ m : Fin T,
      Real.sqrt (2 * L / (↑m.val + 1)) ≤
        |trueArmReward B a - prefixArmMean_at ω a m|} with bad_def
  have h_compl_sub : goodᶜ ⊆ bad := by
    intro ω hω
    simp only [good_def, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall] at hω
    obtain ⟨a, m, hm⟩ := hω
    exact ⟨a, m, le_of_lt (not_le.mp hm)⟩
  -- All sets are measurable (discrete measurable space on product)
  have h_meas : MeasurableSet good := by measurability
  -- P(good) + P(goodᶜ) = 1
  have h_add : (banditMeasure B T).real good +
      (banditMeasure B T).real goodᶜ =
      (banditMeasure B T).real Set.univ :=
    measureReal_add_measureReal_compl h_meas
  have h_univ : (banditMeasure B T).real Set.univ = 1 := probReal_univ
  -- P(goodᶜ) ≤ P(bad) ≤ δ
  have h_compl_bound : (banditMeasure B T).real goodᶜ ≤ δ := by
    calc (banditMeasure B T).real goodᶜ
        ≤ (banditMeasure B T).real bad := measureReal_mono h_compl_sub
      _ ≤ δ := h_bad_prob
  -- P(good) = 1 - P(goodᶜ) ≥ 1 - δ
  linarith

/-- **Probabilistic UCB good event (bridge).**

  With probability ≥ 1 - δ over the random arm rewards, the UCB
  good event holds with parameter L = log(2KT/δ).

  This composes:
  1. `ucb_high_probability_good_event`: P(Bernoulli good event) ≥ 1 - δ
     with Bernoulli parameter L_B = log(2KT/δ)/4
  2. `ucbGoodEvent_from_bernoulli_concentration`: Bernoulli good event →
     ucbGoodEvent(4·L_B) = ucbGoodEvent(log(2KT/δ))

  Under the UCB good event with L, the deterministic UCB analysis applies:
  * `ucb_gap_dependent_regret_presentation` gives
      R_T ≤ ∑_{a:Δ>0} (8L/Δ_a + 2Δ_a)
  * `ucb_regret_bound_complete` gives the min of gap-dependent and
      worst-case bounds.

  This bridges `Bandits.BanditConcentration` (probability) to
  `Bandits.UCB` (deterministic regret analysis). -/
theorem ucb_probabilistic_regret_bridge {K : ℕ} [NeZero K]
    (B : BanditInstance K) {T : ℕ} (hT : 0 < T)
    (δ : ℝ) (hδ : 0 < δ) (hδ_small : δ < 2 * ↑K * ↑T) :
    let L := Real.log (2 * ↑K * ↑T / δ)
    (banditMeasure B T).real
      {ω | BanditInstance.ucbGoodEvent (K := K)
        (fun a n =>
          if h : 1 ≤ n ∧ n ≤ T then
            2 * prefixArmMean_at ω a ⟨n - 1, by omega⟩ - 1 - B.mean a
          else 0)
        L} ≥ 1 - δ := by
  intro L
  -- Step 1: P(Bernoulli good event) ≥ 1 - δ
  -- ucb_high_probability_good_event uses L_B = log(2KT/δ)/4
  have h_prob := ucb_high_probability_good_event B hT δ hδ hδ_small
  -- Step 2: Set inclusion — Bernoulli good ⊆ UCB good(L)
  -- Because 4 * (log(2KT/δ)/4) = log(2KT/δ) = L
  have hK_pos : (0 : ℝ) < ↑K := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne K))
  have hT_pos : (0 : ℝ) < ↑T := Nat.cast_pos.mpr hT
  have hfrac_pos : (0 : ℝ) < 2 * ↑K * ↑T / δ := by positivity
  have hfrac_gt : (1 : ℝ) < 2 * ↑K * ↑T / δ := by rw [lt_div_iff₀ hδ]; linarith
  set L_B := Real.log (2 * ↑K * ↑T / δ) / 4 with L_B_def
  have hL_B_pos : 0 < L_B := div_pos (Real.log_pos hfrac_gt) (by norm_num)
  have hL_eq : L = 4 * L_B := by simp [L_B_def]; ring
  set good_bernoulli : Set (BanditSampleIndex K T → Bool) :=
    {ω | ∀ a : Fin K, ∀ m : Fin T,
      |trueArmReward B a - prefixArmMean_at ω a m| ≤
        Real.sqrt (2 * L_B / (↑m.val + 1))} with good_bernoulli_def
  set good_ucb : Set (BanditSampleIndex K T → Bool) :=
    {ω | BanditInstance.ucbGoodEvent (K := K)
      (fun a n =>
        if h : 1 ≤ n ∧ n ≤ T then
          2 * prefixArmMean_at ω a ⟨n - 1, by omega⟩ - 1 - B.mean a
        else 0)
      L} with good_ucb_def
  have h_sub : good_bernoulli ⊆ good_ucb := by
    intro ω hω
    rw [good_ucb_def, Set.mem_setOf_eq, hL_eq]
    exact ucbGoodEvent_from_bernoulli_concentration B hT L_B hL_B_pos ω hω
  -- Step 3: P(UCB good) ≥ P(Bernoulli good) ≥ 1 - δ
  have : NeZero T := ⟨by omega⟩
  have h_ne_top : (banditMeasure B T) good_ucb ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono (Set.subset_univ _)) (measure_lt_top _ _))
  calc (banditMeasure B T).real good_ucb
      ≥ (banditMeasure B T).real good_bernoulli :=
        measureReal_mono h_sub h_ne_top
    _ ≥ 1 - δ := h_prob

end
