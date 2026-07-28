/-
# Generative Model: Bernstein Concentration

Bernstein concentration machinery for the generative-model product space.
Generic finite-index Bernstein bridge plus specialization to empirical
transition entries, culminating in `generative_model_pac_bernstein`.

## References

* [Azar, Munos, Kappen, *Minimax PAC bounds*][azar2013]
* [Boucheron et al., *Concentration Inequalities*, Ch 2]
-/

import RLGeneralization.Concentration.GenerativeModelCore
import RLGeneralization.Concentration.Bernstein

open Finset BigOperators MeasureTheory ProbabilityTheory ENNReal

noncomputable section

namespace FiniteMDP

variable (M : FiniteMDP)

/-! ### Bernstein Concentration Machinery

The finite-index Bernstein bridge (`bernstein_sum_fintype`) closes the
`Fin N` versus `ℕ` indexing gap. The following theorems specialize
Bernstein's inequality to the actual empirical transition coordinates
with the exact Bernoulli variance profile, culminating in
`generative_model_pac_bernstein`. -/

/-- **Bernstein concentration for empirical transition entries.**

    Given N i.i.d. centered indicator random variables X_i with
    |X_i| <= 1, E[X_i] = 0, Var(X_i) <= 1/4, the sum satisfies
    the one-sided Bernstein bound.

    Direct application of `bernstein_sum` with b = 1, V = N/4. -/
theorem bernstein_per_entry
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega} [IsProbabilityMeasure mu]
    {N : ℕ} (hN : 0 < N)
    (X : ℕ → Omega → ℝ)
    (hX_meas : ∀ i, Measurable (X i))
    (h_indep : iIndepFun X mu)
    (h_bound : ∀ i, ∀ᵐ omega ∂mu, |X i omega| ≤ 1)
    (h_mean : ∀ i, ∫ omega, X i omega ∂mu = 0)
    (h_var : ∀ i, ∫ omega, (X i omega) ^ 2 ∂mu ≤ 1 / 4)
    {t : ℝ} (ht : 0 < t) :
    mu.real {omega | t ≤ ∑ i ∈ range N, X i omega} ≤
      Real.exp (-t ^ 2 / (2 * (↑N * (1 / 4)) + 2 * 1 * t / 3)) := by
  have h_var_sum : ∑ i ∈ range N, ∫ omega, (X i omega) ^ 2 ∂mu ≤
      ↑N * (1 / 4) := by
    calc ∑ i ∈ range N, ∫ omega, (X i omega) ^ 2 ∂mu
        ≤ ∑ _i ∈ range N, (1 / 4 : ℝ) :=
          Finset.sum_le_sum fun i _ => h_var i
      _ = ↑N * (1 / 4) := by
          simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  exact bernstein_sum hN hX_meas h_indep (by positivity : (0 : ℝ) < 1)
    h_bound h_mean (by positivity) h_var_sum ht

/-- A finite-index Bernstein tail bound specialized to independent families
    indexed by a finite type. This closes the `Fin N` versus `ℕ` gap for the
    generative-model product space. -/
theorem bernstein_sum_fintype
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ι : Type*} [Fintype ι]
    {X : ι → Ω → ℝ}
    (hX_meas : ∀ i, Measurable (X i))
    (h_indep : iIndepFun X μ)
    {b : ℝ} (hb : 0 < b)
    (h_bound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ b)
    (h_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    {V : ℝ} (hV : 0 ≤ V)
    (h_var_sum : ∑ i, ∫ ω, (X i ω) ^ 2 ∂μ ≤ V)
    {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t ≤ ∑ i, X i ω} ≤
      Real.exp (-t^2 / (2 * V + 2 * b * t / 3)) := by
  classical
  rcases eq_or_lt_of_le hV with rfl | hV_pos
  · have h_nonneg : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ ∫ ω, (X i ω) ^ 2 ∂μ :=
      fun i _ => integral_nonneg fun ω => sq_nonneg _
    have h_sum_zero : ∑ i, ∫ ω, (X i ω) ^ 2 ∂μ = 0 :=
      le_antisymm h_var_sum (Finset.sum_nonneg h_nonneg)
    have h_each_zero : ∀ i ∈ (Finset.univ : Finset ι), ∫ ω, (X i ω) ^ 2 ∂μ = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg h_nonneg).mp h_sum_zero
    have h_Xi_ae : ∀ i ∈ (Finset.univ : Finset ι), X i =ᵐ[μ] 0 := by
      intro i hi
      have h_int_sq : Integrable (fun ω => (X i ω) ^ 2) μ :=
        Integrable.of_bound ((hX_meas i).pow_const 2).aestronglyMeasurable (b ^ 2)
          (by
            filter_upwards [h_bound i] with ω hω
            rw [Real.norm_eq_abs, abs_pow]
            exact pow_le_pow_left₀ (abs_nonneg _) hω 2)
      have h_sq_ae : (fun ω => (X i ω) ^ 2) =ᵐ[μ] 0 :=
        (integral_eq_zero_iff_of_nonneg_ae
          (ae_of_all μ fun ω => sq_nonneg (X i ω)) h_int_sq).mp
          (h_each_zero i hi)
      filter_upwards [h_sq_ae] with ω hω
      exact sq_eq_zero_iff.mp hω
    have h_sum_ae : ∀ᵐ ω ∂μ, ∑ i, X i ω = 0 := by
      have : ∀ᵐ ω ∂μ, ∀ i, X i ω = 0 := by
        rw [ae_all_iff]
        intro i
        exact h_Xi_ae i (Finset.mem_univ i)
      filter_upwards [this] with ω hω
      exact Finset.sum_eq_zero fun i _ => hω i
    have h_meas_zero : μ {ω | t ≤ ∑ i, X i ω} = 0 := by
      apply measure_mono_null (t := {ω | ∑ i, X i ω ≠ 0})
      · intro ω hω
        simp only [Set.mem_setOf_eq] at hω ⊢
        linarith
      · rw [← ae_iff]
        filter_upwards [h_sum_ae] with ω hω
        exact hω
    have h_real_zero : μ.real {ω | t ≤ ∑ i, X i ω} = 0 := by
      rw [measureReal_eq_zero_iff]
      exact h_meas_zero
    rw [h_real_zero]
    exact (Real.exp_pos _).le
  · set D := V + b * t / 3 with hD_def
    have hD_pos : 0 < D := by positivity
    set lam := t / D with hlam_def
    have hlam_pos : 0 < lam := div_pos ht hD_pos
    have hlam_lt : lam < 3 / b := by
      rw [hlam_def, div_lt_div_iff₀ hD_pos hb]
      nlinarith
    have h_S_meas : Measurable (fun ω => ∑ i, X i ω) :=
      Finset.measurable_sum Finset.univ (fun i _ => hX_meas i)
    have h_exp_int : Integrable
        (fun ω => Real.exp (lam * ∑ i, X i ω)) μ := by
      refine Integrable.of_bound
        ((h_S_meas.const_mul lam).exp.aestronglyMeasurable)
        (Real.exp (lam * Fintype.card ι * b)) ?_
      have h_ae : ∀ᵐ ω ∂μ, ∀ i, |X i ω| ≤ b := by
        rw [ae_all_iff]
        intro i
        exact h_bound i
      filter_upwards [h_ae] with ω hω
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      have h_sum_le : ∑ i, X i ω ≤ Fintype.card ι * b := by
        calc ∑ i, X i ω
            ≤ ∑ _i : ι, b :=
          Finset.sum_le_sum fun i _ => (le_abs_self _).trans (hω i)
          _ = Fintype.card ι * b := by
              rw [Finset.sum_const, Finset.card_univ]
              simp [nsmul_eq_mul]
      nlinarith
    have h_chernoff := measure_ge_le_exp_mul_mgf
      (X := fun ω => ∑ i, X i ω) t hlam_pos.le h_exp_int
    have h_mgf_factor : mgf (fun ω => ∑ i, X i ω) μ lam =
        ∏ i, mgf (X i) μ lam := by
      have := h_indep.mgf_sum hX_meas (Finset.univ : Finset ι) (t := lam)
      simp only [mgf] at this ⊢
      convert this using 2 with ω
      simp
    have h_mgf_le : ∀ i ∈ (Finset.univ : Finset ι), mgf (X i) μ lam ≤
        Real.exp (lam ^ 2 * (∫ ω, (X i ω) ^ 2 ∂μ) /
          (2 * (1 - lam * b / 3))) := by
      intro i _
      exact bernstein_mgf_bound (hX_meas i) hb (h_bound i) (h_mean i)
        (integral_nonneg (fun ω => sq_nonneg _)) (le_refl _)
        hlam_pos hlam_lt
    have h_prod_le : ∏ i, mgf (X i) μ lam ≤
        Real.exp (lam ^ 2 * V / (2 * (1 - lam * b / 3))) := by
      set C := 2 * (1 - lam * b / 3) with hC_def
      have hlamb_lt' : lam * b < 3 := by
        calc lam * b < 3 / b * b := mul_lt_mul_of_pos_right hlam_lt hb
          _ = 3 := div_mul_cancel₀ _ hb.ne'
      have hC_pos : 0 < C := by linarith [hC_def]
      have h_step1 : ∏ i, mgf (X i) μ lam ≤
          ∏ i, Real.exp (lam ^ 2 * (∫ ω, (X i ω) ^ 2 ∂μ) / C) :=
        Finset.prod_le_prod (fun i _ => mgf_nonneg) h_mgf_le
      have h_step2 : ∏ i,
          Real.exp (lam ^ 2 * (∫ ω, (X i ω) ^ 2 ∂μ) / C) =
          Real.exp (∑ i, lam ^ 2 * (∫ ω, (X i ω) ^ 2 ∂μ) / C) :=
        (Real.exp_sum _ _).symm
      have h_step3 : ∑ i, lam ^ 2 * (∫ ω, (X i ω) ^ 2 ∂μ) / C =
          lam ^ 2 / C * ∑ i, ∫ ω, (X i ω) ^ 2 ∂μ := by
        rw [Finset.mul_sum]
        congr 1
        ext i
        ring
      have h_step4 : lam ^ 2 / C * ∑ i, ∫ ω, (X i ω) ^ 2 ∂μ ≤
          lam ^ 2 * V / C := by
        rw [div_mul_eq_mul_div]
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left h_var_sum (sq_nonneg _)) hC_pos.le
      calc ∏ i, mgf (X i) μ lam
          ≤ ∏ i, Real.exp (lam ^ 2 * (∫ ω, (X i ω) ^ 2 ∂μ) / C) := h_step1
        _ = Real.exp (∑ i, lam ^ 2 * (∫ ω, (X i ω) ^ 2 ∂μ) / C) := h_step2
        _ = Real.exp (lam ^ 2 / C * ∑ i, ∫ ω, (X i ω) ^ 2 ∂μ) := by
            rw [h_step3]
        _ ≤ Real.exp (lam ^ 2 * V / C) := Real.exp_le_exp.mpr h_step4
        _ = Real.exp (lam ^ 2 * V / (2 * (1 - lam * b / 3))) := by
            rw [hC_def]
    calc μ.real {ω | t ≤ ∑ i, X i ω}
        ≤ Real.exp (-lam * t) * mgf (fun ω => ∑ i, X i ω) μ lam := h_chernoff
      _ = Real.exp (-lam * t) * ∏ i, mgf (X i) μ lam := by rw [h_mgf_factor]
      _ ≤ Real.exp (-lam * t) * Real.exp (lam ^ 2 * V / (2 * (1 - lam * b / 3))) := by
          gcongr
      _ = Real.exp (-lam * t + lam ^ 2 * V / (2 * (1 - lam * b / 3))) := by
          rw [← Real.exp_add]
      _ = Real.exp (-t ^ 2 / (2 * V + 2 * b * t / 3)) := by
          have h_arg :
              -lam * t + lam ^ 2 * V / (2 * (1 - lam * b / 3)) =
                -t ^ 2 / (2 * V + 2 * b * t / 3) := by
            rw [hlam_def, hD_def]
            have hD_ne : D ≠ 0 := ne_of_gt hD_pos
            have hb_ne : b ≠ 0 := ne_of_gt hb
            field_simp [hD_ne, hb_ne]
            ring_nf
          rw [h_arg]

/-! ### Bernstein specialization to the generative-model product space -/

/-- A one-sided Bernstein tail bound for the centered indicator family attached
    to a fixed transition entry `(s,a,s')` in the generative-model product
    space. -/
theorem coordinate_indicator_bernstein_upper
    {N : ℕ} (hN : 0 < N)
    (s : M.S) (a : M.A) (s' : M.S)
    {t : ℝ} (ht : 0 < t) :
    (M.generativeModelMeasure N).real
      {ω | t ≤ ∑ i : Fin N,
          (M.transitionIndicator s' (ω (s, a, i)) - M.P s a s')} ≤
      Real.exp (-t ^ 2 /
        (2 * ((N : ℝ) * (M.P s a s' - (M.P s a s') ^ 2)) + 2 * t / 3)) := by
  let _ : NeZero N := ⟨Nat.ne_of_gt hN⟩
  let μ : Measure (M.SampleIndex N → M.S) := M.generativeModelMeasure N
  let p : ℝ := M.P s a s'
  let Y : Fin N → (M.SampleIndex N → M.S) → ℝ :=
    fun i ω => M.transitionIndicator s' (ω (s, a, i))
  let X : Fin N → (M.SampleIndex N → M.S) → ℝ :=
    fun i ω => Y i ω - p
  have hp_nonneg : 0 ≤ p := by
    simp [p, M.P_nonneg]
  have hp_le_one : p ≤ 1 := by
    calc
      p ≤ ∑ s'', M.P s a s'' := by
        simpa [p] using
          (Finset.single_le_sum (fun s'' _ => M.P_nonneg s a s'') (Finset.mem_univ s') :
            M.P s a s' ≤ ∑ s'', M.P s a s'')
      _ = 1 := M.P_sum_one s a
  have hY_meas : ∀ i, Measurable (Y i) := by
    intro i
    simpa [Y] using
      ((Measurable.of_discrete (f := M.transitionIndicator s')).comp
        (measurable_pi_apply (s, a, i)))
  have hY_bound : ∀ i, ∀ᵐ ω ∂μ, |Y i ω| ≤ 1 := by
    intro i
    filter_upwards with ω
    have h_nonneg : 0 ≤ Y i ω := by
      simp [Y, M.transitionIndicator_nonneg]
    have h_le_one : Y i ω ≤ 1 := by
      simp [Y, M.transitionIndicator_le_one]
    rw [abs_of_nonneg h_nonneg]
    exact h_le_one
  have hY_int : ∀ i, Integrable (Y i) μ := by
    intro i
    exact Integrable.of_bound (hY_meas i).aestronglyMeasurable 1 (hY_bound i)
  have hY_sq_int : ∀ i, Integrable (fun ω => (Y i ω) ^ 2) μ := by
    intro i
    exact Integrable.of_bound ((hY_meas i).pow_const 2).aestronglyMeasurable 1 <| by
      filter_upwards [hY_bound i] with ω hω
      rw [Real.norm_eq_abs, abs_pow]
      have h_abs_nonneg : 0 ≤ |Y i ω| := abs_nonneg _
      nlinarith [hω, h_abs_nonneg]
  have h_indep_Y :
      iIndepFun Y μ := by
    simpa [μ, Y] using
      (M.sampleCoords_iIndepFun (N := N) s a).comp
        (g := fun (_ : Fin N) (x : M.S) => M.transitionIndicator s' x)
        (fun _ => Measurable.of_discrete)
  have hX_meas : ∀ i, Measurable (X i) := by
    intro i
    simpa [X] using (hY_meas i).sub measurable_const
  have h_indep_X :
      iIndepFun X μ := by
    simpa [X] using h_indep_Y.comp
      (g := fun (_ : Fin N) (x : ℝ) => x - p)
      (fun _ => measurable_id.sub measurable_const)
  have h_bound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ 1 := by
    intro i
    filter_upwards [hY_bound i] with ω hω
    have h_nonneg : 0 ≤ Y i ω := by
      simp [Y, M.transitionIndicator_nonneg]
    have h_le_one : Y i ω ≤ 1 := by
      simp [Y, M.transitionIndicator_le_one]
    have h_abs : |Y i ω - p| ≤ 1 := by
      apply abs_le.mpr
      constructor <;> nlinarith [h_nonneg, h_le_one, hp_nonneg, hp_le_one]
    simpa [X] using h_abs
  have h_mean : ∀ i, ∫ ω, X i ω ∂μ = 0 := by
    intro i
    calc
      ∫ ω, X i ω ∂μ = ∫ ω, Y i ω - p ∂μ := by rfl
      _ = ∫ ω, Y i ω ∂μ - ∫ ω, p ∂μ := by
        exact integral_sub (hY_int i) (integrable_const p)
      _ = p - p := by
        rw [show (∫ ω, Y i ω ∂μ) = p by
          simpa [μ, Y, p] using M.coordinate_indicator_expectation (N := N) s a i s']
        simp [integral_const]
      _ = 0 := by ring
  have h_var_eq : ∀ i, ∫ ω, (X i ω) ^ 2 ∂μ = p - p ^ 2 := by
    intro i
    have h_expY :
        ∫ ω, Y i ω ∂μ = p := by
      simpa [μ, Y, p] using M.coordinate_indicator_expectation (N := N) s a i s'
    have h_expY2 :
        ∫ ω, (Y i ω) ^ 2 ∂μ = p := by
      calc
        ∫ ω, (Y i ω) ^ 2 ∂μ = ∫ ω, Y i ω ∂μ := by
          apply integral_congr_ae
          filter_upwards with ω
          simpa [Y] using M.indicator_sq_eq s' (ω (s, a, i))
        _ = p := h_expY
    have h_expand :
        ∫ ω, (X i ω) ^ 2 ∂μ =
          (∫ ω, (Y i ω) ^ 2 ∂μ - ∫ ω, (2 * p) * Y i ω ∂μ) +
            ∫ ω, p ^ 2 ∂μ := by
      have h_sub_int : Integrable (fun ω => (Y i ω) ^ 2 - (2 * p) * Y i ω) μ :=
        (hY_sq_int i).sub ((hY_int i).const_mul (2 * p))
      calc
        ∫ ω, (X i ω) ^ 2 ∂μ
          = ∫ ω, ((Y i ω) ^ 2 - (2 * p) * Y i ω + p ^ 2) ∂μ := by
              apply integral_congr_ae
              filter_upwards with ω
              simp [X]
              ring
        _ = (∫ ω, ((Y i ω) ^ 2 - (2 * p) * Y i ω) ∂μ) + ∫ ω, p ^ 2 ∂μ := by
              simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
                (integral_add h_sub_int (integrable_const (p ^ 2)))
        _ = (∫ ω, (Y i ω) ^ 2 ∂μ - ∫ ω, (2 * p) * Y i ω ∂μ) +
              ∫ ω, p ^ 2 ∂μ := by
              rw [integral_sub (hY_sq_int i) ((hY_int i).const_mul (2 * p))]
    calc
      ∫ ω, (X i ω) ^ 2 ∂μ
        = (∫ ω, (Y i ω) ^ 2 ∂μ - ∫ ω, (2 * p) * Y i ω ∂μ) +
            ∫ ω, p ^ 2 ∂μ := h_expand
      _ = (p - (2 * p) * p) + p ^ 2 := by
            rw [h_expY2, integral_const_mul, h_expY]
            simp [integral_const]
      _ = p - p ^ 2 := by ring
  have hp_var_nonneg : 0 ≤ p - p ^ 2 := by
    have h_sq_nonneg : 0 ≤ (p - 1 / 2) ^ 2 := sq_nonneg _
    nlinarith
  have h_var_sum :
      ∑ i : Fin N, ∫ ω, (X i ω) ^ 2 ∂μ ≤ (N : ℝ) * (p - p ^ 2) := by
    rw [show (∑ i : Fin N, ∫ ω, (X i ω) ^ 2 ∂μ) = ∑ _i : Fin N, (p - p ^ 2) by
      apply Finset.sum_congr rfl
      intro i _
      exact h_var_eq i]
    rw [Finset.sum_const, Finset.card_univ]
    simp [nsmul_eq_mul]
  have hb : (0 : ℝ) < 1 := by positivity
  have hV : (0 : ℝ) ≤ (N : ℝ) * (p - p ^ 2) := by
    positivity
  simpa [μ, X, mul_one] using
    (bernstein_sum_fintype (μ := μ) (ι := Fin N) hX_meas h_indep_X
      (hb := hb) h_bound h_mean (hV := hV) h_var_sum ht)

/-- Bernstein upper-tail control for one empirical transition entry in the
    actual generative-model sample space. -/
theorem empirical_transition_entry_bernstein_upper
    {N : ℕ} (hN : 0 < N)
    (s : M.S) (a : M.A) (s' : M.S)
    (eps_0 : ℝ) (heps_0 : 0 < eps_0) :
    (M.generativeModelMeasure N).real
      {ω | eps_0 ≤ M.empiricalTransitionRV hN ω s a s' - M.P s a s'} ≤
      Real.exp (-((N : ℝ) * eps_0) ^ 2 /
        (2 * ((N : ℝ) * (M.P s a s' - (M.P s a s') ^ 2)) +
          2 * ((N : ℝ) * eps_0) / 3)) := by
  let _ : NeZero N := ⟨Nat.ne_of_gt hN⟩
  have h_main := M.coordinate_indicator_bernstein_upper hN s a s'
    (t := (N : ℝ) * eps_0) (by positivity)
  have h_subset :
      {ω | eps_0 ≤ M.empiricalTransitionRV hN ω s a s' - M.P s a s'} ⊆
        {ω | (N : ℝ) * eps_0 ≤
            ∑ i : Fin N,
              (M.transitionIndicator s' (ω (s, a, i)) - M.P s a s')} := by
    intro ω hω
    have h_emp :
        M.empiricalTransitionRV hN ω s a s' =
          (∑ i : Fin N, M.transitionIndicator s' (ω (s, a, i))) / N := by
      simpa [empiricalTransitionRV] using
        M.empirical_as_indicator_sum hN (fun s a i => ω (s, a, i)) s a s'
    have hN_real : (0 : ℝ) < N := by
      exact_mod_cast hN
    have h1 :
        eps_0 ≤
          (∑ i : Fin N, M.transitionIndicator s' (ω (s, a, i))) / N -
            M.P s a s' := by
      simpa [h_emp] using hω
    have h1' :
        eps_0 + M.P s a s' ≤
          (∑ i : Fin N, M.transitionIndicator s' (ω (s, a, i))) / N := by
      linarith
    have h2 :
        (eps_0 + M.P s a s') * (N : ℝ) ≤
          ∑ i : Fin N, M.transitionIndicator s' (ω (s, a, i)) := by
      rwa [le_div_iff₀ hN_real] at h1'
    have hsum :
        ∑ i : Fin N, (M.transitionIndicator s' (ω (s, a, i)) - M.P s a s') =
          ∑ i : Fin N, M.transitionIndicator s' (ω (s, a, i)) -
            (N : ℝ) * M.P s a s' := by
      simp [Finset.sum_sub_distrib]
    have htarget :
        (N : ℝ) * eps_0 ≤
          ∑ i : Fin N, M.transitionIndicator s' (ω (s, a, i)) -
            (N : ℝ) * M.P s a s' := by
      nlinarith
    simpa [hsum] using htarget
  have htarget_ne_top :
      (M.generativeModelMeasure N)
        {ω | (N : ℝ) * eps_0 ≤
            ∑ i : Fin N,
              (M.transitionIndicator s' (ω (s, a, i)) - M.P s a s')} ≠ ∞ := by
    have htarget_lt_top :
        (M.generativeModelMeasure N)
          {ω | (N : ℝ) * eps_0 ≤
              ∑ i : Fin N,
                (M.transitionIndicator s' (ω (s, a, i)) - M.P s a s')} < ∞ := by
      calc
        (M.generativeModelMeasure N)
            {ω | (N : ℝ) * eps_0 ≤
                ∑ i : Fin N,
                  (M.transitionIndicator s' (ω (s, a, i)) - M.P s a s')}
            ≤ (M.generativeModelMeasure N) Set.univ := measure_mono (by intro ω _; simp)
        _ = 1 := by simp
        _ < ∞ := by simp
    exact ne_of_lt htarget_lt_top
  exact (measureReal_mono h_subset htarget_ne_top).trans h_main

/-- Bernstein lower-tail control for one empirical transition entry in the
    actual generative-model sample space. -/
theorem empirical_transition_entry_bernstein_lower
    {N : ℕ} (hN : 0 < N)
    (s : M.S) (a : M.A) (s' : M.S)
    (eps_0 : ℝ) (heps_0 : 0 < eps_0) :
    (M.generativeModelMeasure N).real
      {ω | eps_0 ≤ M.P s a s' - M.empiricalTransitionRV hN ω s a s'} ≤
      Real.exp (-((N : ℝ) * eps_0) ^ 2 /
        (2 * ((N : ℝ) * (M.P s a s' - (M.P s a s') ^ 2)) +
          2 * ((N : ℝ) * eps_0) / 3)) := by
  let _ : NeZero N := ⟨Nat.ne_of_gt hN⟩
  let μ : Measure (M.SampleIndex N → M.S) := M.generativeModelMeasure N
  let p : ℝ := M.P s a s'
  let Y : Fin N → (M.SampleIndex N → M.S) → ℝ :=
    fun i ω => M.transitionIndicator s' (ω (s, a, i))
  let X : Fin N → (M.SampleIndex N → M.S) → ℝ :=
    fun i ω => p - Y i ω
  have hp_nonneg : 0 ≤ p := by
    simp [p, M.P_nonneg]
  have hp_le_one : p ≤ 1 := by
    calc
      p ≤ ∑ s'', M.P s a s'' := by
        simpa [p] using
          (Finset.single_le_sum (fun s'' _ => M.P_nonneg s a s'') (Finset.mem_univ s') :
            M.P s a s' ≤ ∑ s'', M.P s a s'')
      _ = 1 := M.P_sum_one s a
  have hY_meas : ∀ i, Measurable (Y i) := by
    intro i
    simpa [Y] using
      ((Measurable.of_discrete (f := M.transitionIndicator s')).comp
        (measurable_pi_apply (s, a, i)))
  have hY_bound : ∀ i, ∀ᵐ ω ∂μ, |Y i ω| ≤ 1 := by
    intro i
    filter_upwards with ω
    have h_nonneg : 0 ≤ Y i ω := by
      simp [Y, M.transitionIndicator_nonneg]
    have h_le_one : Y i ω ≤ 1 := by
      simp [Y, M.transitionIndicator_le_one]
    rw [abs_of_nonneg h_nonneg]
    exact h_le_one
  have hY_int : ∀ i, Integrable (Y i) μ := by
    intro i
    exact Integrable.of_bound (hY_meas i).aestronglyMeasurable 1 (hY_bound i)
  have hY_sq_int : ∀ i, Integrable (fun ω => (Y i ω) ^ 2) μ := by
    intro i
    exact Integrable.of_bound ((hY_meas i).pow_const 2).aestronglyMeasurable 1 <| by
      filter_upwards [hY_bound i] with ω hω
      rw [Real.norm_eq_abs, abs_pow]
      have h_abs_nonneg : 0 ≤ |Y i ω| := abs_nonneg _
      nlinarith [hω, h_abs_nonneg]
  have h_indep_Y :
      iIndepFun Y μ := by
    simpa [μ, Y] using
      (M.sampleCoords_iIndepFun (N := N) s a).comp
        (g := fun (_ : Fin N) (x : M.S) => M.transitionIndicator s' x)
        (fun _ => Measurable.of_discrete)
  have hX_meas : ∀ i, Measurable (X i) := by
    intro i
    simpa [X] using measurable_const.sub (hY_meas i)
  have h_indep_X :
      iIndepFun X μ := by
    simpa [X] using h_indep_Y.comp
      (g := fun (_ : Fin N) (x : ℝ) => p - x)
      (fun _ => measurable_const.sub measurable_id)
  have h_bound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ 1 := by
    intro i
    filter_upwards [hY_bound i] with ω hω
    have h_nonneg : 0 ≤ Y i ω := by
      simp [Y, M.transitionIndicator_nonneg]
    have h_le_one : Y i ω ≤ 1 := by
      simp [Y, M.transitionIndicator_le_one]
    have h_abs : |p - Y i ω| ≤ 1 := by
      apply abs_le.mpr
      constructor <;> nlinarith [h_nonneg, h_le_one, hp_nonneg, hp_le_one]
    simpa [X] using h_abs
  have h_mean : ∀ i, ∫ ω, X i ω ∂μ = 0 := by
    intro i
    calc
      ∫ ω, X i ω ∂μ = ∫ ω, p - Y i ω ∂μ := by rfl
      _ = ∫ ω, p ∂μ - ∫ ω, Y i ω ∂μ := by
        exact integral_sub (integrable_const p) (hY_int i)
      _ = p - p := by
        rw [show (∫ ω, Y i ω ∂μ) = p by
          simpa [μ, Y, p] using M.coordinate_indicator_expectation (N := N) s a i s']
        simp [integral_const]
      _ = 0 := by ring
  have h_var_eq : ∀ i, ∫ ω, (X i ω) ^ 2 ∂μ = p - p ^ 2 := by
    intro i
    have h_expY :
        ∫ ω, Y i ω ∂μ = p := by
      simpa [μ, Y, p] using M.coordinate_indicator_expectation (N := N) s a i s'
    have h_expY2 :
        ∫ ω, (Y i ω) ^ 2 ∂μ = p := by
      calc
        ∫ ω, (Y i ω) ^ 2 ∂μ = ∫ ω, Y i ω ∂μ := by
          apply integral_congr_ae
          filter_upwards with ω
          simpa [Y] using M.indicator_sq_eq s' (ω (s, a, i))
        _ = p := h_expY
    have h_sub_int : Integrable (fun ω => p ^ 2 - (2 * p) * Y i ω) μ :=
      (integrable_const (p ^ 2)).sub ((hY_int i).const_mul (2 * p))
    have h_expand :
        ∫ ω, (X i ω) ^ 2 ∂μ =
          (∫ ω, p ^ 2 - (2 * p) * Y i ω ∂μ) + ∫ ω, (Y i ω) ^ 2 ∂μ := by
      calc
        ∫ ω, (X i ω) ^ 2 ∂μ
          = ∫ ω, (p ^ 2 - (2 * p) * Y i ω + (Y i ω) ^ 2) ∂μ := by
              apply integral_congr_ae
              filter_upwards with ω
              simp [X]
              ring
        _ = (∫ ω, p ^ 2 - (2 * p) * Y i ω ∂μ) + ∫ ω, (Y i ω) ^ 2 ∂μ := by
              simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
                (integral_add h_sub_int (hY_sq_int i))
    calc
      ∫ ω, (X i ω) ^ 2 ∂μ
        = (∫ ω, p ^ 2 - (2 * p) * Y i ω ∂μ) + ∫ ω, (Y i ω) ^ 2 ∂μ := h_expand
      _ = (p ^ 2 - (2 * p) * p) + p := by
            rw [integral_sub (integrable_const (p ^ 2)) ((hY_int i).const_mul (2 * p))]
            rw [integral_const_mul, h_expY, h_expY2]
            simp [integral_const]
      _ = p - p ^ 2 := by ring
  have hp_var_nonneg : 0 ≤ p - p ^ 2 := by
    have h_sq_nonneg : 0 ≤ (p - 1 / 2) ^ 2 := sq_nonneg _
    nlinarith
  have h_var_sum :
      ∑ i : Fin N, ∫ ω, (X i ω) ^ 2 ∂μ ≤ (N : ℝ) * (p - p ^ 2) := by
    rw [show (∑ i : Fin N, ∫ ω, (X i ω) ^ 2 ∂μ) = ∑ _i : Fin N, (p - p ^ 2) by
      apply Finset.sum_congr rfl
      intro i _
      exact h_var_eq i]
    rw [Finset.sum_const, Finset.card_univ]
    simp [nsmul_eq_mul]
  have hb : (0 : ℝ) < 1 := by positivity
  have hV : (0 : ℝ) ≤ (N : ℝ) * (p - p ^ 2) := by positivity
  have h_main := bernstein_sum_fintype (μ := μ) (ι := Fin N) hX_meas h_indep_X
    (hb := hb) h_bound h_mean (hV := hV) h_var_sum (t := (N : ℝ) * eps_0) (by positivity)
  have h_subset :
      {ω | eps_0 ≤ M.P s a s' - M.empiricalTransitionRV hN ω s a s'} ⊆
        {ω | (N : ℝ) * eps_0 ≤ ∑ i : Fin N, (p - M.transitionIndicator s' (ω (s, a, i)))} := by
    intro ω hω
    have h_emp :
        M.empiricalTransitionRV hN ω s a s' =
          (∑ i : Fin N, M.transitionIndicator s' (ω (s, a, i))) / N := by
      simpa [empiricalTransitionRV] using
        M.empirical_as_indicator_sum hN (fun s a i => ω (s, a, i)) s a s'
    have hN_real : (0 : ℝ) < N := by
      exact_mod_cast hN
    have h1 :
        eps_0 ≤
          M.P s a s' -
            (∑ i : Fin N, M.transitionIndicator s' (ω (s, a, i))) / N := by
      simpa [h_emp] using hω
    have h1' :
        eps_0 + (∑ i : Fin N, M.transitionIndicator s' (ω (s, a, i))) / N ≤
          M.P s a s' := by
      linarith
    have h2 :
        (eps_0 + (∑ i : Fin N, M.transitionIndicator s' (ω (s, a, i))) / N) * (N : ℝ) ≤
          M.P s a s' * (N : ℝ) := by
      exact mul_le_mul_of_nonneg_right h1' hN_real.le
    have hN_ne : (N : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hN)
    have h2' :
        eps_0 * (N : ℝ) + ∑ i : Fin N, M.transitionIndicator s' (ω (s, a, i)) ≤
          M.P s a s' * (N : ℝ) := by
      have h_expand :
          (eps_0 + (∑ i : Fin N, M.transitionIndicator s' (ω (s, a, i))) / N) * (N : ℝ) =
            eps_0 * (N : ℝ) + ∑ i : Fin N, M.transitionIndicator s' (ω (s, a, i)) := by
        field_simp [hN_ne]
      rwa [h_expand] at h2
    have hsum :
        ∑ i : Fin N, (p - M.transitionIndicator s' (ω (s, a, i))) =
          (N : ℝ) * p - ∑ i : Fin N, M.transitionIndicator s' (ω (s, a, i)) := by
      simp [p, Finset.sum_sub_distrib]
    have htarget :
        (N : ℝ) * eps_0 ≤
          (N : ℝ) * p - ∑ i : Fin N, M.transitionIndicator s' (ω (s, a, i)) := by
      linarith
    simpa [hsum] using htarget
  have htarget_ne_top :
      (M.generativeModelMeasure N)
        {ω | (N : ℝ) * eps_0 ≤ ∑ i : Fin N, (p - M.transitionIndicator s' (ω (s, a, i)))} ≠ ∞ := by
    have htarget_lt_top :
        (M.generativeModelMeasure N)
          {ω | (N : ℝ) * eps_0 ≤
              ∑ i : Fin N, (p - M.transitionIndicator s' (ω (s, a, i)))} < ∞ := by
      calc
        (M.generativeModelMeasure N)
            {ω | (N : ℝ) * eps_0 ≤ ∑ i : Fin N, (p - M.transitionIndicator s' (ω (s, a, i)))}
            ≤ (M.generativeModelMeasure N) Set.univ := measure_mono (by intro ω _; simp)
        _ = 1 := by simp
        _ < ∞ := by simp
    exact ne_of_lt htarget_lt_top
  exact (measureReal_mono h_subset htarget_ne_top).trans <| by
    simpa [μ, X, p] using h_main

/-- Two-sided Bernstein control for one empirical transition entry in the
    generative-model sample space. -/
theorem empirical_transition_entry_bernstein_concentration
    {N : ℕ} (hN : 0 < N)
    (s : M.S) (a : M.A) (s' : M.S)
    (eps_0 : ℝ) (heps_0 : 0 < eps_0) :
    (M.generativeModelMeasure N).real
      {ω | eps_0 ≤ |M.P s a s' - M.empiricalTransitionRV hN ω s a s'|} ≤
      2 * Real.exp (-((N : ℝ) * eps_0) ^ 2 /
        (2 * ((N : ℝ) * (M.P s a s' - (M.P s a s') ^ 2)) +
          2 * ((N : ℝ) * eps_0) / 3)) := by
  let _ : NeZero N := ⟨Nat.ne_of_gt hN⟩
  have h_upper :
      (M.generativeModelMeasure N).real
        {ω | eps_0 ≤ M.empiricalTransitionRV hN ω s a s' - M.P s a s'} ≤
      Real.exp (-((N : ℝ) * eps_0) ^ 2 /
        (2 * ((N : ℝ) * (M.P s a s' - (M.P s a s') ^ 2)) +
          2 * ((N : ℝ) * eps_0) / 3)) :=
    M.empirical_transition_entry_bernstein_upper hN s a s' eps_0 heps_0
  have h_lower :
      (M.generativeModelMeasure N).real
        {ω | eps_0 ≤ M.P s a s' - M.empiricalTransitionRV hN ω s a s'} ≤
      Real.exp (-((N : ℝ) * eps_0) ^ 2 /
        (2 * ((N : ℝ) * (M.P s a s' - (M.P s a s') ^ 2)) +
          2 * ((N : ℝ) * eps_0) / 3)) :=
    M.empirical_transition_entry_bernstein_lower hN s a s' eps_0 heps_0
  have h_abs_subset :
      {ω | eps_0 ≤ |M.P s a s' - M.empiricalTransitionRV hN ω s a s'|} ⊆
        {ω | eps_0 ≤ M.empiricalTransitionRV hN ω s a s' - M.P s a s'} ∪
        {ω | eps_0 ≤ M.P s a s' - M.empiricalTransitionRV hN ω s a s'} := by
    intro ω hω
    have hω' : eps_0 ≤ |M.P s a s' - M.empiricalTransitionRV hN ω s a s'| := hω
    by_cases hsign : 0 ≤ M.P s a s' - M.empiricalTransitionRV hN ω s a s'
    · have hcase : eps_0 ≤ M.P s a s' - M.empiricalTransitionRV hN ω s a s' := by
        rwa [abs_of_nonneg hsign] at hω'
      exact Or.inr hcase
    · have hcase : eps_0 ≤ M.empiricalTransitionRV hN ω s a s' - M.P s a s' := by
        rw [abs_of_neg (by linarith)] at hω'
        linarith
      exact Or.inl hcase
  have h_union_ne_top :
      (M.generativeModelMeasure N)
        ({ω | eps_0 ≤ M.empiricalTransitionRV hN ω s a s' - M.P s a s'} ∪
          {ω | eps_0 ≤ M.P s a s' - M.empiricalTransitionRV hN ω s a s'}) ≠ ∞ := by
    have h_union_lt_top :
        (M.generativeModelMeasure N)
          ({ω | eps_0 ≤ M.empiricalTransitionRV hN ω s a s' - M.P s a s'} ∪
            {ω | eps_0 ≤ M.P s a s' - M.empiricalTransitionRV hN ω s a s'}) < ∞ := by
      calc
        (M.generativeModelMeasure N)
            ({ω | eps_0 ≤ M.empiricalTransitionRV hN ω s a s' - M.P s a s'} ∪
              {ω | eps_0 ≤ M.P s a s' - M.empiricalTransitionRV hN ω s a s'})
            ≤ (M.generativeModelMeasure N) Set.univ := measure_mono (by intro ω _; simp)
        _ = 1 := by simp
        _ < ∞ := by simp
    exact ne_of_lt h_union_lt_top
  calc
    (M.generativeModelMeasure N).real
        {ω | eps_0 ≤ |M.P s a s' - M.empiricalTransitionRV hN ω s a s'|}
      ≤ (M.generativeModelMeasure N).real
          ({ω | eps_0 ≤ M.empiricalTransitionRV hN ω s a s' - M.P s a s'} ∪
            {ω | eps_0 ≤ M.P s a s' - M.empiricalTransitionRV hN ω s a s'}) :=
          measureReal_mono h_abs_subset h_union_ne_top
    _ ≤ (M.generativeModelMeasure N).real
          {ω | eps_0 ≤ M.empiricalTransitionRV hN ω s a s' - M.P s a s'} +
        (M.generativeModelMeasure N).real
          {ω | eps_0 ≤ M.P s a s' - M.empiricalTransitionRV hN ω s a s'} :=
          measureReal_union_le _ _
    _ ≤ Real.exp (-((N : ℝ) * eps_0) ^ 2 /
          (2 * ((N : ℝ) * (M.P s a s' - (M.P s a s') ^ 2)) +
            2 * ((N : ℝ) * eps_0) / 3)) +
        Real.exp (-((N : ℝ) * eps_0) ^ 2 /
          (2 * ((N : ℝ) * (M.P s a s' - (M.P s a s') ^ 2)) +
            2 * ((N : ℝ) * eps_0) / 3)) := by
          gcongr
    _ = 2 * Real.exp (-((N : ℝ) * eps_0) ^ 2 /
          (2 * ((N : ℝ) * (M.P s a s' - (M.P s a s') ^ 2)) +
            2 * ((N : ℝ) * eps_0) / 3)) := by
          ring

/-- Full PAC bound for the generative model using the Bernstein per-entry
    concentration bound specialized to the actual transition coordinates. -/
theorem generative_model_pac_bernstein
    {N : ℕ} (hN : 0 < N)
    (eps_0 : ℝ) (heps_0 : 0 < eps_0) :
    (M.generativeModelMeasure N).real
      {ω | ∀ s a s',
        |M.P s a s' - M.empiricalTransitionRV hN ω s a s'| < eps_0} ≥
      1 - ∑ p : M.S × M.A × M.S,
        2 * Real.exp (-((N : ℝ) * eps_0) ^ 2 /
          (2 * ((N : ℝ) * (M.P p.1 p.2.1 p.2.2 - (M.P p.1 p.2.1 p.2.2) ^ 2)) +
            2 * ((N : ℝ) * eps_0) / 3)) := by
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
  set good : Set (M.SampleIndex N → M.S) := {ω | ∀ s a s',
    |M.P s a s' - M.empiricalTransitionRV hN ω s a s'| < eps_0}
  have h_add :
      (M.generativeModelMeasure N).real good +
        (M.generativeModelMeasure N).real goodᶜ =
      (M.generativeModelMeasure N).real Set.univ :=
    measureReal_add_measureReal_compl h_meas_good
  have h_univ : (M.generativeModelMeasure N).real Set.univ = 1 := probReal_univ
  have h_ub :
      (M.generativeModelMeasure N).real goodᶜ ≤
        ∑ p : M.S × M.A × M.S,
          2 * Real.exp (-((N : ℝ) * eps_0) ^ 2 /
            (2 * ((N : ℝ) * (M.P p.1 p.2.1 p.2.2 - (M.P p.1 p.2.1 p.2.2) ^ 2)) +
              2 * ((N : ℝ) * eps_0) / 3)) := by
    have h_subset : goodᶜ ⊆ ⋃ (p : M.S × M.A × M.S),
        {ω | eps_0 ≤ |M.P p.1 p.2.1 p.2.2 -
          M.empiricalTransitionRV hN ω p.1 p.2.1 p.2.2|} := by
      intro ω hω
      simp only [good, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_lt] at hω
      obtain ⟨s, a, s', h⟩ := hω
      exact Set.mem_iUnion.mpr ⟨(s, a, s'), h⟩
    calc
      (M.generativeModelMeasure N).real goodᶜ
          ≤ (M.generativeModelMeasure N).real (⋃ (p : M.S × M.A × M.S),
              {ω | eps_0 ≤ |M.P p.1 p.2.1 p.2.2 -
                M.empiricalTransitionRV hN ω p.1 p.2.1 p.2.2|}) :=
            measureReal_mono h_subset
      _ ≤ ∑ p : M.S × M.A × M.S, (M.generativeModelMeasure N).real
            {ω | eps_0 ≤ |M.P p.1 p.2.1 p.2.2 -
              M.empiricalTransitionRV hN ω p.1 p.2.1 p.2.2|} :=
            measureReal_iUnion_fintype_le _
      _ ≤ ∑ p : M.S × M.A × M.S,
            2 * Real.exp (-((N : ℝ) * eps_0) ^ 2 /
              (2 * ((N : ℝ) * (M.P p.1 p.2.1 p.2.2 - (M.P p.1 p.2.1 p.2.2) ^ 2)) +
                2 * ((N : ℝ) * eps_0) / 3)) := by
              exact Finset.sum_le_sum fun p _ =>
                M.empirical_transition_entry_bernstein_concentration
                  hN p.1 p.2.1 p.2.2 eps_0 heps_0
  linarith

end FiniteMDP

end
