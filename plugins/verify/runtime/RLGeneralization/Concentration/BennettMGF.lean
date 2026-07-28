/-
# Bennett MGF Bound and Tail Inequality

The Bennett inequality gives a sharper exponential tail bound than
Bernstein for bounded random variables, by using the full exponential
moment generating function rather than a polynomial approximation.

## Main results

* `bennett_exp_pointwise_bound` : For |x| ≤ b, k ≥ 2:
    (λx)^k / k! ≤ (λx)² · (λb)^{k-2} / k!
* `bennett_mgf_bound` : E[exp(λX)] ≤ exp(σ²/b² · (exp(λb) - λb - 1))
* `bennett_tail` : P(∑X_i ≥ t) ≤ exp(-V/b² · h(bt/V))
    where h is the Bennett function.

## Strategy

The proof follows the same three-layer structure as Bernstein:

1. **Pointwise bound**: For |x| ≤ b and k ≥ 2, the k-th term of
   the Taylor expansion satisfies (λx)^k/k! ≤ (λx)²(λb)^{k-2}/k!.
   Summing gives exp(λx) ≤ 1 + λx + x²/b²·(exp(λb) - λb - 1).

2. **MGF bound**: Integrate the pointwise bound using E[X]=0 and
   E[X²] ≤ σ², then apply 1+y ≤ exp(y).

3. **Tail bound**: Chernoff method + independence, with the Bennett
   exponent giving the full Bennett inequality.

## References

* [Boucheron, Lugosi, Massart, *Concentration Inequalities*], Theorem 2.9
-/

import RLGeneralization.Concentration.Bennett

open MeasureTheory ProbabilityTheory Real Finset

noncomputable section

/-! ### The Bennett Pointwise Exponential Bound

For |x| ≤ b and k ≥ 2, the k-th Taylor term of exp(λx) satisfies:
  (λx)^k / k! ≤ (λx)² · (λb)^{k-2} / k!

This is sharper than the Bernstein pointwise bound (which replaces k!
by 2·3^{k-2}), giving the full exponential (rather than geometric)
series sum.

The key observation: for |x| ≤ b,
  |(λx)|^k = |λx|^2 · |λx|^{k-2} ≤ (λx)² · (λb)^{k-2}

and for odd k with x < 0, (λx)^k < 0 while the RHS ≥ 0. -/

/-- Term-by-term bound for Bennett: for |x| ≤ b and k ≥ 2,
    (λx)^k / k! ≤ (λx)² · (λb)^{k-2} / k!.

    When x < 0 and k is odd, the LHS is negative while the RHS
    is nonneg, so the bound is immediate. When x ≥ 0 or k is even,
    |(λx)|^k ≤ (λ|x|)^2 · (λb)^{k-2} since |x| ≤ b. -/
private lemma bennett_term_bound {x b lam : ℝ}
    (hlam : 0 < lam) (hb : 0 < b) (hx : |x| ≤ b) (k : ℕ) (hk : 2 ≤ k) :
    (lam * x) ^ k / ↑(k.factorial) ≤
    (lam * x) ^ 2 * (lam * b) ^ (k - 2) / ↑(k.factorial) := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_pos.mpr (Nat.factorial_pos k)).le
  -- Need: (λx)^k ≤ (λx)² · (λb)^{k-2}
  -- = |λx|^2 · (λb)^{k-2} (since (λx)² = |λx|²)
  -- Case 1: k even or x ≥ 0 → (λx)^k = |λx|^k ≤ |λx|² · (λb)^{k-2}
  -- Case 2: k odd, x < 0 → (λx)^k < 0 ≤ (λx)² · (λb)^{k-2}
  have h_lamb_nn : 0 ≤ lam * b := by positivity
  have h_sq_nn : 0 ≤ (lam * x) ^ 2 := sq_nonneg _
  -- (λx)^k = (λx)^2 · (λx)^{k-2}
  have hk_split : (lam * x) ^ k = (lam * x) ^ 2 * (lam * x) ^ (k - 2) := by
    rw [← pow_add]; congr 1; omega
  rw [hk_split]
  apply mul_le_mul_of_nonneg_left _ h_sq_nn
  -- |λx| ≤ λb, so (λx)^{k-2} ≤ (λb)^{k-2}
  -- Need: (lam * x) ^ (k - 2) ≤ (lam * b) ^ (k - 2)
  -- Since |lam * x| = lam * |x| ≤ lam * b
  have h_abs : |lam * x| ≤ lam * b := by
    rw [abs_mul, abs_of_pos hlam]
    exact mul_le_mul_of_nonneg_left hx hlam.le
  -- (lam*x)^(k-2) ≤ (lam*b)^(k-2)
  -- Key: |a|^n = |a^n| ≥ a^n, and |a| ≤ c implies |a|^n ≤ c^n for c ≥ 0
  have h1 : (lam * x) ^ (k - 2) ≤ |lam * x| ^ (k - 2) := by
    rw [← abs_pow]; exact le_abs_self _
  exact h1.trans (pow_le_pow_left₀ (abs_nonneg _) h_abs _)

-- Bennett pointwise exponential bound: exp(λx) ≤ 1 + λx + (x²/b²)·(exp(λb)-λb-1)
-- for |x| ≤ b, λ > 0. Sharper than the Bernstein pointwise bound.
-- Proof uses power series expansion, term-by-term bound via bennett_term_bound,
-- and resumming to get the exponential.
set_option maxHeartbeats 800000 in
-- Needs extra heartbeats for the power series telescoping argument.
theorem bennett_exp_pointwise_bound {x b lam : ℝ}
    (hlam : 0 < lam) (hb : 0 < b) (hx : |x| ≤ b) :
    exp (lam * x) ≤ 1 + lam * x +
      (lam * x) ^ 2 * (exp (lam * b) - lam * b - 1) / (lam * b) ^ 2 := by
  -- Strategy: use the power series for exp, split into first two terms + tail,
  -- then bound each tail term using bennett_term_bound.
  have hlamb_pos : 0 < lam * b := mul_pos hlam hb
  have hlamb_sq_pos : 0 < (lam * b) ^ 2 := by positivity
  -- Power series: exp(λx) = ∑ (λx)^n / n!
  have h_exp_hs : HasSum (fun n => (lam * x) ^ n / ↑(n.factorial)) (exp (lam * x)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp (lam * x)
  -- Split: HasSum (fun n => (λx)^{n+2}/(n+2)!) (exp(λx) - 1 - λx)
  have h_tail_hs : HasSum (fun n => (lam * x) ^ (n + 2) / ↑((n + 2).factorial))
      (exp (lam * x) - 1 - lam * x) := by
    have key : ∑ i ∈ Finset.range 2, (lam * x) ^ i / ↑(i.factorial) = 1 + lam * x := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial,
        Nat.cast_one, pow_zero, div_one, zero_add, pow_one]
      norm_num
    rw [show exp (lam * x) - 1 - lam * x = exp (lam * x) - (1 + lam * x) from by ring, ← key]
    exact (hasSum_nat_add_iff' 2).mpr h_exp_hs
  -- Similarly for (λb): exp(λb) - 1 - λb = ∑ (λb)^{n+2}/(n+2)!
  have h_tail_b_hs : HasSum (fun n => (lam * b) ^ (n + 2) / ↑((n + 2).factorial))
      (exp (lam * b) - 1 - lam * b) := by
    have h_exp_b : HasSum (fun n => (lam * b) ^ n / ↑(n.factorial)) (exp (lam * b)) := by
      rw [Real.exp_eq_exp_ℝ]
      exact NormedSpace.expSeries_div_hasSum_exp (lam * b)
    have key : ∑ i ∈ Finset.range 2, (lam * b) ^ i / ↑(i.factorial) = 1 + lam * b := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial,
        Nat.cast_one, pow_zero, div_one, zero_add, pow_one]
      norm_num
    rw [show exp (lam * b) - 1 - lam * b = exp (lam * b) - (1 + lam * b) from by ring, ← key]
    exact (hasSum_nat_add_iff' 2).mpr h_exp_b
  -- Term bound: (λx)^{n+2}/(n+2)! ≤ (λx)² · (λb)^n / (n+2)!
  have h_term : ∀ n, (lam * x) ^ (n + 2) / ↑((n + 2).factorial) ≤
      (lam * x) ^ 2 * (lam * b) ^ n / ↑((n + 2).factorial) := by
    intro n
    exact bennett_term_bound hlam hb hx (n + 2) (by omega)
  -- The bound series: (λx)² · (λb)^n / (n+2)! = (λx)²/(λb)² · (λb)^{n+2}/(n+2)!
  have h_rewrite : ∀ n, (lam * x) ^ 2 * (lam * b) ^ n / ↑((n + 2).factorial) =
      (lam * x) ^ 2 / (lam * b) ^ 2 * ((lam * b) ^ (n + 2) / ↑((n + 2).factorial)) := by
    intro n
    have hlamb_ne : lam * b ≠ 0 := hlamb_pos.ne'
    have hlamb_sq_ne : (lam * b) ^ 2 ≠ 0 := pow_ne_zero 2 hlamb_ne
    have hfact_pos : (0 : ℝ) < ↑(n + 2).factorial :=
      Nat.cast_pos.mpr (Nat.factorial_pos _)
    -- LHS = (lam*x)^2 * (lam*b)^n / (n+2)!
    -- RHS = (lam*x)^2 / (lam*b)^2 * ((lam*b)^(n+2) / (n+2)!)
    --     = (lam*x)^2 / (lam*b)^2 * ((lam*b)^2 * (lam*b)^n / (n+2)!)
    --     = (lam*x)^2 * (lam*b)^n / (n+2)! = LHS
    have key : (lam * b) ^ (n + 2) = (lam * b) ^ 2 * (lam * b) ^ n := by
      rw [pow_add]; ring
    rw [key]
    field_simp
  -- Summable: (λx)² · (λb)^n / (n+2)! is summable
  have h_bound_summable : Summable (fun n =>
      (lam * x) ^ 2 * (lam * b) ^ n / ↑((n + 2).factorial)) := by
    rw [show (fun n => (lam * x) ^ 2 * (lam * b) ^ n / ↑((n + 2).factorial)) =
        (fun n => (lam * x) ^ 2 / (lam * b) ^ 2 *
          ((lam * b) ^ (n + 2) / ↑((n + 2).factorial))) from funext h_rewrite]
    exact h_tail_b_hs.summable.mul_left _
  -- tsum bound: ∑ (λx)^{n+2}/(n+2)! ≤ ∑ (λx)²(λb)^n/(n+2)!
  have h_tsum_le : ∑' n, (lam * x) ^ (n + 2) / ↑((n + 2).factorial) ≤
      ∑' n, (lam * x) ^ 2 * (lam * b) ^ n / ↑((n + 2).factorial) :=
    h_tail_hs.summable.tsum_le_tsum h_term h_bound_summable
  -- Compute the bound tsum: ∑ (λx)²(λb)^n/(n+2)! = (λx)²/(λb)² · (exp(λb) - 1 - λb)
  have h_tsum_eq : ∑' n, (lam * x) ^ 2 * (lam * b) ^ n / ↑((n + 2).factorial) =
      (lam * x) ^ 2 / (lam * b) ^ 2 * (exp (lam * b) - 1 - lam * b) := by
    rw [show (fun n => (lam * x) ^ 2 * (lam * b) ^ n / ↑((n + 2).factorial)) =
        (fun n => (lam * x) ^ 2 / (lam * b) ^ 2 *
          ((lam * b) ^ (n + 2) / ↑((n + 2).factorial))) from funext h_rewrite]
    rw [tsum_mul_left, h_tail_b_hs.tsum_eq]
  -- Rewrite (λx)²/(λb)² · (exp(λb) - 1 - λb) = (λx)² · (exp(λb) - λb - 1) / (λb)²
  have h_rearrange : (lam * x) ^ 2 / (lam * b) ^ 2 * (exp (lam * b) - 1 - lam * b) =
      (lam * x) ^ 2 * (exp (lam * b) - lam * b - 1) / (lam * b) ^ 2 := by ring
  -- Chain the inequalities
  suffices h : exp (lam * x) - 1 - lam * x ≤
      (lam * x) ^ 2 * (exp (lam * b) - lam * b - 1) / (lam * b) ^ 2 by linarith
  calc exp (lam * x) - 1 - lam * x
      = ∑' n, (lam * x) ^ (n + 2) / ↑((n + 2).factorial) := h_tail_hs.tsum_eq.symm
    _ ≤ ∑' n, (lam * x) ^ 2 * (lam * b) ^ n / ↑((n + 2).factorial) := h_tsum_le
    _ = (lam * x) ^ 2 / (lam * b) ^ 2 * (exp (lam * b) - 1 - lam * b) := h_tsum_eq
    _ = (lam * x) ^ 2 * (exp (lam * b) - lam * b - 1) / (lam * b) ^ 2 := h_rearrange

/-! ### Bennett MGF Bound

E[exp(λX)] ≤ exp(σ²/b² · (exp(λb) - λb - 1))

for zero-mean random variables X with |X| ≤ b and E[X²] ≤ σ². -/

-- Bennett MGF bound: E[exp(λX)] ≤ exp(σ²/b²·(exp(λb)-λb-1))
-- for X with E[X]=0, |X|≤b, E[X²]≤σ². Sharper than Bernstein MGF
-- and valid for ALL λ>0 (not just λb<3).
set_option maxHeartbeats 800000 in
-- Needs extra heartbeats for the measure-theoretic integration chain.
theorem bennett_mgf_bound
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX_meas : Measurable X)
    {b : ℝ} (hb : 0 < b)
    (h_bound : ∀ᵐ ω ∂μ, |X ω| ≤ b)
    (h_mean : ∫ ω, X ω ∂μ = 0)
    {sigma_sq : ℝ} (_hsigma : 0 ≤ sigma_sq)
    (h_var : ∫ ω, (X ω) ^ 2 ∂μ ≤ sigma_sq)
    {lam : ℝ} (hlam_pos : 0 < lam) :
    ∫ ω, exp (lam * X ω) ∂μ ≤
      exp (sigma_sq / b ^ 2 * (exp (lam * b) - lam * b - 1)) := by
  have hlamb_pos : 0 < lam * b := mul_pos hlam_pos hb
  have hlamb_sq_pos : 0 < (lam * b) ^ 2 := by positivity
  have hb_sq_pos : 0 < b ^ 2 := by positivity
  -- Step 1: Pointwise bound
  have h_pw : ∀ᵐ ω ∂μ,
      exp (lam * X ω) ≤ 1 + lam * X ω +
      (lam * X ω) ^ 2 * (exp (lam * b) - lam * b - 1) / (lam * b) ^ 2 := by
    filter_upwards [h_bound] with ω hω
    exact bennett_exp_pointwise_bound hlam_pos hb hω
  -- Step 2: Integrate — E[exp(λX)] ≤ 1 + (exp(λb)-λb-1)/b² · σ²
  have h_int : ∫ ω, exp (lam * X ω) ∂μ ≤
      1 + sigma_sq / b ^ 2 * (exp (lam * b) - lam * b - 1) := by
    -- Abbreviation for the constant in the quadratic term
    set C := (exp (lam * b) - lam * b - 1) / (lam * b) ^ 2 with hC_def
    have hC_nn : 0 ≤ C := by
      apply div_nonneg _ hlamb_sq_pos.le
      linarith [add_one_le_exp (lam * b)]
    -- Integrability certificates
    have h_exp_int : Integrable (fun ω => exp (lam * X ω)) μ := by
      apply Integrable.of_bound
        ((hX_meas.const_mul lam).exp.aestronglyMeasurable) (exp (lam * b))
      filter_upwards [h_bound] with ω hω
      rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      apply exp_le_exp.mpr
      have : X ω ≤ |X ω| := le_abs_self _
      nlinarith
    have h_X_int : Integrable X μ :=
      Integrable.of_bound hX_meas.aestronglyMeasurable b
        (by filter_upwards [h_bound] with ω hω; exact (Real.norm_eq_abs _ ▸ hω))
    have h_X2_int : Integrable (fun ω => (X ω) ^ 2) μ :=
      Integrable.of_bound (hX_meas.pow_const 2).aestronglyMeasurable (b ^ 2)
        (by filter_upwards [h_bound] with ω hω
            rw [Real.norm_eq_abs, abs_pow]
            exact pow_le_pow_left₀ (abs_nonneg _) hω 2)
    -- The polynomial integrand has the form 1 + λx + C·(λx)²
    -- Rewrite the quadratic term
    have h_pw_rewrite : ∀ ω, (lam * X ω) ^ 2 * (exp (lam * b) - lam * b - 1) /
        (lam * b) ^ 2 = C * lam ^ 2 * (X ω) ^ 2 := by
      intro ω
      rw [hC_def]
      have : (lam * X ω) ^ 2 = lam ^ 2 * (X ω) ^ 2 := by ring
      rw [this, div_mul_eq_mul_div]
      ring
    -- Pointwise bound rewritten
    have h_pw' : ∀ᵐ ω ∂μ,
        exp (lam * X ω) ≤ 1 + lam * X ω + C * lam ^ 2 * (X ω) ^ 2 := by
      filter_upwards [h_pw] with ω hω
      rwa [h_pw_rewrite] at hω
    -- Integrability of polynomial bound
    have h_poly_int : Integrable (fun ω =>
        1 + lam * X ω + C * lam ^ 2 * (X ω) ^ 2) μ :=
      ((integrable_const 1).add (h_X_int.const_mul lam)).add
        (h_X2_int.const_mul (C * lam ^ 2))
    -- Integrate
    calc ∫ ω, exp (lam * X ω) ∂μ
        ≤ ∫ ω, (1 + lam * X ω + C * lam ^ 2 * (X ω) ^ 2) ∂μ :=
          integral_mono_ae h_exp_int h_poly_int h_pw'
      _ = (∫ ω, (1 + lam * X ω) ∂μ) +
          ∫ ω, (C * lam ^ 2 * (X ω) ^ 2) ∂μ :=
          integral_add ((integrable_const 1).add (h_X_int.const_mul _))
            (h_X2_int.const_mul _)
      _ = ((∫ ω, (1 : ℝ) ∂μ) + ∫ ω, lam * X ω ∂μ) +
          ∫ ω, (C * lam ^ 2 * (X ω) ^ 2) ∂μ := by
          congr 1; exact integral_add (integrable_const 1) (h_X_int.const_mul _)
      _ = (1 + lam * ∫ ω, X ω ∂μ) +
          (C * lam ^ 2 * ∫ ω, (X ω) ^ 2 ∂μ) := by
          congr 1
          · congr 1
            · simp [integral_const]
            · exact integral_const_mul _ _
          · exact integral_const_mul _ _
      _ ≤ 1 + C * lam ^ 2 * sigma_sq := by
          rw [h_mean, mul_zero, add_zero]
          linarith [mul_le_mul_of_nonneg_left h_var
            (mul_nonneg hC_nn (sq_nonneg lam))]
      _ = 1 + sigma_sq / b ^ 2 * (exp (lam * b) - lam * b - 1) := by
          rw [hC_def]; field_simp
  -- Step 3: 1 + y ≤ exp(y)
  calc ∫ ω, exp (lam * X ω) ∂μ
      ≤ 1 + sigma_sq / b ^ 2 * (exp (lam * b) - lam * b - 1) := h_int
    _ ≤ exp (sigma_sq / b ^ 2 * (exp (lam * b) - lam * b - 1)) := by
        linarith [Real.add_one_le_exp
              (sigma_sq / b ^ 2 * (exp (lam * b) - lam * b - 1))]

/-! ### Bennett Tail Bound

P(∑X_i ≥ t) ≤ exp(-V/b² · h(bt/V))

where h(u) = (1+u)log(1+u) - u is the Bennett function.

The proof follows the Chernoff method: optimize exp(-λt) · ∏E[exp(λX_i)]
over λ > 0, using the Bennett MGF bound for each factor.

The optimal λ = log(1 + bt/V)/b gives the Bennett exponent. -/

-- Bennett's inequality: P(∑X_i ≥ t) ≤ exp(-V/b²·h(bt/V))
-- for independent X_i with E[X_i]=0, |X_i|≤b, ∑E[X_i²]≤V.
-- Uses Chernoff with optimal λ* = log(1+bt/V)/b.
set_option maxHeartbeats 1600000 in
-- Needs extra heartbeats for the Chernoff optimization chain.
theorem bennett_tail
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} {N : ℕ} (_hN : 0 < N)
    (hX_meas : ∀ i, Measurable (X i))
    (h_indep : iIndepFun X μ)
    {b : ℝ} (hb : 0 < b)
    (h_bound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ b)
    (h_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    {V : ℝ} (hV : 0 < V)
    (h_var_sum : ∑ i ∈ range N,
      ∫ ω, (X i ω) ^ 2 ∂μ ≤ V)
    {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t ≤ ∑ i ∈ range N, X i ω} ≤
      exp (-(V / b ^ 2 * bennettFun (b * t / V))) := by
  -- Choose λ* = log(1 + bt/V) / b, the optimal Chernoff parameter
  set u := b * t / V with hu_def
  have hu_pos : 0 < u := by positivity
  have h1u_pos : 0 < 1 + u := by linarith
  set lam := Real.log (1 + u) / b with hlam_def
  have hlam_pos : 0 < lam := by
    apply div_pos (Real.log_pos _) hb
    linarith
  -- S is measurable
  have h_S_meas : Measurable (fun ω => ∑ i ∈ range N, X i ω) :=
    Finset.measurable_sum _ (fun i _ => hX_meas i)
  -- exp(λS) is integrable (S bounded by Nb a.s.)
  have h_exp_int : Integrable
      (fun ω => exp (lam * ∑ i ∈ range N, X i ω)) μ := by
    refine Integrable.of_bound
      ((h_S_meas.const_mul lam).exp.aestronglyMeasurable)
      (exp (lam * ↑N * b)) ?_
    have h_ae := ae_all_iff.mpr h_bound
    filter_upwards [h_ae] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    apply exp_le_exp.mpr
    have h_sum_le : ∑ i ∈ range N, X i ω ≤ ↑N * b := by
      calc ∑ i ∈ range N, X i ω
          ≤ ∑ _ ∈ range N, b :=
            Finset.sum_le_sum fun i _ => (le_abs_self _).trans (hω i)
        _ = ↑N * b := by simp [Finset.sum_const, Finset.card_range]
    nlinarith
  -- Chernoff: P(S ≥ t) ≤ exp(-λt) · mgf(S, λ)
  have h_chernoff := measure_ge_le_exp_mul_mgf
    (X := fun ω => ∑ i ∈ range N, X i ω) t hlam_pos.le h_exp_int
  -- Factor MGF: mgf(∑X_i, λ) = ∏ mgf(X_i, λ) by independence
  have h_mgf_factor : mgf (fun ω => ∑ i ∈ range N, X i ω) μ lam =
      ∏ i ∈ range N, mgf (X i) μ lam := by
    have := h_indep.mgf_sum hX_meas (range N) (t := lam)
    simp only [mgf] at this ⊢
    convert this using 2 with ω
    simp [Finset.sum_apply]
  -- Bound each mgf using the Bennett MGF bound
  have h_mgf_le : ∀ i ∈ range N, mgf (X i) μ lam ≤
      exp ((∫ ω, (X i ω) ^ 2 ∂μ) / b ^ 2 *
        (exp (lam * b) - lam * b - 1)) := by
    intro i _
    exact bennett_mgf_bound (hX_meas i) hb (h_bound i) (h_mean i)
      (integral_nonneg (fun ω => sq_nonneg _)) (le_refl _) hlam_pos
  -- Product bound: ∏ mgf(X_i,λ) ≤ exp(V/b² · (exp(λb) - λb - 1))
  have h_prod_le : ∏ i ∈ range N, mgf (X i) μ lam ≤
      exp (V / b ^ 2 * (exp (lam * b) - lam * b - 1)) := by
    -- Step 1: ∏ mgf(X_i, λ) ≤ ∏ exp(σ_i²/b² · (exp(λb) - λb - 1))
    have h_step1 : ∏ i ∈ range N, mgf (X i) μ lam ≤
        ∏ i ∈ range N, exp ((∫ ω, (X i ω) ^ 2 ∂μ) / b ^ 2 *
          (exp (lam * b) - lam * b - 1)) :=
      Finset.prod_le_prod (fun i _ => mgf_nonneg) h_mgf_le
    -- Step 2: ∏ exp(a_i) = exp(∑ a_i)
    have h_step2 : ∏ i ∈ range N,
        exp ((∫ ω, (X i ω) ^ 2 ∂μ) / b ^ 2 *
          (exp (lam * b) - lam * b - 1)) =
        exp (∑ i ∈ range N, (∫ ω, (X i ω) ^ 2 ∂μ) / b ^ 2 *
          (exp (lam * b) - lam * b - 1)) :=
      (exp_sum _ _).symm
    -- Step 3: Factor out the common (exp(λb)-λb-1)/b²
    have h_step3 : ∑ i ∈ range N, (∫ ω, (X i ω) ^ 2 ∂μ) / b ^ 2 *
        (exp (lam * b) - lam * b - 1) =
        (exp (lam * b) - lam * b - 1) / b ^ 2 *
        ∑ i ∈ range N, ∫ ω, (X i ω) ^ 2 ∂μ := by
      rw [Finset.mul_sum]; congr 1; ext i; ring
    -- Step 4: ∑σ_i² ≤ V
    have h_step4 : (exp (lam * b) - lam * b - 1) / b ^ 2 *
        ∑ i ∈ range N, ∫ ω, (X i ω) ^ 2 ∂μ ≤
        V / b ^ 2 * (exp (lam * b) - lam * b - 1) := by
      have h_coeff_nn : 0 ≤ (exp (lam * b) - lam * b - 1) / b ^ 2 := by
        apply div_nonneg _ (sq_nonneg _)
        linarith [add_one_le_exp (lam * b)]
      calc (exp (lam * b) - lam * b - 1) / b ^ 2 *
            ∑ i ∈ range N, ∫ ω, (X i ω) ^ 2 ∂μ
          ≤ (exp (lam * b) - lam * b - 1) / b ^ 2 * V :=
            mul_le_mul_of_nonneg_left h_var_sum h_coeff_nn
        _ = V / b ^ 2 * (exp (lam * b) - lam * b - 1) := by ring
    calc ∏ i ∈ range N, mgf (X i) μ lam
        ≤ ∏ i ∈ range N, exp ((∫ ω, (X i ω) ^ 2 ∂μ) / b ^ 2 *
          (exp (lam * b) - lam * b - 1)) := h_step1
      _ = exp (∑ i ∈ range N, (∫ ω, (X i ω) ^ 2 ∂μ) / b ^ 2 *
          (exp (lam * b) - lam * b - 1)) := h_step2
      _ = exp ((exp (lam * b) - lam * b - 1) / b ^ 2 *
          ∑ i ∈ range N, ∫ ω, (X i ω) ^ 2 ∂μ) := by rw [h_step3]
      _ ≤ exp (V / b ^ 2 * (exp (lam * b) - lam * b - 1)) :=
          exp_le_exp.mpr h_step4
  -- Compute exp(λ*b) = 1 + u (since λ* = log(1+u)/b)
  have h_lamb : lam * b = Real.log (1 + u) := by
    rw [hlam_def]; field_simp
  have h_exp_lamb : exp (lam * b) = 1 + u := by
    rw [h_lamb, exp_log h1u_pos]
  -- The Bennett exponent: -λt + V/b²·(exp(λb)-λb-1) = -V/b²·h(u)
  -- where h(u) = (1+u)log(1+u) - u
  have h_exponent : -lam * t + V / b ^ 2 * (exp (lam * b) - lam * b - 1) =
      -(V / b ^ 2 * bennettFun (b * t / V)) := by
    rw [h_exp_lamb, h_lamb]
    unfold bennettFun
    -- Goal involves log(1+u). Substitute t = u*V/b.
    have hb_ne : (b : ℝ) ≠ 0 := hb.ne'
    have hV_ne : (V : ℝ) ≠ 0 := hV.ne'
    have ht_eq : t = u * V / b := by rw [hu_def]; field_simp
    rw [ht_eq, hlam_def, hu_def]
    field_simp
    ring
  -- Combine: P(S≥t) ≤ exp(-λt)·∏E[exp(λX_i)] ≤ exp(-V/b²·h(bt/V))
  calc μ.real {ω | t ≤ ∑ i ∈ range N, X i ω}
      ≤ exp (-lam * t) *
        mgf (fun ω => ∑ i ∈ range N, X i ω) μ lam := h_chernoff
    _ = exp (-lam * t) *
        ∏ i ∈ range N, mgf (X i) μ lam := by rw [h_mgf_factor]
    _ ≤ exp (-lam * t) *
        exp (V / b ^ 2 * (exp (lam * b) - lam * b - 1)) := by
        gcongr
    _ = exp (-lam * t +
        V / b ^ 2 * (exp (lam * b) - lam * b - 1)) := by
        rw [← exp_add]
    _ = exp (-(V / b ^ 2 * bennettFun (b * t / V))) := by
        rw [h_exponent]

/-- **Bennett implies Bernstein**: The Bennett tail bound is always at
least as tight as the Bernstein tail bound.

This follows from `bennettFun_ge_bernstein`: h(u) ≥ u²/(2(1+u/3)),
which gives V/b²·h(bt/V) ≥ t²/(2(V + bt/3)). -/
theorem bennett_tail_le_bernstein
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} {N : ℕ} (hN : 0 < N)
    (hX_meas : ∀ i, Measurable (X i))
    (h_indep : iIndepFun X μ)
    {b : ℝ} (hb : 0 < b)
    (h_bound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ b)
    (h_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    {V : ℝ} (hV : 0 < V)
    (h_var_sum : ∑ i ∈ range N,
      ∫ ω, (X i ω) ^ 2 ∂μ ≤ V)
    {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t ≤ ∑ i ∈ range N, X i ω} ≤
      exp (-t ^ 2 / (2 * V + 2 * b * t / 3)) := by
  calc μ.real {ω | t ≤ ∑ i ∈ range N, X i ω}
      ≤ exp (-(V / b ^ 2 * bennettFun (b * t / V))) :=
        bennett_tail hN hX_meas h_indep hb h_bound h_mean hV h_var_sum ht
    _ ≤ exp (-t ^ 2 / (2 * V + 2 * b * t / 3)) := by
        apply exp_le_exp.mpr
        -- Need: -(V/b² · h(bt/V)) ≤ -t²/(2V + 2bt/3)
        -- i.e., t²/(2V + 2bt/3) ≤ V/b² · h(bt/V)
        -- i.e., t²/(2(V + bt/3)) ≤ V · h(bt/V) / b²
        -- Apply bennett_exponent_ge_bernstein with v = V/b², substituted variable u = bt/V
        set u := b * t / V with hu_def
        have hu_nn : 0 ≤ u := by positivity
        -- h(u) ≥ u²/(2(1 + u/3)) by bennettFun_ge_bernstein
        have h_ge := bennettFun_ge_bernstein hu_nn
        -- V/b² · h(u) ≥ V/b² · u²/(2(1+u/3))
        -- = V/b² · (bt/V)²/(2(1 + bt/(3V)))
        -- = t²/V · 1/(2(1+bt/(3V))) = t²/(2(V + bt/3))
        -- So -(V/b² · h(u)) ≤ -(t²/(2(V + bt/3)))
        -- = -t²/(2V + 2bt/3)
        have hV_ne : (V : ℝ) ≠ 0 := hV.ne'
        have hb_ne : (b : ℝ) ≠ 0 := hb.ne'
        -- V/b² · u²/(2(1+u/3)) = t²/(2(V + bt/3))
        have h_algebra : V / b ^ 2 * (u ^ 2 / (2 * (1 + u / 3))) =
            t ^ 2 / (2 * V + 2 * b * t / 3) := by
          rw [hu_def]; field_simp
        have h_Vb2_nn : (0 : ℝ) ≤ V / b ^ 2 := by positivity
        have h_key := mul_le_mul_of_nonneg_left h_ge h_Vb2_nn
        have h_rw : -t ^ 2 / (2 * V + 2 * b * t / 3) =
            -(t ^ 2 / (2 * V + 2 * b * t / 3)) := by ring
        rw [h_rw]
        linarith

end
