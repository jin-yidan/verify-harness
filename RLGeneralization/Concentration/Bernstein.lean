/-
# Bernstein's Inequality

Bernstein's inequality for bounded random variables. NOT in Mathlib
(as of v4.28.0). Needed for the variance-sensitive model-based bounds.

## Structure

The proof is decomposed into three layers:

1. **Moment bound** (proved): E[X^k] ≤ σ²b^{k-2} for bounded
   zero-mean X with |X| ≤ b, Var(X) ≤ σ². This is the key
   ingredient connecting variance to higher moments.

2. **MGF bound** (proved): E[exp(λX)] ≤ exp(λ²σ²/(2(1-λb/3))).
   Uses exp power series + factorial bound + geometric series
   for the pointwise bound, then integration + 1+x ≤ exp(x).

3. **Bernstein tail bound** (proved): P(S_n ≥ t) ≤ exp(...).
   Follows from the MGF bound and a Chernoff-style optimization.

## References

* [Boucheron et al., *Concentration Inequalities*]
* [Agarwal et al., *RL: Theory and Algorithms*]
-/

import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential

open MeasureTheory ProbabilityTheory Real Finset

noncomputable section

/-! ### Layer 1: Moment Bound (Proved) -/

/-- **Moment bound for bounded zero-mean random variables**.

  If X has E[X] = 0, |X| ≤ b a.s., and Var(X) ≤ σ², then for k ≥ 2:
    E[|X|^k] ≤ σ² · b^(k-2)

  Proof: |X|^k = |X|² · |X|^(k-2) ≤ |X|² · b^(k-2) since |X| ≤ b.
  Taking expectations: E[|X|^k] ≤ b^(k-2) · E[X²] = b^(k-2) · σ².

  This is the ingredient that makes Bernstein tighter than Hoeffding:
  it links higher moments to variance, not just to the range. -/
theorem moment_bound_of_bounded
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX_meas : AEStronglyMeasurable X μ)
    {b : ℝ} (hb : 0 < b)
    -- X is bounded: |X(ω)| ≤ b a.s.
    (h_bound : ∀ᵐ ω ∂μ, |X ω| ≤ b)
    -- Variance bound
    {sigma_sq : ℝ}
    (h_var : ∫ ω, (X ω) ^ 2 ∂μ ≤ sigma_sq)
    -- For k ≥ 2
    {k : ℕ} (hk : 2 ≤ k) :
    ∫ ω, |X ω|^k ∂μ ≤ sigma_sq * b^(k - 2) := by
  -- |X|^k = |X|² · |X|^{k-2} ≤ |X|² · b^{k-2} pointwise a.s.
  -- So ∫|X|^k ≤ b^{k-2} · ∫|X|² = b^{k-2} · ∫X² ≤ b^{k-2} · σ²
  -- Pointwise: |X|^k = |X|^2 · |X|^{k-2} ≤ |X|^2 · b^{k-2}
  -- ∫ |X|^k ≤ b^{k-2} · ∫ |X|^2 = b^{k-2} · ∫ X² ≤ σ² · b^{k-2}
  -- This requires integral_mono_ae + measurability.
  -- |X|^k ≤ X² · b^{k-2} pointwise, then integrate
  -- Step 1: Pointwise bound |X ω|^k ≤ (X ω) ^ 2 * b^(k-2) a.e.
  -- Step 2: ∫ |X|^k ≤ ∫ X² · b^{k-2} = b^{k-2} · ∫ X²
  -- Step 3: b^{k-2} · ∫ X² ≤ b^{k-2} · σ² = σ² · b^{k-2}
  -- The proof decomposes into three steps, with the
  -- integrability certificates as the main technical challenge.
  -- ∫|X|^k ≤ ∫(X²·b^{k-2}) = b^{k-2}·∫X² ≤ σ²·b^{k-2}
  -- Pointwise bound: |X ω|^k ≤ (X ω) ^ 2 * b^(k-2) a.e.
  have h_pw : ∀ᵐ ω ∂μ, |X ω| ^ k ≤ (X ω) ^ 2 * b ^ (k - 2) := by
    filter_upwards [h_bound] with ω hω
    have habs : |X ω| ^ k = |X ω| ^ 2 * |X ω| ^ (k - 2) := by
      rw [← pow_add]; congr 1; omega
    rw [habs, sq_abs]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    exact pow_le_pow_left₀ (abs_nonneg _) hω _
  calc ∫ ω, |X ω| ^ k ∂μ
      ≤ ∫ ω, (X ω) ^ 2 * b ^ (k - 2) ∂μ := by
        apply integral_mono_ae
        · -- Integrable |X|^k (bounded a.e. by b^k)
          apply Integrable.of_bound (hX_meas.norm.pow k) (b ^ k)
          filter_upwards [h_bound] with ω hω
          simp only [norm_eq_abs, Pi.pow_apply, norm_pow, abs_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) hω k
        · -- Integrable X² * b^{k-2}
          have hX2_int : Integrable (fun ω => (X ω) ^ 2) μ :=
            Integrable.of_bound (hX_meas.pow 2) (b ^ 2)
              (by filter_upwards [h_bound] with ω hω
                  simp only [Real.norm_eq_abs, abs_pow]
                  exact pow_le_pow_left₀ (abs_nonneg _) hω 2)
          exact hX2_int.mul_const _
        · exact h_pw
    _ = (∫ ω, (X ω) ^ 2 ∂μ) * b ^ (k - 2) := integral_mul_const _ _
    _ ≤ sigma_sq * b ^ (k - 2) :=
        mul_le_mul_of_nonneg_right h_var (pow_nonneg hb.le _)

/-- Factorial bound: k! ≥ 2 · 3^(k-2) for k ≥ 2.
    By induction using (k+1)! ≥ 3 · k! ≥ 3 · 2·3^(k-2). -/
theorem factorial_ge_two_mul_three_pow (k : ℕ) (hk : 2 ≤ k) :
    2 * (3 : ℝ) ^ (k - 2) ≤ (k.factorial : ℝ) := by
  induction k with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => omega
    | succ m =>
      cases m with
      | zero => -- k = 2
        simp [Nat.factorial]
      | succ p => -- k = p + 3
        simp only [Nat.factorial, Nat.cast_mul]
        have := ih (by omega : 2 ≤ p + 2)
        -- Goal: 2 * 3^(p+1) ≤ ↑((p+3).factorial)
        -- = ↑((p+3) * (p+2).factorial)
        -- ≥ 3 * (p+2).factorial ≥ 3 * 2 * 3^p = 2 * 3^{p+1}
        -- h_ih : 2 * 3^p ≤ (p+2).factorial (from ih)
        -- Goal: 2 * 3^(p+1) ≤ ((p+3) * (p+2).factorial : ℝ)
        -- this : 2 * 3^p ≤ (p+2)!
        -- Goal: 2 * 3^(p+1) ≤ (p+3)! = (p+3)·(p+2)!
        -- 2·3^{p+1} = 3·(2·3^p) ≤ (p+3)·(2·3^p) ≤ (p+3)·(p+2)!
        have h1 : 2 * (3 : ℝ) ^ p ≤ ↑(Nat.factorial (p + 1 + 1)) := this
        have h2 : (3 : ℝ) ≤ ↑(p + 1 + 1 + 1) := by
          push_cast; linarith [show (0 : ℝ) ≤ ↑p from Nat.cast_nonneg _]
        have h3 : (0 : ℝ) ≤ 2 * 3 ^ p := by positivity
        -- 2·3^{p+1} = 3·2·3^p ≤ (p+3)·2·3^p ≤ (p+3)·(p+2)!
        have key : (2 : ℝ) * 3 ^ (p + 1) ≤ ↑(p + 1 + 1 + 1) * ↑(Nat.factorial (p + 1 + 1)) := by
          calc (2 : ℝ) * 3 ^ (p + 1) = 3 * (2 * 3 ^ p) := by ring
            _ ≤ ↑(p + 1 + 1 + 1) * (2 * 3 ^ p) := by nlinarith
            _ ≤ ↑(p + 1 + 1 + 1) * ↑(Nat.factorial (p + 1 + 1)) := by nlinarith
        -- Goal matches key after Nat normalization
        simp only [Nat.factorial] at key ⊢
        push_cast at key ⊢
        linarith

/-! ### Pointwise Exponential Bound (Helper) -/

set_option maxHeartbeats 400000 in
-- Increased heartbeats: hasSum_nat_add_iff' unification is expensive.
/-- For real u with |u| ≤ c < 3: exp(u) ≤ 1 + u + u²/(2(1-c/3)).
    Uses power series for exp + factorial bound + geometric series. -/
private lemma exp_pointwise_bound {u c : ℝ} (_hc_pos : 0 < c)
    (hu : |u| ≤ c) (hc : c < 3) :
    exp u ≤ 1 + u + u ^ 2 / (2 * (1 - c / 3)) := by
  suffices h : exp u - 1 - u ≤ u ^ 2 / (2 * (1 - c / 3)) by linarith
  have hc3 : c / 3 < 1 := by linarith
  have h_denom_pos : (0 : ℝ) < 2 * (1 - c / 3) := by linarith
  have hau3 : |u| / 3 < 1 := by
    calc |u| / 3 ≤ c / 3 := by apply div_le_div_of_nonneg_right hu; norm_num
      _ < 1 := hc3
  have hau3_nn : 0 ≤ |u| / 3 := div_nonneg (abs_nonneg _) (by norm_num)
  -- Power series: exp u = ∑ u^n/n!
  have h_exp_hs : HasSum (fun n => u ^ n / ↑(n.factorial)) (exp u) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp u
  -- Split: HasSum (fun n => u^(n+2)/(n+2)!) (exp u - 1 - u)
  have h_tail_hs : HasSum (fun n => u ^ (n + 2) / ↑((n + 2).factorial))
      (exp u - 1 - u) := by
    have key : ∑ i ∈ Finset.range 2, u ^ i / ↑(i.factorial) = 1 + u := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial,
        Nat.cast_one, pow_zero, div_one, zero_add, pow_one]
      norm_num
    rw [show exp u - 1 - u = exp u - (1 + u) from by ring, ← key]
    exact (hasSum_nat_add_iff' 2).mpr h_exp_hs
  -- Term bound: u^(n+2)/(n+2)! ≤ |u|²/2 · (|u|/3)^n
  have h_term : ∀ n, u ^ (n + 2) / ↑((n + 2).factorial) ≤
      |u| ^ 2 / 2 * (|u| / 3) ^ n := by
    intro n
    have h_fact : 2 * (3 : ℝ) ^ n ≤ ↑((n + 2).factorial) :=
      factorial_ge_two_mul_three_pow (n + 2) (by omega)
    have h_fact_pos : (0 : ℝ) < ↑((n + 2).factorial) :=
      Nat.cast_pos.mpr (Nat.factorial_pos _)
    calc u ^ (n + 2) / ↑((n + 2).factorial)
        ≤ |u| ^ (n + 2) / ↑((n + 2).factorial) := by
          apply div_le_div_of_nonneg_right _ h_fact_pos.le
          exact (le_abs_self _).trans (abs_pow u (n + 2) ▸ le_refl _)
      _ ≤ |u| ^ (n + 2) / (2 * 3 ^ n) := by
          exact div_le_div_of_nonneg_left (pow_nonneg (abs_nonneg _) _)
            (by positivity) h_fact
      _ = |u| ^ 2 / 2 * (|u| / 3) ^ n := by
          rw [pow_add, div_pow]; ring
  -- Summable bound (geometric)
  have h_bound_sum : Summable (fun n => |u| ^ 2 / 2 * (|u| / 3) ^ n) :=
    (summable_geometric_of_lt_one hau3_nn hau3).mul_left _
  -- tsum bound
  have h_tsum_bound : ∑' n, u ^ (n + 2) / ↑((n + 2).factorial) ≤
      ∑' n, |u| ^ 2 / 2 * (|u| / 3) ^ n :=
    h_tail_hs.summable.tsum_le_tsum h_term h_bound_sum
  -- Geometric series
  have h_geom : ∑' n, |u| ^ 2 / 2 * (|u| / 3) ^ n =
      |u| ^ 2 / (2 * (1 - |u| / 3)) := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hau3_nn hau3]
    have h_ne : (1 : ℝ) - |u| / 3 ≠ 0 := by linarith
    field_simp
  -- Monotonicity: |u| ≤ c → u²/(2(1-|u|/3)) ≤ u²/(2(1-c/3))
  have h_mono : |u| ^ 2 / (2 * (1 - |u| / 3)) ≤ u ^ 2 / (2 * (1 - c / 3)) := by
    rw [sq_abs]
    exact div_le_div_of_nonneg_left (sq_nonneg _) h_denom_pos (by nlinarith [hu])
  calc exp u - 1 - u
      = ∑' n, u ^ (n + 2) / ↑((n + 2).factorial) := h_tail_hs.tsum_eq.symm
    _ ≤ ∑' n, |u| ^ 2 / 2 * (|u| / 3) ^ n := h_tsum_bound
    _ = |u| ^ 2 / (2 * (1 - |u| / 3)) := h_geom
    _ ≤ u ^ 2 / (2 * (1 - c / 3)) := h_mono

/-! ### Layer 2: MGF Bound (Statement) -/

/-- **Bernstein MGF bound** for bounded zero-mean random variables.

  If X has E[X] = 0, |X| ≤ b a.s., Var(X) ≤ σ², then for 0 < λ < 3/b:
    E[exp(λX)] ≤ exp(λ²σ²/(2(1 - λb/3)))

  Proof sketch: Expand exp(λX) = ∑ (λX)^k/k!, take expectations,
  apply `moment_bound_of_bounded` to bound E[X^k] ≤ σ²b^{k-2},
  use k! ≥ 2·3^{k-2} for k ≥ 2 to sum the geometric series,
  then apply 1+x ≤ exp(x).

  This is the key analytic step not in Mathlib. -/
theorem bernstein_mgf_bound
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX_meas : Measurable X)
    {b : ℝ} (hb : 0 < b)
    (h_bound : ∀ᵐ ω ∂μ, |X ω| ≤ b)
    (h_mean : ∫ ω, X ω ∂μ = 0)
    {sigma_sq : ℝ} (_hsigma : 0 ≤ sigma_sq)
    (h_var : ∫ ω, (X ω) ^ 2 ∂μ ≤ sigma_sq)
    {lam : ℝ} (hlam_pos : 0 < lam) (hlam_lt : lam < 3 / b) :
    ∫ ω, exp (lam * X ω) ∂μ ≤
      exp (lam^2 * sigma_sq / (2 * (1 - lam * b / 3))) := by
  -- Uses Mathlib's CGF Taylor approach (same as Hoeffding proof)
  -- but with a variance-dependent bound instead of range-dependent.
  -- cgf(λ) = cgf''(u)·λ²/2, and cgf''(u) = Var[X; tilted by u]
  -- ≤ σ²/(1-ub/3) (refined bound for bounded r.v.s)
  -- Step 1: Pointwise bound
  -- For |x| ≤ b and 0 < λb < 3:
  -- exp(λx) ≤ 1 + λx + λ²x²/(2(1-λb/3))
  -- (from power series: (λx)^k/k! ≤ λ²x²(λb)^{k-2}/(2·3^{k-2}))
  have h_pw : ∀ᵐ ω ∂μ,
      exp (lam * X ω) ≤ 1 + lam * X ω +
      lam ^ 2 * (X ω) ^ 2 / (2 * (1 - lam * b / 3)) := by
    -- This is a standard real analysis bound. For |x| ≤ b, λb < 3:
    -- exp(λx) = 1 + λx + ∑_{k≥2} (λx)^k/k!
    -- ≤ 1 + λx + (λx)² · ∑_{j≥0} |λx|^j / ((j+2)!)
    -- ≤ 1 + λx + λ²x² · ∑_{j≥0} (λb/3)^j / 2
    -- = 1 + λx + λ²x²/(2(1-λb/3))
    -- The key step k! ≥ 2·3^{k-2} uses induction.
    filter_upwards [h_bound] with ω hω
    -- Apply pointwise bound with u = lam * X ω, c = lam * b
    have hlamb_pos : 0 < lam * b := mul_pos hlam_pos hb
    have hlamb_lt : lam * b < 3 := by
      calc lam * b < 3 / b * b := mul_lt_mul_of_pos_right hlam_lt hb
        _ = 3 := div_mul_cancel₀ _ hb.ne'
    have hu_le : |lam * X ω| ≤ lam * b := by
      rw [abs_mul, abs_of_pos hlam_pos]
      exact mul_le_mul_of_nonneg_left hω hlam_pos.le
    have h := exp_pointwise_bound hlamb_pos hu_le hlamb_lt
    -- Rewrite (lam * X ω)^2 = lam^2 * (X ω) ^ 2
    rwa [show (lam * X ω) ^ 2 = lam ^ 2 * (X ω) ^ 2 from by ring] at h
  -- Step 2: Integrate
  -- E[exp(λX)] ≤ 1 + 0 + λ²σ²/(2(1-λb/3))
  -- (using E[X]=0, E[X²] ≤ σ²)
  have h_int : ∫ ω, exp (lam * X ω) ∂μ ≤
      1 + lam ^ 2 * sigma_sq / (2 * (1 - lam * b / 3)) := by
    -- ∫ exp(λX) ≤ ∫ (1 + λX + λ²X²/(2(1-λb/3)))
    -- = 1 + λ·E[X] + λ²/(2(1-λb/3))·E[X²]
    -- = 1 + 0 + λ²σ²/(2(1-λb/3))
    -- ∫ exp(λX) ≤ ∫ (1 + λX + λ²X²/(2(1-λb/3)))
    -- = 1 + λ E[X] + λ²/(2(1-λb/3)) E[X²]
    -- = 1 + 0 + λ²σ²/(2(1-λb/3))
    -- Abbreviation for the constant denominator
    set C := 2 * (1 - lam * b / 3) with hC_def
    have hlamb_lt' : lam * b < 3 := by
      calc lam * b < 3 / b * b := mul_lt_mul_of_pos_right hlam_lt hb
        _ = 3 := div_mul_cancel₀ _ hb.ne'
    have hC_pos : 0 < C := by linarith [hC_def]
    -- Integrability: exp(λX) bounded a.e. by exp(λb)
    have h_exp_int : Integrable (fun ω => exp (lam * X ω)) μ := by
      apply Integrable.of_bound
        ((hX_meas.const_mul lam).exp.aestronglyMeasurable) (exp (lam * b))
      filter_upwards [h_bound] with ω hω
      rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      apply exp_le_exp.mpr
      have : X ω ≤ |X ω| := le_abs_self _
      nlinarith
    -- Integrability: X bounded ⟹ X, X² integrable
    have h_X_int : Integrable X μ :=
      Integrable.of_bound hX_meas.aestronglyMeasurable b
        (by filter_upwards [h_bound] with ω hω; exact (Real.norm_eq_abs _ ▸ hω))
    have h_X2_int : Integrable (fun ω => (X ω) ^ 2) μ :=
      Integrable.of_bound (hX_meas.pow_const 2).aestronglyMeasurable (b ^ 2)
        (by filter_upwards [h_bound] with ω hω
            rw [Real.norm_eq_abs, abs_pow]
            exact pow_le_pow_left₀ (abs_nonneg _) hω 2)
    -- Integrability: polynomial 1 + λX + λ²X²/C
    have h_poly_int : Integrable (fun ω => 1 + lam * X ω +
        lam ^ 2 * (X ω) ^ 2 / C) μ :=
      ((integrable_const 1).add (h_X_int.const_mul lam)).add
        (h_X2_int.const_mul (lam ^ 2) |>.div_const C)
    -- Bound ∫ exp(λX) via integral_mono_ae + linearity
    calc ∫ ω, exp (lam * X ω) ∂μ
        ≤ ∫ ω, (1 + lam * X ω + lam ^ 2 * (X ω) ^ 2 / C) ∂μ :=
          integral_mono_ae h_exp_int h_poly_int h_pw
      _ = (∫ ω, (1 + lam * X ω) ∂μ) +
          ∫ ω, (lam ^ 2 * (X ω) ^ 2 / C) ∂μ :=
          integral_add ((integrable_const 1).add (h_X_int.const_mul _))
            (h_X2_int.const_mul _ |>.div_const _)
      _ = ((∫ ω, (1 : ℝ) ∂μ) + ∫ ω, lam * X ω ∂μ) +
          ∫ ω, (lam ^ 2 * (X ω) ^ 2 / C) ∂μ := by
          congr 1; exact integral_add (integrable_const 1) (h_X_int.const_mul _)
      _ = (1 + lam * ∫ ω, X ω ∂μ) +
          (lam ^ 2 / C * ∫ ω, (X ω) ^ 2 ∂μ) := by
          congr 1
          · congr 1
            · simp [integral_const]
            · exact integral_const_mul _ _
          · rw [integral_div, integral_const_mul]; ring
      _ = 1 + lam ^ 2 / C * ∫ ω, (X ω) ^ 2 ∂μ := by
          rw [h_mean, mul_zero, add_zero]
      _ ≤ 1 + lam ^ 2 / C * sigma_sq := by
          gcongr
      _ = 1 + lam ^ 2 * sigma_sq / C := by ring
  -- Step 3: 1 + x ≤ exp(x)
  calc ∫ ω, exp (lam * X ω) ∂μ
      ≤ 1 + lam ^ 2 * sigma_sq / (2 * (1 - lam * b / 3)) := h_int
    _ ≤ exp (lam ^ 2 * sigma_sq / (2 * (1 - lam * b / 3))) :=
        by linarith [Real.add_one_le_exp
              (lam ^ 2 * sigma_sq / (2 * (1 - lam * b / 3)))]

/-! ### Layer 3: Bernstein Tail Bound (Statement) -/

/-- **Bernstein's inequality** (one-sided tail bound).

  For independent zero-mean random variables X₁,...,X_N with
  |Xᵢ| ≤ b a.s. and ∑Var(Xᵢ) ≤ V:

    P(∑Xᵢ ≥ t) ≤ exp(-t²/(2V + 2bt/3))

  Follows from `bernstein_mgf_bound` via the Chernoff method
  (Mathlib's `measure_ge_le_exp_add`) and independence
  (Mathlib's `iIndepFun`). -/
theorem bernstein_sum
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} {N : ℕ} (_hN : 0 < N)
    (hX_meas : ∀ i, Measurable (X i))
    (h_indep : iIndepFun X μ)
    {b : ℝ} (hb : 0 < b)
    (h_bound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ b)
    (h_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    {V : ℝ} (hV : 0 ≤ V)
    (h_var_sum : ∑ i ∈ range N,
      ∫ ω, (X i ω) ^ 2 ∂μ ≤ V)
    {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t ≤ ∑ i ∈ range N, X i ω} ≤
      exp (-t^2 / (2 * V + 2 * b * t / 3)) := by
  -- Chernoff method: P(S ≥ t) ≤ inf_λ exp(-λt) · ∏ E[exp(λXᵢ)]
  -- With λ = t/(V + bt/3): exp(-t²/(2V + 2bt/3))
  -- Uses: bernstein_mgf_bound for each Xᵢ, independence for
  -- product, and optimization over λ.
  -- Case split: V = 0 vs V > 0
  -- (V = 0 means all X_i = 0 a.s., so P(S ≥ t) = 0;
  --  V > 0 uses Chernoff with λ = t/(V+bt/3))
  rcases eq_or_lt_of_le hV with rfl | hV_pos
  · -- V = 0: all variances zero, X_i = 0 a.s., S = 0 a.s., P(S≥t) = 0
    -- Step 1: each ∫ (X i)^2 = 0
    have h_nonneg : ∀ i ∈ range N, 0 ≤ ∫ ω, (X i ω) ^ 2 ∂μ :=
      fun i _ => integral_nonneg fun ω => sq_nonneg _
    have h_sum_zero : ∑ i ∈ range N, ∫ ω, (X i ω) ^ 2 ∂μ = 0 :=
      le_antisymm h_var_sum (Finset.sum_nonneg h_nonneg)
    have h_each_zero : ∀ i ∈ range N, ∫ ω, (X i ω) ^ 2 ∂μ = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg h_nonneg).mp h_sum_zero
    -- Step 2: X i = 0 a.e. for each i in range N
    have h_Xi_ae : ∀ i ∈ range N, X i =ᵐ[μ] 0 := by
      intro i hi
      have h_int_sq : Integrable (fun ω => (X i ω) ^ 2) μ :=
        Integrable.of_bound ((hX_meas i).pow_const 2).aestronglyMeasurable (b ^ 2)
          (by filter_upwards [h_bound i] with ω hω
              rw [Real.norm_eq_abs, abs_pow]
              exact pow_le_pow_left₀ (abs_nonneg _) hω 2)
      have h_sq_ae : (fun ω => (X i ω) ^ 2) =ᵐ[μ] 0 :=
        (integral_eq_zero_iff_of_nonneg_ae
          (ae_of_all μ fun ω => sq_nonneg (X i ω)) h_int_sq).mp
          (h_each_zero i hi)
      filter_upwards [h_sq_ae] with ω hω
      simp only [Pi.zero_apply] at hω ⊢
      exact sq_eq_zero_iff.mp hω
    -- Step 3: ∑ X i = 0 a.e.
    have h_sum_ae : ∀ᵐ ω ∂μ, ∑ i ∈ range N, X i ω = 0 := by
      -- Use ae_all_iff: ∀ᵐ ω, ∀ i, (i ∈ range N → X i ω = 0)
      have : ∀ᵐ ω ∂μ, ∀ i, i ∈ range N → X i ω = 0 := by
        rw [ae_all_iff]
        intro i
        by_cases hi : i ∈ range N
        · filter_upwards [h_Xi_ae i hi] with ω hω _
          exact hω
        · exact ae_of_all μ fun ω hi' => absurd hi' hi
      filter_upwards [this] with ω hω
      exact Finset.sum_eq_zero fun i hi => hω i hi
    -- Step 4: μ {ω | t ≤ ∑ X i ω} = 0
    have h_meas_zero : μ {ω | t ≤ ∑ i ∈ range N, X i ω} = 0 := by
      apply measure_mono_null (t := {ω | ∑ i ∈ range N, X i ω ≠ 0})
      · intro ω hω
        simp only [Set.mem_setOf_eq] at hω ⊢
        linarith
      · rw [← ae_iff]
        filter_upwards [h_sum_ae] with ω hω
        exact hω
    -- Step 5: μ.real = 0 ≤ exp(...)
    have h_real_zero : μ.real {ω | t ≤ ∑ i ∈ range N, X i ω} = 0 := by
      rw [measureReal_eq_zero_iff]
      exact h_meas_zero
    rw [h_real_zero]
    exact (exp_pos _).le
  · -- V > 0: Chernoff method with λ = t/(V + bt/3)
    set D := V + b * t / 3 with hD_def
    have hD_pos : 0 < D := by positivity
    set lam := t / D with hlam_def
    have hlam_pos : 0 < lam := div_pos ht hD_pos
    have hlam_lt : lam < 3 / b := by
      rw [hlam_def, div_lt_div_iff₀ hD_pos hb]; nlinarith
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
    -- Bound each mgf: mgf(X_i,λ) ≤ exp(λ²σ_i²/(2(1-λb/3)))
    have h_mgf_le : ∀ i ∈ range N, mgf (X i) μ lam ≤
        exp (lam ^ 2 * (∫ ω, (X i ω) ^ 2 ∂μ) /
          (2 * (1 - lam * b / 3))) := by
      intro i _
      exact bernstein_mgf_bound (hX_meas i) hb (h_bound i) (h_mean i)
        (integral_nonneg (fun ω => sq_nonneg _)) (le_refl _)
        hlam_pos hlam_lt
    -- Product bound: ∏ mgf(X_i,λ) ≤ exp(λ²V/(2(1-λb/3)))
    have h_prod_le : ∏ i ∈ range N, mgf (X i) μ lam ≤
        exp (lam ^ 2 * V / (2 * (1 - lam * b / 3))) := by
      -- Abbreviation for the denominator
      set C := 2 * (1 - lam * b / 3) with hC_def
      have hlamb_lt' : lam * b < 3 := by
        calc lam * b < 3 / b * b := mul_lt_mul_of_pos_right hlam_lt hb
          _ = 3 := div_mul_cancel₀ _ hb.ne'
      have hC_pos : 0 < C := by linarith [hC_def]
      -- Step 1: ∏ mgf(X_i, λ) ≤ ∏ exp(λ²σ_i²/C)
      have h_step1 : ∏ i ∈ range N, mgf (X i) μ lam ≤
          ∏ i ∈ range N, exp (lam ^ 2 * (∫ ω, (X i ω) ^ 2 ∂μ) / C) :=
        Finset.prod_le_prod (fun i _ => mgf_nonneg) h_mgf_le
      -- Step 2: ∏ exp(a_i) = exp(∑ a_i)
      have h_step2 : ∏ i ∈ range N,
          exp (lam ^ 2 * (∫ ω, (X i ω) ^ 2 ∂μ) / C) =
          exp (∑ i ∈ range N, lam ^ 2 * (∫ ω, (X i ω) ^ 2 ∂μ) / C) :=
        (exp_sum _ _).symm
      -- Step 3: ∑ (λ²σ_i²/C) = λ²/C · ∑ σ_i²
      have h_step3 : ∑ i ∈ range N, lam ^ 2 * (∫ ω, (X i ω) ^ 2 ∂μ) / C =
          lam ^ 2 / C * ∑ i ∈ range N, ∫ ω, (X i ω) ^ 2 ∂μ := by
        rw [Finset.mul_sum]; congr 1; ext i; ring
      -- Step 4: λ²/C · ∑ σ_i² ≤ λ²/C · V = λ²V/C
      have h_step4 : lam ^ 2 / C * ∑ i ∈ range N, ∫ ω, (X i ω) ^ 2 ∂μ ≤
          lam ^ 2 * V / C := by
        rw [div_mul_eq_mul_div]
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left h_var_sum (sq_nonneg _)) hC_pos.le
      calc ∏ i ∈ range N, mgf (X i) μ lam
          ≤ ∏ i ∈ range N, exp (lam ^ 2 * (∫ ω, (X i ω) ^ 2 ∂μ) / C) := h_step1
        _ = exp (∑ i ∈ range N, lam ^ 2 * (∫ ω, (X i ω) ^ 2 ∂μ) / C) := h_step2
        _ = exp (lam ^ 2 / C * ∑ i ∈ range N, ∫ ω, (X i ω) ^ 2 ∂μ) := by
            rw [h_step3]
        _ ≤ exp (lam ^ 2 * V / C) := exp_le_exp.mpr h_step4
    -- Combine: P(S≥t) ≤ exp(-λt)·exp(λ²V/...) = exp(-t²/(2V+2bt/3))
    calc μ.real {ω | t ≤ ∑ i ∈ range N, X i ω}
        ≤ exp (-lam * t) *
          mgf (fun ω => ∑ i ∈ range N, X i ω) μ lam := h_chernoff
      _ = exp (-lam * t) *
          ∏ i ∈ range N, mgf (X i) μ lam := by rw [h_mgf_factor]
      _ ≤ exp (-lam * t) *
          exp (lam ^ 2 * V / (2 * (1 - lam * b / 3))) := by
          gcongr
      _ = exp (-lam * t +
          lam ^ 2 * V / (2 * (1 - lam * b / 3))) := by
          rw [← exp_add]
      _ = exp (-t ^ 2 / (2 * V + 2 * b * t / 3)) := by
          congr 1
          rw [hlam_def, show D = V + b * t / 3 from rfl]
          have h_denom_ne : V + b * t / 3 ≠ 0 := hD_pos.ne'
          have h1mb_ne : (1 : ℝ) - t / (V + b * t / 3) * b / 3 ≠ 0 := by
            have : t / (V + b * t / 3) * b < 3 := by
              calc t / (V + b * t / 3) * b
                  < 3 / b * b := by gcongr
                _ = 3 := div_mul_cancel₀ _ hb.ne'
            linarith
          field_simp; ring

/-! ### Two-Sided Bernstein Inequality

  Boucheron et al., Corollary 2.11: For independent zero-mean r.v.s
  with |X_i| ≤ b and ∑E[X_i²] ≤ V:

    P(|S| ≥ t) ≤ 2·exp(-t²/(2(V + bt/3)))

  This follows from the one-sided bound applied to both S and -S. -/

/-- **Two-sided Bernstein inequality** (Boucheron et al. Corollary 2.11).

  For independent zero-mean bounded random variables X₁,...,X_N with
  |X_i| ≤ b a.s. and ∑ E[X_i²] ≤ V:

    P(|∑ X_i| ≥ t) ≤ 2·exp(-t²/(2V + 2bt/3))

  Proof: apply the one-sided `bernstein_sum` to both S and -S. -/
theorem bernstein_two_sided
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} {N : ℕ} (hN : 0 < N)
    (hX_meas : ∀ i, Measurable (X i))
    (h_indep : iIndepFun X μ)
    {b : ℝ} (hb : 0 < b)
    (h_bound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ b)
    (h_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    {V : ℝ} (hV : 0 ≤ V)
    (h_var_sum : ∑ i ∈ range N, ∫ ω, (X i ω) ^ 2 ∂μ ≤ V)
    {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t ≤ |∑ i ∈ range N, X i ω|} ≤
      2 * exp (-t ^ 2 / (2 * V + 2 * b * t / 3)) := by
  -- Upper tail: P(S ≥ t) ≤ exp(...)
  have h_upper := bernstein_sum hN hX_meas h_indep hb h_bound h_mean hV h_var_sum ht
  -- -X_i: independent, zero-mean, bounded, same variance
  have h_neg_meas : ∀ i, Measurable (fun ω => -X i ω) := fun i => (hX_meas i).neg
  have h_neg_indep : iIndepFun (fun i ω => -X i ω) μ := by
    simpa using h_indep.comp
      (g := fun (_ : ℕ) (x : ℝ) => -x)
      (fun _ => measurable_neg)
  have h_neg_bound : ∀ i, ∀ᵐ ω ∂μ, |(fun ω => -X i ω) ω| ≤ b := by
    intro i; filter_upwards [h_bound i] with ω hω; simp [abs_neg, hω]
  have h_neg_mean : ∀ i, ∫ ω, (fun ω => -X i ω) ω ∂μ = 0 := by
    intro i; simp [integral_neg, h_mean i]
  have h_neg_var : ∑ i ∈ range N, ∫ ω, ((fun ω => -X i ω) ω) ^ 2 ∂μ ≤ V := by
    simp only [neg_sq]; exact h_var_sum
  -- Lower tail: P(∑(-X_i) ≥ t) ≤ exp(...)
  have h_lower := bernstein_sum hN h_neg_meas h_neg_indep hb
    h_neg_bound h_neg_mean hV h_neg_var ht
  -- {|S| ≥ t} ⊆ {S ≥ t} ∪ {∑(-X_i) ≥ t}
  have h_subset : {ω | t ≤ |∑ i ∈ range N, X i ω|} ⊆
      {ω | t ≤ ∑ i ∈ range N, X i ω} ∪
      {ω | t ≤ ∑ i ∈ range N, (fun ω => -X i ω) ω} := by
    intro ω hω
    simp only [Set.mem_union, Set.mem_setOf_eq, Finset.sum_neg_distrib]
    simp only [Set.mem_setOf_eq] at hω
    cases le_abs.mp hω with
    | inl h => exact Or.inl h
    | inr h => exact Or.inr (by linarith)
  -- Combine via union bound
  calc μ.real {ω | t ≤ |∑ i ∈ range N, X i ω|}
      ≤ μ.real ({ω | t ≤ ∑ i ∈ range N, X i ω} ∪
          {ω | t ≤ ∑ i ∈ range N, (fun ω => -X i ω) ω}) :=
        measureReal_mono h_subset
    _ ≤ μ.real {ω | t ≤ ∑ i ∈ range N, X i ω} +
        μ.real {ω | t ≤ ∑ i ∈ range N, (fun ω => -X i ω) ω} :=
        measureReal_union_le _ _
    _ ≤ exp (-t ^ 2 / (2 * V + 2 * b * t / 3)) +
        exp (-t ^ 2 / (2 * V + 2 * b * t / 3)) :=
        add_le_add h_upper h_lower
    _ = 2 * exp (-t ^ 2 / (2 * V + 2 * b * t / 3)) := by ring

/-! ### Chebyshev-Cantelli Inequality (One-Sided Chebyshev)

  Boucheron et al., Exercise 2.3. For any random variable Y with
  E[Y] = 0 and E[Y²] ≤ σ², and for any t > 0:

    P(Y ≥ t) ≤ σ² / (σ² + t²)

  **Proof**: For any u > 0, P(Y ≥ t) = P(Y+u ≥ t+u) ≤ P((Y+u)² ≥ (t+u)²)
  ≤ E[(Y+u)²]/(t+u)² by Markov. Since E[Y]=0, E[(Y+u)²] = E[Y²]+u².
  The bound (E[Y²]+u²)/(t+u)² is minimized at u = E[Y²]/t, giving
  E[Y²]/(E[Y²]+t²). We prove the pre-optimized version.

  Unlike Hoeffding/Bernstein, this requires NO independence or boundedness,
  only finite second moment. -/

/-- **Chebyshev-Cantelli (pre-optimized)**.

  For Y with E[Y]=0 and E[Y²] ≤ σ², and any shift u > 0:

    P(Y ≥ t) ≤ (σ² + u²) / (t + u)²

  This yields the Chebyshev-Cantelli bound σ²/(σ²+t²) at u = σ²/t. -/
theorem chebyshev_cantelli_aux
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y : Ω → ℝ}
    (hY_int : Integrable Y μ)
    (hY_sq_int : Integrable (fun ω => (Y ω) ^ 2) μ)
    (h_mean : ∫ ω, Y ω ∂μ = 0)
    {sigma_sq : ℝ} (_hsigma : 0 ≤ sigma_sq)
    (h_var : ∫ ω, (Y ω) ^ 2 ∂μ ≤ sigma_sq)
    {t : ℝ} (ht : 0 < t) {u : ℝ} (hu : 0 < u) :
    μ.real {ω | t ≤ Y ω} ≤ (sigma_sq + u ^ 2) / (t + u) ^ 2 := by
  have htu : 0 < t + u := by linarith
  -- {Y ≥ t} ⊆ {(Y+u)² ≥ (t+u)²}
  have h_subset : {ω | t ≤ Y ω} ⊆ {ω | (t + u) ^ 2 ≤ (Y ω + u) ^ 2} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    nlinarith [sq_nonneg (Y ω + u - (t + u))]
  -- E[(Y+u)²] = E[Y²] + u²  (since E[Y]=0)
  have h_shift_int : Integrable (fun ω => (Y ω + u) ^ 2) μ := by
    have : (fun ω => (Y ω + u) ^ 2) = fun ω => (Y ω) ^ 2 + 2 * u * Y ω + u ^ 2 := by
      ext ω; ring
    rw [this]; exact (hY_sq_int.add (hY_int.const_mul _)).add (integrable_const _)
  have h_E_shift : ∫ ω, (Y ω + u) ^ 2 ∂μ = (∫ ω, (Y ω) ^ 2 ∂μ) + u ^ 2 := by
    -- E[(Y+u)²] = E[Y² + 2uY + u²] = E[Y²] + 2u·E[Y] + u² = E[Y²] + u²
    calc ∫ ω, (Y ω + u) ^ 2 ∂μ
        = ∫ ω, ((Y ω) ^ 2 + (2 * u * Y ω + u ^ 2)) ∂μ := by
          congr 1; ext ω; ring
      _ = (∫ ω, (Y ω) ^ 2 ∂μ) + ∫ ω, (2 * u * Y ω + u ^ 2) ∂μ := by
          exact integral_add hY_sq_int ((hY_int.const_mul _).add (integrable_const _))
      _ = (∫ ω, (Y ω) ^ 2 ∂μ) + (2 * u * (∫ ω, Y ω ∂μ) + u ^ 2) := by
          congr 1
          calc ∫ ω, (2 * u * Y ω + u ^ 2) ∂μ
              = (∫ ω, (2 * u) * Y ω ∂μ) + ∫ _, u ^ 2 ∂μ :=
                integral_add (hY_int.const_mul _) (integrable_const _)
            _ = 2 * u * (∫ ω, Y ω ∂μ) + u ^ 2 := by
                rw [integral_const_mul, integral_const, smul_eq_mul]
                simp [probReal_univ]
      _ = (∫ ω, (Y ω) ^ 2 ∂μ) + u ^ 2 := by rw [h_mean, mul_zero, zero_add]
  -- E[(Y+u)²] ≤ σ² + u²
  have h_E_le : ∫ ω, (Y ω + u) ^ 2 ∂μ ≤ sigma_sq + u ^ 2 := by
    rw [h_E_shift]; linarith
  -- Markov: P((Y+u)² ≥ c) ≤ E[(Y+u)²]/c  for c > 0
  -- We use: P(Z ≥ c) ≤ E[Z]/c for nonneg Z
  -- Chain: P(Y≥t) ≤ P((Y+u)²≥(t+u)²) ≤ E[(Y+u)²]/(t+u)² ≤ (σ²+u²)/(t+u)²
  have h_sq_nonneg : 0 ≤ᵐ[μ] fun ω => (Y ω + u) ^ 2 :=
    ae_of_all μ fun ω => sq_nonneg _
  have h_c_pos : (0 : ℝ) < (t + u) ^ 2 := by positivity
  calc μ.real {ω | t ≤ Y ω}
      ≤ μ.real {ω | (t + u) ^ 2 ≤ (Y ω + u) ^ 2} :=
        measureReal_mono h_subset
    _ ≤ (∫ ω, (Y ω + u) ^ 2 ∂μ) / (t + u) ^ 2 := by
        -- Markov: ε · μ{f ≥ ε} ≤ ∫f for nonneg f
        -- mul_meas_ge_le_integral_of_nonneg : 0 ≤ᵐ f → Integrable f → 0 ≤ ε →
        --   ε * (μ {ω | ε ≤ f ω}).toReal ≤ ∫ f
        -- Markov: ε * μ.real{f ≥ ε} ≤ ∫f  (Mathlib uses μ.real directly)
        have h_markov := mul_meas_ge_le_integral_of_nonneg
          h_sq_nonneg h_shift_int ((t + u) ^ 2)
        -- h_markov : (t+u)² * μ.real{(Y+u)² ≥ (t+u)²} ≤ ∫(Y+u)²
        rw [le_div_iff₀ h_c_pos]
        linarith
    _ ≤ (sigma_sq + u ^ 2) / (t + u) ^ 2 :=
        div_le_div_of_nonneg_right h_E_le (by positivity)

end
