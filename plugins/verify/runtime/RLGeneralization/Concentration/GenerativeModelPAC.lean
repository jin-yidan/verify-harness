/-
# Generative Model: PAC Sample Complexity

Sample complexity inversion and capstone PAC theorems for the
generative model, including both Hoeffding-based and Bernstein-based
rates with existential sample count formulations.

## Main Results

* `pac_rl_generative_model_bernstein` — PAC with Bernstein log-rate
* `pac_rl_generative_model_bernstein_existential` — existential N₀
* `pac_rl_generative_model_bernstein_optimal` — with optimal policy witness

## References

* [Azar, Munos, Kappen, *Minimax PAC bounds*][azar2013]
* [Agarwal et al., *RL: Theory and Algorithms*]
-/

import RLGeneralization.Concentration.GenerativeModelMinimax

open Finset BigOperators MeasureTheory ProbabilityTheory ENNReal

noncomputable section

namespace FiniteMDP

variable (M : FiniteMDP)

/-! ### Sample Complexity Inversion

The capstone theorem bounds the value gap as a function of per-entry error
tolerance `eps_0` and sample count `N`. This section inverts the relationship:
given desired value gap `ε` and confidence `1-δ`, we show there exists a
sufficient sample count `N₀`.

The proof uses the Hoeffding-based capstone for cleaner algebraic inversion.
The Bernstein-based capstone yields tighter constants. -/

/-- Each transition probability is bounded by 1, since probabilities are
    nonneg and sum to 1 over the next-state space. -/
lemma P_le_one (s : M.S) (a : M.A) (s' : M.S) : M.P s a s' ≤ 1 := by
  calc M.P s a s' ≤ ∑ s'' : M.S, M.P s a s'' :=
        Finset.single_le_sum (f := fun s'' => M.P s a s'')
          (fun s'' _ => M.P_nonneg s a s'') (Finset.mem_univ s')
    _ = 1 := M.P_sum_one s a

/-- The per-entry error tolerance chosen to make the deterministic
    value-gap bound `2γR_max|S|ε₀/(1-γ)²` equal the target `ε`.
    Defined as `ε(1-γ)²/(2γR_max|S|)`. Requires `γ > 0`. -/
noncomputable def pac_eps_0 (ε : ℝ) : ℝ :=
  ε * (1 - M.γ) ^ 2 / (2 * M.γ * M.R_max * ↑(Fintype.card M.S))

lemma pac_eps_0_pos {ε : ℝ} (hε : 0 < ε) (hγ : 0 < M.γ) :
    0 < M.pac_eps_0 ε := by
  unfold pac_eps_0
  apply div_pos
  · exact mul_pos hε (sq_pos_of_pos (sub_pos.mpr M.γ_lt_one))
  · exact mul_pos (mul_pos (mul_pos (by norm_num : (0:ℝ) < 2) hγ) M.R_max_pos)
      (Nat.cast_pos.mpr Fintype.card_pos)

/-- With the chosen `pac_eps_0`, the deterministic value-gap bound equals ε. -/
lemma pac_value_gap_eq {ε : ℝ} (hε : 0 < ε) (hγ : 0 < M.γ) :
    2 * M.γ * M.R_max * (↑(Fintype.card M.S) * M.pac_eps_0 ε) /
      (1 - M.γ) ^ 2 = ε := by
  unfold pac_eps_0
  have hγ_ne : M.γ ≠ 0 := ne_of_gt hγ
  have hR_ne : M.R_max ≠ 0 := ne_of_gt M.R_max_pos
  have hS_ne : (Fintype.card M.S : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fintype.card_ne_zero)
  have h1γ_ne : (1 : ℝ) - M.γ ≠ 0 := ne_of_gt (sub_pos.mpr M.γ_lt_one)
  field_simp [hγ_ne, hR_ne, hS_ne, h1γ_ne]

/-- The Hoeffding failure term `K·2·exp(-2Nc²)` tends to zero as `N → ∞`.
    For any `c > 0` and `δ > 0`, there exists `N₀` such that for all `N ≥ N₀`
    the failure is at most `δ`.

    Proof uses `1 + x ≤ exp(x)`, so `exp(-x) ≤ 1/(1+x)`, giving a polynomial
    sufficient condition that avoids log/exp inversion. -/
lemma hoeffding_failure_eventually_small
    (c : ℝ) (hc : 0 < c) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ↑(Fintype.card M.S) * ↑(Fintype.card M.S) * ↑(Fintype.card M.A) *
        (2 * Real.exp (-2 * ↑N * c ^ 2)) ≤ δ := by
  -- K = |S|²|A| > 0
  set K : ℝ := ↑(Fintype.card M.S) * ↑(Fintype.card M.S) *
    ↑(Fintype.card M.A)
  have hK_pos : 0 < K := by positivity
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
  -- We need N large enough that K * 2 * exp(-2Nc²) ≤ δ.
  -- Key bound: 1 + x ≤ exp(x) for all x, so exp(-x) ≤ 1/(1+x) for x > -1.
  -- With x = 2Nc²: exp(-2Nc²) ≤ 1/(1 + 2Nc²).
  -- So K * 2/(1 + 2Nc²) ≤ δ when 1 + 2Nc² ≥ 2K/δ, i.e., N ≥ K/(δc²).
  -- Choose N₀ = max 1 ⌈K/(δ·c²)⌉₊.
  refine ⟨max 1 ⌈K / (δ * c ^ 2)⌉₊, by omega, fun N hN => ?_⟩
  -- N ≥ ⌈K/(δc²)⌉₊ ≥ K/(δc²)
  have hdc_pos : 0 < δ * c ^ 2 := mul_pos hδ hc2
  have hNge : K / (δ * c ^ 2) ≤ ↑N := by
    have h1 : K / (δ * c ^ 2) ≤ ↑⌈K / (δ * c ^ 2)⌉₊ := Nat.le_ceil _
    have h2 : ⌈K / (δ * c ^ 2)⌉₊ ≤ max 1 ⌈K / (δ * c ^ 2)⌉₊ :=
      le_max_right _ _
    have h3 : max 1 ⌈K / (δ * c ^ 2)⌉₊ ≤ N := hN
    calc K / (δ * c ^ 2) ≤ ↑⌈K / (δ * c ^ 2)⌉₊ := h1
      _ ≤ ↑(max 1 ⌈K / (δ * c ^ 2)⌉₊) := Nat.cast_le.mpr h2
      _ ≤ ↑N := Nat.cast_le.mpr h3
  -- From hNge: K ≤ N·δ·c²
  have hKN : K ≤ ↑N * (δ * c ^ 2) := by
    rwa [div_le_iff₀ hdc_pos] at hNge
  -- exp(2Nc²) ≥ 1 + 2Nc² (from x+1 ≤ exp(x))
  have h_exp_ge : 2 * ↑N * c ^ 2 + 1 ≤ Real.exp (2 * ↑N * c ^ 2) :=
    Real.add_one_le_exp _
  -- Therefore 2K ≤ δ·exp(2Nc²)
  have h2K : 2 * K ≤ δ * Real.exp (2 * ↑N * c ^ 2) :=
    calc 2 * K ≤ 2 * (↑N * (δ * c ^ 2)) := by linarith
      _ = δ * (2 * ↑N * c ^ 2) := by ring
      _ ≤ δ * (2 * ↑N * c ^ 2 + 1) := by linarith
      _ ≤ δ * Real.exp (2 * ↑N * c ^ 2) :=
          mul_le_mul_of_nonneg_left h_exp_ge hδ.le
  -- K·2·exp(-2Nc²) · exp(2Nc²) = 2K  [since exp(-x)·exp(x) = 1]
  -- and 2K ≤ δ·exp(2Nc²), so dividing by exp(2Nc²) > 0 gives the result.
  have hexp_pos : 0 < Real.exp (2 * ↑N * c ^ 2) := Real.exp_pos _
  have h_prod : K * (2 * Real.exp (-2 * ↑N * c ^ 2)) *
      Real.exp (2 * ↑N * c ^ 2) = 2 * K := by
    have h1 : Real.exp (-2 * ↑N * c ^ 2) * Real.exp (2 * ↑N * c ^ 2) = 1 := by
      rw [← Real.exp_add]
      simp [Real.exp_zero]
    nlinarith [h1]
  -- K * 2 * exp(-2Nc²) ≤ δ
  have h_ineq : K * (2 * Real.exp (-2 * ↑N * c ^ 2)) *
      Real.exp (2 * ↑N * c ^ 2) ≤ δ * Real.exp (2 * ↑N * c ^ 2) := by
    rw [h_prod]; exact h2K
  exact le_of_mul_le_mul_right h_ineq hexp_pos

/-! ### Bernstein Log-Rate Inversion

The following upgrades the polynomial-in-1/δ Hoeffding inversion above to
a logarithmic `log(1/δ)` rate using the Bernstein capstone.

Key steps:
1. Bound each per-entry Bernstein exponent uniformly using `p(1-p) ≤ 1/4`.
2. Sum over `|S|²|A|` entries to get `K·2·exp(-N·c)` where `c = ε₀²/(1/2+2ε₀/3)`.
3. Invert via `Real.log`: N ≥ log(2K/δ)/c suffices. -/

/-- Bernstein coefficient: `c = ε₀²/(1/2 + 2ε₀/3)`, the exponent rate
    after bounding the per-entry variance `p(1-p)` by `1/4`. -/
noncomputable def bernsteinCoeff (eps_0 : ℝ) : ℝ :=
  eps_0 ^ 2 / (1 / 2 + 2 * eps_0 / 3)

lemma bernsteinCoeff_pos {eps_0 : ℝ} (heps : 0 < eps_0) :
    0 < bernsteinCoeff eps_0 := by
  apply div_pos (sq_pos_of_pos heps)
  linarith

/-- Each Bernstein per-entry failure term is bounded by the uniform
    exponential `2·exp(-N·c)` after replacing `p(1-p)` with `1/4`. -/
lemma bernstein_entry_uniform_bound
    {N : ℕ} (hN : 0 < N) (eps_0 : ℝ) (heps : 0 < eps_0)
    (s : M.S) (a : M.A) (s' : M.S) :
    2 * Real.exp (-((N : ℝ) * eps_0) ^ 2 /
      (2 * ((N : ℝ) * (M.P s a s' - (M.P s a s') ^ 2)) +
        2 * ((N : ℝ) * eps_0) / 3)) ≤
    2 * Real.exp (-(↑N * bernsteinCoeff eps_0)) := by
  -- Strategy: show the exponent with actual variance ≤ exponent with 1/4,
  -- then exp(smaller) ≤ exp(larger) ≤ bound.
  -- We'll prove a*exp(x) ≤ a*exp(y) via a*exp(x)/a*exp(y) argument.
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hp_le : M.P s a s' - (M.P s a s') ^ 2 ≤ 1 / 4 := by
    nlinarith [M.P_nonneg s a s', M.P_le_one s a s',
               sq_nonneg (M.P s a s' - 1/2)]
  have h_denom_pos : 0 < 2 * ((N : ℝ) * (M.P s a s' -
      (M.P s a s') ^ 2)) + 2 * ((N : ℝ) * eps_0) / 3 := by
    have : 0 ≤ M.P s a s' - (M.P s a s') ^ 2 := by
      nlinarith [M.P_nonneg s a s', M.P_le_one s a s']
    nlinarith
  have h_unif_pos : (0 : ℝ) < 1 / 2 + 2 * eps_0 / 3 := by linarith
  -- denom_actual ≤ N*(1/2 + 2ε₀/3) = denom_uniform
  have h_denom_le : 2 * (↑N * (M.P s a s' - (M.P s a s') ^ 2)) +
      2 * (↑N * eps_0) / 3 ≤ ↑N * (1 / 2 + 2 * eps_0 / 3) := by
    nlinarith
  -- Key: -(N*ε₀)²/denom_actual ≤ -(N*ε₀)²/denom_uniform
  -- because denom_actual ≤ denom_uniform and the numerator is negative
  -- And -(N*ε₀)²/denom_uniform = -N*c
  -- So exp(-(N*ε₀)²/denom_actual) ≤ exp(-N*c)
  -- Multiply through by denom_actual*denom_uniform to avoid division:
  -- Need: exp(actual_exponent) ≤ exp(uniform_exponent)
  -- actual_exponent ≤ uniform_exponent because:
  --   actual: -(N*ε₀)² / D_actual,  uniform: -N*c = -(N*ε₀)² / D_uniform
  --   D_actual ≤ D_uniform, so actual ≤ uniform (both negative, larger denom → less negative)
  -- Use exp_div_exp or direct multiplication
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
  apply Real.exp_le_exp.mpr
  -- Goal: -(↑N * eps_0) ^ 2 / denom_actual ≤ -(↑N * bernsteinCoeff eps_0)
  -- Rewrite -(↑N * c) as -(N*ε₀)² / (N*(1/2+2ε₀/3))
  have h_uniform_eq : -(↑N * bernsteinCoeff eps_0) =
      -(↑N * eps_0) ^ 2 / (↑N * (1 / 2 + 2 * eps_0 / 3)) := by
    unfold bernsteinCoeff; field_simp
  rw [h_uniform_eq]
  -- Now: -(a²)/D_act ≤ -(a²)/D_unif, where D_act ≤ D_unif
  -- Since a² > 0, -(a²) < 0, and D_act, D_unif > 0:
  -- (-a²)/D_act ≤ (-a²)/D_unif ↔ D_act ≤ D_unif (divide negative by larger → more negative)
  -- (-a²)/D_act ≤ (-a²)/D_unif when D_act ≤ D_unif and -a² ≤ 0
  -- Proof: multiply both sides by D_act * D_unif > 0
  have h_num_nonpos : -(↑N * eps_0) ^ 2 ≤ 0 := by
    nlinarith [sq_nonneg (↑N * eps_0)]
  have h_unif_denom_pos : 0 < ↑N * (1 / 2 + 2 * eps_0 / 3) := by
    positivity
  rw [div_le_div_iff₀ h_denom_pos h_unif_denom_pos]
  exact mul_le_mul_of_nonpos_left h_denom_le h_num_nonpos

/-- The Bernstein failure sum is bounded by `K·2·exp(-N·c)`. -/
lemma bernstein_sum_le_uniform
    {N : ℕ} (hN : 0 < N) (eps_0 : ℝ) (heps : 0 < eps_0) :
    ∑ p : M.S × M.A × M.S,
      2 * Real.exp (-((N : ℝ) * eps_0) ^ 2 /
        (2 * ((N : ℝ) * (M.P p.1 p.2.1 p.2.2 -
          (M.P p.1 p.2.1 p.2.2) ^ 2)) +
          2 * ((N : ℝ) * eps_0) / 3)) ≤
    ↑(Fintype.card (M.S × M.A × M.S)) *
      (2 * Real.exp (-(↑N * bernsteinCoeff eps_0))) := by
  calc ∑ p : M.S × M.A × M.S, _ ≤
      ∑ _ : M.S × M.A × M.S,
        2 * Real.exp (-(↑N * bernsteinCoeff eps_0)) := by
        apply Finset.sum_le_sum; intro ⟨s, a, s'⟩ _
        exact M.bernstein_entry_uniform_bound hN eps_0 heps s a s'
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **Bernstein log-rate failure bound.**
    When `N ≥ log(2K/δ) / c` where `c = bernsteinCoeff ε₀`,
    the Bernstein failure sum is at most `δ`.

    This gives `N₀ = O(log(1/δ))`, improving on the polynomial rate
    from `hoeffding_failure_eventually_small`. -/
lemma bernstein_failure_le_delta
    {N : ℕ} (hN : 0 < N) (eps_0 : ℝ) (heps : 0 < eps_0)
    (δ : ℝ) (hδ : 0 < δ)
    (hNge : Real.log (2 * ↑(Fintype.card (M.S × M.A × M.S)) / δ) /
      bernsteinCoeff eps_0 ≤ ↑N) :
    ∑ p : M.S × M.A × M.S,
      2 * Real.exp (-((N : ℝ) * eps_0) ^ 2 /
        (2 * ((N : ℝ) * (M.P p.1 p.2.1 p.2.2 -
          (M.P p.1 p.2.1 p.2.2) ^ 2)) +
          2 * ((N : ℝ) * eps_0) / 3)) ≤ δ := by
  have hK_pos : (0 : ℝ) < Fintype.card (M.S × M.A × M.S) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hc_pos : 0 < bernsteinCoeff eps_0 := bernsteinCoeff_pos heps
  -- Step 1: bound the sum by K·2·exp(-Nc)
  have h_sum := M.bernstein_sum_le_uniform hN eps_0 heps
  -- Step 2: from hNge, N·c ≥ log(2K/δ)
  have h_Nc : Real.log (2 * ↑(Fintype.card (M.S × M.A × M.S)) / δ) ≤
      ↑N * bernsteinCoeff eps_0 := by
    rwa [div_le_iff₀ hc_pos] at hNge
  -- Step 3: exp(-Nc) ≤ exp(-log(2K/δ)) = δ/(2K)
  have h2K_pos : 0 < 2 * ↑(Fintype.card (M.S × M.A × M.S)) / δ := by positivity
  have h_exp_le : Real.exp (-(↑N * bernsteinCoeff eps_0)) ≤
      δ / (2 * ↑(Fintype.card (M.S × M.A × M.S))) := by
    calc Real.exp (-(↑N * bernsteinCoeff eps_0))
        ≤ Real.exp (-(Real.log (2 * ↑(Fintype.card (M.S × M.A × M.S)) / δ))) :=
          Real.exp_le_exp_of_le (neg_le_neg h_Nc)
      _ = (Real.exp (Real.log (2 * ↑(Fintype.card (M.S × M.A × M.S)) / δ)))⁻¹ :=
          Real.exp_neg _
      _ = (2 * ↑(Fintype.card (M.S × M.A × M.S)) / δ)⁻¹ := by
          rw [Real.exp_log h2K_pos]
      _ = δ / (2 * ↑(Fintype.card (M.S × M.A × M.S))) := by rw [inv_div]
  -- Step 4: K·2·exp(-Nc) ≤ K·2·δ/(2K) = δ
  calc ∑ p : M.S × M.A × M.S, _
      ≤ ↑(Fintype.card (M.S × M.A × M.S)) *
        (2 * Real.exp (-(↑N * bernsteinCoeff eps_0))) := h_sum
    _ ≤ ↑(Fintype.card (M.S × M.A × M.S)) *
        (2 * (δ / (2 * ↑(Fintype.card (M.S × M.A × M.S))))) := by gcongr
    _ = δ := by field_simp

/-- **Minimax PAC with Bernstein concentration (composed).**

    End-to-end composition of:
    1. `generative_model_pac_bernstein` — transition concentration w.h.p.
    2. `minimax_from_empirical_fixed_points_good_event` — deterministic value gap

    When `N ≥ log(2|S×A×S|/δ) / bernsteinCoeff(ε_T)`, the empirical greedy
    policy satisfies:
      V_ref(s) - V̂(s) ≤ 2γ·R_max·|S|·ε_T / (1-γ)²
    with probability ≥ 1-δ.

    This theorem directly exposes the per-entry transition tolerance ε_T
    and the corresponding minimax rate, making the composition between
    concentration and deterministic reduction explicit. The `conditional`
    minimax_sample_complexity theorem is now discharged for all cases
    where Bernstein concentration provides the transition-error bound. -/
theorem minimax_pac_bernstein_composed
    {N : ℕ} (hN : 0 < N)
    (ε_T : ℝ) (hε_T : 0 < ε_T) (δ : ℝ) (hδ : 0 < δ)
    (hNge : Real.log (2 * ↑(Fintype.card (M.S × M.A × M.S)) / δ) /
      bernsteinCoeff ε_T ≤ ↑N)
    (π_ref : M.StochasticPolicy) (V_ref : M.StateValueFn)
    (hV : M.isValueOf V_ref π_ref) :
    (M.generativeModelMeasure N).real
      {ω | ∀ s, V_ref s - M.empiricalGreedyValue hN ω s ≤
        2 * M.γ * M.R_max * (↑(Fintype.card M.S) * ε_T) /
          (1 - M.γ) ^ 2} ≥ 1 - δ := by
  -- Compose: Bernstein capstone gives value gap w.h.p. via Bernstein failure
  have h_capstone :=
    M.minimax_value_gap_high_probability_from_empirical_fixed_points_bernstein
      hN ε_T hε_T
      (fun _ => π_ref) (fun _ => V_ref) (fun _ => hV)
  have h_fail := M.bernstein_failure_le_delta hN ε_T hε_T δ hδ hNge
  linarith

/-- **PAC sample complexity with Bernstein log-rate.**
    Given ε > 0, δ > 0, γ > 0, and any reference policy, when
    `N ≥ log(2|S|²|A|/δ) / bernsteinCoeff(pac_eps_0 ε)`,
    the empirical greedy policy is ε-optimal with probability ≥ 1-δ.

    The sample count scales as `O(log(1/δ))` — the near-minimax rate.
    This improves on `pac_rl_generative_model` which uses polynomial rate. -/
theorem pac_rl_generative_model_bernstein
    {N : ℕ} (hN : 0 < N)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hγ : 0 < M.γ)
    (hNge : Real.log (2 * ↑(Fintype.card (M.S × M.A × M.S)) / δ) /
      bernsteinCoeff (M.pac_eps_0 ε) ≤ ↑N)
    (π_ref : M.StochasticPolicy) (V_ref : M.StateValueFn)
    (hV : M.isValueOf V_ref π_ref) :
    (M.generativeModelMeasure N).real
      {ω | ∀ s, V_ref s - M.empiricalGreedyValue hN ω s ≤ ε} ≥
      1 - δ := by
  have hc_pos := M.pac_eps_0_pos hε hγ
  -- Apply the Bernstein capstone
  have h_capstone :=
    M.minimax_value_gap_high_probability_from_empirical_fixed_points_bernstein
      hN (M.pac_eps_0 ε) hc_pos
      (fun _ => π_ref) (fun _ => V_ref) (fun _ => hV)
  -- Rewrite the value-gap bound to ε
  have h_sets_eq :
      {ω : M.SampleIndex N → M.S |
        ∀ s, V_ref s - M.empiricalGreedyValue hN ω s ≤
          2 * M.γ * M.R_max * (↑(Fintype.card M.S) * M.pac_eps_0 ε) /
            (1 - M.γ) ^ 2} =
      {ω | ∀ s, V_ref s - M.empiricalGreedyValue hN ω s ≤ ε} := by
    ext ω
    simp only [Set.mem_setOf_eq, M.pac_value_gap_eq hε hγ]
  rw [h_sets_eq] at h_capstone
  -- The Bernstein failure sum ≤ δ
  have h_fail := M.bernstein_failure_le_delta hN
    (M.pac_eps_0 ε) hc_pos δ hδ hNge
  linarith

/-- **PAC theorem for generative-model RL.**
    Given any reference policy `π_ref` with value `V_ref` in the true MDP
    (e.g. the optimal policy), there exists a sample count `N₀` such that
    for `N ≥ N₀` i.i.d. samples per (s,a) pair from the generative model,
    the plug-in empirical greedy policy satisfies
    `V_ref(s) - V̂(s) ≤ ε` for all states with probability ≥ `1 - δ`.

    Uses Bernstein concentration internally, achieving `N₀ = O(log(1/δ))`.
    Delegates to `pac_rl_generative_model_bernstein_existential`.

    Requires `γ > 0`; the `γ = 0` case is trivial (value = immediate reward). -/
theorem pac_rl_generative_model
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hγ : 0 < M.γ)
    (π_ref : M.StochasticPolicy) (V_ref : M.StateValueFn)
    (hV : M.isValueOf V_ref π_ref) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ (N : ℕ) (hN : 0 < N), N₀ ≤ N →
      (M.generativeModelMeasure N).real
        {ω | ∀ s, V_ref s - M.empiricalGreedyValue hN ω s ≤ ε} ≥
        1 - δ := by
  -- Use Bernstein concentration (log-rate) instead of Hoeffding (polynomial rate)
  set c := bernsteinCoeff (M.pac_eps_0 ε) with hc_def
  have hc_pos : 0 < c := bernsteinCoeff_pos (M.pac_eps_0_pos hε hγ)
  set L := Real.log (2 * ↑(Fintype.card (M.S × M.A × M.S)) / δ) with hL_def
  set N₀ := max 1 ⌈L / c⌉₊ with hN₀_def
  refine ⟨N₀, by omega, fun N hN hNge => ?_⟩
  have hNge' : L / c ≤ ↑N := by
    calc L / c ≤ ↑⌈L / c⌉₊ := Nat.le_ceil _
      _ ≤ ↑N₀ := Nat.cast_le.mpr (le_max_right _ _)
      _ ≤ ↑N := Nat.cast_le.mpr hNge
  exact M.pac_rl_generative_model_bernstein hN ε δ hε hδ hγ hNge' π_ref V_ref hV

/-- **PAC theorem for generative-model RL (optimal-value form).**
    For any finite discounted MDP with `γ > 0`, there exists an optimal
    value function `V*` dominating all policies, and a sample count `N₀`
    with `O(log(1/δ))` scaling (via Bernstein concentration),
    such that with `N ≥ N₀` i.i.d. samples per (s,a) pair from the
    generative model, the plug-in empirical greedy policy satisfies
    `V*(s) - V̂(s) ≤ ε` for all states with probability at least `1 - δ`.

    Requires `γ > 0`; the `γ = 0` case is trivial. -/
theorem pac_rl_generative_model_optimal
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hγ : 0 < M.γ) :
    ∃ (V_star : M.StateValueFn),
      -- V_star dominates all policy values (it is the optimal value function)
      (∀ (π : M.StochasticPolicy) (V_pi : M.StateValueFn),
        M.isValueOf V_pi π → ∀ s, V_pi s ≤ V_star s) ∧
      -- Sample complexity: N ≥ N₀ suffices for PAC guarantee
      ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ (N : ℕ) (hN : 0 < N), N₀ ≤ N →
        (M.generativeModelMeasure N).real
          {ω | ∀ s, V_star s - M.empiricalGreedyValue hN ω s ≤ ε} ≥
          1 - δ := by
  -- Construct the optimal Q-function via Banach fixed point
  obtain ⟨Q_star, hQ_star⟩ := M.exists_bellmanOptimalQ_fixedPoint
  -- Extract optimal policy and value from Q*
  have h_opt := M.optimal_policy_exists Q_star hQ_star
  set V_star : M.StateValueFn :=
    fun s => Finset.univ.sup' Finset.univ_nonempty (Q_star s)
  set π_star := M.greedyStochasticPolicy Q_star
  refine ⟨V_star, h_opt.2, ?_⟩
  exact M.pac_rl_generative_model ε δ hε hδ hγ π_star V_star h_opt.1

/-! ### Existential Bernstein PAC with Log-Rate

The following provides alternative forms of the Bernstein PAC result with
`O(log(1/δ))` scaling (note: `pac_rl_generative_model` now also uses Bernstein).
This removes the free `N` hypothesis from `pac_rl_generative_model_bernstein`,
making the sample-complexity statement self-contained. -/

/-- **Existential PAC sample complexity with Bernstein log-rate.**

    Given any reference policy `π_ref` with value `V_ref` in the true MDP,
    there exists a sample count `N₀` such that for `N ≥ N₀` i.i.d. samples
    per (s,a) pair from the generative model, the plug-in empirical greedy
    policy satisfies `V_ref(s) - V̂(s) ≤ ε` for all states with
    probability ≥ `1 - δ`.

    Unlike `pac_rl_generative_model` which uses Hoeffding (polynomial in 1/δ),
    this version uses Bernstein concentration and achieves `N₀ = O(log(1/δ))`.
    The `hNge` hypothesis of `pac_rl_generative_model_bernstein` is
    discharged by choosing `N₀ = max 1 ⌈log(2K/δ)/c⌉₊` where
    `c = bernsteinCoeff(pac_eps_0 ε)`.

    Requires `γ > 0`; the `γ = 0` case is trivial (value = immediate reward). -/
theorem pac_rl_generative_model_bernstein_existential
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hγ : 0 < M.γ)
    (π_ref : M.StochasticPolicy) (V_ref : M.StateValueFn)
    (hV : M.isValueOf V_ref π_ref) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ (N : ℕ) (hN : 0 < N), N₀ ≤ N →
      (M.generativeModelMeasure N).real
        {ω | ∀ s, V_ref s - M.empiricalGreedyValue hN ω s ≤ ε} ≥
        1 - δ := by
  -- The Bernstein coefficient c > 0
  set c := bernsteinCoeff (M.pac_eps_0 ε) with hc_def
  have hc_pos : 0 < c := bernsteinCoeff_pos (M.pac_eps_0_pos hε hγ)
  -- The log term (may or may not be positive)
  set L := Real.log (2 * ↑(Fintype.card (M.S × M.A × M.S)) / δ) with hL_def
  -- Choose N₀ large enough that L/c ≤ N₀
  set N₀ := max 1 ⌈L / c⌉₊ with hN₀_def
  refine ⟨N₀, by omega, fun N hN hNge => ?_⟩
  -- Show the hNge hypothesis of pac_rl_generative_model_bernstein holds
  have hNge' : L / c ≤ ↑N := by
    calc L / c ≤ ↑⌈L / c⌉₊ := Nat.le_ceil _
      _ ≤ ↑N₀ := Nat.cast_le.mpr (le_max_right _ _)
      _ ≤ ↑N := Nat.cast_le.mpr hNge
  exact M.pac_rl_generative_model_bernstein hN ε δ hε hδ hγ hNge' π_ref V_ref hV

/-- **Existential PAC with Bernstein log-rate (optimal-value form).**

    For any finite discounted MDP with `γ > 0`, there exists an optimal
    value function `V*` dominating all policies, and a sample count `N₀`
    with `O(log(1/δ))` scaling, such that the empirical greedy policy
    is ε-optimal with probability ≥ 1 - δ for `N ≥ N₀`. -/
theorem pac_rl_generative_model_bernstein_optimal
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hγ : 0 < M.γ) :
    ∃ (V_star : M.StateValueFn),
      (∀ (π : M.StochasticPolicy) (V_pi : M.StateValueFn),
        M.isValueOf V_pi π → ∀ s, V_pi s ≤ V_star s) ∧
      ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ (N : ℕ) (hN : 0 < N), N₀ ≤ N →
        (M.generativeModelMeasure N).real
          {ω | ∀ s, V_star s - M.empiricalGreedyValue hN ω s ≤ ε} ≥
          1 - δ := by
  obtain ⟨Q_star, hQ_star⟩ := M.exists_bellmanOptimalQ_fixedPoint
  have h_opt := M.optimal_policy_exists Q_star hQ_star
  set V_star : M.StateValueFn :=
    fun s => Finset.univ.sup' Finset.univ_nonempty (Q_star s)
  set π_star := M.greedyStochasticPolicy Q_star
  exact ⟨V_star, h_opt.2,
    M.pac_rl_generative_model_bernstein_existential ε δ hε hδ hγ
      π_star V_star h_opt.1⟩

end FiniteMDP

end
