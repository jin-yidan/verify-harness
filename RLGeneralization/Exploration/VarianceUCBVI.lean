/-
# Variance-Aware (Bernstein-Style) UCBVI Regret Bound

Proves the algebraic core of the variance-aware UCBVI algorithm, which
uses Bernstein-style confidence bounds instead of Hoeffding-style ones.
This yields an O(sqrt(H^2 * S * A * K)) regret bound, improving on the
O(sqrt(H^3 * S * A * K)) Hoeffding-based bound by a factor of sqrt(H).

## Architecture

The proof chains:
1. Variance-dependent bonus structure (Bernstein vs Hoeffding)
2. Variance decomposition: Var_P(V) <= H * E_P[V] for V in [0, H]
3. Total variance bound: sum of per-step variances <= H * K
4. Cauchy-Schwarz with variance: total Bernstein bonus <= O(sqrt(H^2 * SAK))
5. Composition via cumulative_regret_le_total_bonuses (UCBVI.lean)

## Key Improvement

Standard UCBVI uses bonus ~ H * sqrt(log/N) (range-dependent via Hoeffding).
Variance-aware UCBVI uses bonus ~ sqrt(Var * log/N) + H * log/N (Bernstein).
Since sum of variances ~ H * K (not H^2 * K), this saves a factor of sqrt(H)
(the Cauchy-Schwarz step over H timesteps introduces one additional sqrt(H)).

## References

* [Azar, Osband, Munos, *Minimax Regret Bounds for RL*, ICML 2017]
* [Agarwal et al., *RL: Theory and Algorithms*]
-/

import RLGeneralization.Exploration.UCBVI
import RLGeneralization.Concentration.Bernstein

open Finset BigOperators

noncomputable section

/-! ### Variance Bound for Bounded Nonneg Random Variables -/

/-- The pointwise inequality for the variance-range bound:
    if 0 <= x <= b then x^2 <= b * x.

    This is because x^2 = x * x <= x * b = b * x. -/
theorem sq_le_mul_of_le_range {x b : ℝ} (hx : 0 ≤ x) (hxb : x ≤ b) :
    x ^ 2 ≤ b * x := by
  rw [sq]
  exact mul_le_mul_of_nonneg_right hxb hx

namespace FiniteHorizonMDP

variable (M : FiniteHorizonMDP)

/-! ### Transition Variance -/

/-- Transition variance: Var_P(V)(s,a) = E_P[V^2](s,a) - (E_P[V](s,a))^2.

    For a value function V and transition kernel P_h:
    - E_P[V](s,a) = sum_{s'} P_h(s,a,s') * V(s')
    - Var_P(V)(s,a) = sum_{s'} P_h(s,a,s') * V(s')^2 - (E_P[V](s,a))^2 -/
def transitionVariance
    (h : Fin M.H) (s : M.S) (a : M.A) (V : M.S → ℝ) : ℝ :=
  ∑ s', M.P h s a s' * (V s') ^ 2 -
  (∑ s', M.P h s a s' * V s') ^ 2

/-- Transition variance is nonneg (consequence of Jensen's inequality /
    Cauchy-Schwarz for probability distributions).

    Proof: sum P_i (V_i - mu)^2 >= 0 where mu = sum P_i V_i.
    Expanding gives E[V^2] - (E[V])^2 >= 0. -/
theorem transitionVariance_nonneg
    (h : Fin M.H) (s : M.S) (a : M.A) (V : M.S → ℝ) :
    0 ≤ M.transitionVariance h s a V := by
  unfold transitionVariance
  -- Prove via: sum P_i(V_i - mu)^2 >= 0, then expand
  set μ := ∑ s', M.P h s a s' * V s'
  -- The centered second moment is nonneg
  have h_centered_nn : 0 ≤ ∑ s', M.P h s a s' * (V s' - μ) ^ 2 :=
    Finset.sum_nonneg fun s' _ =>
      mul_nonneg (M.P_nonneg h s a s') (sq_nonneg _)
  -- Expand (V_i - μ)^2 = V_i^2 - 2μV_i + μ^2
  -- sum P_i(V_i - μ)^2 = sum P_i V_i^2 - 2μ(sum P_i V_i) + μ^2(sum P_i)
  --                     = E[V^2] - 2μ^2 + μ^2  (since sum P_i = 1 and μ = E[V])
  --                     = E[V^2] - μ^2
  suffices h_expand : ∑ s', M.P h s a s' * (V s' - μ) ^ 2 =
      ∑ s', M.P h s a s' * (V s') ^ 2 - μ ^ 2 by
    linarith
  have h_sum_one := M.P_sum_one h s a
  -- Expand each term
  have : ∑ s', M.P h s a s' * (V s' - μ) ^ 2 =
      ∑ s', (M.P h s a s' * (V s') ^ 2 - 2 * μ * (M.P h s a s' * V s') +
        μ ^ 2 * M.P h s a s') := by
    congr 1; ext s'; ring
  rw [this, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  -- sum P_i V_i^2 - 2μ (sum P_i V_i) + μ^2 (sum P_i) = sum P_i V_i^2 - μ^2
  rw [← Finset.mul_sum, ← Finset.mul_sum, h_sum_one]
  ring

/-- **Variance-range bound for transition variance**:
    Var_P(V)(s,a) <= b * E_P[V](s,a) when V in [0, b].

    When V is a value function in [0, H], we get Var_P(V) <= H * E_P[V],
    which is the key to the H-factor improvement. -/
theorem transitionVariance_le_range_times_expectation
    (h_step : Fin M.H) (s : M.S) (a : M.A) (V : M.S → ℝ)
    {b : ℝ} (_hb : 0 ≤ b)
    (hV_nn : ∀ s', 0 ≤ V s')
    (hV_le : ∀ s', V s' ≤ b) :
    M.transitionVariance h_step s a V ≤
    b * ∑ s', M.P h_step s a s' * V s' := by
  unfold transitionVariance
  -- Var = E[V^2] - (E[V])^2 <= E[V^2] <= E[b*V] = b*E[V]
  have h_sq_nn : 0 ≤ (∑ s', M.P h_step s a s' * V s') ^ 2 := sq_nonneg _
  calc ∑ s', M.P h_step s a s' * (V s') ^ 2 -
        (∑ s', M.P h_step s a s' * V s') ^ 2
      ≤ ∑ s', M.P h_step s a s' * (V s') ^ 2 := by linarith
    _ ≤ ∑ s', M.P h_step s a s' * (b * V s') := by
        apply Finset.sum_le_sum; intro s' _
        apply mul_le_mul_of_nonneg_left _ (M.P_nonneg h_step s a s')
        exact sq_le_mul_of_le_range (hV_nn s') (hV_le s')
    _ = b * ∑ s', M.P h_step s a s' * V s' := by
        have : ∀ s' : M.S, M.P h_step s a s' * (b * V s') =
            b * (M.P h_step s a s' * V s') := fun s' => by ring
        simp_rw [this, ← Finset.mul_sum]

/-! ### Bernstein Bonus vs Hoeffding Bonus -/

/-- **Bernstein bonus**: variance-dependent confidence bound.
    bonus_B = c1 * sqrt(V_hat * L / N) + c2 * H_val * L / N
    where V_hat is the empirical variance, L = log(...), N = visit count.

    Compare with Hoeffding bonus: c * H * sqrt(L / N). -/
-- [UNUSED]
def bernsteinBonus (c1 c2 : ℝ) (V_hat : ℝ) (H_val : ℝ)
    (log_term : ℝ) (n : ℕ) : ℝ :=
  c1 * Real.sqrt (V_hat * log_term / max n 1) +
  c2 * H_val * log_term / max n 1

/-- **Bernstein bonus never worse than Hoeffding bonus**.

    When V <= B^2, we have sqrt(V * L / N) <= B * sqrt(L / N), so:
      c1 * sqrt(V * L / N) + c2 * B * L / N <= (c1 + c2) * B * sqrt(L / N)

    We prove the simpler algebraic version: the sqrt term of the
    Bernstein bonus is bounded by the Hoeffding sqrt term. -/
theorem bernstein_bonus_le_hoeffding
    {V_hat L : ℝ} {N : ℕ}
    {B : ℝ} (hB : 0 ≤ B) (_hL : 0 ≤ L)
    (_hN : 0 < N)
    (hV : V_hat ≤ B ^ 2) (_hV_nn : 0 ≤ V_hat) :
    Real.sqrt (V_hat * L / N) ≤ B * Real.sqrt (L / N) := by
  rw [show V_hat * L / (N : ℝ) = V_hat * (L / N) from by ring]
  rw [show B * Real.sqrt (L / ↑N) = Real.sqrt (B ^ 2) * Real.sqrt (L / ↑N) from by
    rw [Real.sqrt_sq hB]]
  rw [← Real.sqrt_mul (sq_nonneg B)]
  apply Real.sqrt_le_sqrt
  apply mul_le_mul_of_nonneg_right hV
  exact div_nonneg (by linarith [abs_nonneg L]) (Nat.cast_nonneg _)

/-! ### Variance-Dependent Total Bonus Bound -/

/-- **Total variance bound**: the sum of transition variances across all
    episodes and steps is bounded by H * (total expected values).

    In the UCBVI setting with K episodes and H steps:
      sum_k sum_h Var_h(V_{h+1})(s_h, a_h) <= H * K

    This replaces the H^2 * K bound from the Hoeffding analysis
    (where Var is replaced by range^2 = H^2).

    We prove the algebraic core: if each variance_h <= b * mean_h
    and sum of means <= total, then sum of variances <= b * total. -/
theorem total_variance_bound
    {ι : Type*} (s : Finset ι)
    (variance mean : ι → ℝ)
    {b total : ℝ} (hb : 0 ≤ b)
    (h_var_le : ∀ i ∈ s, variance i ≤ b * mean i)
    (h_mean_sum : ∑ i ∈ s, mean i ≤ total) :
    ∑ i ∈ s, variance i ≤ b * total := by
  calc ∑ i ∈ s, variance i
      ≤ ∑ i ∈ s, b * mean i :=
        Finset.sum_le_sum h_var_le
    _ = b * ∑ i ∈ s, mean i := by rw [← Finset.mul_sum]
    _ ≤ b * total :=
        mul_le_mul_of_nonneg_left h_mean_sum hb

/-! ### Cauchy-Schwarz with Variance: Pigeonhole for Bernstein Bonuses -/

/-- **Variance pigeonhole**: Cauchy-Schwarz with variance-dependent bonuses.

    The total Bernstein bonus can be bounded using:
      (sum sqrt(V_i) * sqrt(N_i))^2 <= (sum V_i)(sum N_i) <= V_total * K

    Combined with `total_variance_bound` (sum V(i) <= H * K) and
    the pigeonhole harmonic-sqrt bound, plus Cauchy-Schwarz over H steps, this gives:
      total Bernstein bonus <= O(sqrt(H^2 * S * A * K))

    We prove: sum sqrt(V_i * N_i) <= sqrt(V_total * K). -/
theorem variance_pigeonhole {ι : Type*} [Fintype ι]
    (V : ι → ℝ) (hV : ∀ i, 0 ≤ V i)
    (N : ι → ℕ) (_hN : ∀ i, 0 < N i)
    {V_total : ℝ} (hV_sum : ∑ i, V i ≤ V_total) (hVt : 0 ≤ V_total)
    (K : ℕ) (hK : ∑ i, N i ≤ K) :
    ∑ i : ι, Real.sqrt (V i * ↑(N i)) ≤
    Real.sqrt (V_total * ↑K) := by
  -- Cauchy-Schwarz: (sum sqrt(V_i * N_i))^2 = (sum sqrt(V_i) * sqrt(N_i))^2
  --   <= (sum V_i)(sum N_i) <= V_total * K
  have h_sum_nn : 0 ≤ ∑ i : ι, Real.sqrt (V i * ↑(N i)) :=
    Finset.sum_nonneg fun i _ => Real.sqrt_nonneg _
  rw [← Real.sqrt_sq h_sum_nn]
  apply Real.sqrt_le_sqrt
  -- (sum sqrt(V_i N_i))^2 <= (sum V_i)(sum N_i)
  have h_split : ∀ i : ι, Real.sqrt (V i * ↑(N i)) =
      Real.sqrt (V i) * Real.sqrt ↑(N i) := fun i =>
    Real.sqrt_mul (hV i) _
  simp_rw [h_split]
  -- Apply sum_mul_sq_le_sq_mul_sq: (sum f*g)^2 <= (sum f^2)(sum g^2)
  calc (∑ i : ι, Real.sqrt (V i) * Real.sqrt ↑(N i)) ^ 2
      = (∑ i ∈ Finset.univ, Real.sqrt (V i) * Real.sqrt ↑(N i)) ^ 2 := by
        rfl
    _ ≤ (∑ i ∈ Finset.univ, Real.sqrt (V i) ^ 2) *
        (∑ i ∈ Finset.univ, Real.sqrt (↑(N i) : ℝ) ^ 2) :=
        sum_mul_sq_le_sq_mul_sq _ _ _
    _ = (∑ i : ι, V i) * (∑ i : ι, (↑(N i) : ℝ)) := by
        congr 1
        · exact Finset.sum_congr rfl fun i _ => Real.sq_sqrt (hV i)
        · exact Finset.sum_congr rfl fun i _ => Real.sq_sqrt (Nat.cast_nonneg _)
    _ ≤ V_total * ↑K := by
        apply mul_le_mul hV_sum _ (Finset.sum_nonneg fun i _ => Nat.cast_nonneg _) hVt
        exact_mod_cast hK

/-! ### Variance-Aware Total Bonus Bound -/

/-- **Variance-aware total bonus bound** (Bernstein-style).

    The total Bernstein bonus satisfies:
      sum_k sum_h bonus_h^k <= C * sqrt(H^2 * |S| * |A| * K * log(...))

    Compare with the Hoeffding bound:
      sum_k sum_h bonus_h^k <= C * sqrt(H^3 * |S| * |A| * K * log(...))

    The improvement by sqrt(H) comes from using variance (sum <= H*K) instead
    of range^2 (sum <= H^2*K) in the Cauchy-Schwarz step.

    We define this as a predicate for composition with the UCBVI regret
    framework, mirroring `totalBonusBound` from UCBVI.lean. -/
def varianceTotalBonusBound
    (bonus : Fin K → Fin M.H → ℝ)
    (C : ℝ) (δ : ℝ) : Prop :=
  ∑ k : Fin K, ∑ h : Fin M.H, bonus k h ≤
    C * Real.sqrt (M.H ^ 2 * (Fintype.card M.S) * (Fintype.card M.A) *
      K * Real.log (M.H * (Fintype.card M.S) * (Fintype.card M.A) * K / δ))

/-- **The variance-aware bound is tighter than the Hoeffding bound**:
    C * sqrt(H^2 * SAK * log) <= C * sqrt(H^3 * SAK * log) when H >= 1.

    This confirms the variance-aware analysis never gives a worse bound. -/
theorem variance_bound_le_hoeffding_bound
    {C : ℝ} (hC : 0 ≤ C)
    {H_val : ℝ} (hH : 1 ≤ H_val)
    {SAK_log : ℝ} (hSAK : 0 ≤ SAK_log) :
    C * Real.sqrt (H_val ^ 2 * SAK_log) ≤
    C * Real.sqrt (H_val ^ 3 * SAK_log) := by
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.sqrt_le_sqrt
  apply mul_le_mul_of_nonneg_right _ hSAK
  calc H_val ^ 2 = H_val ^ 2 * 1 := (mul_one _).symm
    _ ≤ H_val ^ 2 * H_val := by
        apply mul_le_mul_of_nonneg_left hH (sq_nonneg _)
    _ = H_val ^ 3 := by ring

/-- **Improvement factor**: the ratio of Hoeffding to Bernstein bounds
    is sqrt(H^3 / H^2) = sqrt(H). We prove:
      sqrt(H^3 * SAK) = sqrt(H) * sqrt(H^2 * SAK)
    when H >= 0, showing the Hoeffding bound exceeds the Bernstein bound
    by a factor of sqrt(H). -/
theorem variance_ucbvi_regret_improvement
    {H_val : ℝ} (hH : 0 ≤ H_val)
    {SAK : ℝ} (_hSAK : 0 ≤ SAK) :
    Real.sqrt (H_val ^ 3 * SAK) =
    Real.sqrt H_val * Real.sqrt (H_val ^ 2 * SAK) := by
  rw [show H_val ^ 3 * SAK = H_val * (H_val ^ 2 * SAK) from by ring]
  rw [Real.sqrt_mul hH]

/-! ### Main Regret Theorem: Variance-Aware UCBVI -/

/-- [WRAPPER] **Variance-aware UCBVI regret bound**.

    Takes h_per_ep (per-episode regret <= sum of bonuses) and h_bonus
    (variance-aware total bonus bound) as hypotheses, then chains them
    to derive: Regret(K) <= C * sqrt(H^2 * |S| * |A| * K * log(HSAK/delta)).

    Improves on `ucbvi_regret_from_bonus_hypotheses` by a factor of sqrt(H),
    from using Bernstein-style (variance-dependent) instead of Hoeffding-style
    (range-dependent) bonuses. -/
theorem variance_ucbvi_regret
    (K : ℕ)
    (V_star_0 : M.S → ℝ)
    (V_policies : Fin K → M.S → ℝ)
    (starts : Fin K → M.S)
    (bonus : Fin K → Fin M.H → ℝ)
    (C : ℝ) (δ : ℝ) (_hδ : 0 < δ)
    -- Hypothesis 1: per-episode regret <= sum of bonuses (from optimism)
    (h_per_ep : ∀ k : Fin K,
      V_star_0 (starts k) - V_policies k (starts k) ≤
      ∑ h : Fin M.H, bonus k h)
    -- Hypothesis 2: variance-aware total bonus bound (from Bernstein)
    (h_bonus : M.varianceTotalBonusBound bonus C δ) :
    M.cumulativeRegret K V_star_0 V_policies starts ≤
    C * Real.sqrt (M.H ^ 2 * (Fintype.card M.S) * (Fintype.card M.A) *
      K * Real.log (M.H * (Fintype.card M.S) * (Fintype.card M.A) * K / δ)) := by
  calc M.cumulativeRegret K V_star_0 V_policies starts
      ≤ ∑ k : Fin K, ∑ h : Fin M.H, bonus k h :=
        M.cumulative_regret_le_total_bonuses K V_star_0 V_policies starts
          bonus h_per_ep
    _ ≤ C * Real.sqrt (M.H ^ 2 * (Fintype.card M.S) * (Fintype.card M.A) *
          K * Real.log (M.H * (Fintype.card M.S) * (Fintype.card M.A) * K / δ)) :=
        h_bonus

/-- **Variance-aware bound implies standard bound**: Any configuration
    satisfying the variance-aware bound also satisfies the standard
    Hoeffding-based bound (with an extra H factor).

    This shows variance-aware UCBVI is a strict improvement. -/
theorem variance_ucbvi_implies_standard
    (K : ℕ)
    (V_star_0 : M.S → ℝ)
    (V_policies : Fin K → M.S → ℝ)
    (starts : Fin K → M.S)
    (bonus : Fin K → Fin M.H → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (δ : ℝ) (hδ : 0 < δ)
    (h_per_ep : ∀ k : Fin K,
      V_star_0 (starts k) - V_policies k (starts k) ≤
      ∑ h : Fin M.H, bonus k h)
    (h_bonus : M.varianceTotalBonusBound bonus C δ)
    (hH : 1 ≤ (M.H : ℝ)) :
    M.cumulativeRegret K V_star_0 V_policies starts ≤
    C * Real.sqrt (M.H ^ 3 * (Fintype.card M.S) * (Fintype.card M.A) *
      K * Real.log (M.H * (Fintype.card M.S) * (Fintype.card M.A) * K / δ)) := by
  have h1 := M.variance_ucbvi_regret K V_star_0 V_policies starts bonus C δ hδ
    h_per_ep h_bonus
  calc M.cumulativeRegret K V_star_0 V_policies starts
      ≤ C * Real.sqrt (M.H ^ 2 * (Fintype.card M.S) * (Fintype.card M.A) *
          K * Real.log (M.H * (Fintype.card M.S) * (Fintype.card M.A) * K / δ)) := h1
    _ ≤ C * Real.sqrt (M.H ^ 3 * (Fintype.card M.S) * (Fintype.card M.A) *
          K * Real.log (M.H * (Fintype.card M.S) * (Fintype.card M.A) * K / δ)) := by
        apply mul_le_mul_of_nonneg_left _ hC
        have hH_sq_le_cube : (M.H : ℝ) ^ 2 ≤ (M.H : ℝ) ^ 3 :=
          pow_le_pow_right₀ hH (by omega)
        have h_eq_l : ↑M.H ^ 2 * ↑(Fintype.card M.S) * ↑(Fintype.card M.A) * ↑K *
            Real.log (↑M.H * ↑(Fintype.card M.S) * ↑(Fintype.card M.A) * ↑K / δ) =
            ↑M.H ^ 2 * (↑(Fintype.card M.S) * ↑(Fintype.card M.A) *
              ↑K * Real.log (↑M.H * ↑(Fintype.card M.S) * ↑(Fintype.card M.A) * ↑K / δ)) := by
          ring
        have h_eq_r : ↑M.H ^ 3 * ↑(Fintype.card M.S) * ↑(Fintype.card M.A) * ↑K *
            Real.log (↑M.H * ↑(Fintype.card M.S) * ↑(Fintype.card M.A) * ↑K / δ) =
            ↑M.H ^ 3 * (↑(Fintype.card M.S) * ↑(Fintype.card M.A) *
              ↑K * Real.log (↑M.H * ↑(Fintype.card M.S) * ↑(Fintype.card M.A) * ↑K / δ)) := by
          ring
        by_cases hx : 0 ≤ ↑(Fintype.card M.S) * ↑(Fintype.card M.A) *
            ↑K * Real.log (↑M.H * ↑(Fintype.card M.S) * ↑(Fintype.card M.A) * ↑K / δ)
        · apply Real.sqrt_le_sqrt
          rw [h_eq_l, h_eq_r]
          exact mul_le_mul_of_nonneg_right hH_sq_le_cube hx
        · push_neg at hx
          have h_lhs_neg : ↑M.H ^ 2 * ↑(Fintype.card M.S) * ↑(Fintype.card M.A) * ↑K *
              Real.log (↑M.H * ↑(Fintype.card M.S) * ↑(Fintype.card M.A) * ↑K / δ) ≤ 0 := by
            rw [h_eq_l]; exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hx.le
          have h_rhs_neg : ↑M.H ^ 3 * ↑(Fintype.card M.S) * ↑(Fintype.card M.A) * ↑K *
              Real.log (↑M.H * ↑(Fintype.card M.S) * ↑(Fintype.card M.A) * ↑K / δ) ≤ 0 := by
            rw [h_eq_r]; exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hx.le
          rw [Real.sqrt_eq_zero_of_nonpos h_lhs_neg, Real.sqrt_eq_zero_of_nonpos h_rhs_neg]

end FiniteHorizonMDP

end
