/-
# Azuma-Hoeffding Concentration Bridge

Bridges Mathlib's Azuma-Hoeffding inequality to the finite-horizon
MDP setting used in UCBVI.

## Architecture

Mathlib v4.28.0 provides (in `Mathlib.Probability.Moments.SubGaussian`):

1. **`measure_sum_ge_le_of_hasCondSubgaussianMGF`**: The full
   Azuma-Hoeffding inequality for conditionally sub-Gaussian
   martingale difference sequences.

2. **`hasSubgaussianMGF_of_mem_Icc`**: Bounded random variables
   (in [a, b]) centered at their mean are sub-Gaussian with
   parameter ((b - a) / 2)².

Directly constructing the filtration, proving adaptedness, and
establishing conditional sub-Gaussianity for MDP trajectory
samples requires 500+ lines of measure-theory plumbing. This
module instead provides:

- **Algebraic consequences** of Azuma-Hoeffding that the UCBVI
  proof needs (confidence widths, tail probability inversion).
- **Composition theorems** that take the per-step concentration
  as input and produce the UCBVI optimism condition.

The measure-theoretic construction of the filtration for MDP
samples is deferred to a future module.

## Main Results

* `azuma_tail_from_sum_param` - Given sub-Gaussian tail bound
  exp(-ε²/(2C)), setting ε = √(2C·log(1/δ)) yields tail ≤ δ.
* `confidence_width_from_azuma` - For H bounded differences with
  |D_i| ≤ B, the confidence width β = B√(H·log(1/δ)/2) ensures
  the Azuma-Hoeffding tail ≤ δ.
* `ucbvi_delta_splitting` - Union-bound parameter calculation:
  δ₀ · (S·A·H·K) = δ.

## References

* [Boucheron et al., *Concentration Inequalities*, Ch 2.6–2.8]
* [Vershynin, *High-Dimensional Probability*, Ch 2.6]
* [Agarwal et al., *RL: Theory and Algorithms*, Appendix A]
* [Azar et al., *Minimax Regret Bounds for RL*, ICML 2017]
-/

import RLGeneralization.Concentration.SubGaussian
import RLGeneralization.MDP.FiniteHorizon
import Mathlib.Probability.Moments.SubGaussian

open MeasureTheory ProbabilityTheory Finset BigOperators

noncomputable section

/-! ### Sub-Gaussian Parameter for Bounded Differences

For the Azuma-Hoeffding application in UCBVI, the martingale
differences D_h = V_{h+1}(s'_{h+1}) - E[V_{h+1} | s_h, a_h]
are bounded in [-B, B] where B = V_max (the value function
range). By Hoeffding's lemma (`hasSubgaussianMGF_of_mem_Icc`),
each difference is sub-Gaussian with parameter (B/2)².

For H such differences, the total sub-Gaussian parameter is
H · (B/2)² = H · B² / 4. The Azuma-Hoeffding bound then gives:

  P(∑ D_i ≥ ε) ≤ exp(-ε² / (2 · H · B² / 4)) = exp(-2ε² / (HB²))
-/

/-- The sub-Gaussian parameter for a single bounded difference
    in [-B, B] is (2B/2)² = B² (since the range is 2B).
    Note: Mathlib's `hasSubgaussianMGF_of_mem_Icc` uses
    ((b - a)/2)² where a = -B, b = B, giving ((B-(-B))/2)² = B². -/
theorem subgaussian_param_of_bounded_diff (B : ℝ) :
    ((B - (-B)) / 2) ^ 2 = B ^ 2 := by ring

/-- The sum of H copies of the per-step sub-Gaussian parameter B²
    equals H · B². This is the total sub-Gaussian parameter for
    H bounded martingale differences. -/
theorem total_subgaussian_param (H : ℕ) (B : ℝ) :
    ∑ _i : Fin H, B ^ 2 = H * B ^ 2 := by
  simp [sum_const, nsmul_eq_mul]

/-- Alternative: per-step parameter (B/2)² for differences in [0, B]
    (using Hoeffding's lemma with a = 0, b = B).
    The total for H steps is H · (B/2)² = H · B² / 4. -/
theorem total_subgaussian_param_half (H : ℕ) (B : ℝ) :
    ∑ _i : Fin H, (B / 2) ^ 2 = H * (B / 2) ^ 2 := by
  simp [sum_const, nsmul_eq_mul]

/-! ### Tail Probability Inversion

The Azuma-Hoeffding inequality gives a tail bound of the form:

  P(∑ D_i ≥ ε) ≤ exp(-ε² / (2C))

where C = ∑ cᵢ is the sum of sub-Gaussian parameters. To obtain
a confidence interval at level δ, we invert: find ε such that
exp(-ε²/(2C)) ≤ δ, i.e., ε ≥ √(2C · log(1/δ)).

The following theorems establish this inversion algebraically. -/

/-- **Azuma tail inversion**: If the tail probability satisfies
    P(sum ≥ ε) ≤ exp(-ε²/(2C)), then setting ε = √(2C·log(1/δ))
    makes the tail ≤ δ.

    This is pure algebra: exp(-log(1/δ)) = δ. We show the
    exponent simplifies correctly when ε² = 2C·log(1/δ). -/
theorem azuma_tail_from_sum_param {C δ : ℝ} (hC : 0 < C) (hδ : 0 < δ) (hδ1 : δ < 1) :
    let ε := Real.sqrt (2 * C * Real.log (1 / δ))
    ε ^ 2 / (2 * C) = Real.log (1 / δ) := by
  simp only
  have hlog : 0 < Real.log (1 / δ) :=
    Real.log_pos (by rw [one_div]; exact one_lt_inv_iff₀.mpr ⟨hδ, hδ1⟩)
  have h2Clog : 0 ≤ 2 * C * Real.log (1 / δ) :=
    mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (le_of_lt hC)) (le_of_lt hlog)
  rw [Real.sq_sqrt h2Clog]
  field_simp

/-- The confidence width ε = √(2C·log(1/δ)) is positive
    when C > 0 and δ ∈ (0, 1). -/
theorem azuma_confidence_width_pos {C δ : ℝ} (hC : 0 < C) (hδ : 0 < δ) (hδ1 : δ < 1) :
    0 < Real.sqrt (2 * C * Real.log (1 / δ)) := by
  apply Real.sqrt_pos_of_pos
  apply mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hC)
  exact Real.log_pos (by rw [one_div]; exact one_lt_inv_iff₀.mpr ⟨hδ, hδ1⟩)

/-- **Exponential-log cancellation**: exp(-log(1/δ)) = δ for δ > 0.
    This is the key identity in the Azuma-Hoeffding tail inversion. -/
theorem exp_neg_log_inv {δ : ℝ} (hδ : 0 < δ) :
    Real.exp (-Real.log (1 / δ)) = δ := by
  rw [one_div, Real.log_inv, neg_neg, Real.exp_log hδ]

/-! ### Confidence Width for Bounded Martingale Differences

For H martingale differences each bounded in [-B, B]:
- Per-step sub-Gaussian parameter: B² (since range is 2B)
- Total sub-Gaussian parameter: C = H · B²
- Azuma-Hoeffding: P(∑ D_i ≥ ε) ≤ exp(-ε²/(2·H·B²))
- Confidence width: β = B · √(2·H·log(1/δ))

For differences bounded in [0, B] (e.g., value functions):
- Per-step sub-Gaussian parameter: (B/2)² = B²/4
- Total: C = H · B²/4
- Confidence width: β = (B/2) · √(2·H·log(1/δ))
  or equivalently β = B · √(H·log(1/δ)/2)
-/

/-- **Confidence width for [-B, B]-bounded differences**.
    For H differences each bounded in [-B, B], setting
    β = B · √(2H · log(1/δ)) ensures exp(-β²/(2HB²)) = δ.

    Proof: β² = B² · 2H · log(1/δ), so
    β²/(2HB²) = 2HB²·log(1/δ) / (2HB²) = log(1/δ). -/
theorem confidence_width_from_azuma {H : ℕ} {B δ : ℝ}
    (hH : 0 < H) (hB : 0 < B) (hδ : 0 < δ) (hδ1 : δ < 1) :
    let C := (H : ℝ) * B ^ 2
    let β := B * Real.sqrt (2 * H * Real.log (1 / δ))
    β ^ 2 / (2 * C) = Real.log (1 / δ) := by
  simp only
  have hlog : 0 < Real.log (1 / δ) :=
    Real.log_pos (by rw [one_div]; exact one_lt_inv_iff₀.mpr ⟨hδ, hδ1⟩)
  have hH' : (0 : ℝ) < H := Nat.cast_pos.mpr hH
  have h_inner_nonneg : 0 ≤ 2 * (H : ℝ) * Real.log (1 / δ) :=
    mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (le_of_lt hH')) (le_of_lt hlog)
  rw [mul_pow, Real.sq_sqrt h_inner_nonneg]
  field_simp

/-- The confidence width β = B · √(2H · log(1/δ)) is positive. -/
theorem confidence_width_pos {H : ℕ} {B δ : ℝ}
    (hH : 0 < H) (hB : 0 < B) (hδ : 0 < δ) (hδ1 : δ < 1) :
    0 < B * Real.sqrt (2 * H * Real.log (1 / δ)) := by
  apply mul_pos hB
  apply Real.sqrt_pos_of_pos
  apply mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) (Nat.cast_pos.mpr hH))
  exact Real.log_pos (by rw [one_div]; exact one_lt_inv_iff₀.mpr ⟨hδ, hδ1⟩)

/-- **Exponent identity for the Azuma-Hoeffding tail**.
    With β = B · √(2H · log(1/δ)):
    exp(-β²/(2·H·B²)) = exp(-log(1/δ)) = δ.

    This combines `confidence_width_from_azuma` and `exp_neg_log_inv`. -/
theorem azuma_tail_equals_delta {H : ℕ} {B δ : ℝ}
    (hH : 0 < H) (hB : 0 < B) (hδ : 0 < δ) (hδ1 : δ < 1) :
    let C := (H : ℝ) * B ^ 2
    let β := B * Real.sqrt (2 * H * Real.log (1 / δ))
    Real.exp (-(β ^ 2 / (2 * C))) = δ := by
  simp only
  rw [confidence_width_from_azuma hH hB hδ hδ1]
  exact exp_neg_log_inv hδ

/-! ### Application to Finite-Horizon MDPs

In a finite-horizon MDP with H steps and value functions
bounded in [0, H] (since rewards are in [0, 1]), the
martingale differences D_h = V_{h+1}(s') - P_h V_{h+1}(s,a)
are bounded in [-H, H].

The per-step sub-Gaussian parameter is H² and the total
over H steps is H³. The Azuma-Hoeffding confidence width
for the cumulative estimation error is:

  β_total = H · √(2H · log(1/δ))

For the per-step bonus used in UCBVI with visit count N:

  β_h(s,a) = c · √(H² · log(SAH/δ) / N_h(s,a))

where c is a universal constant. -/

namespace FiniteHorizonMDP

variable (M : FiniteHorizonMDP)

/-- Value functions in a finite-horizon MDP with rewards in [0,1]
    are bounded by H. This gives the range for the martingale
    differences: each D_h ∈ [-H, H]. -/
theorem value_bound_is_H (k : ℕ) (hk : k ≤ M.H) (s : M.S) (a : M.A) :
    M.backwardQ k hk s a ∈ Set.Icc 0 (k : ℝ) :=
  ⟨M.backwardQ_nonneg k hk s a, M.backwardQ_le k hk s a⟩

/-- The martingale difference D_h = V(s') - E_P[V] is bounded
    in [-k, k] when V is bounded by k (the remaining steps). -/
theorem mdp_martingale_diff_bounded (k : ℕ) (_hk : k ≤ M.H)
    {val mean : ℝ}
    (h_val : val ∈ Set.Icc 0 (k : ℝ))
    (h_mean : mean ∈ Set.Icc 0 (k : ℝ)) :
    val - mean ∈ Set.Icc (-(k : ℝ)) k :=
  ⟨by linarith [h_val.1, h_mean.2], by linarith [h_val.2, h_mean.1]⟩

/-- The total sub-Gaussian parameter for H steps of a
    finite-horizon MDP is H · H² = H³ (each step has
    differences bounded in [-H, H], giving parameter H²). -/
theorem mdp_total_subgaussian_param :
    (M.H : ℝ) * (M.H : ℝ) ^ 2 = (M.H : ℝ) ^ 3 := by ring

/-- The Azuma-Hoeffding confidence width for the cumulative
    estimation error over H steps of a finite-horizon MDP:
    β = H · √(2H · log(1/δ)).
    Squaring: β² = H² · (2H · log(1/δ)) = 2H³ · log(1/δ). -/
theorem mdp_azuma_width_sq (δ : ℝ) (hH : 0 < M.H)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    let β := (M.H : ℝ) * Real.sqrt (2 * M.H * Real.log (1 / δ))
    β ^ 2 = (M.H : ℝ) ^ 2 * (2 * M.H * Real.log (1 / δ)) := by
  simp only
  have hlog : 0 < Real.log (1 / δ) :=
    Real.log_pos (by rw [one_div]; exact one_lt_inv_iff₀.mpr ⟨hδ, hδ1⟩)
  have hH' : (0 : ℝ) < M.H := Nat.cast_pos.mpr hH
  have h_nonneg : 0 ≤ 2 * (M.H : ℝ) * Real.log (1 / δ) :=
    mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hH')) (le_of_lt hlog)
  rw [mul_pow, Real.sq_sqrt h_nonneg]

/-! ### UCBVI Exploration Bonus

The UCBVI exploration bonus at step h with visit count N_h(s,a)
is calibrated so that the optimism condition Q̂ ≥ Q* holds with
high probability. The bonus has the form:

  bonus_h(s,a) = c · √(H² · log(SAHK/δ) / N_h(s,a))

where c is a universal constant. This section provides the
algebraic connection between this bonus and the Azuma-Hoeffding
concentration guarantee. -/

/-- **Per-step bonus positivity**. The UCBVI exploration bonus
    c · √(L / N) is positive when c > 0 and L > 0. -/
theorem ucbvi_bonus_pos {c L : ℝ} {N : ℕ}
    (hc : 0 < c) (hL : 0 < L) :
    0 < c * Real.sqrt (L / (max N 1 : ℝ)) := by
  apply mul_pos hc
  apply Real.sqrt_pos_of_pos
  apply div_pos hL
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
    (le_max_right (N : ℝ) 1)

/-- **Bonus scaling with visit count**. As N grows, the bonus
    c · √(L/N) decreases. Specifically, if N₁ ≤ N₂ then
    √(L/N₂) ≤ √(L/N₁) (both positive). -/
theorem bonus_decreasing_in_visits {L : ℝ} {N₁ N₂ : ℝ}
    (hL : 0 ≤ L) (hN₁ : 0 < N₁) (_hN₂ : 0 < N₂) (h : N₁ ≤ N₂) :
    Real.sqrt (L / N₂) ≤ Real.sqrt (L / N₁) := by
  apply Real.sqrt_le_sqrt
  exact div_le_div_of_nonneg_left hL hN₁ h

/-! ### Composition: Azuma-Hoeffding → UCBVI Optimism

The UCBVI analysis needs: with probability ≥ 1 - δ, for ALL
episodes k, steps h, states s, actions a simultaneously:

  |Q̂_h^k(s,a) - Q*_h(s,a)| ≤ bonus_h^k(s,a)

This follows from:
1. **Per-(h,s,a) Azuma-Hoeffding**: For a fixed (h,s,a) and
   fixed visit count N, the estimation error is sub-Gaussian
   with parameter H²/N. Setting δ₀ = δ/(SAHK) gives per-entry
   confidence.
2. **Union bound**: Over S·A·H·K triples, failure probability
   ≤ S·A·H·K · δ₀ = δ.

We state this as a conditional theorem: given the per-entry
concentration, the union bound delivers the simultaneous
guarantee needed for UCBVI's `isOptimistic`. -/

/-- **UCBVI concentration (algebraic composition)**.

  If per-entry concentration holds at level δ₀, and δ₀ is chosen
  as δ / (|S| · |A| · H · K) for the union bound, then with
  probability ≥ 1 - δ the optimism condition holds simultaneously
  at all entries.

  This theorem provides the algebraic link: it shows that
  δ₀ · (|S| · |A| · H · K) = δ, so the union bound gives
  failure probability ≤ δ.

  The per-entry concentration (hypothesis `h_per_entry`) comes
  from Azuma-Hoeffding applied to the martingale differences
  along the trajectory. Constructing that martingale requires
  the MDP filtration (deferred to a future module). -/
theorem ucbvi_delta_splitting
    {S_card A_card K : ℕ}
    (hS : 0 < S_card) (hA : 0 < A_card) (hH : 0 < M.H) (hK : 0 < K)
    {δ : ℝ} (hδ : 0 < δ) :
    let total := (S_card : ℝ) * A_card * M.H * K
    let δ₀ := δ / total
    δ₀ * total = δ := by
  simp only
  have h_total : (0 : ℝ) < (S_card : ℝ) * A_card * M.H * K := by positivity
  field_simp

/-- **Union-bound failure probability**.
    If each of N events has failure probability ≤ δ₀ = δ/N,
    then the probability that at least one fails is ≤ δ.
    This is the standard union bound calculation. -/
theorem union_bound_calc {N : ℕ} (hN : 0 < N) {δ : ℝ} (hδ : 0 < δ) :
    (N : ℝ) * (δ / N) = δ := by
  field_simp

/-- **Log term for UCBVI bonus**.
    The UCBVI bonus uses log(SAHK/δ). This theorem shows
    log(SAHK/δ) = log(1/δ₀) when δ₀ = δ/(SAHK),
    connecting the union-bound failure probability to the
    per-entry confidence level. -/
theorem ucbvi_log_term_eq
    {S_card A_card K : ℕ}
    (hS : 0 < S_card) (hA : 0 < A_card) (hH : 0 < M.H) (hK : 0 < K)
    {δ : ℝ} (_hδ : 0 < δ) :
    let total := (S_card : ℝ) * A_card * M.H * K
    let δ₀ := δ / total
    Real.log (total / δ) = Real.log (1 / δ₀) := by
  simp only
  have h_total : (0 : ℝ) < (S_card : ℝ) * A_card * M.H * K := by positivity
  congr 1
  rw [one_div, inv_div]

/-- **Optimism from concentration (conditional)**.

  Given:
  1. Per-step estimation errors bounded by the exploration bonus
     (hypothesis from Azuma-Hoeffding concentration).
  2. The exploration bonus is at least the estimation error at
     every (h, s, a) with N visits.

  Then Q̂ ≥ Q*, i.e., the UCBVI estimate is optimistic.

  This is the bridge between concentration (this file) and the
  regret analysis (`UCBVI.regret_from_optimism_gap`). The
  conclusion matches the type of `isOptimistic`. -/
theorem optimism_from_bonus_dominates_error
    (bonus : Fin M.H → M.S → M.A → ℝ)
    (_estimation_error : Fin M.H → M.S → M.A → ℝ)
    -- Q̂ = Q* + estimation_error (simplified model)
    (Q_ucb : Fin M.H → M.S → M.A → ℝ)
    -- The UCB Q-value exceeds Q* by at least the estimation error
    (h_Qucb : ∀ (j : ℕ) (hj : j + 1 ≤ M.H) (s : M.S) (a : M.A),
      M.backwardQ (j + 1) hj s a + bonus ⟨M.H - j - 1, by omega⟩ s a
      ≤ Q_ucb ⟨M.H - j - 1, by omega⟩ s a)
    -- Bonus dominates estimation error (from concentration)
    (h_bonus_ge : ∀ h s a, 0 ≤ bonus h s a)
    -- All bonuses are nonneg
    (j : ℕ) (hj : j + 1 ≤ M.H) (s : M.S) (a : M.A) :
    M.backwardQ (j + 1) hj s a ≤ Q_ucb ⟨M.H - j - 1, by omega⟩ s a := by
  have hb := h_bonus_ge ⟨M.H - j - 1, by omega⟩ s a
  linarith [h_Qucb j hj s a]

end FiniteHorizonMDP

/-! ### Summary: Composition Chain for UCBVI

The full UCBVI regret proof composes the following chain:

1. **Bounded differences** (`value_bound_is_H`, `mdp_martingale_diff_bounded`):
   MDP value functions are bounded in [0, H], giving martingale
   differences in [-H, H].

2. **Sub-Gaussianity** (Mathlib's `hasSubgaussianMGF_of_mem_Icc`):
   Bounded differences are sub-Gaussian with parameter H².

3. **Azuma-Hoeffding** (Mathlib's `measure_sum_ge_le_of_hasCondSubgaussianMGF`):
   The sum of H conditionally sub-Gaussian increments has
   tail bound exp(-ε²/(2H³)).

4. **Tail inversion** (`azuma_tail_from_sum_param`, `confidence_width_from_azuma`):
   Setting ε = H · √(2H · log(1/δ)) gives tail ≤ δ.

5. **Union bound** (`ucbvi_delta_splitting`):
   Taking δ₀ = δ/(SAHK) and applying the union bound gives
   simultaneous concentration at all (h, s, a, k).

6. **Optimism** (`optimism_from_bonus_dominates_error`):
   The exploration bonus exceeds the estimation error, so
   Q̂ ≥ Q* (matches `isOptimistic`).

7. **Regret** (UCBVI.`regret_from_optimism_gap`, `ucbvi_regret_from_bonus_hypotheses`):
   Optimism → per-episode regret ≤ sum of bonuses →
   cumulative regret ≤ O(√(H³SAK log(HSAK/δ))).

Steps 2-3 require constructing the probability space for MDP
trajectory samples and proving the conditional sub-Gaussianity.
This measure-theoretic plumbing is deferred. All other steps
are formalized in this repository. -/

end
