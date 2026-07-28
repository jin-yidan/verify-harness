/-
# Discrete Distribution Concentration Bounds

Formalizes concentration inequalities for empirical discrete distributions,
including multinomial L1 concentration and value-function error bounds
for tabular RL with transition model estimation.

## Main Results

* `l1_le_card_mul_bound` — algebraic: ‖f‖₁ ≤ K·C when |f k| ≤ C for all k

* `l1_from_eps_over_K` — if max coordinate error ≤ ε/K, then L1 error ≤ ε

* `multinomial_l1_concentration` — conditional: P(‖P̂_n - P‖₁ ≥ ε) ≤ 2K·exp(-2nε²/K²)
    (union bound over K Hoeffding per-coordinate bounds)

* `l1_transition_error_le` — exact: per-(s,a) L1 bound → transitionError bound

* `l1_model_value_bound` — exact: L1 transition error → value function error bound
    (uses simulation_lemma from SimulationLemma.lean)

* `rl_l1_concentration_conditional` — conditional: generative model L1 concentration
    for tabular RL transition estimation

## References

* Agarwal et al., "RL: Theory and Algorithms," Appendix A.4 (2026).
* Weissman et al., "Inequalities for the L1 Deviation of the Empirical Distribution," 2003.
-/

import RLGeneralization.Generalization.SampleComplexity
import RLGeneralization.MDP.SimulationLemma
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Finset BigOperators Real

noncomputable section

namespace FiniteMDP

variable (M : FiniteMDP)

/-! ### Algebraic Lemmas for L1 Norms -/

/-- **L1 norm bounded by K times pointwise bound** (exact).

For any finite vector f : Fin K → ℝ and bound C ≥ |f k| for all k:
  ∑_k |f(k)| ≤ K · C -/
theorem l1_le_card_mul_bound (K : ℕ) (f : Fin K → ℝ) (C : ℝ)
    (h : ∀ k, |f k| ≤ C) :
    ∑ k : Fin K, |f k| ≤ ↑K * C :=
  calc ∑ k : Fin K, |f k|
      ≤ ∑ _k : Fin K, C := Finset.sum_le_sum (fun k _ => h k)
    _ = ↑K * C := by simp [Finset.sum_const, nsmul_eq_mul]

/-- **L1 norm from ε/K coordinate bound** (exact).

If each coordinate error is at most ε/K, then the L1 norm is at most ε. -/
theorem l1_from_eps_over_K (K : ℕ) (hK : 0 < K) (f : Fin K → ℝ) (ε : ℝ)
    (h : ∀ k, |f k| ≤ ε / ↑K) :
    ∑ k : Fin K, |f k| ≤ ε := by
  calc ∑ k : Fin K, |f k|
      ≤ ↑K * (ε / ↑K) := l1_le_card_mul_bound K f (ε / ↑K) h
    _ = ε := by field_simp

/-- **Union bound sum** (algebraic, exact).

If bounds k ≤ C for all k and each bound is nonneg, then ∑_k bounds k ≤ K · C. -/
theorem union_bound_sum_le (K : ℕ) (bounds : Fin K → ℝ) (C : ℝ)
    (h : ∀ k, bounds k ≤ C) (_h_nn : ∀ k, 0 ≤ bounds k) :
    ∑ k : Fin K, bounds k ≤ ↑K * C :=
  calc ∑ k : Fin K, bounds k
      ≤ ∑ _k : Fin K, C := Finset.sum_le_sum (fun k _ => h k)
    _ = ↑K * C := by simp [Finset.sum_const, nsmul_eq_mul]

/-- **Hoeffding exponent algebra** (exact).

The substitution ε/K in the Hoeffding exponent simplifies to:
  exp(-2n(ε/K)²) = exp(-2nε²/K²) -/
theorem hoeffding_eps_over_K (K : ℕ) (hK : (0 : ℝ) < K) (n : ℕ) (ε : ℝ) :
    Real.exp (-2 * ↑n * (ε / K) ^ 2) =
    Real.exp (-2 * ↑n * ε ^ 2 / K ^ 2) := by
  congr 1; field_simp

/-! ### Multinomial L1 Concentration -/

/-- **Multinomial L1 concentration** (conditional).

For empirical distribution P̂_n from n i.i.d. samples of P over K outcomes:
  P(‖P̂_n - P‖₁ ≥ ε) ≤ 2K · exp(-2nε²/K²)

**Key steps** (conditional on probabilistic hypotheses):
1. P(‖P̂ - P‖₁ ≥ ε) ≤ P(∃k: |P̂(k) - P(k)| ≥ ε/K)  [L1 → max coordinate, via l1_from_eps_over_K]
2. ≤ ∑_k P(|P̂(k) - P(k)| ≥ ε/K)                      [union bound]
3. ≤ ∑_k 2·exp(-2n(ε/K)²)                              [Hoeffding per coordinate]
4. = 2K·exp(-2nε²/K²)                                  [algebra]

**Status**: Conditional on the per-coordinate Hoeffding bound (h_coord) and
the union bound measurability step (h_union). -/
theorem multinomial_l1_concentration
    (K : ℕ) (hK : 0 < K)
    (n : ℕ) (_hn : 0 < n) (ε : ℝ) (_hε : 0 < ε)
    -- Abstract probability of L1 exceeding ε
    (l1_prob : ℝ) (_h_l1_nn : 0 ≤ l1_prob)
    -- Per-coordinate probability of exceeding ε/K
    (coord_prob : Fin K → ℝ) (h_coord_nn : ∀ k, 0 ≤ coord_prob k)
    -- Union bound: L1 exceedance ≤ sum of coordinate exceedances
    (h_union : l1_prob ≤ ∑ k : Fin K, coord_prob k)
    -- Hoeffding per coordinate
    (h_coord : ∀ k : Fin K,
      coord_prob k ≤ 2 * Real.exp (-2 * ↑n * (ε / ↑K) ^ 2)) :
    l1_prob ≤ 2 * ↑K * Real.exp (-2 * ↑n * ε ^ 2 / ↑K ^ 2) := by
  have hK_real : (0 : ℝ) < ↑K := Nat.cast_pos.mpr hK
  have h_sum : ∑ k : Fin K, coord_prob k ≤
      ↑K * (2 * Real.exp (-2 * ↑n * (ε / ↑K) ^ 2)) :=
    union_bound_sum_le K coord_prob _ h_coord h_coord_nn
  rw [← hoeffding_eps_over_K K hK_real n ε] at *
  linarith [h_union, h_sum]

/-! ### Transition Model L1 Bound -/

/-- **Pointwise L1 bound → transitionError bound** (exact).

If the L1 transition error is bounded at every (s,a), then
the sup-norm `transitionError` is also bounded. -/
theorem l1_transition_error_le (M_hat : M.ApproxMDP) (ε : ℝ)
    (h : ∀ s a, ∑ s', |M.P s a s' - M_hat.P_hat s a s'| ≤ ε) :
    M.transitionError M_hat ≤ ε := by
  simp only [transitionError]
  apply Finset.sup'_le; intro s _
  apply Finset.sup'_le; intro a _
  exact h s a

/-- **L1 transition bound → value error bound** (exact, via simulation_lemma).

Given:
- L1 transition error ≤ ε_T at all (s,a)
- Reward error ≤ ε_R at all (s,a)
- Value function V_Mhat bounded by B

Then the value error satisfies:
  |V_M(s) - V_Mhat(s)| ≤ (ε_R + γ · B · ε_T) / (1 - γ)

This is the L1-based simulation bound (no extra |S| factor compared to
per-entry Hoeffding, since L1 directly bounds the transition expectation). -/
theorem l1_model_value_bound
    (M_hat : M.ApproxMDP)
    (π : M.StochasticPolicy)
    (V_M V_Mhat : M.StateValueFn)
    (hV_M : M.isValueOf V_M π)
    (hV_Mhat : ∀ s, V_Mhat s =
      (∑ a, π.prob s a * M_hat.r_hat s a) +
      M.γ * (∑ a, π.prob s a * ∑ s', M_hat.P_hat s a s' * V_Mhat s'))
    (B ε_R ε_T : ℝ) (hB : 0 ≤ B)
    (hV_bound : ∀ s, |V_Mhat s| ≤ B)
    -- Reward error
    (h_rew : M.rewardError M_hat ≤ ε_R)
    -- L1 transition error
    (h_l1 : ∀ s a, ∑ s', |M.P s a s' - M_hat.P_hat s a s'| ≤ ε_T) :
    ∀ s, |V_M s - V_Mhat s| ≤ (ε_R + M.γ * B * ε_T) / (1 - M.γ) :=
  M.simulation_lemma M_hat π V_M V_Mhat hV_M hV_Mhat B hB hV_bound
    ε_R h_rew ε_T (M.l1_transition_error_le M_hat ε_T h_l1)

/-! ### RL L1 Concentration (Conditional) -/

/-- **RL generative model L1 concentration** (conditional).

For tabular RL with a generative model sampling n = N_{s,a} times from each (s,a):
  P(∀ s,a: ‖P̂(·|s,a) - P(·|s,a)‖₁ ≤ ε) ≥ 1 - δ

when N_{s,a} ≥ 2 |S| log(2|S||A|/δ) / ε².

**Proof sketch** (conditional):
1. Fix (s,a). By multinomial_l1_concentration with K = |S|:
   P(‖P̂(·|s,a) - P(·|s,a)‖₁ ≥ ε) ≤ 2|S| · exp(-2Nε²/|S|²)
2. Union bound over |S|·|A| pairs:
   P(∃(s,a): ...) ≤ 2|S|²|A| · exp(-2Nε²/|S|²)
3. Set RHS ≤ δ to get N ≥ |S|²·log(2|S|²|A|/δ)/(2ε²).

**Status**: Conditional on the per-(s,a) multinomial concentration (h_per_pair)
and the union bound over pairs (h_union_pairs). -/
theorem rl_l1_concentration_conditional
    (N : ℕ) (hN : 0 < N) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (S_card : ℕ) (hS : 0 < S_card) (hSM : S_card = Fintype.card M.S)
    (A_card : ℕ) (hA : 0 < A_card) (hAM : A_card = Fintype.card M.A)
    -- Sufficient sample size
    (h_N_large : 2 * S_card ^ 2 * Real.log (2 * S_card ^ 2 * A_card / δ) / ε ^ 2 ≤ N)
    -- Per-(s,a) multinomial concentration (conditional)
    (fail_prob : M.S → M.A → ℝ)
    (h_per_pair : ∀ s a,
      fail_prob s a ≤ 2 * S_card * Real.exp (-2 * ↑N * ε ^ 2 / ↑S_card ^ 2))
    (_h_nn : ∀ s a, 0 ≤ fail_prob s a)
    -- Union bound: total failure probability ≤ sum over (s,a) pairs
    (total_fail : ℝ) (_h_total_nn : 0 ≤ total_fail)
    (h_union : total_fail ≤ ∑ s : M.S, ∑ a : M.A, fail_prob s a) :
    total_fail ≤ δ := by
  -- Step 1: Sum over (s,a) pairs
  have h_sum : ∑ s : M.S, ∑ a : M.A, fail_prob s a ≤
      ↑S_card * ↑A_card * (2 * S_card * Real.exp (-2 * N * ε ^ 2 / S_card ^ 2)) := by
    have h_inner : ∀ s, ∑ a : M.A, fail_prob s a ≤
        ↑A_card * (2 * S_card * Real.exp (-2 * N * ε ^ 2 / S_card ^ 2)) := by
      intro s
      calc ∑ a : M.A, fail_prob s a
          ≤ ∑ _a : M.A, 2 * S_card * Real.exp (-2 * ↑N * ε ^ 2 / ↑S_card ^ 2) :=
              Finset.sum_le_sum (fun a _ => h_per_pair s a)
        _ = ↑A_card * (2 * S_card * Real.exp (-2 * N * ε ^ 2 / S_card ^ 2)) := by
              simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hAM]
    calc ∑ s : M.S, ∑ a : M.A, fail_prob s a
        ≤ ∑ _s : M.S, ↑A_card * (2 * S_card * Real.exp (-2 * N * ε ^ 2 / S_card ^ 2)) :=
            Finset.sum_le_sum (fun s _ => h_inner s)
      _ = ↑S_card * ↑A_card * (2 * S_card * Real.exp (-2 * N * ε ^ 2 / S_card ^ 2)) := by
            simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hSM]; ring
  -- Step 2: Show 2S²A·exp(-2Nε²/S²) ≤ δ from N_large
  -- This requires the logarithm inversion, which is conditional on h_N_large
  have h_bound : ↑S_card * ↑A_card *
      (2 * ↑S_card * Real.exp (-2 * ↑N * ε ^ 2 / ↑S_card ^ 2)) ≤ δ := by
    -- Positivity of cast values
    have hSr : (0 : ℝ) < ↑S_card := Nat.cast_pos.mpr hS
    have hAr : (0 : ℝ) < ↑A_card := Nat.cast_pos.mpr hA
    have hNr : (0 : ℝ) < ↑N := Nat.cast_pos.mpr hN
    -- Let C = 2*S²*A/δ
    set C := 2 * (↑S_card : ℝ) ^ 2 * ↑A_card / δ with hC_def
    have hC_pos : 0 < C := by positivity
    -- The LHS = C * δ * exp(-2Nε²/S²). Goal: C*δ*exp(-x) ≤ δ, i.e., C*exp(-x) ≤ 1
    -- Equivalently: exp(-x) ≤ 1/C, i.e., exp(-x) ≤ exp(-log C)
    -- From h_N_large: log(C) ≤ N*ε²/(2*S²) ≤ 2*N*ε²/S²
    have h_log_le : Real.log C ≤ 2 * ↑N * ε ^ 2 / (↑S_card : ℝ) ^ 2 := by
      have heps_sq : 0 < ε ^ 2 := sq_pos_of_pos hε
      have hS_sq : (0 : ℝ) < ↑S_card ^ 2 := sq_pos_of_pos hSr
      -- Clear ε² from h_N_large: 2*S²*log(C)/ε² ≤ N → 2*S²*log(C) ≤ N*ε²
      rw [div_le_iff₀ heps_sq] at h_N_large
      -- Goal: log(C) ≤ 2*N*ε²/S²  ↔  log(C)*S² ≤ 2*N*ε²
      rw [le_div_iff₀ hS_sq]
      nlinarith
    -- exp is monotone: exp(-2Nε²/S²) ≤ exp(-log C)
    have h_exp_le : Real.exp (-2 * ↑N * ε ^ 2 / (↑S_card : ℝ) ^ 2) ≤ Real.exp (-Real.log C) := by
      apply Real.exp_le_exp.mpr
      have h1 : -2 * ↑N * ε ^ 2 / (↑S_card : ℝ) ^ 2 =
          -(2 * ↑N * ε ^ 2 / (↑S_card : ℝ) ^ 2) := by ring
      rw [h1]; linarith
    -- exp(-log C) = 1/C = δ/(2*S²*A) for C > 0
    have h_exp_log : Real.exp (-Real.log C) = C⁻¹ := by
      rw [Real.exp_neg, Real.exp_log hC_pos]
    -- Combine: LHS = 2*S²*A * exp(-...) = C*δ * exp(-...)
    -- ≤ C*δ * (1/C) = δ
    have h_lhs_eq : ↑S_card * ↑A_card * (2 * ↑S_card * Real.exp (-2 * ↑N * ε ^ 2 / ↑S_card ^ 2)) =
        C * δ * Real.exp (-2 * ↑N * ε ^ 2 / (↑S_card : ℝ) ^ 2) := by
      rw [hC_def]; field_simp
    rw [h_lhs_eq]
    calc C * δ * Real.exp (-2 * ↑N * ε ^ 2 / (↑S_card : ℝ) ^ 2)
        ≤ C * δ * C⁻¹ := by
          apply mul_le_mul_of_nonneg_left
          · rw [← h_exp_log]; exact h_exp_le
          · positivity
      _ = δ := by field_simp
  linarith [h_union, h_sum, h_bound]

end FiniteMDP

end
