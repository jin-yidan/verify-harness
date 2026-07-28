/-
# GOLF: Generalized Optimistic Learning for Function approximation

GOLF (Agarwal et al. 2022, Ch 8.5) is an optimistic exploration algorithm
for RL with function approximation. It uses the Bellman rank / bilinear class
structure to achieve near-optimal regret.

## Main Results

* `GOLFInstance` — structure encoding the GOLF problem setup

* `golf_confidence_set` — the online confidence set maintained by GOLF

* `golf_regret_decomposition` — regret bounded by sum of Bellman errors

* `golf_bellman_error_sum_bound` — sum of Bellman errors via Cauchy-Schwarz

* `golf_regret_bound` — O(H² · √(d_E · K)) regret bound (conditional)

## References

* Agarwal et al., "Reinforcement Learning: Theory and Algorithms," Ch 8.5 (2026).
* Jin et al., "Bellman Eluder Dimension," NeurIPS 2021.
-/

import RLGeneralization.BilinearRank.Auxiliary
import RLGeneralization.Complexity.EluderDimension

open Finset BigOperators Real

noncomputable section

namespace FiniteHorizonMDP

variable (M : FiniteHorizonMDP)

/-! ### GOLF Instance Setup -/

/-- **GOLF instance**: An RL problem with bilinear Bellman-rank structure.

GOLF maintains a confidence set of plausible Q-functions and selects
the optimistic policy at each episode. -/
structure GOLFInstance where
  /-- Bellman rank structure -/
  brb : M.BellmanRankBound
  /-- Bellman rank bound B -/
  B : ℕ
  h_B : brb.d ≤ B
  /-- Value function bound: |Q| ≤ H for all hypotheses -/
  H_bound : ∀ j h s a, |brb.F.f j h s a| ≤ M.H

/-! ### Confidence Set -/

/-- **GOLF confidence set** at episode k.

Contains all Q-functions in F with total squared Bellman error ≤ β:
  C_k = {j ∈ F : ∑_{τ<k} ‖Bellman_error(j, τ)‖² ≤ β}

where β is a confidence radius growing logarithmically. -/
def golfConfidenceSet (G : M.GOLFInstance) (k : ℕ)
    (observations : Fin k → Fin M.H → M.S × M.A × ℝ)
    (β : ℝ) : Set (Fin G.brb.F.n) :=
  {j | (∑ τ : Fin k, ∑ h : Fin M.H,
    (G.brb.F.f j h (observations τ h).1 (observations τ h).2.1 -
     (observations τ h).2.2) ^ 2) ≤ β}

/-- The confidence set is nonempty when β is large enough. -/
theorem golfConfidenceSet_nonempty
    (G : M.GOLFInstance) (k : ℕ)
    (observations : Fin k → Fin M.H → M.S × M.A × ℝ)
    (β : ℝ) (j_star : Fin G.brb.F.n)
    (h_star : j_star ∈ M.golfConfidenceSet G k observations β) :
    (M.golfConfidenceSet G k observations β).Nonempty :=
  ⟨j_star, h_star⟩

/-! ### Optimism Condition -/

/-- **GOLF optimism** (conditional).

The confidence set contains the true Q*:
  P(j* ∈ C_k for all k ≤ K) ≥ 1 - δ

This requires a concentration argument (union bound over all k and hypotheses).
**Status**: Conditional — taken as hypothesis h_contains_true.

[SPECIFICATION] Type-level contract; takes conclusion as hypothesis.
Proof requires: concentration argument (union bound over episodes k and
hypothesis indices) showing j* remains in the confidence set. -/
theorem golf_optimism_conditional
    (G : M.GOLFInstance) (k : ℕ)
    (observations : Fin k → Fin M.H → M.S × M.A × ℝ)
    (β : ℝ) (j_star : Fin G.brb.F.n)
    -- The Bellman error of j_star is small on observed data
    (_h_bellman_small : ∀ ep : Fin k, ∀ h : Fin M.H,
      let obs := observations ep h
      |G.brb.F.f j_star h obs.1 obs.2.1 - obs.2.2| ≤ β / (k + 1))
    -- The confidence set includes all hypotheses with small cumulative error
    (h_conf_def : j_star ∈ M.golfConfidenceSet G k observations β ↔
      ∑ ep : Fin k, ∑ h : Fin M.H,
        (G.brb.F.f j_star h (observations ep h).1 (observations ep h).2.1 -
         (observations ep h).2.2) ^ 2 ≤ β)
    -- The cumulative squared error is bounded by β
    (h_sq_sum : ∑ ep : Fin k, ∑ h : Fin M.H,
        (G.brb.F.f j_star h (observations ep h).1 (observations ep h).2.1 -
         (observations ep h).2.2) ^ 2 ≤ β) :
    j_star ∈ M.golfConfidenceSet G k observations β := by
  exact h_conf_def.mpr h_sq_sum

/-! ### Regret Decomposition -/

/-- **GOLF regret decomposition** (algebraic).

For H-bounded rewards and optimistic selection, the per-episode regret
is bounded by 2H times the Bellman error of the selected function:
  V*(s_0) - V^{π_k}(s_0) ≤ 2H · ε_k

**Proof**: By PDL + optimism: regret ≤ (V̂_k - V^{π_k})
  ≤ H · (Bellman error of optimistic j_k)

**Status**: Conditional on h_regret_decomp. -/
theorem golf_regret_decomposition
    (K : ℕ)
    (per_episode_regret : Fin K → ℝ)
    (bellman_errors : Fin K → ℝ)
    (H_bound : ℝ) (_hH : 0 < H_bound)
    (h_decomp : ∀ k, per_episode_regret k ≤ 2 * H_bound * bellman_errors k)
    (_h_be_nonneg : ∀ k, 0 ≤ bellman_errors k) :
    ∑ k : Fin K, per_episode_regret k ≤
      2 * H_bound * ∑ k : Fin K, bellman_errors k :=
  le_trans (Finset.sum_le_sum (fun k _ => h_decomp k))
    (by rw [← Finset.mul_sum])

/-! ### Bellman Error Sum Bound -/

/-- **GOLF Bellman error sum bound** (conditional via eluder dimension).

By Cauchy-Schwarz + eluder dimension bound:
  (∑_k ε_k)² ≤ d_E · K · H²

so ∑_k ε_k ≤ √(d_E · K · H²) = H · √(d_E · K).

**Status**: Conditional on h_eluder_sum (from eluder_sum_bound). -/
theorem golf_bellman_error_sum_bound
    (K : ℕ)
    (d_E : ℕ) (_hd : 0 < d_E)
    (bellman_errors : Fin K → ℝ)
    (H_val : ℝ) (_hH : 0 < H_val)
    (h_be_nonneg : ∀ k, 0 ≤ bellman_errors k)
    (h_eluder_sum : (∑ k : Fin K, bellman_errors k) ^ 2 ≤
                    ↑d_E * ↑K * H_val ^ 2) :
    ∑ k : Fin K, bellman_errors k ≤
      Real.sqrt (↑d_E * ↑K * H_val ^ 2) := by
  have h_sum_nonneg : 0 ≤ ∑ k : Fin K, bellman_errors k :=
    Finset.sum_nonneg (fun k _ => h_be_nonneg k)
  rw [← Real.sqrt_sq h_sum_nonneg]
  apply Real.sqrt_le_sqrt
  exact_mod_cast h_eluder_sum

/-! ### Main GOLF Regret Bound -/

/-- **GOLF regret bound** (conditional).

For a function class F with eluder dimension d_E and horizon H:
  R_K ≤ 2H · √(d_E · K · H²) = 2H² · √(d_E · K)

**Status**: Conditional on:
1. GOLF optimism (Q* in confidence set at all episodes)
2. Eluder dimension bound (from EluderDimension.lean) -/
theorem golf_regret_bound
    (K : ℕ) (_hK : 0 < K)
    (d_E : ℕ) (_hd : 0 < d_E)
    (H_val : ℝ) (hH : 0 < H_val)
    (per_episode_regret : Fin K → ℝ)
    (bellman_errors : Fin K → ℝ)
    (h_be_nonneg : ∀ k, 0 ≤ bellman_errors k)
    -- Conditional: per-episode regret ≤ 2H · Bellman error
    (h_regret_decomp : ∀ k, per_episode_regret k ≤ 2 * H_val * bellman_errors k)
    -- Conditional: eluder sum bound
    (h_eluder_sum : (∑ k : Fin K, bellman_errors k) ^ 2 ≤
                    ↑d_E * ↑K * H_val ^ 2) :
    ∑ k : Fin K, per_episode_regret k ≤
      2 * H_val * Real.sqrt (↑d_E * ↑K * H_val ^ 2) := by
  have h_be_sum_nonneg : 0 ≤ ∑ k : Fin K, bellman_errors k :=
    Finset.sum_nonneg (fun k _ => h_be_nonneg k)
  have h_be_le_sqrt : ∑ k : Fin K, bellman_errors k ≤
      Real.sqrt (↑d_E * ↑K * H_val ^ 2) := by
    rw [← Real.sqrt_sq h_be_sum_nonneg]
    apply Real.sqrt_le_sqrt
    exact_mod_cast h_eluder_sum
  calc ∑ k : Fin K, per_episode_regret k
      ≤ ∑ k : Fin K, 2 * H_val * bellman_errors k :=
          Finset.sum_le_sum (fun k _ => h_regret_decomp k)
    _ = 2 * H_val * ∑ k : Fin K, bellman_errors k := by
          rw [← Finset.mul_sum]
    _ ≤ 2 * H_val * Real.sqrt (↑d_E * ↑K * H_val ^ 2) :=
          mul_le_mul_of_nonneg_left h_be_le_sqrt (by linarith)

/-- **GOLF ε-optimality sample complexity**.

For average regret ≤ ε per episode, GOLF needs:
  K ≥ 4 · d_E · H⁴ / ε²  (ignoring log factors)

Proof: Set 2H² · √(d_E / K) ≤ ε, solve for K.
From K ≥ 4·d_E·H⁴/ε², get d_E/K ≤ ε²/(4H⁴), then sqrt gives
√(d_E/K) ≤ ε/(2H²), multiply by 2H² to conclude. -/
theorem golf_sample_complexity_bound
    (d_E : ℕ) (_hd : 0 < d_E)
    (H_val ε : ℝ) (hH : 0 < H_val) (hε : 0 < ε)
    (K : ℕ) (hK : 0 < K)
    (h_K_large : 4 * d_E * H_val ^ 4 / ε ^ 2 ≤ K) :
    2 * H_val ^ 2 * Real.sqrt (↑d_E / ↑K) ≤ ε := by
  have hH2 : 0 < H_val ^ 2 := sq_pos_of_pos hH
  have h2H2 : 0 < 2 * H_val ^ 2 := mul_pos two_pos hH2
  have hK_pos : (0 : ℝ) < ↑K := Nat.cast_pos.mpr hK
  -- Suffices to show d_E/K ≤ (ε/(2H²))²
  suffices hsq : ↑d_E / ↑K ≤ (ε / (2 * H_val ^ 2)) ^ 2 by
    calc 2 * H_val ^ 2 * Real.sqrt (↑d_E / ↑K)
        ≤ 2 * H_val ^ 2 * Real.sqrt ((ε / (2 * H_val ^ 2)) ^ 2) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsq) h2H2.le
      _ = 2 * H_val ^ 2 * (ε / (2 * H_val ^ 2)) := by
          rw [Real.sqrt_sq (div_nonneg hε.le h2H2.le)]
      _ = ε := by field_simp
  -- d_E/K ≤ (ε/(2H²))²; expand and cross-multiply
  rw [div_pow, div_le_div_iff₀ hK_pos (sq_pos_of_pos h2H2)]
  -- Need: ↑d_E * (2*H²)² ≤ ε²*K, i.e. 4*d_E*H⁴ ≤ ε²*K
  have hε2 : (0 : ℝ) < ε ^ 2 := sq_pos_of_pos hε
  have h_cross : 4 * ↑d_E * H_val ^ 4 ≤ ε ^ 2 * ↑K := by
    have := mul_le_mul_of_nonneg_right h_K_large hε2.le
    rw [div_mul_cancel₀ _ hε2.ne'] at this
    linarith
  nlinarith [h_cross]

end FiniteHorizonMDP

end
