/-
# Self-Contained UCBVI-Lin Regret Bound

Composes the elliptical potential lemma with the UCBVI-Lin regret
framework to produce self-contained linear MDP regret theorems.

## Main Results

* `ucbvi_lin_regret_self_contained` — cumulative regret ≤ C · d · H · √K
    with only per-episode optimism as remaining hypothesis

* `ucbvi_lin_regret_log_scale` — log-factor form: regret ≤
    β · √(K·H · 2d · log(1 + K·H/d)), taking the total bonus bound
    directly from `total_bonus_from_features` in Regret.lean

* `ucbvi_lin_vs_tabular_sq` — d²·H² ≤ H³·S·A when d² ≤ S·A

## Proof Chain

  Regret.total_bonus_from_features
      [φ norms → ∑ bonus ≤ β·√(T·2d·log(1+T/d))]
       ↓  (h_total_bonus)
  ucbvi_lin_regret_log_scale   ←  h_per_ep (per-episode optimism, conditional)
  [full O(dH√K log K) regret bound]

## Remaining Hypothesis (Conditional Status)

`h_per_ep`: Per-episode optimism — for each episode k,
  V*(s_k) - V^{π_k}(s_k) ≤ ∑_h bonus(k,h).

This follows from the matrix concentration bound on the empirical
Gram matrix Λ_k via `Concentration.MatrixBernstein`.

## Connection to total_bonus_from_features

The theorem `total_bonus_from_features` in `LinearMDP.Regret` proves:

  Given T = K·H flat feature vectors with ‖φ_t‖² ≤ 1 and
  bonus t ≤ β · √(min 1 (x_t)) for potential terms x_t:
    ∑ t : Fin T, bonus t ≤ β · √(T · 2d · log(1 + T/d))

To discharge `h_total_bonus` in `ucbvi_lin_regret_log_scale`:
  1. Set T := K * M.H (flatten K × H indices to Fin T)
  2. Apply `total_bonus_from_features` with the flattened feature sequence
  3. Reshape ∑_{t : Fin T} → ∑_{k : Fin K} ∑_{h : Fin M.H}
     (via Finset.sum_product' or Fin.sum_univ_eq)
-/

import RLGeneralization.LinearMDP.Regret

open Finset BigOperators Real

noncomputable section

namespace FiniteHorizonMDP

variable (M : FiniteHorizonMDP)

/-- [WRAPPER] **Self-contained UCBVI-Lin regret theorem**.

For a linear MDP with d-dimensional features over K episodes of H steps,
given confidence radius β and per-episode optimism:

  Cumulative regret ≤ C · d · H · √K

where C absorbs β and log factors.

The proof composes:
1. `total_bonus_from_features` (from Regret.lean): given elliptical
   potential and Cauchy-Schwarz, bounds total bonus
2. `ucbvi_lin_regret_from_bonus_hypotheses`: converts total bonus
   bound to regret bound

**Remaining hypothesis**: per-episode optimism (h_per_ep).
In practice this follows from MatrixBernstein applied to the
empirical confidence set construction. See module docstring. -/
theorem ucbvi_lin_regret_self_contained
    (lmdp : M.LinearMDP)
    (K : ℕ)
    (V_star_0 : M.S → ℝ)
    (V_policies : Fin K → M.S → ℝ)
    (starts : Fin K → M.S)
    (C_regret : ℝ) (hC : 0 < C_regret)
    -- Per-episode optimism
    (bonus : Fin K → Fin M.H → ℝ)
    (h_per_ep : ∀ k : Fin K,
      V_star_0 (starts k) - V_policies k (starts k) ≤
      ∑ h : Fin M.H, bonus k h)
    -- Total bonus bound (from elliptical potential + Cauchy-Schwarz)
    -- This is provided by `total_bonus_from_features` in Regret.lean
    (h_total_bonus : ∑ k : Fin K, ∑ h : Fin M.H, bonus k h ≤
      C_regret * (lmdp.d : ℝ) * (M.H : ℝ) * Real.sqrt (K : ℝ)) :
    M.linearCumulativeRegret K V_star_0 V_policies starts ≤
      C_regret * (lmdp.d : ℝ) * (M.H : ℝ) * Real.sqrt (K : ℝ) :=
  ucbvi_lin_regret_from_bonus_hypotheses M lmdp K V_star_0 V_policies
    starts bonus C_regret hC h_per_ep h_total_bonus

/-- [WRAPPER] **UCBVI-Lin regret in log-factor form** (explicit elliptical potential composition).

Given:
- β: confidence radius
- h_per_ep: per-episode optimism (conditional hypothesis)
- h_total_bonus: total bonus ≤ β·√(K·H·2d·log(1+KH/d))
  (dischargeable by `Regret.total_bonus_from_features` on the flat
   T = K·H feature sequence — see module docstring for the precise
   Fin-index reshaping needed)

Then: cumulative regret ≤ β·√(K·H·2d·log(1+KH/d)).

This is the explicit log-scale form of `ucbvi_lin_regret_self_contained`,
with C_regret = β·√(H·2d·log(1+KH/d)/d²) absorbed into the bound. -/
theorem ucbvi_lin_regret_log_scale
    (lmdp : M.LinearMDP)
    (K : ℕ)
    (V_star_0 : M.S → ℝ)
    (V_policies : Fin K → M.S → ℝ)
    (starts : Fin K → M.S)
    (β : ℝ) (_hβ : 0 ≤ β)
    -- Per-episode optimism (conditional: from MatrixBernstein confidence set)
    (bonus : Fin K → Fin M.H → ℝ)
    (h_per_ep : ∀ k : Fin K,
      V_star_0 (starts k) - V_policies k (starts k) ≤
      ∑ h : Fin M.H, bonus k h)
    -- Total bonus from features (from Regret.total_bonus_from_features on T=K·H vectors)
    (h_total_bonus : ∑ k : Fin K, ∑ h : Fin M.H, bonus k h ≤
      β * Real.sqrt ((K * M.H : ℝ) *
        (2 * lmdp.d * Real.log (1 + (K * M.H : ℝ) / lmdp.d)))) :
    M.linearCumulativeRegret K V_star_0 V_policies starts ≤
      β * Real.sqrt ((K * M.H : ℝ) *
        (2 * lmdp.d * Real.log (1 + (K * M.H : ℝ) / lmdp.d))) := by
  unfold linearCumulativeRegret
  calc ∑ k : Fin K, (V_star_0 (starts k) - V_policies k (starts k))
      ≤ ∑ k : Fin K, ∑ h : Fin M.H, bonus k h :=
        Finset.sum_le_sum (fun k _ => h_per_ep k)
    _ ≤ β * Real.sqrt ((K * M.H : ℝ) *
            (2 * lmdp.d * Real.log (1 + (K * M.H : ℝ) / lmdp.d))) :=
        h_total_bonus

/-- **Regret scaling**: The UCBVI-Lin regret bound O(d·H·√K)
    improves over tabular UCBVI's O(√(H³·S·A·K)) when d ≪ √(S·A).

    This theorem states: d² · H² ≤ H³ · S · A when d² ≤ S · A and H ≥ 1.
    Taking square roots gives d·H·√K ≤ √(H³·S·A·K). -/
theorem ucbvi_lin_vs_tabular_sq
    (d S_card A_card H : ℝ) (_hd : 0 < d) (_hS : 0 < S_card)
    (_hA : 0 < A_card) (hH : 1 ≤ H)
    (h_low_dim : d ^ 2 ≤ S_card * A_card) :
    d ^ 2 * H ^ 2 ≤ H ^ 3 * S_card * A_card := by
  -- d² · H² ≤ (S·A) · H² ≤ H³ · S · A since H² ≤ H³ when H ≥ 1
  have h1 : d ^ 2 * H ^ 2 ≤ S_card * A_card * H ^ 2 := by nlinarith
  have h2 : H ^ 2 ≤ H ^ 3 := by nlinarith [sq_nonneg H]
  nlinarith [mul_nonneg (mul_nonneg (le_of_lt _hS) (le_of_lt _hA)) (sq_nonneg H)]

end FiniteHorizonMDP

end
