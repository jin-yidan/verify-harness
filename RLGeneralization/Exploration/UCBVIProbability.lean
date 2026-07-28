/-
# UCBVI Regret Composition

Composes the UCBVI algebraic core (`UCBVI.lean`) into end-to-end regret
bounds, conditional on deterministic bonus hypotheses.

`ConcentrationEvent` packages the bonus-covering property as a structure;
the probability guarantee (that this event holds with prob ≥ 1-δ) is not
formalized and would require a measure-theoretic construction.

All theorems are deterministic compositions: they assume the bonus covers
the transition estimation error and that the total bonus is bounded, then
derive the cumulative regret bound algebraically.

## Main Results

* `ConcentrationEvent` — Structure packaging bonus-covering hypotheses
* `optimism_on_good_event` — Q̂ ≥ Q* given nonneg gap hypothesis
* `ucbvi_high_probability_regret` — R(K) ≤ C·H²·√(SAK·log(SAHK/δ))
    given per-episode and total bonus hypotheses
* `ucbvi_expected_regret` — expected regret bound given high-prob bound
    and failure-case bound hypotheses

## References

* [Azar, Osband, Munos, *Minimax Regret Bounds for RL*, ICML 2017]
* [Agarwal et al., *RL: Theory and Algorithms*, Ch 4]
-/

import RLGeneralization.Exploration.UCBVI
import RLGeneralization.Concentration.Hoeffding

open Finset BigOperators

noncomputable section

namespace FiniteHorizonMDP

variable (M : FiniteHorizonMDP)

/-! ### Concentration Event -/

/-- The **concentration event**: the empirical transition kernel P̂
    is close to the true kernel P at every (s,a,h) triple.

    Formally: for all h, s, a, and all value functions V with 0 ≤ V ≤ H:
      |∑_{s'} (P̂_h - P_h)(s'|s,a) · V(s')| ≤ bonus_h(s,a)

    This holds with probability ≥ 1-δ by Hoeffding + union bound. -/
structure ConcentrationEvent (K : ℕ) (δ : ℝ) where
  /-- Empirical transition estimates -/
  P_hat : Fin M.H → M.S → M.A → M.S → ℝ
  /-- Exploration bonus function -/
  bonus : Fin M.H → M.S → M.A → ℝ
  /-- Bonus is nonneg -/
  bonus_nonneg : ∀ h s a, 0 ≤ bonus h s a
  /-- Hypothesis: the bonus covers the transition estimation error for
      all bounded value functions V with 0 ≤ V ≤ H. This is the defining
      property of the concentration event (follows from Hoeffding + union bound
      over (s,a,h) triples, but the measure-theoretic construction is not
      formalized here). -/
  bonus_covers : ∀ (h : Fin M.H) (s : M.S) (a : M.A) (V : M.S → ℝ),
    (∀ s', 0 ≤ V s') → (∀ s', V s' ≤ M.H) →
    |∑ s', (P_hat h s a s' - M.P h s a s') * V s'| ≤ bonus h s a
/-! ### Optimism -/

/-- **Optimism on the good event**: The UCBVI Q-function dominates Q*.

  On the concentration event, for all (h, s, a):
    Q̂_h(s,a) ≥ Q*_h(s,a)

  Proof sketch (backward induction on h = H, H-1, ..., 0):
  - Base: Q̂_H = 0 = Q*_H ✓
  - Step: Q̂_h = r̂_h + P̂ V̂_{h+1} + bonus
        ≥ r_h + P V*_{h+1} (using bonus ≥ |P̂V - PV| and V̂ ≥ V* by IH)
        = Q*_h ✓

  Hypothesis: the per-step optimism gap Q̂_h(s,a) - Q*_h(s,a) ≥ 0 for
  all (h,s,a). This is the conclusion of backward induction combined with
  the concentration event's bonus covering property. -/
theorem optimism_on_good_event
    (_ce : M.ConcentrationEvent K δ)
    (Q_hat Q_star : Fin M.H → M.S → M.A → ℝ)
    -- Hypothesis: backward induction + bonus coverage yields nonneg gap
    (h_gap_nonneg : ∀ h s a, 0 ≤ Q_hat h s a - Q_star h s a) :
    ∀ h s a, Q_star h s a ≤ Q_hat h s a := by
  intro h s a; linarith [h_gap_nonneg h s a]

/-! ### High-Probability Regret Bound -/

/-- [WRAPPER] **UCBVI high-probability regret bound.**

  Takes h_per_ep (per-episode regret <= bonus sum) and h_total (total
  bonus bound) as hypotheses, returns the O(H²√(SAK log(SAHK/δ))) bound.

  The H² factor comes from summing H bonus terms per episode, each
  scaling with the value range [0, H]. The √(SAK) factor comes from
  pigeonhole on visit counts. -/
theorem ucbvi_high_probability_regret
    (K : ℕ) (_hK : 0 < K)
    (δ : ℝ) (_hδ : 0 < δ)
    (V_star_0 : M.S → ℝ)
    (V_policies : Fin K → M.S → ℝ)
    (starts : Fin K → M.S)
    -- Hypothesis: per-episode regret ≤ sum of bonuses
    -- (follows from optimism + backward induction; not formalized here)
    (bonus_sum : Fin K → ℝ)
    (h_per_ep : ∀ k : Fin K,
      V_star_0 (starts k) - V_policies k (starts k) ≤ bonus_sum k)
    -- Hypothesis: total bonus ≤ C·H²·√(SAK·log(SAHK/δ))
    -- (follows from pigeonhole on visit counts + Hoeffding; not formalized here)
    (C : ℝ) (_hC_pos : 0 < C)
    (h_total : ∑ k : Fin K, bonus_sum k ≤
      C * (M.H : ℝ) ^ 2 * Real.sqrt (
        Fintype.card M.S * Fintype.card M.A * K *
        Real.log (Fintype.card M.S * Fintype.card M.A * M.H * K / δ))) :
    M.cumulativeRegret K V_star_0 V_policies starts ≤
    C * (M.H : ℝ) ^ 2 * Real.sqrt (
      Fintype.card M.S * Fintype.card M.A * K *
      Real.log (Fintype.card M.S * Fintype.card M.A * M.H * K / δ)) := by
  unfold cumulativeRegret
  calc ∑ k : Fin K, (V_star_0 (starts k) - V_policies k (starts k))
      ≤ ∑ k : Fin K, bonus_sum k :=
        Finset.sum_le_sum (fun k _ => h_per_ep k)
    _ ≤ _ := h_total

/-! ### Expected Regret -/

/-- **UCBVI expected regret bound.**

  E[R(K)] ≤ Õ(H² · √(SAK))

  The expected regret integrates the high-probability bound:
    E[R(K)] = E[R(K) · 1_{good}] + E[R(K) · 1_{bad}]
            ≤ C·H²·√(SAK·log(SAHK/δ)) + δ·K·H  (bad event contributes ≤ KH)
            = Õ(H²√(SAK))  (choosing δ = 1/K)

  Takes both the high-probability bound and the bad-event contribution
  as hypotheses (full integration requires measure-theoretic machinery). -/
theorem ucbvi_expected_regret
    (K : ℕ) (_hK : 0 < K)
    (expected_regret : ℝ) (_h_exp_nn : 0 ≤ expected_regret)
    -- Hypothesis: expected regret decomposes into good-event and bad-event parts
    -- (requires measure-theoretic integration; not formalized here)
    (regret_good regret_bad : ℝ)
    (h_decomp : expected_regret ≤ regret_good + regret_bad)
    -- Hypothesis: good-event contribution ≤ C·H²·√(SAK)
    (C : ℝ) (_hC : 0 < C)
    (h_good : regret_good ≤
      C * (M.H : ℝ) ^ 2 * Real.sqrt (Fintype.card M.S * Fintype.card M.A * K))
    -- Hypothesis: bad-event contribution ≤ 1 (δ·KH with δ = 1/K, negligible)
    (h_bad : regret_bad ≤ 1) :
    expected_regret ≤
      C * (M.H : ℝ) ^ 2 * Real.sqrt (
        Fintype.card M.S * Fintype.card M.A * K) + 1 := by
  linarith

end FiniteHorizonMDP

end
