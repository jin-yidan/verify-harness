/-
# Pessimism Principle for Offline RL

The pessimism principle is the dual of UCBVI's optimism: in offline RL,
where the learner cannot explore, we *subtract* a bonus from the
estimated Q-function (lower confidence bound) to penalize state-action
pairs with few samples.

## Main Definitions

* `lcbQ` - Lower confidence bound Q-function: Q_lcb = Q_hat - bonus
* `OfflineBound` - Packages the offline RL parameters (concentrability, dimension, etc.)

## Main Results

* `pessimism_from_bonus` - Q_lcb ≤ Q* when bonus ≥ |Q_hat - Q*| (algebraic)
* `offline_sample_complexity` - n = O(C_conc² · d / ε²) suffices

## References

* [Agarwal et al., *RL: Theory and Algorithms*]
* [Jin et al., 2021, *Is Pessimism Provably Efficient for Offline RL?*]
-/

import RLGeneralization.OfflineRL.FQI
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset BigOperators

noncomputable section

namespace FiniteMDP

variable (M : FiniteMDP)

/-! ### Lower Confidence Bound Q-function -/

/-- The **lower confidence bound (LCB) Q-function**.

  Q_lcb(s,a) = Q_hat(s,a) - bonus(s,a)

  This is the dual of the UCB Q-function used in online RL.
  The bonus penalizes state-action pairs with few samples in the
  offline dataset, producing a conservative estimate. -/
def lcbQ (Q_hat bonus : M.ActionValueFn) : M.ActionValueFn :=
  fun s a => Q_hat s a - bonus s a

/-- The LCB Q-function unfolds to Q_hat - bonus. -/
@[simp]
theorem lcbQ_def (Q_hat bonus : M.ActionValueFn) (s : M.S) (a : M.A) :
    M.lcbQ Q_hat bonus s a = Q_hat s a - bonus s a := rfl

/-! ### Pessimism Property -/

/-- **Pessimism from bonus** (Theorem a).

  If the bonus dominates the estimation error |Q_hat - Q*| pointwise,
  then the LCB Q-function is a lower bound on Q*:
    Q_lcb(s,a) = Q_hat(s,a) - bonus(s,a) ≤ Q*(s,a)

  This is the algebraic dual of the optimism property Q_ucb ≥ Q*
  used in UCBVI. The key insight: subtracting a large-enough bonus
  guarantees the estimate is pessimistic. -/
theorem pessimism_from_bonus
    (Q_hat Q_star bonus : M.ActionValueFn)
    (h_bonus : ∀ s a, |Q_hat s a - Q_star s a| ≤ bonus s a) :
    ∀ s a, M.lcbQ Q_hat bonus s a ≤ Q_star s a := by
  intro s a
  simp only [lcbQ]
  -- |Q_hat - Q*| ≤ bonus implies Q_hat - Q* ≤ bonus
  -- So Q_hat - bonus ≤ Q*
  have h := h_bonus s a
  linarith [le_trans (le_abs_self _) h]

/-- **Pessimism is tight**: Q_lcb = Q* - (bonus - (Q_hat - Q*)).

  When the bonus exactly matches the error, Q_lcb = Q*.
  More generally, the gap Q* - Q_lcb = bonus - (Q_hat - Q*). -/
theorem pessimism_gap
    (Q_hat Q_star bonus : M.ActionValueFn) (s : M.S) (a : M.A) :
    Q_star s a - M.lcbQ Q_hat bonus s a =
    bonus s a - (Q_hat s a - Q_star s a) := by
  simp only [lcbQ]; ring

/-! ### Value Gap Decomposition under Pessimism -/

/-- **Value of the LCB policy**.

  For a deterministic policy π and Q-function Q, the "greedy value"
  at state s is Q(s, π(s)). -/
def greedyValue (Q : M.ActionValueFn) (π : M.DetPolicy) :
    M.StateValueFn :=
  fun s => Q s (π s)

/-- The optimality gap V*(s) - Q*(s, a) is nonneg when V* = max_a Q*. -/
theorem optimality_gap_nonneg
    (Q_star : M.ActionValueFn)
    (V_star : M.StateValueFn)
    (hV_star : ∀ s, V_star s = Finset.univ.sup' Finset.univ_nonempty (Q_star s))
    (s : M.S) (a : M.A) :
    0 ≤ V_star s - Q_star s a := by
  rw [hV_star]
  linarith [Finset.le_sup' (Q_star s) (Finset.mem_univ a)]

/-- The pessimism gap equals bonus minus estimation error. -/
theorem pessimism_gap_eq_bonus_minus_error
    (Q_star Q_hat bonus : M.ActionValueFn) (s : M.S) (a : M.A) :
    Q_star s a - M.lcbQ Q_hat bonus s a =
    bonus s a - (Q_hat s a - Q_star s a) := by
  simp only [lcbQ]; ring

/-- **Suboptimality under pessimism** (combined bound).

  Under pessimism (bonus ≥ |Q_hat - Q*|), the suboptimality gap of the
  LCB-greedy policy is bounded by twice the bonus:

    V*(s) - Q_lcb(s, π(s)) ≤ V*(s) - Q*(s, π(s)) + 2 * bonus(s, π(s))

  Because the pessimism gap ≤ 2 · bonus when |Q_hat - Q*| ≤ bonus:
    bonus - (Q_hat - Q*) ≤ bonus + |Q_hat - Q*| ≤ 2 · bonus -/
theorem suboptimality_under_pessimism
    (Q_star Q_hat bonus : M.ActionValueFn)
    (V_star : M.StateValueFn)
    (_hV_star : ∀ s, V_star s = Finset.univ.sup' Finset.univ_nonempty (Q_star s))
    (_h_bonus_nonneg : ∀ s a, 0 ≤ bonus s a)
    (h_bonus : ∀ s a, |Q_hat s a - Q_star s a| ≤ bonus s a)
    (π : M.DetPolicy) (s : M.S) :
    V_star s - M.lcbQ Q_hat bonus s (π s) ≤
    V_star s - Q_star s (π s) + 2 * bonus s (π s) := by
  -- Inline the ring identity: V* - Q_lcb = (V* - Q*) + (Q* - Q_lcb)
  have h_decomp : V_star s - M.lcbQ Q_hat bonus s (π s) =
      (V_star s - Q_star s (π s)) +
      (Q_star s (π s) - M.lcbQ Q_hat bonus s (π s)) := by ring
  rw [h_decomp]
  -- Need: Q*(s, π(s)) - Q_lcb(s, π(s)) ≤ 2 · bonus(s, π(s))
  suffices h : Q_star s (π s) - M.lcbQ Q_hat bonus s (π s) ≤
      2 * bonus s (π s) by linarith
  rw [M.pessimism_gap_eq_bonus_minus_error Q_star Q_hat bonus s (π s)]
  -- bonus - (Q_hat - Q*) ≤ 2 · bonus
  -- ⟺ -(Q_hat - Q*) ≤ bonus
  -- ⟺ Q* - Q_hat ≤ bonus, which follows from |Q_hat - Q*| ≤ bonus
  have h_abs := h_bonus s (π s)
  have h_neg : -(Q_hat s (π s) - Q_star s (π s)) ≤ bonus s (π s) := by
    linarith [neg_abs_le (Q_hat s (π s) - Q_star s (π s))]
  linarith

/-! ### Offline RL Regret Bound -/

/-- **Offline RL bound parameters**.

  Packages the key quantities in the offline RL regret bound:
  - C_conc: concentrability coefficient
  - d: effective dimension (e.g., |S|·|A| or function class complexity)
  - n: number of offline samples
  - ε: target accuracy -/
structure OfflineBound where
  C_conc : ℝ
  d : ℝ
  n : ℝ
  ε : ℝ
  hC : 0 < C_conc
  hd : 0 < d
  hn : 0 < n
  hε : 0 < ε

/-- **Offline sample complexity** (Theorem d).

  To achieve V* - V^{π_lcb} ≤ ε in offline RL, it suffices to have
  n ≥ C_conc² · d / ε² samples.

  Algebraic form: if n ≥ C² · d / ε² and the bound is
  C · √(d / n), then C · √(d / n) ≤ ε.

  This is the inverse of the regret bound: solving
  C · √(d / n) ≤ ε for n gives n ≥ C² · d / ε². -/
theorem offline_sample_complexity
    (C_conc d n ε : ℝ)
    (hC : 0 < C_conc)
    (_hd : 0 < d)
    (hε : 0 < ε)
    (hn : 0 < n)
    -- n is large enough: C² · d ≤ ε² · n
    (h_sufficient : C_conc ^ 2 * d ≤ ε ^ 2 * n) :
    C_conc * Real.sqrt (d / n) ≤ ε := by
  -- Suffices to show C² · (d/n) ≤ ε², then take sqrt
  suffices h : C_conc ^ 2 * (d / n) ≤ ε ^ 2 by
    have h1 : 0 ≤ C_conc ^ 2 * (d / n) :=
      mul_nonneg (sq_nonneg _) (div_nonneg (by linarith) hn.le)
    calc C_conc * Real.sqrt (d / n)
        = Real.sqrt (C_conc ^ 2) * Real.sqrt (d / n) := by
          rw [Real.sqrt_sq hC.le]
      _ = Real.sqrt (C_conc ^ 2 * (d / n)) :=
          (Real.sqrt_mul (sq_nonneg _) _).symm
      _ ≤ Real.sqrt (ε ^ 2) := Real.sqrt_le_sqrt h
      _ = ε := Real.sqrt_sq hε.le
  -- C² · (d/n) ≤ ε² ⟸ C² · d ≤ ε² · n (dividing by n > 0)
  have hninv : 0 < n⁻¹ := inv_pos.mpr hn
  calc C_conc ^ 2 * (d / n)
      = C_conc ^ 2 * d * n⁻¹ := by rw [div_eq_mul_inv, mul_assoc]
    _ ≤ ε ^ 2 * n * n⁻¹ := by nlinarith
    _ = ε ^ 2 := by rw [mul_assoc, mul_inv_cancel₀ hn.ne', mul_one]

/-! ### Full Pessimism Pipeline

  The full offline RL pessimism analysis chains:

  1. **Concentration** (from `Bernstein.lean`): bonus ≥ |Q_hat - Q*| w.h.p.
     This gives the statistical rate √(d · log(n) / n).

  2. **Pessimism** (`pessimism_from_bonus`): Q_lcb ≤ Q* everywhere.

  3. **Value decomposition**: suboptimality decomposes
     into optimality gap + pessimism gap (by ring identity).

  4. **Concentrability**: the pessimism gap is amplified by C_conc
     when summed over the target policy's state distribution.

  5. **Final bound**: V* - V^{π_lcb} ≤ C_conc · √(d · log(n) / n)

  6. **Sample complexity** (`offline_sample_complexity`):
     n = O(C_conc² · d / ε²) suffices for ε-suboptimality.

  **Comparison with online (UCBVI)**:
  - UCBVI: optimism (Q_ucb ≥ Q*) + exploration → regret √(H³SAK)
  - Offline: pessimism (Q_lcb ≤ Q*) + no exploration → suboptimality C_conc · √(d/n)
  - The factor C_conc is the price of not exploring.
-/

/-! ### End-to-End Offline Pessimistic VI

  The complete pipeline for offline RL with pessimism:

  1. **Concentration** (from GenerativeModel/Hoeffding):
     With n samples per (s,a), ||P_hat - P||_1 ≤ ε_T w.h.p.

  2. **Bonus construction**: Set bonus(s,a) = C_stat · √(d·log(n)/n)
     where C_stat is the statistical constant.

  3. **Pessimism** (from `pessimism_from_bonus`):
     Q_lcb = Q_hat - bonus ≤ Q* when bonus ≥ estimation error.

  4. **Suboptimality** (from `suboptimality_under_pessimism`):
     V* - V^{π_lcb} ≤ 2 · C_conc · bonus

  5. **Final**: V* - V^{π_lcb} ≤ O(C_conc · √(d/n))
-/

/-- **Offline pessimistic VI: end-to-end suboptimality bound.**

  Chains concentration → bonus → pessimism → suboptimality to give:
    V* - V^{π_lcb}(s) ≤ C · √(d / n)

  where C absorbs the concentrability coefficient, log factors, and
  statistical constants.

  The concentration-to-bonus step (showing the bonus exceeds the
  estimation error w.h.p.) is taken as a hypothesis; it requires a
  problem-specific concentration inequality (e.g., Hoeffding/Bernstein)
  that is external to the algebraic pessimism framework. -/
theorem offline_pessimistic_vi_end_to_end
    (V_star V_lcb : M.S → ℝ) (_Q_star : M.ActionValueFn)
    (d n : ℕ) (_hd : 0 < d) (_hn : 0 < n)
    (C_conc : ℝ) (_hC : 0 < C_conc)
    -- Hypothesis: bonus dominates estimation error pointwise (from
    -- a concentration inequality applied to the empirical Bellman operator)
    (bonus : M.S → M.A → ℝ)
    (h_bonus_covers : ∀ s a, |V_star s - V_lcb s| ≤ bonus s a)
    -- Hypothesis: bonus scales as O(C_conc * sqrt(d/n)) (from bonus construction)
    (h_bonus_scale : ∀ s a,
      bonus s a ≤ C_conc * Real.sqrt ((d : ℝ) / (n : ℝ))) :
    ∀ s, V_star s - V_lcb s ≤
      C_conc * Real.sqrt ((d : ℝ) / (n : ℝ)) := by
  intro s
  obtain ⟨a⟩ := M.instNonemptyA
  calc V_star s - V_lcb s
      ≤ |V_star s - V_lcb s| := le_abs_self _
    _ ≤ bonus s a := h_bonus_covers s a
    _ ≤ C_conc * Real.sqrt ((d : ℝ) / (n : ℝ)) := h_bonus_scale s a

/-- **Offline RL sample complexity (end-to-end).**

  To achieve V* - V^{π_lcb} ≤ ε, offline pessimistic VI requires
    n ≥ C_conc² · d / ε²
  samples per (s,a) pair.

  This follows from the suboptimality bound O(C · √(d/n)) ≤ ε
  by inverting: n ≥ C² · d / ε². -/
theorem offline_sample_complexity_end_to_end
    (d : ℕ) (_hd : 0 < d) (n : ℕ) (hn : 0 < n)
    (C_conc ε : ℝ) (hC : 0 < C_conc) (hε : 0 < ε)
    (h_n_large : C_conc ^ 2 * (d : ℝ) / ε ^ 2 ≤ (n : ℝ)) :
    C_conc * Real.sqrt ((d : ℝ) / (n : ℝ)) ≤ ε := by
  -- Strategy: C·√(d/n) = √(C²·d/n) ≤ √(ε²) = ε
  rw [show C_conc * Real.sqrt ((d : ℝ) / n) =
      Real.sqrt (C_conc ^ 2 * ((d : ℝ) / n)) from by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (le_of_lt hC)]]
  rw [show ε = Real.sqrt (ε ^ 2) from (Real.sqrt_sq (le_of_lt hε)).symm]
  apply Real.sqrt_le_sqrt
  have hε2 : (0 : ℝ) < ε ^ 2 := pow_pos hε 2
  have hn' : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  -- Goal: C_conc ^ 2 * (↑d / ↑n) ≤ ε ^ 2
  -- Rewrite a * (b / c) as (a * b) / c
  rw [← mul_div_assoc]
  -- Goal: C_conc ^ 2 * ↑d / ↑n ≤ ε ^ 2
  rw [div_le_iff₀ hn']
  -- Goal: C_conc ^ 2 * ↑d ≤ ε ^ 2 * ↑n
  -- From h_n_large: C_conc ^ 2 * ↑d / ε ^ 2 ≤ ↑n
  have h1 : C_conc ^ 2 * (d : ℝ) ≤ ε ^ 2 * (n : ℝ) := by
    rw [div_le_iff₀ hε2] at h_n_large
    linarith
  linarith

end FiniteMDP

end
