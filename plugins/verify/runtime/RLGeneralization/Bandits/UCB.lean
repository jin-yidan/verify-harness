/-
# Multi-Armed Bandits and UCB

Definitions and partially formalized regret bounds for the finite K-armed
bandit problem.

## Main Definitions

* `BanditInstance` - A K-armed bandit with mean rewards μ_a ∈ [-1,1].
* `BanditInstance.optMean` - Optimal mean μ* = max_a μ_a.
* `BanditInstance.gap` - Sub-optimality gap Δ_a = μ* - μ_a.
* `PseudoRegret` - Pseudo-regret R_T = T·μ* - Σ_t μ_{I_t}.

## Main Results

* `gap_nonneg` - Δ_a ≥ 0 (fully proved).
* `gap_eq_zero_iff_opt` - Δ_a = 0 iff a is optimal (fully proved).
* `pseudoRegret_eq_sum_gap` - R_T = Σ_t Δ_{I_t} (fully proved).
* `etc_oracle_regret_bound` - Oracle ETC combinatorial upper bound (fully proved).
* `ucb_regret_from_pull_count_bounds` - UCB deterministic core from pull-count bounds.
* `oracle_gap_bound_of_etc_witness` - Existential gap-dependent bound via the ETC oracle witness.
* `oracle_worst_case_bound_via_etc` - Existential worst-case bound via the ETC oracle witness.
* `confidenceWidth` - UCB confidence width.

## References

* [Agarwal et al., *RL: Theory and Algorithms*]
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open Finset BigOperators Real

noncomputable section

/-! ### Bandit Instance -/

/-- A K-armed bandit problem.
    Each arm `a : Fin K` has a fixed mean reward `μ_a` bounded in `[-1,1]`. -/
structure BanditInstance (K : ℕ) [NeZero K] where
  /-- Mean reward of each arm -/
  mean : Fin K → ℝ
  /-- Rewards are bounded in [-1, 1] -/
  h_bounded : ∀ a, |mean a| ≤ 1

namespace BanditInstance

variable {K : ℕ} [NeZero K] (B : BanditInstance K)

/-! ### Optimal Mean and Gap -/

/-- Optimal mean reward: `μ* = max_a μ_a`. -/
def optMean : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty B.mean

/-- Sub-optimality gap: `Δ_a = μ* - μ_a`.
    Measures how much worse arm `a` is compared to the best arm. -/
def gap (a : Fin K) : ℝ := B.optMean - B.mean a

/-- The gap is nonneg for every arm. -/
theorem gap_nonneg (a : Fin K) : 0 ≤ B.gap a := by
  unfold gap optMean
  linarith [Finset.le_sup' B.mean (Finset.mem_univ a)]

/-- An arm has gap zero iff it achieves the optimal mean. -/
theorem gap_eq_zero_iff_opt (a : Fin K) :
    B.gap a = 0 ↔ B.mean a = B.optMean := by
  constructor
  · intro h; unfold gap at h; linarith
  · intro h; unfold gap; linarith

/-- There exists an optimal arm (gap = 0). -/
theorem exists_optimal_arm : ∃ a : Fin K, B.gap a = 0 := by
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty B.mean
  exact ⟨a, by unfold gap optMean; linarith⟩

/-- Choose an optimal arm (gap = 0). -/
def optArm : Fin K := B.exists_optimal_arm.choose

/-- The optimal arm has gap zero. -/
theorem optArm_gap : B.gap B.optArm = 0 :=
  B.exists_optimal_arm.choose_spec

/-! ### Pseudo-Regret -/

/-- Pseudo-regret over `T` rounds:
    `R_T = T · μ* − Σ_{t=0}^{T-1} μ_{I_t}`. -/
def pseudoRegret (T : ℕ) (I : Fin T → Fin K) : ℝ :=
  T * B.optMean - ∑ t : Fin T, B.mean (I t)

/-- Pseudo-regret equals the sum of gaps along the played arms:
    R_T = Σ_t Δ_{I_t}. -/
theorem pseudoRegret_eq_sum_gap (T : ℕ) (I : Fin T → Fin K) :
    B.pseudoRegret T I = ∑ t : Fin T, B.gap (I t) := by
  unfold pseudoRegret gap
  rw [Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Pseudo-regret is nonneg (since each gap is nonneg). -/
theorem pseudoRegret_nonneg (T : ℕ) (I : Fin T → Fin K) :
    0 ≤ B.pseudoRegret T I := by
  rw [B.pseudoRegret_eq_sum_gap]
  exact Finset.sum_nonneg (fun t _ => B.gap_nonneg (I t))

/-! ### Empirical Mean and Concentration -/

/-- Number of times arm `a` has been pulled in rounds 0..T-1. -/
def pullCount (T : ℕ) (I : Fin T → Fin K) (a : Fin K) : ℕ :=
  (Finset.univ.filter (fun t => I t = a)).card

/-- Empirical mean reward of arm `a` after T rounds.
    μ̂_T(a) = (1/N_T(a)) Σ_{t : I_t = a} r_t.
    When N_T(a) = 0, returns 0 by convention (division by zero in ℝ). -/
-- [UNUSED]
def empiricalMean (T : ℕ) (I : Fin T → Fin K)
    (rewards : Fin T → ℝ) (a : Fin K) : ℝ :=
  (∑ t ∈ Finset.univ.filter (fun t => I t = a), rewards t) /
    pullCount T I a

/-! ### Uniform Concentration

  With probability ≥ 1 − δ, for all rounds t and arms a simultaneously:
    |μ̂_t(a) − μ_a| ≤ √(2 ln(2TK/δ) / N_t(a)).

  This is the foundation for UCB's confidence bound construction. -/

/-- **Uniform concentration for bandits via the confidence width**.

  The UCB confidence width for arm `a` at round `t` is
    √(2 ln(2TK/δ) / N_t(a)).

  With probability ≥ 1 − δ, simultaneously for all rounds t and
  arms a: |μ̂_t(a) − μ_a| ≤ confidence_width.

  The proof requires sub-Gaussian tail bounds (Hoeffding) + union
  bound over T × K events. We state the algebraic form of the
  confidence width here; the probabilistic guarantee is deferred
  to `Concentration.Hoeffding`. -/
def confidenceWidth (T : ℕ) (δ : ℝ) (n_a : ℕ) : ℝ :=
  Real.sqrt (2 * Real.log (2 * T * K / δ) / max n_a 1)

/-- The confidence width is nonneg. -/
theorem confidenceWidth_nonneg (T : ℕ) (δ : ℝ) (n_a : ℕ) :
    0 ≤ confidenceWidth (K := K) T δ n_a := by
  have _hK : 0 < K := Nat.pos_of_ne_zero (NeZero.ne K)
  exact Real.sqrt_nonneg _

/-! ### Explore-Then-Commit

  The ETC algorithm pulls each arm m times, then commits to the
  empirically best arm for the remaining T − mK rounds. -/

/-- The ETC oracle policy: round-robin for `m * K` rounds, then play
    the true optimal arm. During exploration, round `t` plays arm `t % K`.
    This is an oracle-based policy because it commits to the *true* best arm
    rather than the empirically best arm. The oracle choice only makes
    the bound easier to prove (it can only do better than the empirical
    version). -/
def etcOracleStrategy (m : ℕ) (T : ℕ) (t : Fin T) : Fin K :=
  if t.val < m * K then
    ⟨t.val % K, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne K))⟩
  else
    B.optArm

/-- The number of elements `t` in a filter `{t : Fin T | t.val < m * K ∧ t.val % K = a.val}`
    is at most `m`. Each such `t` has the form `a.val + j * K` for a unique `j < m`,
    so the injection `t ↦ t / K` maps into `{0, ..., m-1}`. -/
private theorem card_filter_mod_le (T : ℕ) (m : ℕ) (a : Fin K) (_hle : m * K ≤ T) :
    ((Finset.univ : Finset (Fin T)).filter
      (fun t => t.val < m * K ∧ t.val % K = a.val)).card ≤ m := by
  by_cases hm0 : m = 0
  · simp only [hm0, Nat.zero_mul, Nat.not_lt_zero, false_and]
    simp only [Finset.filter_false]
    exact le_refl 0
  · have hK : 0 < K := Nat.pos_of_ne_zero (NeZero.ne K)
    -- Map the filtered set to Finset.range m via t ↦ t.val / K
    -- and show this map is injective on the filtered set.
    set S := (Finset.univ : Finset (Fin T)).filter
      (fun t => t.val < m * K ∧ t.val % K = a.val) with hS_def
    -- The image lands in Finset.range m
    have hmem : ∀ t ∈ S, t.val / K ∈ Finset.range m := by
      intro t ht
      simp only [hS_def, Finset.mem_filter, Finset.mem_univ, true_and] at ht
      rw [Finset.mem_range]
      rw [Nat.div_lt_iff_lt_mul hK]
      linarith [ht.1]
    -- The map is injective on S
    have hinj : Set.InjOn (fun t : Fin T => t.val / K) (↑S) := by
      intro t₁ ht₁ t₂ ht₂ heq
      simp only [hS_def, Finset.coe_filter,
        Finset.mem_univ, true_and, Set.mem_setOf_eq] at ht₁ ht₂
      have hdiv : t₁.val / K = t₂.val / K := heq
      ext
      calc t₁.val = K * (t₁.val / K) + t₁.val % K := (Nat.div_add_mod t₁.val K).symm
        _ = K * (t₂.val / K) + t₂.val % K := by rw [hdiv, ht₁.2, ht₂.2]
        _ = t₂.val := Nat.div_add_mod t₂.val K
    -- card S ≤ card (range m) = m
    calc S.card ≤ (Finset.range m).card :=
          Finset.card_le_card_of_injOn (fun t => t.val / K) hmem hinj
      _ = m := Finset.card_range m

/-- Bound on the sum of gaps over all T rounds for the ETC oracle ETC policy.
    The key insight: commit-phase contributes 0 (optimal arm), and
    exploration-phase contributes at most `m * Σ gap(a)` because each arm
    appears at most `m` times in round-robin. -/
private theorem etc_oracle_regret_le (m : ℕ) (T : ℕ) (hm_fit : m * K ≤ T) :
    ∑ t : Fin T, B.gap (B.etcOracleStrategy m T t) ≤
    ↑m * ∑ a : Fin K, B.gap a := by
  -- Step 1: Split into exploration + commit, show commit = 0
  suffices h : ∑ t : Fin T, B.gap (B.etcOracleStrategy m T t) =
      ∑ t ∈ Finset.univ.filter (fun t : Fin T => t.val < m * K),
        B.gap ⟨t.val % K, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne K))⟩ by
    rw [h]; clear h
    -- Step 2: Group by arm and bound
    -- Define the arm assignment function
    set f : Fin T → Fin K := fun t =>
      ⟨t.val % K, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne K))⟩ with hf_def
    set S := Finset.univ.filter (fun t : Fin T => t.val < m * K) with hS_def
    -- Group sum by arm
    have hfiber : ∑ t ∈ S, B.gap (f t) =
        ∑ a ∈ (Finset.univ : Finset (Fin K)),
          ∑ t ∈ S.filter (fun t => f t = a), B.gap (f t) :=
      (Finset.sum_fiberwise_of_maps_to (fun t _ => Finset.mem_univ (f t)) _).symm
    rw [hfiber]
    -- Each inner sum: terms = gap(a), count ≤ m
    calc ∑ a ∈ Finset.univ, ∑ t ∈ S.filter (fun t => f t = a), B.gap (f t)
        = ∑ a ∈ Finset.univ,
            ((S.filter (fun t => f t = a)).card : ℝ) * B.gap a := by
          apply Finset.sum_congr rfl; intro a _
          have : ∀ t ∈ S.filter (fun t => f t = a), B.gap (f t) = B.gap a := by
            intro t ht; rw [(Finset.mem_filter.mp ht).2]
          rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ a ∈ Finset.univ, (m : ℝ) * B.gap a := by
          apply Finset.sum_le_sum; intro a _
          apply mul_le_mul_of_nonneg_right _ (B.gap_nonneg a)
          -- Card bound: {t ∈ S | f t = a} ≤ m
          have hcard : (S.filter (fun t => f t = a)).card ≤ m := by
            apply le_trans _ (card_filter_mod_le T m a hm_fit)
            apply Finset.card_le_card
            intro t ht
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
            exact ⟨by rw [hS_def] at ht; exact (Finset.mem_filter.mp ht.1).2,
                   by rw [hf_def] at ht; exact Fin.val_eq_of_eq ht.2⟩
          exact_mod_cast hcard
      _ = ↑m * ∑ a ∈ Finset.univ, B.gap a := by rw [Finset.mul_sum]
      _ = ↑m * ∑ a : Fin K, B.gap a := rfl
  -- Prove Step 1: the total sum equals the exploration sum
  -- Split into two parts
  conv_lhs => rw [show ∑ t : Fin T, B.gap (B.etcOracleStrategy m T t) =
    ∑ t ∈ (Finset.univ : Finset (Fin T)), B.gap (B.etcOracleStrategy m T t) from rfl]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun t : Fin T => t.val < m * K)]
  -- Commit phase is 0
  have hcommit : ∑ t ∈ Finset.univ.filter (fun t : Fin T => ¬(t.val < m * K)),
      B.gap (B.etcOracleStrategy m T t) = 0 := by
    apply Finset.sum_eq_zero; intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at ht
    simp only [etcOracleStrategy, show ¬(t.val < m * K) from Nat.not_lt.mpr ht, ite_false]
    exact B.optArm_gap
  rw [hcommit, add_zero]
  -- Exploration phase: simplify strategy
  apply Finset.sum_congr rfl; intro t ht
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
  simp only [etcOracleStrategy, ht, ite_true]

/-- **Oracle ETC combinatorial upper bound** (deliberate oracle benchmark).

  For the oracle ETC strategy that round-robins for `m * K` steps and then
  commits to the true optimal arm, the pseudo-regret satisfies:
    R_T ≤ m · Σ_a Δ_a.

  This is a genuine combinatorial proof about the oracle witness itself.
  It is weaker than the standard ETC theorem because the commit phase uses the
  true best arm instead of the empirically best arm.

  **Design note**: this theorem is an intentional oracle benchmark, not a
  claimed formalization of the standard ETC algorithm. The standard ETC
  result (committing to the empirically best arm) requires concentration
  inequalities to bound the probability of misidentification; see LML's
  `etc_regret` for the measure-theoretic version. -/
theorem etc_oracle_regret_bound
    (T : ℕ) (_hT : K ≤ T)
    (δ : ℝ) (_hδ_pos : 0 < δ) (_hδ_le : δ ≤ 1)
    (m : ℕ) (_hm : 0 < m)
    -- m explorations per arm fit within T rounds
    (hm_fit : m * K ≤ T)
    -- Minimum gap among sub-optimal arms
    (Δ_min : ℝ) (_hΔ_min_pos : 0 < Δ_min)
    (_hΔ_min_le : ∀ a, B.gap a ≠ 0 → Δ_min ≤ B.gap a)
    -- Sufficient exploration: m ≥ (8/Δ_min²) ln(2K/δ)
    (_hm_suf : (8 / Δ_min ^ 2) * Real.log (2 * K / δ) ≤ m) :
    -- Conclusion: ∃ a strategy whose regret is bounded
    ∃ (I : Fin T → Fin K),
    B.pseudoRegret T I ≤ m * ∑ a : Fin K, B.gap a := by
  exact ⟨B.etcOracleStrategy m T, by
    rw [B.pseudoRegret_eq_sum_gap]
    exact B.etc_oracle_regret_le m T hm_fit⟩

/-! ### UCB Algorithm and Regret -/

-- [UNUSED]
/-- UCB index for arm `a` at round `t`:
    UCB_t(a) = μ̂_t(a) + √(2 ln(2TK/δ) / N_t(a)). -/
def ucbIndex (emp_mean_a : ℝ) (n_a : ℕ) (log_term : ℝ) : ℝ :=
  emp_mean_a + Real.sqrt (2 * log_term / max n_a 1)

/-- **UCB gap-dependent regret bound, deterministic core**.

  Given any strategy `I` and per-arm pull count bounds, the regret
  satisfies R_T ≤ Σ_a pullBound(a) * Δ_a. This is the deterministic
  core of the UCB analysis: the probabilistic part (showing UCB achieves
  the right pull counts under concentration) is separated out. -/
theorem ucb_regret_from_pull_count_bounds
    (T : ℕ) (I : Fin T → Fin K)
    (pullBound : Fin K → ℕ)
    (h_pull : ∀ a, (pullCount T I a : ℝ) ≤ pullBound a) :
    B.pseudoRegret T I ≤ ∑ a : Fin K, pullBound a * B.gap a := by
  rw [B.pseudoRegret_eq_sum_gap]
  -- Rewrite Σ_t gap(I(t)) by grouping over arms (fiberwise sum)
  have hfiber : ∑ t : Fin T, B.gap (I t) =
      ∑ a : Fin K, ∑ t ∈ Finset.univ.filter (fun t => I t = a), B.gap (I t) := by
    exact (Finset.sum_fiberwise_of_maps_to (fun t _ => Finset.mem_univ (I t)) _).symm
  rw [hfiber]
  apply Finset.sum_le_sum
  intro a _
  -- Each inner term equals gap(a) since I(t) = a on the fiber
  have : ∀ t ∈ Finset.univ.filter (fun t => I t = a), B.gap (I t) = B.gap a := by
    intro t ht
    rw [(Finset.mem_filter.mp ht).2]
  rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
  unfold pullCount at h_pull
  have hcard := h_pull a
  calc ((Finset.univ.filter fun t => I t = a).card : ℝ) * B.gap a
      ≤ ↑(pullBound a) * B.gap a :=
    mul_le_mul_of_nonneg_right hcard (B.gap_nonneg a)

/-- Each gap is at most 2, since all means lie in [-1, 1]. -/
private theorem gap_le_two (a : Fin K) : B.gap a ≤ 2 := by
  unfold gap optMean
  have ha := B.h_bounded a
  rw [abs_le] at ha
  have hopt : Finset.univ.sup' Finset.univ_nonempty B.mean ≤ 1 := by
    apply Finset.sup'_le
    intro b _
    exact (abs_le.mp (B.h_bounded b)).2
  linarith

/-- **Existential gap-dependent bound via the ETC oracle witness**.

  This theorem does not formalize UCB. It shows that the ETC oracle witness
  with `m = 1` satisfies a gap-dependent upper bound of the same coarse shape
  as the usual UCB statement. It is kept only as a benchmark warning example
  of a genuine theorem whose name should not overclaim algorithmic content. -/
theorem oracle_gap_bound_of_etc_witness
    (T : ℕ) (_hT : K ≤ T)
    (δ : ℝ) (_hδ_pos : 0 < δ) (_hδ_le : δ ≤ 1) :
    ∃ (I : Fin T → Fin K),
    B.pseudoRegret T I ≤
      ∑ a : Fin K,
        if B.gap a = 0 then 0
        else 8 * Real.log (2 * T * K / δ) / B.gap a + 2 * B.gap a := by
  -- Use ETC with m = 1: explore each arm once, then exploit optimal.
  -- The ETC(m=1) regret ≤ 1 * Σ gap(a) = Σ gap(a).
  -- Then show per-arm: gap(a) ≤ (if gap=0 then 0 else 8*log/gap + 2*gap).
  have hK_pos : 0 < K := Nat.pos_of_ne_zero (NeZero.ne K)
  have hm_fit : 1 * K ≤ T := by linarith [_hT]
  refine ⟨B.etcOracleStrategy 1 T, ?_⟩
  rw [B.pseudoRegret_eq_sum_gap]
  have hstep1 := B.etc_oracle_regret_le 1 T hm_fit
  simp only [Nat.cast_one, one_mul] at hstep1
  calc ∑ t : Fin T, B.gap (B.etcOracleStrategy 1 T t)
      ≤ ∑ a : Fin K, B.gap a := hstep1
    _ ≤ ∑ a : Fin K,
          if B.gap a = 0 then 0
          else 8 * Real.log (2 * T * K / δ) / B.gap a + 2 * B.gap a := by
        apply Finset.sum_le_sum; intro a _
        by_cases hga : B.gap a = 0
        · simp [hga]
        · rw [if_neg hga]
          -- Need: gap(a) ≤ 8*log(2TK/δ)/gap(a) + 2*gap(a)
          -- Equivalently: 0 ≤ 8*log(2TK/δ)/gap(a) + gap(a)
          -- Both terms are nonneg.
          have hga_pos : 0 < B.gap a := lt_of_le_of_ne (B.gap_nonneg a) (Ne.symm hga)
          -- log(2TK/δ) ≥ 0
          have hlog_nonneg : 0 ≤ Real.log (2 * ↑T * ↑K / δ) := by
            apply Real.log_nonneg
            rw [le_div_iff₀ _hδ_pos]
            have hT_pos : (1 : ℝ) ≤ ↑T := by
              exact_mod_cast le_trans hK_pos _hT
            have hK_real : (1 : ℝ) ≤ ↑K := by exact_mod_cast hK_pos
            calc 1 * δ = δ := one_mul δ
              _ ≤ 1 := _hδ_le
              _ = 2 * (1 / 2) := by ring
              _ ≤ 2 * (↑T * ↑K) := by
                  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
                  calc (1 : ℝ) / 2 ≤ 1 := by norm_num
                    _ = 1 * 1 := (one_mul 1).symm
                    _ ≤ ↑T * ↑K := mul_le_mul hT_pos hK_real (by linarith) (by linarith)
              _ = 2 * ↑T * ↑K := by ring
          linarith [div_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hlog_nonneg) hga_pos.le]

/-- **Existential worst-case bound via the ETC oracle witness**.

  This is the corresponding worst-case estimate obtained from the same oracle
  ETC witness used in `oracle_gap_bound_of_etc_witness`. It is not a UCB theorem. -/
theorem oracle_worst_case_bound_via_etc
    (T : ℕ) (_hT : K ≤ T)
    (δ : ℝ) (_hδ_pos : 0 < δ) (_hδ_le : δ ≤ 1) :
    ∃ (I : Fin T → Fin K),
    B.pseudoRegret T I ≤
      4 * Real.sqrt (K * T * Real.log (2 * T * K / δ)) + 2 * K := by
  -- Use ETC with m = 1: regret ≤ Σ gap(a) ≤ 2K ≤ 4√(KT·log) + 2K.
  have hK_pos : 0 < K := Nat.pos_of_ne_zero (NeZero.ne K)
  have hm_fit : 1 * K ≤ T := by linarith [_hT]
  refine ⟨B.etcOracleStrategy 1 T, ?_⟩
  rw [B.pseudoRegret_eq_sum_gap]
  have hstep1 := B.etc_oracle_regret_le 1 T hm_fit
  simp only [Nat.cast_one, one_mul] at hstep1
  calc ∑ t : Fin T, B.gap (B.etcOracleStrategy 1 T t)
      ≤ ∑ a : Fin K, B.gap a := hstep1
    _ ≤ ∑ _a : Fin K, (2 : ℝ) := by
        apply Finset.sum_le_sum; intro a _
        exact B.gap_le_two a
    _ = 2 * ↑K := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]
    _ ≤ 4 * Real.sqrt (↑K * ↑T * Real.log (2 * ↑T * ↑K / δ)) + 2 * ↑K := by
        linarith [Real.sqrt_nonneg (↑K * ↑T * Real.log (2 * ↑T * ↑K / δ))]

/-! ### UCB Pull-Count Analysis

  Key ingredients for the UCB gap-dependent regret bound:
  1. **Confidence threshold**: after O(log/Δ²) pulls, confidence width < Δ/2
  2. **Index domination**: under concentration, suboptimal arm's UCB ≤ μ*
  3. **Gap-dependent composition**: R_T ≤ ∑_{a:Δ>0} (8L/Δ + Δ)

  Together with the Hoeffding concentration in BanditConcentration.lean,
  these give the standard UCB gap-dependent regret decomposition target. -/

/-- **Confidence width threshold**: if `n ≥ 8·L/Δ²`, then `√(2L/n) ≤ Δ/2`.
    Once a suboptimal arm has been pulled O(log/Δ²) times, its confidence
    width shrinks below half its sub-optimality gap. -/
theorem confidence_threshold
    (L : ℝ) (Δ : ℝ) (hΔ : 0 < Δ)
    (n : ℕ) (hn : 1 ≤ n) (h_suf : 8 * L / Δ ^ 2 ≤ ↑n) :
    Real.sqrt (2 * L / ↑n) ≤ Δ / 2 := by
  have hΔ2 : (0 : ℝ) < Δ / 2 := by linarith
  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr (by omega)
  have hΔsq_pos : (0 : ℝ) < Δ ^ 2 := by positivity
  have h8L : 8 * L ≤ ↑n * Δ ^ 2 := (div_le_iff₀ hΔsq_pos).mp h_suf
  have h_key : 2 * L / ↑n ≤ (Δ / 2) ^ 2 := by
    rw [show (Δ / 2) ^ 2 = Δ ^ 2 / 4 from by ring]
    rw [div_le_div_iff₀ hn_pos (by norm_num : (0:ℝ) < 4)]
    linarith
  calc Real.sqrt (2 * L / ↑n)
      ≤ Real.sqrt ((Δ / 2) ^ 2) := Real.sqrt_le_sqrt h_key
    _ = |Δ / 2| := Real.sqrt_sq_eq_abs _
    _ = Δ / 2 := abs_of_pos hΔ2

/-- Under concentration, a sufficiently-explored suboptimal arm's UCB
    index is at most μ*: if |μ̂ − μ| ≤ w and Δ ≥ 2w, then μ̂ + w ≤ μ*. -/
theorem ucb_index_le_opt_mean
    (μ_hat μ_true μ_star w : ℝ)
    (h_conc : |μ_hat - μ_true| ≤ w)
    (h_gap : μ_star - μ_true ≥ 2 * w) :
    μ_hat + w ≤ μ_star := by
  have := (abs_le.mp h_conc).2; linarith

/-- Under concentration, the optimal arm's UCB index is at least μ*:
    if |μ̂* − μ*| ≤ w, then μ* ≤ μ̂* + w. -/
theorem ucb_index_opt_ge_opt_mean
    (μ_hat μ_star w : ℝ)
    (h_conc : |μ_hat - μ_star| ≤ w) :
    μ_star ≤ μ_hat + w := by
  have := (abs_le.mp h_conc).1; linarith

/-- **UCB gap-dependent regret bound**.

  Under the pull-count hypothesis—each suboptimal arm `a` has
  `pullCount(a) ≤ 8·L/Δ_a² + 1`—the pseudo-regret satisfies:
    R_T ≤ ∑_{a : Δ>0} (8·L/Δ_a + Δ_a).

  The pull-count hypothesis follows from `confidence_threshold`,
  `ucb_index_le_opt_mean`, and `ucb_index_opt_ge_opt_mean`:
  under the concentration event (Hoeffding, see `arm_mean_concentration`
  in BanditConcentration), once arm `a` has been pulled
  ⌈8·L/Δ_a²⌉ times, its confidence width drops below Δ_a/2, so
  its UCB index falls below the optimal arm's index.

  **Caveat**: The sequential UCB selection argument is not formalized;
  the pull-count hypothesis is taken as given. The algebraic
  composition is fully proved. -/
theorem ucb_gap_dependent_regret
    (T : ℕ) (I : Fin T → Fin K)
    (L : ℝ)
    (h_pull : ∀ a, B.gap a ≠ 0 →
      (pullCount T I a : ℝ) ≤ 8 * L / B.gap a ^ 2 + 1) :
    B.pseudoRegret T I ≤
    ∑ a : Fin K,
      if B.gap a = 0 then 0
      else 8 * L / B.gap a + B.gap a := by
  rw [B.pseudoRegret_eq_sum_gap]
  have hfiber : ∑ t : Fin T, B.gap (I t) =
      ∑ a : Fin K,
        ∑ t ∈ Finset.univ.filter (fun t => I t = a), B.gap (I t) :=
    (Finset.sum_fiberwise_of_maps_to (fun t _ => Finset.mem_univ (I t)) _).symm
  rw [hfiber]
  apply Finset.sum_le_sum; intro a _
  by_cases hga : B.gap a = 0
  · rw [if_pos hga]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    rw [ht]; exact hga
  · rw [if_neg hga]
    have hga_pos : 0 < B.gap a :=
      lt_of_le_of_ne (B.gap_nonneg a) (Ne.symm hga)
    have h_each : ∀ t ∈ Finset.univ.filter (fun t => I t = a),
        B.gap (I t) = B.gap a := by
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
      rw [ht]
    rw [Finset.sum_congr rfl h_each, Finset.sum_const, nsmul_eq_mul]
    have h_eq : (8 * L / B.gap a ^ 2 + 1) * B.gap a =
        8 * L / B.gap a + B.gap a := by field_simp [hga_pos.ne']
    calc ((Finset.univ.filter fun t => I t = a).card : ℝ) * B.gap a
        ≤ (8 * L / B.gap a ^ 2 + 1) * B.gap a :=
          mul_le_mul_of_nonneg_right (h_pull a hga) hga_pos.le
      _ = 8 * L / B.gap a + B.gap a := h_eq

/-! ### UCB Good-Event Framework

  The UCB algorithm's correctness relies on a "good event" where
  concentration holds for all arms simultaneously. Under this event,
  the UCB selection rule ensures suboptimal arms are pulled at most
  O(log(T)/Δ²) times.

  The key lemma is the contrapositive argument: if a suboptimal arm
  has been pulled ≥ 8L/Δ² times, its UCB index is below the optimal
  arm's UCB index, so UCB would not select it.

  This section formalizes the good event and the algebraic chain from
  the good event to the pull-count bound, then composes with the
  gap-dependent regret theorem. -/

/-- The UCB good event: concentration holds for all arms with confidence
    width parameter `L`. Under this event, for every arm `a` and every
    pull count `n ≥ 1`, `|μ̂(a,n) − μ(a)| ≤ √(2L/n)`. -/
def ucbGoodEvent (emp_errors : Fin K → ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ a : Fin K, ∀ n : ℕ, 1 ≤ n →
    |emp_errors a n| ≤ Real.sqrt (2 * L / ↑n)

/-- **Algebraic core of the pull-count argument.**

    Under the good event, once a suboptimal arm `a` has been pulled
    `n ≥ 8L/Δ²` times (with `n ≥ 1`), its UCB index falls below μ*.

    This is the key algebraic fact: `confidence_threshold` gives
    `√(2L/n) ≤ Δ/2`, then `ucb_index_le_opt_mean` gives
    `μ̂ + √(2L/n) ≤ μ*`.

    The full pull-count bound (`pullCount ≤ 8L/Δ² + 1`) additionally
    requires a sequential counting argument (showing that UCB's selection
    rule prevents further pulls once the index drops). That bookkeeping
    is taken as hypothesis in `ucb_gap_dependent_regret`. -/
theorem ucb_index_dominated_after_sufficient_pulls
    (L : ℝ) (_hL : 0 < L) (a : Fin K) (hga : B.gap a ≠ 0)
    (n : ℕ) (hn : 1 ≤ n) (h_suf : 8 * L / B.gap a ^ 2 ≤ ↑n)
    (μ_hat : ℝ) (h_conc : |μ_hat - B.mean a| ≤ Real.sqrt (2 * L / ↑n)) :
    μ_hat + Real.sqrt (2 * L / ↑n) ≤ B.optMean := by
  have hga_pos : 0 < B.gap a :=
    lt_of_le_of_ne (B.gap_nonneg a) (Ne.symm hga)
  have h_width : Real.sqrt (2 * L / ↑n) ≤ B.gap a / 2 :=
    confidence_threshold L (B.gap a) hga_pos n hn h_suf
  have h_gap_ge : B.optMean - B.mean a ≥ 2 * Real.sqrt (2 * L / ↑n) := by
    calc B.optMean - B.mean a = B.gap a := rfl
      _ = 2 * (B.gap a / 2) := by ring
      _ ≥ 2 * Real.sqrt (2 * L / ↑n) := by linarith
  exact ucb_index_le_opt_mean μ_hat (B.mean a) B.optMean
    (Real.sqrt (2 * L / ↑n)) h_conc h_gap_ge

/-- **UCB gap-dependent regret under the good event (conditional form).**

    If the pull-count bound holds (each suboptimal arm pulled at most
    `8L/Δ² + 1` times), the regret satisfies:
      R_T ≤ ∑_{a:Δ>0} (8L/Δ_a + Δ_a)

    The pull-count bound follows from `ucb_index_dominated_after_sufficient_pulls`
    via a sequential counting argument: once an arm's UCB index drops below μ*,
    UCB will never select it again (since the optimal arm's index ≥ μ* by
    `ucb_index_opt_ge_opt_mean`). The sequential bookkeeping is not formalized;
    the pull-count hypothesis bridges this gap. -/
theorem ucb_gap_dependent_regret_from_good_event
    (T : ℕ) (I : Fin T → Fin K)
    (L : ℝ) (_hL : 0 < L)
    -- Pull-count bound holds under the good event
    (h_pull_good : ∀ a, B.gap a ≠ 0 →
      (pullCount T I a : ℝ) ≤ 8 * L / B.gap a ^ 2 + 1) :
    B.pseudoRegret T I ≤
      ∑ a : Fin K,
        if B.gap a = 0 then 0
        else 8 * L / B.gap a + B.gap a :=
  B.ucb_gap_dependent_regret T I L h_pull_good

/-! ### UCB Pull-Count Bound via Counting Argument

  The key combinatorial lemma: if arm `a` cannot be selected at any
  round where its running pull count reaches `threshold`, then its
  total pull count is at most `threshold`.

  This is a pure combinatorial/counting argument on `Fin T → Fin K`,
  independent of probability or algorithm state. -/

/-- Running pull count: number of times arm `a` was selected in rounds
    before `t` (i.e., rounds `s` with `s.val < t`). -/
def runningPullCount (t : ℕ) (T : ℕ) (I : Fin T → Fin K) (a : Fin K) : ℕ :=
  (Finset.univ.filter (fun s : Fin T => s.val < t ∧ I s = a)).card

set_option linter.unusedSectionVars false in
/-- At round `t`, the running pull count plus the indicator of `I t = a`
    equals the running pull count at `t + 1`. -/
private theorem runningPullCount_step (T : ℕ) (I : Fin T → Fin K) (a : Fin K)
    (t : Fin T) :
    runningPullCount (t.val + 1) T I a =
    runningPullCount t.val T I a + if I t = a then 1 else 0 := by
  unfold runningPullCount
  -- Split: {s | s.val < t+1 ∧ I s = a} = {s | s.val < t ∧ I s = a} ∪ {t | I t = a}
  by_cases hit : I t = a
  · rw [if_pos hit]
    -- {s | s.val < t+1 ∧ I s = a} = {s | s.val < t ∧ I s = a} ∪ {t}
    have h_eq : Finset.univ.filter (fun s : Fin T => s.val < t.val + 1 ∧ I s = a) =
        (Finset.univ.filter (fun s : Fin T => s.val < t.val ∧ I s = a)) ∪ {t} := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
        Finset.mem_singleton]
      constructor
      · intro ⟨hlt, heq⟩
        by_cases hst : s = t
        · right; exact hst
        · left
          exact ⟨by omega, heq⟩
      · intro h
        cases h with
        | inl h => exact ⟨by omega, h.2⟩
        | inr h => rw [h]; exact ⟨by omega, hit⟩
    rw [h_eq]
    have h_disj : Disjoint (Finset.univ.filter (fun s : Fin T => s.val < t.val ∧ I s = a))
        {t} := by
      simp only [Finset.disjoint_singleton_right, Finset.mem_filter, Finset.mem_univ,
        true_and, not_and]
      intro h; omega
    rw [Finset.card_union_of_disjoint h_disj, Finset.card_singleton]
  · rw [if_neg hit, add_zero]
    congr 1
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro ⟨hlt, heq⟩
      constructor
      · by_contra hge
        push_neg at hge
        have : s = t := Fin.ext (by omega)
        rw [this] at heq; exact hit heq
      · exact heq
    · intro ⟨hlt, heq⟩
      exact ⟨by omega, heq⟩

set_option linter.unusedSectionVars false in
/-- The running pull count at T equals the total pull count. -/
private theorem runningPullCount_at_T (T : ℕ) (I : Fin T → Fin K) (a : Fin K) :
    runningPullCount T T I a = pullCount T I a := by
  unfold runningPullCount pullCount
  congr 1
  ext s
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro ⟨_, h⟩; exact h
  · intro h; exact ⟨s.isLt, h⟩

/-- **Pull-count bound from selection domination.**

    If at every round `t` where arm `a` has already been pulled
    `≥ threshold` times, the selection rule does NOT choose arm `a`,
    then the total pull count of arm `a` is at most `threshold`.

    Proof: The rounds where `I t = a` form a set S. After the first
    `threshold` elements of S (in chronological order), the running
    pull count reaches `threshold`, so by `h_not_selected`, no more
    selections occur. Therefore `|S| ≤ threshold`.

    This is a pure combinatorial argument — no probability, no
    algorithm state. -/
theorem pull_count_le_of_selection_domination
    (T : ℕ) (I : Fin T → Fin K) (a : Fin K)
    (threshold : ℕ)
    (h_not_selected : ∀ t : Fin T,
      threshold ≤ runningPullCount t.val T I a → I t ≠ a) :
    pullCount T I a ≤ threshold := by
  -- We prove: runningPullCount t T I a ≤ threshold for all t ≤ T,
  -- then specialize to t = T.
  suffices h : ∀ t : ℕ, t ≤ T → runningPullCount t T I a ≤ threshold by
    rw [← runningPullCount_at_T]
    exact h T (le_refl T)
  intro t ht
  induction t with
  | zero =>
    -- At t=0, no rounds have been played
    unfold runningPullCount
    simp only [Nat.not_lt_zero, false_and, Finset.filter_false, Finset.card_empty]
    exact Nat.zero_le _
  | succ n ih =>
    -- runningPullCount (n+1) = runningPullCount n + (if I ⟨n, _⟩ = a then 1 else 0)
    have hn_lt : n < T := by omega
    have ih' := ih (by omega)
    set t_fin : Fin T := ⟨n, hn_lt⟩ with ht_fin_def
    have h_eq : n + 1 = t_fin.val + 1 := rfl
    rw [h_eq, runningPullCount_step T I a t_fin]
    by_cases hit : I t_fin = a
    · -- If arm a was selected at round n, running count was < threshold
      -- (otherwise h_not_selected would prevent selection)
      rw [if_pos hit]
      by_contra h_gt
      push_neg at h_gt
      -- runningPullCount n + 1 > threshold means runningPullCount n ≥ threshold
      have h_ge : threshold ≤ runningPullCount t_fin.val T I a := by omega
      exact h_not_selected t_fin h_ge hit
    · rw [if_neg hit, add_zero]
      exact ih'

/-- **Strict UCB index domination after many pulls.**

    When `8L/Δ² < n` (strictly) and the concentration bound holds,
    the suboptimal arm's UCB index is **strictly** below μ*.

    This is the strict version of `ucb_index_dominated_after_sufficient_pulls`,
    needed for the counting argument (which requires strict inequality to
    resolve tie-breaking in the UCB selection rule).

    Proof: `8L < nΔ²` implies `2L/n < Δ²/4`, so `√(2L/n) < Δ/2` strictly.
    Then `μ̂ + √(2L/n) ≤ μ + 2√(2L/n) < μ + Δ = μ*`. -/
theorem ucb_index_strictly_dominated
    (L : ℝ) (_hL : 0 < L) (a : Fin K) (hga : B.gap a ≠ 0)
    (n : ℕ) (_hn : 1 ≤ n) (h_suf : 8 * L / B.gap a ^ 2 < ↑n)
    (μ_hat : ℝ) (h_conc : |μ_hat - B.mean a| ≤ Real.sqrt (2 * L / ↑n)) :
    μ_hat + Real.sqrt (2 * L / ↑n) < B.optMean := by
  have hga_pos : 0 < B.gap a :=
    lt_of_le_of_ne (B.gap_nonneg a) (Ne.symm hga)
  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr (by omega)
  have hΔsq_pos : (0 : ℝ) < B.gap a ^ 2 := by positivity
  -- 8L < n * Δ²
  have h8L : 8 * L < ↑n * B.gap a ^ 2 := (div_lt_iff₀ hΔsq_pos).mp h_suf
  -- 2L/n < Δ²/4
  have h_key : 2 * L / ↑n < (B.gap a / 2) ^ 2 := by
    rw [show (B.gap a / 2) ^ 2 = B.gap a ^ 2 / 4 from by ring]
    rw [div_lt_div_iff₀ hn_pos (by norm_num : (0:ℝ) < 4)]
    linarith
  -- √(2L/n) < Δ/2  (strict, from strict inequality on the argument)
  have h_sqrt : Real.sqrt (2 * L / ↑n) < B.gap a / 2 := by
    calc Real.sqrt (2 * L / ↑n)
        < Real.sqrt ((B.gap a / 2) ^ 2) :=
          Real.sqrt_lt_sqrt (by positivity) h_key
      _ = |B.gap a / 2| := Real.sqrt_sq_eq_abs _
      _ = B.gap a / 2 := abs_of_pos (by linarith)
  -- μ̂ ≤ μ + √(2L/n) from concentration
  have h_upper := (abs_le.mp h_conc).2
  -- Chain: μ̂ + √(2L/n) ≤ μ + 2√(2L/n) < μ + Δ = μ*
  have h_mean_gap : B.mean a + B.gap a = B.optMean := by unfold gap; ring
  linarith

/-- **Composed UCB gap-dependent regret under the good event.**

    Under the UCB selection rule with strict index domination after
    sufficient exploration, the regret satisfies:
      R_T ≤ ∑_{a:Δ>0} threshold(a) · Δ_a

    This composes `pull_count_le_of_selection_domination` (counting
    argument) with the fiberwise regret decomposition.

    The per-arm threshold can be instantiated as `⌈8L/Δ²⌉₊ + 1` using
    `ucb_index_strictly_dominated` to discharge the strict domination
    hypothesis under the good event. -/
theorem ucb_gap_dependent_regret_full
    (T : ℕ) (I : Fin T → Fin K)
    -- UCB index function
    (ucb_idx : Fin T → Fin K → ℝ)
    -- UCB selection rule: the played arm has maximal index
    (h_ucb_rule : ∀ t : Fin T, ∀ b : Fin K, ucb_idx t b ≤ ucb_idx t (I t))
    -- Optimal arm's index ≥ μ*
    (h_opt_index : ∀ t : Fin T, B.optMean ≤ ucb_idx t B.optArm)
    -- Per-arm thresholds
    (threshold : Fin K → ℕ)
    -- Strict domination: after threshold(a) pulls, suboptimal arm's index < μ*
    (h_dominated : ∀ a : Fin K, B.gap a ≠ 0 → ∀ t : Fin T,
      threshold a ≤ runningPullCount t.val T I a →
      ucb_idx t a < B.optMean) :
    B.pseudoRegret T I ≤
      ∑ a : Fin K,
        if B.gap a = 0 then 0
        else ↑(threshold a) * B.gap a := by
  rw [B.pseudoRegret_eq_sum_gap]
  have hfiber : ∑ t : Fin T, B.gap (I t) =
      ∑ a : Fin K,
        ∑ t ∈ Finset.univ.filter (fun t => I t = a), B.gap (I t) :=
    (Finset.sum_fiberwise_of_maps_to (fun t _ => Finset.mem_univ (I t)) _).symm
  rw [hfiber]
  apply Finset.sum_le_sum; intro a _
  by_cases hga : B.gap a = 0
  · -- Optimal arm: contribution = 0
    rw [if_pos hga]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    rw [ht]; exact hga
  · -- Suboptimal arm: pullCount ≤ threshold via counting argument
    rw [if_neg hga]
    have h_each : ∀ t ∈ Finset.univ.filter (fun t => I t = a),
        B.gap (I t) = B.gap a := by
      intro t ht; rw [(Finset.mem_filter.mp ht).2]
    rw [Finset.sum_congr rfl h_each, Finset.sum_const, nsmul_eq_mul]
    have hga_pos : 0 < B.gap a :=
      lt_of_le_of_ne (B.gap_nonneg a) (Ne.symm hga)
    apply mul_le_mul_of_nonneg_right _ hga_pos.le
    -- Key: pullCount a ≤ threshold a
    have h_pc : pullCount T I a ≤ threshold a := by
      apply pull_count_le_of_selection_domination
      intro t h_ge hit
      -- Strict domination: ucb_idx t a < μ*
      have h_strict := h_dominated a hga t h_ge
      -- UCB rule: ucb_idx t optArm ≤ ucb_idx t (I t)
      have h_sel := h_ucb_rule t B.optArm
      rw [hit] at h_sel
      -- ucb_idx t optArm ≤ ucb_idx t a < μ* ≤ ucb_idx t optArm : contradiction
      linarith [h_opt_index t]
    exact_mod_cast h_pc

/-- **UCB gap-dependent regret: clean presentation form.**

    Under the UCB selection rule and the good event (all arms
    concentrated with parameter `L`), the gap-dependent regret bound:

      R_T ≤ ∑_{a:Δ>0} (8L/Δ_a + 2Δ_a)

    This instantiates `ucb_gap_dependent_regret_full` with the
    canonical threshold `⌈8L/Δ²⌉₊ + 1` and simplifies using
    `⌈x⌉₊ · Δ ≤ (x + 1) · Δ` for `x ≥ 0`.

    The `2Δ` (vs a leaner asymptotic presentation using `Δ`) comes from the integer ceiling:
    we need a strictly-greater-than threshold for the counting argument,
    which adds one unit of `Δ` per arm. This is standard in formalized
    proofs of UCB (cf. Auer et al., 2002).

    **Probability guarantee** (not formalized in this file):
    Setting `L = log(2TK/δ)`, the good event holds with probability
    ≥ 1 − δ by Hoeffding's inequality (see `all_arms_concentration`
    in `BanditConcentration.lean`). -/
theorem ucb_gap_dependent_regret_presentation
    (T : ℕ) (I : Fin T → Fin K)
    (L : ℝ) (hL : 0 < L)
    -- UCB index function and selection rule
    (ucb_idx : Fin T → Fin K → ℝ)
    (h_ucb_rule : ∀ t : Fin T, ∀ b : Fin K, ucb_idx t b ≤ ucb_idx t (I t))
    (h_opt_index : ∀ t : Fin T, B.optMean ≤ ucb_idx t B.optArm)
    -- Good event: strict domination after ⌈8L/Δ²⌉₊ + 1 pulls
    (h_good : ∀ a : Fin K, B.gap a ≠ 0 → ∀ t : Fin T,
      ⌈8 * L / B.gap a ^ 2⌉₊ + 1 ≤ runningPullCount t.val T I a →
      ucb_idx t a < B.optMean) :
    B.pseudoRegret T I ≤
      ∑ a : Fin K,
        if B.gap a = 0 then 0
        else 8 * L / B.gap a + 2 * B.gap a := by
  -- Step 1: apply the full theorem with canonical thresholds
  have h_base := B.ucb_gap_dependent_regret_full T I ucb_idx h_ucb_rule h_opt_index
    (fun a => ⌈8 * L / B.gap a ^ 2⌉₊ + 1) h_good
  -- Step 2: simplify threshold(a) · Δ_a to 8L/Δ_a + 2Δ_a
  calc B.pseudoRegret T I
      ≤ ∑ a, if B.gap a = 0 then 0
          else ↑(⌈8 * L / B.gap a ^ 2⌉₊ + 1) * B.gap a := h_base
    _ ≤ ∑ a, if B.gap a = 0 then 0
          else 8 * L / B.gap a + 2 * B.gap a := by
        apply Finset.sum_le_sum; intro a _
        by_cases hga : B.gap a = 0
        · simp [hga]
        · rw [if_neg hga, if_neg hga]
          have hga_pos : 0 < B.gap a :=
            lt_of_le_of_ne (B.gap_nonneg a) (Ne.symm hga)
          -- ⌈8L/Δ²⌉₊ + 1 ≤ 8L/Δ² + 2 as reals, so product ≤ (8L/Δ² + 2)·Δ = 8L/Δ + 2Δ
          have hx_nonneg : 0 ≤ 8 * L / B.gap a ^ 2 := by positivity
          -- Key: ⌈x⌉₊ ≤ ⌊x⌋₊ + 1 ≤ x + 1  for x ≥ 0
          have h_ceil : (⌈8 * L / B.gap a ^ 2⌉₊ : ℝ) ≤ 8 * L / B.gap a ^ 2 + 1 := by
            have h1 : ⌈8 * L / B.gap a ^ 2⌉₊ ≤ ⌊8 * L / B.gap a ^ 2⌋₊ + 1 :=
              Nat.ceil_le_floor_add_one _
            calc (⌈8 * L / B.gap a ^ 2⌉₊ : ℝ)
                ≤ ↑(⌊8 * L / B.gap a ^ 2⌋₊ + 1) := by exact_mod_cast h1
              _ = ↑⌊8 * L / B.gap a ^ 2⌋₊ + 1 := by push_cast; ring
              _ ≤ 8 * L / B.gap a ^ 2 + 1 := by linarith [Nat.floor_le hx_nonneg]
          -- Now: (⌈x⌉₊ + 1) · Δ ≤ (x + 2) · Δ = xΔ + 2Δ
          have h_bound : (↑(⌈8 * L / B.gap a ^ 2⌉₊ + 1) : ℝ) * B.gap a ≤
              8 * L / B.gap a + 2 * B.gap a := by
            push_cast
            have h_rw : (8 * L / B.gap a ^ 2 + 2) * B.gap a =
                8 * L / B.gap a + 2 * B.gap a := by
              field_simp [hga_pos.ne']
            linarith [mul_le_mul_of_nonneg_right
              (show (↑⌈8 * L / B.gap a ^ 2⌉₊ + 1 : ℝ) ≤ 8 * L / B.gap a ^ 2 + 2 by
                linarith [h_ceil]) hga_pos.le]
          exact h_bound

/-! ### Worst-Case Conversion and Minimax Comparison

  The gap-dependent UCB bound R_T ≤ ∑_{a:Δ>0} (8L/Δ_a + 2Δ_a) is optimal
  when gaps are known, but for worst-case analysis we need a bound in terms
  of K, T, and L alone.

  The standard conversion splits arms at threshold ε = √(C/T):
  * Arms with Δ_a ≥ ε: use the gap-dependent bound, C/Δ + 2Δ ≤ √(CT) + 4.
  * Arms with 0 < Δ_a < ε: use the trivial bound, T·Δ < √(CT).

  Each arm contributes ≤ 2√(CT) + 4, summing to 2K√(CT) + 4K.
  With C = 8L and L = log(2TK/δ), this is O(K√(T·log(T))). -/

/-- **Worst-case conversion from gap-dependent regret.**

  If each suboptimal arm's regret contribution is at most
  `min(C/Δ_a + 2Δ_a, T·Δ_a)` (the minimum of the gap-dependent
  and trivial per-arm bounds), then R_T ≤ 2K·√(C·T) + 4K.

  The proof uses threshold splitting at ε = √(C/T):
  * Large-gap arms (Δ ≥ ε): `C/Δ + 2Δ ≤ √(CT) + 4`.
  * Small-gap arms (Δ < ε): `T·Δ ≤ √(CT)`.

  Both are ≤ 2√(CT) + 4, so summing over K arms gives the result.

  The `C` parameter is `8L` in the UCB application, where `L = log(2TK/δ)`. -/
theorem ucb_worst_case_from_gap_dependent
    (T : ℕ) (hT : 0 < T) (I : Fin T → Fin K)
    (C : ℝ) (hC : 0 ≤ C)
    -- Per-arm regret is bounded by min(gap-dependent, trivial)
    (h_regret_bound : B.pseudoRegret T I ≤
      ∑ a : Fin K,
        if B.gap a = 0 then 0
        else min (C / B.gap a + 2 * B.gap a) (↑T * B.gap a)) :
    B.pseudoRegret T I ≤ 2 * ↑K * Real.sqrt (C * ↑T) + 4 * ↑K := by
  have hT_pos : (0 : ℝ) < ↑T := Nat.cast_pos.mpr hT
  calc B.pseudoRegret T I
      ≤ ∑ a : Fin K,
          if B.gap a = 0 then 0
          else min (C / B.gap a + 2 * B.gap a) (↑T * B.gap a) := h_regret_bound
    _ ≤ ∑ _a : Fin K, (2 * Real.sqrt (C * ↑T) + 4) := by
        apply Finset.sum_le_sum; intro a _
        by_cases hga : B.gap a = 0
        · simp only [if_pos hga]; positivity
        · rw [if_neg hga]
          have hga_pos : 0 < B.gap a :=
            lt_of_le_of_ne (B.gap_nonneg a) (Ne.symm hga)
          by_cases hC0 : C = 0
          · -- C = 0: gap-dependent term is just 2Δ ≤ 4
            subst hC0
            simp only [zero_div, zero_mul, zero_add, Real.sqrt_zero, mul_zero]
            linarith [min_le_left (2 * B.gap a) (↑T * B.gap a), B.gap_le_two a]
          · have hC_pos : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
            by_cases hcase : C / ↑T ≤ B.gap a ^ 2
            · -- Large gap: C/Δ ≤ √(CT), 2Δ ≤ 4
              calc min (C / B.gap a + 2 * B.gap a) (↑T * B.gap a)
                  ≤ C / B.gap a + 2 * B.gap a := min_le_left _ _
                _ ≤ Real.sqrt (C * ↑T) + 2 * 2 := by
                    have h1 : C / B.gap a ≤ Real.sqrt (C * ↑T) := by
                      rw [div_le_iff₀ hga_pos]
                      have h_Csq : C ^ 2 ≤ C * ↑T * B.gap a ^ 2 := by
                        have h_Cle : C ≤ ↑T * B.gap a ^ 2 := by
                          have := (div_le_iff₀ hT_pos).mp hcase
                          linarith
                        nlinarith
                      calc C = Real.sqrt (C ^ 2) := (Real.sqrt_sq hC_pos.le).symm
                        _ ≤ Real.sqrt (C * ↑T * B.gap a ^ 2) :=
                            Real.sqrt_le_sqrt h_Csq
                        _ = Real.sqrt (C * ↑T) * Real.sqrt (B.gap a ^ 2) := by
                            rw [Real.sqrt_mul (by positivity)]
                        _ = Real.sqrt (C * ↑T) * |B.gap a| := by
                            rw [Real.sqrt_sq_eq_abs]
                        _ = Real.sqrt (C * ↑T) * B.gap a := by
                            rw [abs_of_pos hga_pos]
                    linarith [B.gap_le_two a]
                _ ≤ 2 * Real.sqrt (C * ↑T) + 4 := by
                    linarith [Real.sqrt_nonneg (C * ↑T)]
            · -- Small gap: TΔ ≤ √(CT)
              push_neg at hcase
              have h_TDsq : ↑T ^ 2 * B.gap a ^ 2 ≤ C * ↑T := by
                have h_lt : B.gap a ^ 2 * ↑T < C := by
                  rw [lt_div_iff₀ hT_pos] at hcase
                  linarith
                nlinarith
              calc min (C / B.gap a + 2 * B.gap a) (↑T * B.gap a)
                  ≤ ↑T * B.gap a := min_le_right _ _
                _ ≤ Real.sqrt (C * ↑T) := by
                    calc ↑T * B.gap a
                        = Real.sqrt (↑T ^ 2) * Real.sqrt (B.gap a ^ 2) := by
                          rw [Real.sqrt_sq hT_pos.le,
                              Real.sqrt_sq_eq_abs, abs_of_pos hga_pos]
                      _ = Real.sqrt (↑T ^ 2 * B.gap a ^ 2) := by
                          rw [← Real.sqrt_mul (by positivity)]
                      _ ≤ Real.sqrt (C * ↑T) :=
                          Real.sqrt_le_sqrt h_TDsq
                _ ≤ 2 * Real.sqrt (C * ↑T) + 4 := by
                    linarith [Real.sqrt_nonneg (C * ↑T)]
    _ = ↑K * (2 * Real.sqrt (C * ↑T) + 4) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = 2 * ↑K * Real.sqrt (C * ↑T) + 4 * ↑K := by ring

/-- **Complete UCB regret bound.**

  The UCB regret satisfies the minimum of the gap-dependent
  and worst-case forms:

    R_T ≤ min(∑_{a:Δ>0} (8L/Δ_a + 2Δ_a), 2K√(8LT) + 4K)

  This combines `ucb_gap_dependent_regret_presentation` (gap-dependent)
  with `ucb_worst_case_from_gap_dependent` (worst-case conversion).

  The hypotheses are those of the gap-dependent form: the UCB selection
  rule, the optimal-arm index lower bound, and the strict domination
  property under the good event. The trivial per-arm bound T·Δ_a
  is used for the worst-case conversion.

  With L = log(2TK/δ), the worst-case bound becomes O(K√(T·log(T))),
  which is sqrt(K) worse than the minimax-optimal O(sqrt(K*T*log T)).
  The extra sqrt(K) comes from the naive per-arm decomposition. -/
theorem ucb_regret_bound_complete
    (T : ℕ) (hT : 0 < T) (I : Fin T → Fin K)
    (L : ℝ) (hL : 0 < L)
    -- UCB index function and selection rule
    (ucb_idx : Fin T → Fin K → ℝ)
    (h_ucb_rule : ∀ t : Fin T, ∀ b : Fin K, ucb_idx t b ≤ ucb_idx t (I t))
    (h_opt_index : ∀ t : Fin T, B.optMean ≤ ucb_idx t B.optArm)
    -- Good event: strict domination after sufficient pulls
    (h_good : ∀ a : Fin K, B.gap a ≠ 0 → ∀ t : Fin T,
      ⌈8 * L / B.gap a ^ 2⌉₊ + 1 ≤ runningPullCount t.val T I a →
      ucb_idx t a < B.optMean)
    -- Trivial per-arm bound: each arm contributes at most T * Δ_a
    (h_trivial : ∀ a : Fin K, B.gap a ≠ 0 →
      ((Finset.univ.filter (fun t : Fin T => I t = a)).card : ℝ) * B.gap a ≤
        ↑T * B.gap a) :
    B.pseudoRegret T I ≤
      min (∑ a : Fin K,
            if B.gap a = 0 then 0
            else 8 * L / B.gap a + 2 * B.gap a)
          (2 * ↑K * Real.sqrt (8 * L * ↑T) + 4 * ↑K) := by
  -- First, establish the gap-dependent bound
  have h_gap_dep := B.ucb_gap_dependent_regret_presentation T I L hL
    ucb_idx h_ucb_rule h_opt_index h_good
  -- For the worst-case bound, we need the per-arm min bound
  have h_min_bound : B.pseudoRegret T I ≤
      ∑ a : Fin K,
        if B.gap a = 0 then 0
        else min (8 * L / B.gap a + 2 * B.gap a) (↑T * B.gap a) := by
    rw [B.pseudoRegret_eq_sum_gap]
    have hfiber : ∑ t : Fin T, B.gap (I t) =
        ∑ a : Fin K,
          ∑ t ∈ Finset.univ.filter (fun t => I t = a), B.gap (I t) :=
      (Finset.sum_fiberwise_of_maps_to (fun t _ => Finset.mem_univ (I t)) _).symm
    rw [hfiber]
    apply Finset.sum_le_sum; intro a _
    by_cases hga : B.gap a = 0
    · rw [if_pos hga]
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
      rw [ht]; exact hga
    · rw [if_neg hga]
      have hga_pos : 0 < B.gap a :=
        lt_of_le_of_ne (B.gap_nonneg a) (Ne.symm hga)
      have h_each : ∀ t ∈ Finset.univ.filter (fun t => I t = a),
          B.gap (I t) = B.gap a := by
        intro t ht; rw [(Finset.mem_filter.mp ht).2]
      rw [Finset.sum_congr rfl h_each, Finset.sum_const, nsmul_eq_mul]
      -- The per-arm contribution = count * Δ. Bound by min of two estimates.
      apply le_min
      · -- Gap-dependent: count * Δ ≤ (8L/Δ² + 1) * Δ = 8L/Δ + Δ ≤ 8L/Δ + 2Δ
        -- This follows from the pull-count bound in the full theorem
        -- Actually we need to re-derive the pull-count bound here
        have h_pc : pullCount T I a ≤ ⌈8 * L / B.gap a ^ 2⌉₊ + 1 := by
          apply pull_count_le_of_selection_domination
          intro t h_ge hit
          have h_strict := h_good a hga t h_ge
          have h_sel := h_ucb_rule t B.optArm
          rw [hit] at h_sel
          linarith [h_opt_index t]
        have h_ceil_bound : (↑(⌈8 * L / B.gap a ^ 2⌉₊ + 1) : ℝ) * B.gap a ≤
            8 * L / B.gap a + 2 * B.gap a := by
          push_cast
          have hx_nn : 0 ≤ 8 * L / B.gap a ^ 2 := by positivity
          have h_ceil : (⌈8 * L / B.gap a ^ 2⌉₊ : ℝ) ≤ 8 * L / B.gap a ^ 2 + 1 := by
            calc (⌈8 * L / B.gap a ^ 2⌉₊ : ℝ)
                ≤ ↑(⌊8 * L / B.gap a ^ 2⌋₊ + 1) := by exact_mod_cast Nat.ceil_le_floor_add_one _
              _ = ↑⌊8 * L / B.gap a ^ 2⌋₊ + 1 := by push_cast; ring
              _ ≤ 8 * L / B.gap a ^ 2 + 1 := by linarith [Nat.floor_le hx_nn]
          have : (8 * L / B.gap a ^ 2 + 2) * B.gap a =
              8 * L / B.gap a + 2 * B.gap a := by
            field_simp [hga_pos.ne']
          linarith [mul_le_mul_of_nonneg_right
            (show (↑⌈8 * L / B.gap a ^ 2⌉₊ + 1 : ℝ) ≤ 8 * L / B.gap a ^ 2 + 2 by
              linarith) hga_pos.le]
        unfold pullCount at h_pc
        calc ((Finset.univ.filter fun t => I t = a).card : ℝ) * B.gap a
            ≤ (↑(⌈8 * L / B.gap a ^ 2⌉₊ + 1) : ℝ) * B.gap a := by
              apply mul_le_mul_of_nonneg_right _ hga_pos.le
              exact_mod_cast h_pc
          _ ≤ 8 * L / B.gap a + 2 * B.gap a := h_ceil_bound
      · -- Trivial bound: count * Δ ≤ T * Δ
        exact h_trivial a hga
  -- Now get the worst-case bound
  have h_worst := B.ucb_worst_case_from_gap_dependent T hT I (8 * L) (by linarith) h_min_bound
  exact le_min h_gap_dep h_worst

omit [NeZero K] in
/-- **UCB matches the minimax lower bound up to logarithmic factors.**

  The UCB worst-case bound is O(K√(T·log(T))), while the minimax
  lower bound is Ω(√(K·T)). The ratio is at most
  K · √(log(T)) / √K = √K · √(log(T)).

  More precisely, for any `R_upper ≥ 0` bounding the UCB regret and
  any `R_lower ≥ 0` giving the minimax lower bound:
  * If `R_upper ≤ c_u · K · √(L · T)` (UCB worst case with L = log(T)),
  * and `R_lower ≥ c_l · √(K · T)`,
  * then `R_upper / R_lower ≤ (c_u / c_l) · √(K · L)`.

  This shows that UCB is within a √(K · log(T)) factor of optimal.
  The extra √K comes from the per-arm-to-global conversion; algorithms
  like MOSS or IMED close this gap. -/
theorem ucb_matches_lower_bound
    (R_upper R_lower : ℝ)
    (c_u c_l : ℝ) (hc_u : 0 ≤ c_u) (hc_l : 0 < c_l)
    (L : ℝ) (hL : 0 ≤ L)
    (hK_pos : 0 < K) (hT : ℕ) (hT_pos : 0 < hT)
    -- UCB worst-case bound
    (h_upper : R_upper ≤ c_u * ↑K * Real.sqrt (L * ↑hT))
    -- Minimax lower bound
    (h_lower : c_l * Real.sqrt (↑K * ↑hT) ≤ R_lower) :
    R_upper ≤ (c_u / c_l) * Real.sqrt (↑K * L) * R_lower := by
  have hK_real : (0 : ℝ) < ↑K := Nat.cast_pos.mpr hK_pos
  have hT_real : (0 : ℝ) < ↑hT := Nat.cast_pos.mpr hT_pos
  -- Key algebraic identity: K · √(LT) = √(KL) · √(KT)
  -- So c_u · K · √(LT) = c_u · √(KL) · √(KT) ≤ (c_u/c_l) · √(KL) · (c_l · √(KT))
  --                      ≤ (c_u/c_l) · √(KL) · R_lower
  -- Key identity: K · √(LT) = √(K²·LT) = √(KL·KT) = √(KL) · √(KT)
  have h_split : ↑K * Real.sqrt (L * ↑hT) =
      Real.sqrt (↑K * L) * Real.sqrt (↑K * ↑hT) := by
    have hK_sq : ↑K = Real.sqrt (↑K ^ 2) := (Real.sqrt_sq hK_real.le).symm
    calc ↑K * Real.sqrt (L * ↑hT)
        = Real.sqrt (↑K ^ 2) * Real.sqrt (L * ↑hT) := by rw [← hK_sq]
      _ = Real.sqrt (↑K ^ 2 * (L * ↑hT)) := by
          rw [← Real.sqrt_mul (by positivity : (0:ℝ) ≤ ↑K ^ 2)]
      _ = Real.sqrt (↑K * L * (↑K * ↑hT)) := by congr 1; ring
      _ = Real.sqrt (↑K * L) * Real.sqrt (↑K * ↑hT) := by
          rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ ↑K * L)]
  -- Rewrite upper bound: c_u · K · √(LT) = (c_u/c_l) · √(KL) · (c_l · √(KT))
  have h_rw : c_u * ↑K * Real.sqrt (L * ↑hT) =
      c_u / c_l * Real.sqrt (↑K * L) * (c_l * Real.sqrt (↑K * ↑hT)) := by
    rw [show c_u * ↑K * Real.sqrt (L * ↑hT) =
        c_u * (↑K * Real.sqrt (L * ↑hT)) from by ring, h_split]
    field_simp
  calc R_upper
      ≤ c_u * ↑K * Real.sqrt (L * ↑hT) := h_upper
    _ = c_u / c_l * Real.sqrt (↑K * L) * (c_l * Real.sqrt (↑K * ↑hT)) := h_rw
    _ ≤ c_u / c_l * Real.sqrt (↑K * L) * R_lower := by
        apply mul_le_mul_of_nonneg_left h_lower
        · exact mul_nonneg (div_nonneg hc_u hc_l.le) (Real.sqrt_nonneg _)

end BanditInstance

end
