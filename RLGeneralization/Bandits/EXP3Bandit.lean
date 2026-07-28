/-
# EXP3 Bandit: Importance-Weighted Exponential Weights

Extends the Hedge/EXP3 full-information analysis (in `EXP3.lean`) to the
actual bandit setting where only the loss of the chosen arm is observed.
The key idea is the importance-weighted (IW) loss estimator:

    l̃_t(a) = l_t(a) · 𝟙{a_t = a} / p_t(a)

which is unbiased but has higher variance, introducing an extra √K factor
in the regret bound compared to Hedge:

    E[Regret] ≤ O(√(K T log K))      (bandit EXP3)
    vs. Regret ≤ O(√(T log K))       (full-information Hedge)

## Main Definitions

* `BanditEXP3Config` — EXP3 bandit configuration with chosen arms and weights.
* `importanceWeightedLoss` — the IW estimator l̃_t(a).

## Main Results

* `iw_loss_unbiased` — Σ_{a'} p(a') · l̃_t(a)[a_t=a'] = l_t(a).
* `iw_loss_variance_bound` — E[l̃_t(a)²] ≤ 1 / p_t(a).
* `exp3_bandit_regret_bound` — Regret ≤ log(K)/η + η · Σ_t Σ_a p_t(a) · l̃_t(a)².
* `exp3_expected_regret` — E[Regret] ≤ log(K)/η + η·K·T.
* `exp3_optimized` — E[Regret] ≤ 2√(K T log K) with η = √(log K / (KT)).
* `exp3_vs_hedge` — The √K gap: √(KT log K) vs √(T log K).

## References

* [Auer, Cesa-Bianchi, Freund, Schapire, "The nonstochastic multiarmed bandit problem", 2002]
* [Agarwal et al., *RL: Theory and Algorithms*]
-/

import RLGeneralization.Bandits.EXP3

open Finset BigOperators Real

noncomputable section

/-! ### Bandit EXP3 Configuration -/

/-- Configuration for the EXP3 bandit algorithm.
    Unlike full-information Hedge, the learner only observes the loss of the
    arm actually played. The importance-weighted estimator compensates for
    partial feedback at the cost of increased variance. -/
structure BanditEXP3Config (K : ℕ) [NeZero K] (T : ℕ) where
  /-- The adversarial bandit instance (losses in [0,1]). -/
  bandit : AdversarialBanditInstance K T
  /-- Learning rate η > 0. -/
  η : ℝ
  /-- Learning rate is positive. -/
  hη_pos : 0 < η
  /-- Probability weights: p_t(a) forms a distribution over arms. -/
  weights : Fin T → Fin K → ℝ
  /-- Weights are nonneg. -/
  h_weights_nonneg : ∀ t a, 0 ≤ weights t a
  /-- Weights sum to 1. -/
  h_weights_sum : ∀ t, ∑ a : Fin K, weights t a = 1
  /-- The arm actually played in each round. -/
  chosen : Fin T → Fin K
  /-- Weights are strictly positive (needed for IW estimator to be well-defined).
      In EXP3, this is guaranteed by mixing with the uniform distribution. -/
  h_weights_pos : ∀ t a, 0 < weights t a

namespace BanditEXP3Config

variable {K : ℕ} [NeZero K] {T : ℕ}

/-! ### Importance-Weighted Loss Estimator -/

/-- Importance-weighted loss estimator:
    l̃_t(a) = l_t(a) · 𝟙{chosen_t = a} / p_t(a).
    Only the chosen arm contributes; the division by p_t(a) debiases. -/
def importanceWeightedLoss (cfg : BanditEXP3Config K T) (t : Fin T) (a : Fin K) : ℝ :=
  cfg.bandit.loss t a * (if cfg.chosen t = a then 1 else 0) / cfg.weights t a

/-- The IW loss is nonneg (since loss ≥ 0, indicator ≥ 0, weight > 0). -/
theorem iw_loss_nonneg (cfg : BanditEXP3Config K T) (t : Fin T) (a : Fin K) :
    0 ≤ cfg.importanceWeightedLoss t a := by
  unfold importanceWeightedLoss
  apply div_nonneg
  · apply mul_nonneg (cfg.bandit.h_loss_nonneg t a)
    split_ifs <;> linarith
  · exact le_of_lt (cfg.h_weights_pos t a)

/-! ### Unbiasedness of the IW Estimator -/

/-- The IW loss estimator is unbiased:
    Σ_{a'} p_t(a') · l̃_t(a)[chosen=a'] = l_t(a).

    When we take expectation over the random choice a_t ~ p_t,
    the importance weighting exactly cancels the selection bias:
    E_{a_t}[l̃_t(a)] = Σ_{a'} p(a') · l(a) · 𝟙{a'=a} / p(a) = l(a). -/
theorem iw_loss_unbiased (cfg : BanditEXP3Config K T) (t : Fin T) (a : Fin K) :
    ∑ a' : Fin K, cfg.weights t a' *
      (cfg.bandit.loss t a * (if a' = a then 1 else 0) / cfg.weights t a') =
    cfg.bandit.loss t a := by
  -- Only the term a' = a survives; the rest vanish due to the indicator.
  have h_split : ∑ a' : Fin K, cfg.weights t a' *
      (cfg.bandit.loss t a * (if a' = a then 1 else 0) / cfg.weights t a') =
    ∑ a' : Fin K, (if a' = a then cfg.bandit.loss t a else 0) := by
    apply Finset.sum_congr rfl
    intro a' _
    split_ifs with h
    · -- a' = a: p(a) * (l(a) * 1 / p(a)) = l(a)
      rw [mul_one]
      rw [mul_div_cancel₀ _ (ne_of_gt (cfg.h_weights_pos t a'))]
    · simp
  rw [h_split, Finset.sum_ite_eq' Finset.univ a (fun _ => cfg.bandit.loss t a)]
  simp

/-! ### Variance Bound for the IW Estimator -/

/-- The expected squared IW loss satisfies:
    Σ_{a'} p(a') · l̃_t(a)²[chosen=a'] ≤ 1 / p_t(a).

    Proof: the only nonzero term is a' = a, contributing
    p(a) · (l(a)/p(a))² = l(a)²/p(a) ≤ 1/p(a). -/
theorem iw_loss_variance_bound (cfg : BanditEXP3Config K T) (t : Fin T) (a : Fin K) :
    ∑ a' : Fin K, cfg.weights t a' *
      ((cfg.bandit.loss t a * (if a' = a then 1 else 0) / cfg.weights t a') ^ 2) ≤
    1 / cfg.weights t a := by
  -- Simplify: only a' = a contributes
  have h_split : ∑ a' : Fin K, cfg.weights t a' *
      ((cfg.bandit.loss t a * (if a' = a then 1 else 0) / cfg.weights t a') ^ 2) =
    ∑ a' : Fin K, (if a' = a then cfg.weights t a' *
      ((cfg.bandit.loss t a / cfg.weights t a') ^ 2) else 0) := by
    apply Finset.sum_congr rfl
    intro a' _
    split_ifs with h
    · congr 1; congr 1; rw [mul_one]
    · simp
  rw [h_split, Finset.sum_ite_eq' Finset.univ a]
  simp only [Finset.mem_univ, ↓reduceIte]
  -- Now we have: p(a) · (l(a)/p(a))² ≤ 1/p(a)
  -- i.e., l(a)² / p(a) ≤ 1 / p(a)
  have hp_pos := cfg.h_weights_pos t a
  have hp_ne : cfg.weights t a ≠ 0 := ne_of_gt hp_pos
  -- Rewrite p · (l/p)² = p · l²/p² = l²/p
  have key : cfg.weights t a * (cfg.bandit.loss t a / cfg.weights t a) ^ 2 =
      cfg.bandit.loss t a ^ 2 / cfg.weights t a := by
    rw [div_pow]
    field_simp
  rw [key]
  apply div_le_div_of_nonneg_right _ (le_of_lt hp_pos)
  -- l(a)² ≤ 1
  have h0 := cfg.bandit.h_loss_nonneg t a
  have h1 := cfg.bandit.h_loss_le_one t a
  nlinarith [sq_nonneg (cfg.bandit.loss t a), sq_nonneg (1 - cfg.bandit.loss t a)]

/-! ### Per-Round Variance Sum Bound

  Summing 1/p_t(a) over all arms:
  Σ_a p_t(a) · E[l̃_t(a)²] ≤ Σ_a p_t(a) · (1/p_t(a)) = K.
-/

/-- The sum of reciprocals of a probability distribution over Fin K equals K
    when all weights are equal (uniform), but in general Σ_a 1 = K. -/
theorem sum_one_eq_K (K : ℕ) [NeZero K] :
    ∑ _a : Fin K, (1 : ℝ) = (K : ℝ) := by
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- Key identity: Σ_a p(a) · (1/p(a)) = K when weights are a probability distribution.
    This is because each term p(a)/p(a) = 1 (when p(a) > 0). -/
theorem weighted_inverse_sum (cfg : BanditEXP3Config K T) (t : Fin T) :
    ∑ a : Fin K, cfg.weights t a * (1 / cfg.weights t a) = (K : ℝ) := by
  have : ∑ a : Fin K, cfg.weights t a * (1 / cfg.weights t a) =
      ∑ _a : Fin K, (1 : ℝ) := by
    apply Finset.sum_congr rfl
    intro a _
    rw [one_div, mul_inv_cancel₀ (ne_of_gt (cfg.h_weights_pos t a))]
  rw [this]
  exact sum_one_eq_K K

/-! ### Bandit Regret Bound (Potential-Function Argument)

  The EXP3 bandit regret bound follows the same potential-function structure
  as Hedge, but applied to the IW losses l̃_t instead of the true losses l_t.

  Regret ≤ log(K)/η + η · Σ_t Σ_a p_t(a) · l̃_t(a)²

  This is a conditional result: the potential-function telescoping is taken
  as a hypothesis, since it requires the same analytic machinery as Hedge
  (the exp inequality) applied to the IW losses.
-/

-- [UNUSED]
/-- Weighted IW loss: Σ_a p_t(a) · l̃_t(a). This equals the weighted true loss
    by unbiasedness. -/
def weightedIWLoss (cfg : BanditEXP3Config K T) (t : Fin T) : ℝ :=
  ∑ a : Fin K, cfg.weights t a * cfg.importanceWeightedLoss t a

/-- Weighted squared IW loss: Σ_a p_t(a) · l̃_t(a)². -/
def weightedSqIWLoss (cfg : BanditEXP3Config K T) (t : Fin T) : ℝ :=
  ∑ a : Fin K, cfg.weights t a * (cfg.importanceWeightedLoss t a) ^ 2

/-- The weighted squared IW loss is nonneg. -/
theorem weightedSqIWLoss_nonneg (cfg : BanditEXP3Config K T) (t : Fin T) :
    0 ≤ cfg.weightedSqIWLoss t := by
  unfold weightedSqIWLoss
  apply Finset.sum_nonneg
  intro a _
  apply mul_nonneg (le_of_lt (cfg.h_weights_pos t a))
  exact sq_nonneg _

/-- [WRAPPER] **EXP3 bandit regret bound (potential-function form)**.

  Returns h_potential directly. The potential-function telescoping
  (requiring exp(-x) ≤ 1-x+x² applied to importance-weighted losses)
  is taken as a hypothesis. Conclusion:
  Regret ≤ log(K)/η + η · Σ_t Σ_a p_t(a) · l̃_t(a)². -/
theorem exp3_bandit_regret_bound
    (cfg : BanditEXP3Config K T)
    (a_star : Fin K)
    -- Hypothesis: Potential-function telescoping for IW losses.
    -- Requires the exp(-x) ≤ 1-x+x² inequality applied to importance-weighted
    -- losses, combined with log-sum-exp telescoping (same structure as Hedge).
    (h_potential :
      cfg.bandit.regretAgainst cfg.weights a_star ≤
      Real.log K / cfg.η +
      cfg.η * ∑ t : Fin T, cfg.weightedSqIWLoss t) :
    cfg.bandit.regretAgainst cfg.weights a_star ≤
    Real.log K / cfg.η +
    cfg.η * ∑ t : Fin T, cfg.weightedSqIWLoss t :=
  h_potential

/-! ### Expected Regret Bound

  Taking expectations:
    E[Σ_t Σ_a p_t(a) · l̃_t(a)²] ≤ Σ_t Σ_a 1 = K · T

  because for each (t, a): E[p_t(a) · l̃_t(a)²] ≤ p_t(a) · (1/p_t(a)) = 1.

  Hence: E[Regret] ≤ log(K)/η + η · K · T.
-/

/-- [WRAPPER] **Weighted squared IW loss bound.**

    Returns h_iw_sq_bound directly. The bound Σ_a p_t(a) · l̃_t(a)² ≤ K
    requires expectation over the random arm choice a_t ~ p_t
    (measure-theoretic); taken as a hypothesis here. -/
theorem weightedSqIWLoss_le_K
    (cfg : BanditEXP3Config K T)
    (t : Fin T)
    -- Hypothesis: E_{a_t}[l̃_t(a)²] ≤ 1/p_t(a) implies Σ_a p_t(a)·E[l̃_t(a)²] ≤ K.
    -- Requires measure-theoretic integration over the random arm choice a_t ∼ p_t.
    (h_iw_sq_bound : cfg.weightedSqIWLoss t ≤ K) :
    cfg.weightedSqIWLoss t ≤ (K : ℝ) :=
  h_iw_sq_bound

/-- [WRAPPER] **EXP3 expected regret bound**.

  Takes h_potential (potential-function bound) and h_iw_sq_per_round
  (per-round IW variance bound) as hypotheses, then chains them
  algebraically to derive: E[Regret] ≤ log(K)/η + η · K · T.

  The extra factor of K (compared to Hedge's bound of log(K)/η + η·T)
  arises because IW squared losses sum to K per round instead of 1. -/
theorem exp3_expected_regret
    {K : ℕ} [NeZero K] {T : ℕ}
    (cfg : BanditEXP3Config K T)
    (a_star : Fin K)
    -- Hypothesis: potential-function bound (see exp3_bandit_regret_bound)
    (h_potential :
      cfg.bandit.regretAgainst cfg.weights a_star ≤
      Real.log K / cfg.η +
      cfg.η * ∑ t : Fin T, cfg.weightedSqIWLoss t)
    -- Hypothesis: per-round IW variance bound (see weightedSqIWLoss_le_K)
    (h_iw_sq_per_round : ∀ t, cfg.weightedSqIWLoss t ≤ K) :
    cfg.bandit.regretAgainst cfg.weights a_star ≤
    Real.log K / cfg.η + cfg.η * (K * T) := by
  have hη_pos := cfg.hη_pos
  have h_sum_le : ∑ t : Fin T, cfg.weightedSqIWLoss t ≤ ∑ _t : Fin T, (K : ℝ) :=
    Finset.sum_le_sum (fun t _ => h_iw_sq_per_round t)
  have h_sum_eq : ∑ _t : Fin T, (K : ℝ) = (K : ℝ) * (T : ℝ) := by
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]
  calc cfg.bandit.regretAgainst cfg.weights a_star
      ≤ Real.log ↑K / cfg.η + cfg.η * ∑ t : Fin T, cfg.weightedSqIWLoss t :=
        h_potential
    _ ≤ Real.log ↑K / cfg.η + cfg.η * (↑K * ↑T) := by
        have : cfg.η * ∑ t : Fin T, cfg.weightedSqIWLoss t ≤ cfg.η * (↑K * ↑T) := by
          apply mul_le_mul_of_nonneg_left _ hη_pos.le
          linarith
        linarith

/-! ### Optimized Learning Rate for EXP3

  Setting η = √(log(K) / (K·T)) minimizes the bound log(K)/η + η·K·T.
  The minimum value is 2·√(K·T·log K).
-/

/-- **Optimized EXP3 bandit regret bound**.

  With learning rate η = √(log(K) / (K·T)), the expected regret satisfies:

    E[Regret] ≤ 2 · √(K · T · log K)

  This is the standard EXP3 regret rate for adversarial bandits. -/
theorem exp3_optimized
    {K : ℕ} [NeZero K] {T : ℕ}
    (hK : 2 ≤ K)
    (hT : 0 < T)
    (cfg : BanditEXP3Config K T)
    (a_star : Fin K)
    -- Hypothesis: expected regret bound (output of exp3_expected_regret)
    (h_regret : cfg.bandit.regretAgainst cfg.weights a_star ≤
      Real.log K / cfg.η + cfg.η * (K * T))
    (hη_opt : cfg.η = Real.sqrt (Real.log K / (K * T))) :
    cfg.bandit.regretAgainst cfg.weights a_star ≤
    2 * Real.sqrt (K * T * Real.log K) := by
  have hK_pos : (0 : ℝ) < (K : ℝ) := Nat.cast_pos.mpr (by omega)
  have hK_real : (1 : ℝ) < (K : ℝ) := by exact_mod_cast (show 1 < K by omega)
  have hlogK_pos : 0 < Real.log (K : ℝ) := Real.log_pos hK_real
  have hT_pos : (0 : ℝ) < (T : ℝ) := Nat.cast_pos.mpr hT
  have hKT_pos : (0 : ℝ) < (K : ℝ) * (T : ℝ) := mul_pos hK_pos hT_pos
  -- The bound log(K)/η + η·(K·T) has the form c/η + η·D with c = log K, D = K·T
  -- Minimized at η = √(c/D) giving value 2·√(c·D) = 2·√(K·T·log K)
  calc cfg.bandit.regretAgainst cfg.weights a_star
      ≤ Real.log ↑K / cfg.η + cfg.η * (↑K * ↑T) := h_regret
    _ = 2 * Real.sqrt (Real.log ↑K * (↑K * ↑T)) :=
        opt_learning_rate_value (Real.log K) hlogK_pos (↑K * ↑T) hKT_pos cfg.η hη_opt
    _ = 2 * Real.sqrt (↑K * ↑T * Real.log ↑K) := by ring_nf

/-! ### Comparison: EXP3 Bandit vs. Hedge (Full Information)

  The √K gap between bandit and full-information settings:
  - Hedge (full info):  Regret ≤ 2√(T · log K)
  - EXP3 (bandit):      E[Regret] ≤ 2√(K · T · log K)

  The ratio is √K, which is the "price of bandit feedback":
  observing only one arm's loss (instead of all K) costs a √K factor.
-/

/-- **The price of bandit feedback**: √(K·T·log K) ≥ √(T·log K).

  The EXP3 bandit bound has an extra √K factor compared to Hedge,
  reflecting the information loss from observing only the chosen arm. -/
theorem exp3_vs_hedge
    (K : ℕ) (hK : 2 ≤ K) (T : ℕ) :
    Real.sqrt (T * Real.log K) ≤ Real.sqrt (K * T * Real.log K) := by
  apply Real.sqrt_le_sqrt
  calc (T : ℝ) * Real.log ↑K
      = 1 * ((T : ℝ) * Real.log ↑K) := by ring
    _ ≤ (K : ℝ) * ((T : ℝ) * Real.log ↑K) := by
        gcongr
        exact_mod_cast (show 1 ≤ K by omega)
    _ = ↑K * ↑T * Real.log ↑K := by ring

/-- **Tight comparison**: The ratio of bandit to full-info regret bounds
    is exactly √K, i.e., 2√(KT log K) = √K · 2√(T log K).
    This algebraic identity confirms that the extra factor is precisely √K. -/
theorem exp3_bandit_hedge_ratio
    (K : ℕ) (_hK : 2 ≤ K) (T : ℕ) (_hT : 0 < T) :
    2 * Real.sqrt (K * T * Real.log K) =
    Real.sqrt K * (2 * Real.sqrt (T * Real.log K)) := by
  rw [show (K : ℝ) * ↑T * Real.log ↑K = ↑K * (↑T * Real.log ↑K) from by ring]
  rw [Real.sqrt_mul (Nat.cast_nonneg K)]
  ring

/-! ### Near-Minimax Optimality

  The minimax regret for K-armed adversarial bandits is Θ(√(KT)).
  The EXP3 bound 2√(KT log K) exceeds this by a √(log K) factor.
  EXP3.P or EXP3-IX variants are known to close this gap.
-/

/-- EXP3's bound 2√(KT log K) ≤ 2√(K²T) = 2K√T, showing it is at most
    quadratic in K. This is a coarse bound but confirms polynomial rates. -/
theorem exp3_bound_le_coarse
    (K : ℕ) (_hK : 2 ≤ K) (T : ℕ) (_hT : 0 < T) :
    2 * Real.sqrt (K * T * Real.log K) ≤ 2 * Real.sqrt (K * T * K) := by
  gcongr
  exact Real.log_le_self (le_of_lt (Nat.cast_pos.mpr (by omega : 0 < K)))

end BanditEXP3Config

end
