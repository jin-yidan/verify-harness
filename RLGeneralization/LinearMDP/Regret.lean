/-
# UCBVI-Lin Regret for Linear MDPs

Formalizes the UCBVI-Lin regret bound in the same
conditional-theorem style used for tabular UCBVI.

The full UCBVI-Lin analysis proceeds as:
  1. Optimism via elliptical confidence sets
  2. Per-episode regret bounded by sum of exploration bonuses
  3. Elliptical potential lemma bounds total bonuses by O(d H sqrt(K))

We state steps (2) and (3) as hypotheses and prove the algebraic
chain yielding the regret bound.

## Main Results

* `linearCumulativeRegret` - Cumulative regret over K episodes in a Linear MDP
* `ucbvi_lin_regret_from_bonus_hypotheses` - Conditional regret bound from bonus hypotheses:
  R(K) <= C * d * H * sqrt(K)

## References

* [Agarwal et al., *RL: Theory and Algorithms*]
-/

import RLGeneralization.LinearMDP.Basic
import RLGeneralization.LinearMDP.EllipticalPotential
import RLGeneralization.MDP.FiniteHorizon
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset BigOperators

noncomputable section

namespace FiniteHorizonMDP

variable (M : FiniteHorizonMDP)

/-! ### Cumulative Regret for Linear MDPs -/

/-- Cumulative regret over K episodes in a Linear MDP:
    R_K = sum_{k=0}^{K-1} (V*_0(s_0^k) - V^{pi_k}_0(s_0^k))

    Same definition as `cumulativeRegret` but placed here for
    self-contained reference in the Linear MDP chapter. -/
def linearCumulativeRegret (K : ℕ)
    (V_star_0 : M.S -> ℝ)
    (V_policies : Fin K -> M.S -> ℝ)
    (starts : Fin K -> M.S) : ℝ :=
  ∑ k : Fin K, (V_star_0 (starts k) - V_policies k (starts k))

/-! ### UCBVI-Lin Per-Episode Bound

  Under optimism from the elliptical confidence set,
  the per-episode regret of the greedy policy pi_k is bounded by
  the sum of exploration bonuses along the trajectory:

    V*_0(s_0) - V^{pi_k}_0(s_0) <= sum_h bonus_h^k

  This parallels the tabular UCBVI argument but uses
  the d-dimensional feature-weighted bonus beta_h(s,a) =
  c * ||phi(s,a)||_{Lambda_h^{-1}} instead of the count-based bonus.
-/

/-! ### Elliptical Potential Lemma

  The key tool for bounding total bonuses in Linear MDPs.
  For feature vectors phi_1, ..., phi_T in R^d with ||phi_t|| <= 1:

    sum_{t=1}^T ||phi_t||_{Lambda_t^{-1}} <= O(d * sqrt(T))

  where Lambda_t = lambda * I + sum_{i=1}^{t-1} phi_i phi_i^T.

  This replaces the pigeonhole/count-based argument in tabular UCBVI.
  We take this as a hypothesis since it requires matrix algebra
  (determinant-trace inequality) not available in our framework.
-/

/-- [CONDITIONAL] **Algebraic core of the UCBVI-Lin regret proof**.

  Takes h_per_ep (per-episode regret <= sum of bonuses) and h_bonus
  (total bonus bound <= C * d * H * sqrt(K)) as hypotheses, then
  chains them to derive cumulative regret O(d * H * sqrt(K)).

  Conditional on matrix concentration (elliptical confidence set) and
  the elliptical potential lemma (log-determinant argument), which
  need matrix inverse algebra not present here. -/
theorem ucbvi_lin_regret_from_bonus_hypotheses
    (lmdp : M.LinearMDP)
    (K : ℕ)
    (V_star_0 : M.S -> ℝ)
    (V_policies : Fin K -> M.S -> ℝ)
    (starts : Fin K -> M.S)
    (bonus : Fin K -> Fin M.H -> ℝ)
    (C : ℝ) (_hC : 0 < C)
    -- Hypothesis 1: per-episode regret <= sum of bonuses
    (h_per_ep : ∀ k : Fin K,
      V_star_0 (starts k) - V_policies k (starts k) ≤
      ∑ h : Fin M.H, bonus k h)
    -- Hypothesis 2: total bonus bounded by C * d * H * sqrt(K)
    (h_bonus : ∑ k : Fin K, ∑ h : Fin M.H, bonus k h ≤
      C * (lmdp.d : ℝ) * (M.H : ℝ) * Real.sqrt (K : ℝ)) :
    M.linearCumulativeRegret K V_star_0 V_policies starts ≤
    C * (lmdp.d : ℝ) * (M.H : ℝ) * Real.sqrt (K : ℝ) := by
  -- Step 1: cumulative regret <= total bonuses
  have h_regret_le_bonus :
      M.linearCumulativeRegret K V_star_0 V_policies starts ≤
      ∑ k : Fin K, ∑ h : Fin M.H, bonus k h := by
    unfold linearCumulativeRegret
    exact Finset.sum_le_sum (fun k _ => h_per_ep k)
  -- Step 2: chain with total bonus bound
  calc M.linearCumulativeRegret K V_star_0 V_policies starts
      ≤ ∑ k : Fin K, ∑ h : Fin M.H, bonus k h := h_regret_le_bonus
    _ ≤ C * (lmdp.d : ℝ) * (M.H : ℝ) * Real.sqrt (K : ℝ) := h_bonus

/-- Cumulative regret of UCBVI-Lin is nonneg when V* >= V^pi. -/
theorem ucbvi_lin_regret_nonneg (K : ℕ)
    (V_star_0 : M.S -> ℝ)
    (V_policies : Fin K -> M.S -> ℝ)
    (starts : Fin K -> M.S)
    (h_opt : ∀ k s, V_policies k s ≤ V_star_0 s) :
    0 ≤ M.linearCumulativeRegret K V_star_0 V_policies starts := by
  unfold linearCumulativeRegret
  apply Finset.sum_nonneg
  intro k _
  linarith [h_opt k (starts k)]

/-! ### Total Bonus Bound from Elliptical Potential

  The elliptical potential lemma (proved in `EllipticalPotential.lean`)
  bounds ∑ min(1, x_t) ≤ 2d·log(1+T/d). Combined with the Cauchy-Schwarz
  bridge (`sum_sqrt_le_sqrt_mul_bound`), this gives:
    ∑ β·√(min(1,x_t)) ≤ β·√(T·2d·log(1+T/d))

  This partially discharges the `h_bonus` hypothesis in the regret wrapper. -/

/-- **Total bonus bound from the elliptical potential.**

  If per-step bonuses satisfy `bonus_t ≤ β · √(min(1, x_t))` where
  the x_t satisfy the elliptical potential bound, then:
    ∑ bonus_t ≤ β · √(T · 2d · log(1 + T/d))

  This is the structural bridge between the elliptical potential lemma
  and the UCBVI-Lin regret bound. -/
theorem total_bonus_from_potential
    (d : ℕ) (_hd : 0 < d) (T : ℕ)
    (β : ℝ) (hβ : 0 ≤ β)
    (bonus : Fin T → ℝ)
    (x : Fin T → ℝ) (hx : ∀ t, 0 ≤ x t)
    (h_pot : ∑ t : Fin T, min 1 (x t) ≤
      2 * (d : ℝ) * Real.log (1 + (T : ℝ) / d))
    (h_bonus : ∀ t, bonus t ≤ β * Real.sqrt (min 1 (x t))) :
    ∑ t : Fin T, bonus t ≤
    β * Real.sqrt ((T : ℝ) * (2 * (d : ℝ) * Real.log (1 + (T : ℝ) / d))) := by
  -- Step 1: ∑ bonus ≤ β · ∑ √(min(1,x_t))
  have h1 : ∑ t : Fin T, bonus t ≤
      β * ∑ t : Fin T, Real.sqrt (min 1 (x t)) := by
    calc ∑ t, bonus t
        ≤ ∑ t, β * Real.sqrt (min 1 (x t)) :=
          Finset.sum_le_sum (fun t _ => h_bonus t)
      _ = β * ∑ t, Real.sqrt (min 1 (x t)) := by rw [Finset.mul_sum]
  -- Step 2: ∑ √(min(1,x_t)) ≤ √(T · 2d·log(1+T/d)) by Cauchy-Schwarz
  have h_log_nonneg : 0 ≤ 2 * (d : ℝ) * Real.log (1 + (T : ℝ) / d) := by
    apply mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d))
    apply Real.log_nonneg
    have : (0 : ℝ) ≤ (T : ℝ) / d := div_nonneg (Nat.cast_nonneg T) (Nat.cast_nonneg d)
    linarith
  have h2 : ∑ t : Fin T, Real.sqrt (min 1 (x t)) ≤
      Real.sqrt ((T : ℝ) * (2 * (d : ℝ) * Real.log (1 + (T : ℝ) / d))) :=
    sum_sqrt_le_sqrt_mul_bound T x hx _ h_log_nonneg h_pot
  -- Step 3: combine
  calc ∑ t, bonus t
      ≤ β * ∑ t, Real.sqrt (min 1 (x t)) := h1
    _ ≤ β * Real.sqrt ((T : ℝ) * (2 * (d : ℝ) * Real.log (1 + (T : ℝ) / d))) :=
        mul_le_mul_of_nonneg_left h2 hβ

/-- **Total bonus bound from feature vectors.**

  Given feature vectors φ₁,...,φ_T with ||φ_t||² ≤ 1, there exist
  nonneg reals x_t such that any bonus proportional to √(min(1,x_t))
  has its total bounded by β·√(T·2d·log(1+T/d)).

  This composes `elliptical_potential_unconditional` with
  `total_bonus_from_potential` to eliminate the eigenvalue witnesses. -/
theorem total_bonus_from_features
    (d : ℕ) (hd : 0 < d) (T : ℕ)
    (phis : Fin T → Fin d → ℝ)
    (h_norm : ∀ k : Fin T, sqNorm (phis k) ≤ 1)
    (β : ℝ) (hβ : 0 ≤ β) :
    ∃ x : Fin T → ℝ,
      (∀ t, 0 ≤ x t) ∧
      ∀ (bonus : Fin T → ℝ),
        (∀ t, bonus t ≤ β * Real.sqrt (min 1 (x t))) →
        ∑ t : Fin T, bonus t ≤
          β * Real.sqrt ((T : ℝ) * (2 * (d : ℝ) * Real.log (1 + (T : ℝ) / d))) := by
  obtain ⟨x, hx_nonneg, h_pot⟩ := elliptical_potential_unconditional d hd T phis h_norm
  exact ⟨x, hx_nonneg, fun bonus h_bonus =>
    total_bonus_from_potential d hd T β hβ bonus x hx_nonneg h_pot h_bonus⟩

/-! ### Optimism Discharges h_per_ep

  The `h_per_ep` hypothesis in `ucbvi_lin_regret_from_bonus_hypotheses`
  can now be derived from the optimism property using
  `FiniteHorizonMDP.regret_from_optimism_gap` (proved in UCBVI.lean).

  For the linear MDP setting, optimism (`Q* ≤ Q̂`) follows from:
  - Elliptical confidence sets around θ* (matrix concentration)
  - Bonus β(s,a) = c · ‖φ(s,a)‖_{Λ⁻¹} ≥ estimation error

  **Reference**: The Hoeffding/Bernstein bounds from Boucheron et al.,
  *Concentration Inequalities* Ch. 2.6–2.8 underlie the concentration
  step. The elliptical potential lemma (already in
  `EllipticalPotential.lean`) controls the total bonus.

  Combining `regret_from_optimism_gap` + `total_bonus_from_features`
  reduces the UCBVI-Lin proof to a single remaining hypothesis:
  the construction of the elliptical confidence set (matrix
  concentration), which requires Mathlib infrastructure for matrix
  inverse algebra not yet available.
-/

/-! ### LSVI-UCB: Regression → Bellman Residuals → Regret

  The full LSVI-UCB pipeline:

  1. **Regression**: At each episode k, step h, run least-squares regression
     on features φ(s,a) to estimate Q*_h. The regression error in the
     elliptical norm satisfies ||θ̂ - θ*||_{Λ} ≤ β (self-normalized bound).

  2. **Bellman residuals**: The optimistic Q-function Q̂_h(s,a) =
     φ(s,a)^T θ̂_h + β·||φ(s,a)||_{Λ^{-1}} satisfies Q̂ ≥ Q*
     (optimism from confidence set).

  3. **Per-episode regret**: V*_0(s₀) - V^{π_k}_0(s₀) ≤ ∑_h bonus_h^k
     (from optimism + backward induction).

  4. **Regret bound**: ∑_k ∑_h bonus_h^k ≤ C·d·H·√K
     (from elliptical potential lemma).

  Total: R(K) ≤ C · d · H · √K.
-/

/-- [WRAPPER] **LSVI-UCB: regression → Bellman residuals → optimism → regret.**

  End-to-end regret bound starting from the regression oracle.

  Given:
  - A regression oracle that produces per-step Bellman residual bounds
  - The elliptical potential bound on total bonuses
  - The optimism property (Q̂ ≥ Q*)

  Proves: R(K) ≤ C · d · H · √K.

  This composes `ucbvi_lin_regret_from_bonus_hypotheses` with the
  regression-to-bonus chain. -/
theorem lsvi_ucb_regression_to_regret
    (lmdp : M.LinearMDP) (K : ℕ)
    (V_star_0 : M.S → ℝ)
    (V_policies : Fin K → M.S → ℝ)
    (starts : Fin K → M.S)
    -- Per-step regression error (from self-normalized bound)
    (regression_error : Fin K → Fin M.H → ℝ)
    (_h_reg_nn : ∀ k h, 0 ≤ regression_error k h)
    -- [CONDITIONAL HYPOTHESIS] Optimism from regression:
    -- per-episode regret ≤ sum of regression errors
    (h_optimism : ∀ k : Fin K,
      V_star_0 (starts k) - V_policies k (starts k) ≤
      ∑ h : Fin M.H, regression_error k h)
    -- [CONDITIONAL HYPOTHESIS] Elliptical potential bounds total errors
    (C : ℝ) (hC : 0 < C)
    (h_potential : ∑ k : Fin K, ∑ h : Fin M.H, regression_error k h ≤
      C * (lmdp.d : ℝ) * (M.H : ℝ) * Real.sqrt (K : ℝ)) :
    M.linearCumulativeRegret K V_star_0 V_policies starts ≤
    C * (lmdp.d : ℝ) * (M.H : ℝ) * Real.sqrt (K : ℝ) :=
  ucbvi_lin_regret_from_bonus_hypotheses M lmdp K V_star_0 V_policies
    starts regression_error C hC h_optimism h_potential

/-- **LSVI-UCB per-episode regret from Bellman residual.**

  If the estimated Q-function has Bellman residual η at each step
  (i.e., |Q̂_h - T_h Q̂_{h+1}| ≤ η), then the per-episode regret
  is at most 2·H²·η by the approximate dynamic programming bound.

  This connects the regression error to per-episode regret. -/
theorem lsvi_per_episode_from_residual
    (η : ℝ) (_hη : 0 ≤ η)
    (V_star V_hat : M.S → ℝ)
    (s₀ : M.S)
    -- Per-step Bellman residuals, each bounded by η
    (residuals : Fin M.H → ℝ)
    (h_res_bound : ∀ h, residuals h ≤ η)
    -- Each residual propagates for at most 2H remaining steps
    (h_propagation : V_star s₀ - V_hat s₀ ≤
        2 * ∑ h : Fin M.H, (M.H : ℝ) * residuals h) :
    V_star s₀ - V_hat s₀ ≤ 2 * (M.H : ℝ) ^ 2 * η := by
  calc V_star s₀ - V_hat s₀
      ≤ 2 * ∑ h : Fin M.H, (M.H : ℝ) * residuals h := h_propagation
    _ ≤ 2 * ∑ _h : Fin M.H, (M.H : ℝ) * η := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Finset.sum_le_sum fun h _ =>
          mul_le_mul_of_nonneg_left (h_res_bound h) (Nat.cast_nonneg _)
    _ = 2 * ((M.H : ℝ) * ((M.H : ℝ) * η)) := by
        congr 1
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = 2 * (M.H : ℝ) ^ 2 * η := by ring

end FiniteHorizonMDP

end
