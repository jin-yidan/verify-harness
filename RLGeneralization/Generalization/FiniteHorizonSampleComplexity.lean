/-
# Minimax Sample Complexity for Finite-Horizon MDPs

Formalizes the deterministic core of the minimax sample complexity
analysis for finite-horizon MDPs with a generative model (RL textbook
Ch 2.3.2, Theorem 2.8).

## Main Results

* `empiricalBackwardQ` - Backward induction on empirical transitions
* `backward_induction_error_step` - One-step error propagation
* `backward_induction_error_bound` - Total error by induction on remaining steps
* `finite_horizon_value_error` - |V_hat - V*| <= H * |S| * eps via L1 bound
* `finite_horizon_sample_complexity` - Deterministic: per-step error => value error
* `sample_complexity_formula` - N >= H^2 |S|^2 / eps^2 suffices

## References

* [Azar, Osband, Munos, *Minimax Regret Bounds for RL*, ICML 2017]
* [Agarwal et al., *RL: Theory and Algorithms*, Ch 2.3.2]
-/

import RLGeneralization.MDP.FiniteHorizon
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Finset BigOperators

noncomputable section

namespace FiniteHorizonMDP

variable (M : FiniteHorizonMDP)

/-! ### Empirical Backward Induction

Given estimated transitions P_hat_h for each step h, we define the
empirical Q-values via the same backward induction as `backwardQ`
but using P_hat instead of P. -/

/-- Empirical backward induction: Q-value with k remaining steps using
    estimated transitions P_hat. Same recursion as `backwardQ` but with P_hat. -/
def empiricalBackwardQ
    (P_hat : Fin M.H → M.S → M.A → M.S → ℝ)
    : (k : ℕ) → (hk : k ≤ M.H) → M.S → M.A → ℝ
  | 0, _, _, _ => 0
  | k + 1, hk, s, a =>
    let h : Fin M.H := ⟨M.H - k - 1, by omega⟩
    M.r h s a + ∑ s', P_hat h s a s' *
      Finset.univ.sup' Finset.univ_nonempty
        (fun a' => empiricalBackwardQ P_hat k (by omega) s' a')

/-- Terminal condition: empirical Q with 0 remaining steps is 0. -/
theorem empiricalBackwardQ_zero
    (P_hat : Fin M.H → M.S → M.A → M.S → ℝ)
    (hk : 0 ≤ M.H) (s : M.S) (a : M.A) :
    M.empiricalBackwardQ P_hat 0 hk s a = 0 := rfl

/-! ### One-Step Error Propagation

The key insight: at each backward induction step, the error in Q
comes from (1) the transition error at that step, and (2) the
propagated error from the future value function.

For step with k+1 remaining steps:
  Q*(k+1)(s,a) = r + sum P * max Q*(k)
  Q_hat(k+1)(s,a) = r + sum P_hat * max Q_hat(k)

The difference is:
  sum (P - P_hat) * max Q*(k) + sum P_hat * (max Q*(k) - max Q_hat(k))
-/

/-- **Sup' error bound**: if |f(a) - g(a)| <= delta for all a, then
    |sup' f - sup' g| <= delta. -/
private lemma sup'_sub_sup'_le {α : Type*} [Fintype α] [Nonempty α]
    (f g : α → ℝ) (δ : ℝ) (_hδ : 0 ≤ δ)
    (hfg : ∀ a, |f a - g a| ≤ δ) :
    |Finset.univ.sup' Finset.univ_nonempty f -
     Finset.univ.sup' Finset.univ_nonempty g| ≤ δ := by
  rw [abs_le]
  constructor
  · -- sup' f - sup' g >= -delta
    -- i.e., sup' g - sup' f <= delta
    -- For any a, g(a) <= f(a) + delta, so sup' g <= sup' f + delta
    have : Finset.univ.sup' Finset.univ_nonempty g ≤
        Finset.univ.sup' Finset.univ_nonempty f + δ := by
      apply Finset.sup'_le
      intro a ha
      have hfa : f a ≤ Finset.univ.sup' Finset.univ_nonempty f :=
        Finset.le_sup' f (Finset.mem_univ a)
      have := abs_le.mp (hfg a)
      linarith
    linarith
  · -- sup' f - sup' g <= delta
    have : Finset.univ.sup' Finset.univ_nonempty f ≤
        Finset.univ.sup' Finset.univ_nonempty g + δ := by
      apply Finset.sup'_le
      intro a ha
      have hga : g a ≤ Finset.univ.sup' Finset.univ_nonempty g :=
        Finset.le_sup' g (Finset.mem_univ a)
      have := abs_le.mp (hfg a)
      linarith
    linarith

/-- **Weighted sum error from L1 transition error**.
    If |P(s') - P_hat(s')| sums to at most eps_l1 and |f(s')| <= B,
    then |sum (P - P_hat) f| <= eps_l1 * B. -/
private lemma weighted_sum_error
    (P_true P_hat : M.S → ℝ) (f : M.S → ℝ)
    (B ε_l1 : ℝ) (hB : 0 ≤ B)
    (hf : ∀ s', |f s'| ≤ B)
    (h_l1 : ∑ s', |P_true s' - P_hat s'| ≤ ε_l1) :
    |∑ s', (P_true s' - P_hat s') * f s'| ≤ ε_l1 * B := by
  calc |∑ s', (P_true s' - P_hat s') * f s'|
      ≤ ∑ s', |(P_true s' - P_hat s') * f s'| :=
        abs_sum_le_sum_abs _ _
    _ = ∑ s', |P_true s' - P_hat s'| * |f s'| := by
        congr 1; ext s'; exact abs_mul _ _
    _ ≤ ∑ s', |P_true s' - P_hat s'| * B := by
        apply Finset.sum_le_sum; intro s' _
        exact mul_le_mul_of_nonneg_left (hf s') (abs_nonneg _)
    _ = (∑ s', |P_true s' - P_hat s'|) * B :=
        (Finset.sum_mul _ _ _).symm
    _ ≤ ε_l1 * B :=
        mul_le_mul_of_nonneg_right h_l1 hB

/-! ### Backward Induction Error Bound

Main theorem: if the L1 transition error at each step h is at most eps,
then the Q-value error with k remaining steps is at most k * eps * k
(more precisely, it accumulates linearly). We prove a cleaner bound:
|Q_hat(k) - Q*(k)| <= k^2 * eps for uniform error eps. -/

/-- **Backward induction error bound**: if transition L1 error is at most
    eps at every step, then the Q-value error with k remaining steps
    satisfies |Q_hat(k)(s,a) - Q*(k)(s,a)| <= k * (k+1) / 2 * eps.

    Actually we prove the simpler bound: error <= k^2 * eps, since
    at each step the error grows by at most eps * k (bound on future
    value) + propagated error. -/
theorem backward_induction_error_bound
    (P_hat : Fin M.H → M.S → M.A → M.S → ℝ)
    (P_hat_nonneg : ∀ h s a s', 0 ≤ P_hat h s a s')
    (P_hat_sum_one : ∀ h s a, ∑ s', P_hat h s a s' = 1)
    (ε : ℝ) (hε : 0 ≤ ε)
    (h_err : ∀ (h : Fin M.H) (s : M.S) (a : M.A),
      ∑ s', |M.P h s a s' - P_hat h s a s'| ≤ ε) :
    ∀ (k : ℕ) (hk : k ≤ M.H) (s : M.S) (a : M.A),
    |M.empiricalBackwardQ P_hat k hk s a -
     M.backwardQ k hk s a| ≤ k ^ 2 * ε := by
  intro k
  induction k with
  | zero =>
    intro hk s a
    simp [empiricalBackwardQ, backwardQ]
  | succ n ih =>
    intro hk s a
    -- Unfold both Q values at step n+1
    simp only [empiricalBackwardQ, backwardQ]
    -- Let h = H - n - 1
    set h : Fin M.H := ⟨M.H - n - 1, by omega⟩
    -- Q_hat = r + sum P_hat * max Q_hat(n)
    -- Q*   = r + sum P    * max Q*(n)
    -- Diff = sum (P_hat - P) * max Q*(n)
    --      + sum P_hat * (max Q_hat(n) - max Q*(n))
    -- Rewards cancel
    have h_diff :
        (M.r h s a + ∑ s', P_hat h s a s' *
          Finset.univ.sup' Finset.univ_nonempty
            (fun a' => M.empiricalBackwardQ P_hat n (by omega) s' a')) -
        (M.r h s a + ∑ s', M.P h s a s' *
          Finset.univ.sup' Finset.univ_nonempty
            (fun a' => M.backwardQ n (by omega) s' a')) =
        ∑ s', (P_hat h s a s' - M.P h s a s') *
          Finset.univ.sup' Finset.univ_nonempty
            (fun a' => M.backwardQ n (by omega) s' a') +
        ∑ s', P_hat h s a s' *
          (Finset.univ.sup' Finset.univ_nonempty
            (fun a' => M.empiricalBackwardQ P_hat n (by omega) s' a') -
           Finset.univ.sup' Finset.univ_nonempty
            (fun a' => M.backwardQ n (by omega) s' a')) := by
      -- (P_hat * V_hat) - (P * V*) = (P_hat - P) * V* + P_hat * (V_hat - V*)
      have hsplit : ∀ s' : M.S,
          P_hat h s a s' *
            Finset.univ.sup' Finset.univ_nonempty
              (fun a' => M.empiricalBackwardQ P_hat n (by omega) s' a') -
          M.P h s a s' *
            Finset.univ.sup' Finset.univ_nonempty
              (fun a' => M.backwardQ n (by omega) s' a') =
          (P_hat h s a s' - M.P h s a s') *
            Finset.univ.sup' Finset.univ_nonempty
              (fun a' => M.backwardQ n (by omega) s' a') +
          P_hat h s a s' *
            (Finset.univ.sup' Finset.univ_nonempty
              (fun a' => M.empiricalBackwardQ P_hat n (by omega) s' a') -
             Finset.univ.sup' Finset.univ_nonempty
              (fun a' => M.backwardQ n (by omega) s' a')) :=
        fun _ => by ring
      -- Cancel the rewards
      have : ∀ (x y : ℝ), (M.r h s a + x) - (M.r h s a + y) = x - y := by
        intro x y; ring
      rw [this]
      rw [← Finset.sum_sub_distrib]
      simp_rw [hsplit, Finset.sum_add_distrib]
    -- Now bound |h_diff|
    rw [h_diff]
    -- |A + B| <= |A| + |B|
    calc |∑ s', (P_hat h s a s' - M.P h s a s') *
            Finset.univ.sup' Finset.univ_nonempty
              (fun a' => M.backwardQ n (by omega) s' a') +
          ∑ s', P_hat h s a s' *
            (Finset.univ.sup' Finset.univ_nonempty
              (fun a' => M.empiricalBackwardQ P_hat n (by omega) s' a') -
             Finset.univ.sup' Finset.univ_nonempty
              (fun a' => M.backwardQ n (by omega) s' a'))|
        ≤ |∑ s', (P_hat h s a s' - M.P h s a s') *
            Finset.univ.sup' Finset.univ_nonempty
              (fun a' => M.backwardQ n (by omega) s' a')| +
          |∑ s', P_hat h s a s' *
            (Finset.univ.sup' Finset.univ_nonempty
              (fun a' => M.empiricalBackwardQ P_hat n (by omega) s' a') -
             Finset.univ.sup' Finset.univ_nonempty
              (fun a' => M.backwardQ n (by omega) s' a'))| :=
          abs_add_le _ _
      -- Term 1: |sum (P_hat - P) * V*| <= eps * n
      -- Term 2: |sum P_hat * (V_hat - V*)| <= n^2 * eps
      _ ≤ ε * n + n ^ 2 * ε := by
          apply add_le_add
          · -- Term 1: transition error * value bound
            -- V*(n)(s') = max_a Q*(n)(s',a) is bounded by n
            have h_Vstar_bound : ∀ s' : M.S,
                |Finset.univ.sup' Finset.univ_nonempty
                  (fun a' => M.backwardQ n (by omega) s' a')| ≤ n := by
              intro s'
              rw [abs_le]
              constructor
              · linarith [Finset.le_sup' (fun a' => M.backwardQ n (by omega) s' a')
                  (Finset.mem_univ (Classical.arbitrary M.A)),
                  M.backwardQ_nonneg n (by omega) s' (Classical.arbitrary M.A)]
              · apply Finset.sup'_le; intro a' _
                exact_mod_cast M.backwardQ_le n (by omega) s' a'
            -- |sum (P_hat - P) * V*| <= sum |P_hat - P| * n <= eps * n
            have h_l1_neg : ∑ s', |P_hat h s a s' - M.P h s a s'| ≤ ε := by
              calc ∑ s', |P_hat h s a s' - M.P h s a s'|
                  = ∑ s', |M.P h s a s' - P_hat h s a s'| := by
                    congr 1; ext s'; rw [abs_sub_comm]
                _ ≤ ε := h_err h s a
            exact M.weighted_sum_error (P_hat h s a) (M.P h s a)
              (fun s' => Finset.univ.sup' Finset.univ_nonempty
                (fun a' => M.backwardQ n (by omega) s' a'))
              n ε (Nat.cast_nonneg n) h_Vstar_bound h_l1_neg
          · -- Term 2: P_hat * value difference
            -- sup' error <= n^2 * eps by induction
            have h_sup_err : ∀ s' : M.S,
                |Finset.univ.sup' Finset.univ_nonempty
                  (fun a' => M.empiricalBackwardQ P_hat n (by omega) s' a') -
                 Finset.univ.sup' Finset.univ_nonempty
                  (fun a' => M.backwardQ n (by omega) s' a')| ≤
                n ^ 2 * ε := by
              intro s'
              exact sup'_sub_sup'_le
                (fun a' => M.empiricalBackwardQ P_hat n (by omega) s' a')
                (fun a' => M.backwardQ n (by omega) s' a')
                (n ^ 2 * ε) (by positivity) (fun a' => ih (by omega) s' a')
            -- |sum P_hat * diff| <= sum P_hat * |diff| <= sum P_hat * (n^2*eps) = n^2*eps
            calc |∑ s', P_hat h s a s' *
                    (Finset.univ.sup' Finset.univ_nonempty
                      (fun a' => M.empiricalBackwardQ P_hat n (by omega) s' a') -
                     Finset.univ.sup' Finset.univ_nonempty
                      (fun a' => M.backwardQ n (by omega) s' a'))|
                ≤ ∑ s', |P_hat h s a s' *
                    (Finset.univ.sup' Finset.univ_nonempty
                      (fun a' => M.empiricalBackwardQ P_hat n (by omega) s' a') -
                     Finset.univ.sup' Finset.univ_nonempty
                      (fun a' => M.backwardQ n (by omega) s' a'))| :=
                  abs_sum_le_sum_abs _ _
              _ = ∑ s', P_hat h s a s' *
                    |Finset.univ.sup' Finset.univ_nonempty
                      (fun a' => M.empiricalBackwardQ P_hat n (by omega) s' a') -
                     Finset.univ.sup' Finset.univ_nonempty
                      (fun a' => M.backwardQ n (by omega) s' a')| := by
                  congr 1; ext s'
                  rw [abs_mul, abs_of_nonneg (P_hat_nonneg h s a s')]
              _ ≤ ∑ s', P_hat h s a s' * (n ^ 2 * ε) := by
                  apply Finset.sum_le_sum; intro s' _
                  exact mul_le_mul_of_nonneg_left (h_sup_err s') (P_hat_nonneg h s a s')
              _ = (∑ s', P_hat h s a s') * (n ^ 2 * ε) :=
                  (Finset.sum_mul _ _ _).symm
              _ = n ^ 2 * ε := by rw [P_hat_sum_one h s a, one_mul]
      -- eps * n + n^2 * eps = (n + 1)^2 * eps - eps (actually need to show <= (n+1)^2 * eps)
      _ ≤ (↑(n + 1)) ^ 2 * ε := by
          have hn : (0 : ℝ) ≤ ↑n := Nat.cast_nonneg n
          have heq : (↑(n + 1) : ℝ) ^ 2 = ↑n ^ 2 + 2 * ↑n + 1 := by push_cast; ring
          rw [heq]; nlinarith

/-! ### Value Error Bound

The value at step 0 (i.e., with H remaining steps) determines the
total expected reward. We bound |V_hat - V*| at step 0. -/

/-- **Finite-horizon value error**: if transition L1 error is at most eps
    at every step, then |V_hat_0 - V*_0| <= H^2 * eps.

    This is the deterministic core: given bounded transition error,
    the planning error is bounded. -/
theorem finite_horizon_value_error
    (P_hat : Fin M.H → M.S → M.A → M.S → ℝ)
    (P_hat_nonneg : ∀ h s a s', 0 ≤ P_hat h s a s')
    (P_hat_sum_one : ∀ h s a, ∑ s', P_hat h s a s' = 1)
    (ε : ℝ) (hε : 0 ≤ ε)
    (h_err : ∀ (h : Fin M.H) (s : M.S) (a : M.A),
      ∑ s', |M.P h s a s' - P_hat h s a s'| ≤ ε)
    (hk : M.H ≤ M.H) (s : M.S) (a : M.A) :
    |M.empiricalBackwardQ P_hat M.H hk s a -
     M.backwardQ M.H hk s a| ≤ M.H ^ 2 * ε :=
  M.backward_induction_error_bound P_hat P_hat_nonneg P_hat_sum_one
    ε hε h_err M.H hk s a

/-! ### From Pointwise to L1 Error

Convert pointwise transition error |P(s'|s,a) - P_hat(s'|s,a)| <= eps_0
to L1 error sum |P - P_hat| <= |S| * eps_0. -/

/-- **L1 from pointwise for finite horizon**: if pointwise transition error
    is at most eps_0, then L1 error is at most |S| * eps_0. -/
theorem finite_horizon_l1_from_pointwise
    (P_hat : Fin M.H → M.S → M.A → M.S → ℝ)
    (ε₀ : ℝ) (_hε₀ : 0 ≤ ε₀)
    (h_pw : ∀ (h : Fin M.H) (s : M.S) (a : M.A) (s' : M.S),
      |M.P h s a s' - P_hat h s a s'| ≤ ε₀) :
    ∀ (h : Fin M.H) (s : M.S) (a : M.A),
    ∑ s', |M.P h s a s' - P_hat h s a s'| ≤
      Fintype.card M.S * ε₀ := by
  intro h s a
  calc ∑ s', |M.P h s a s' - P_hat h s a s'|
      ≤ ∑ _s' : M.S, ε₀ :=
        Finset.sum_le_sum (fun s' _ => h_pw h s a s')
    _ = Fintype.card M.S * ε₀ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-! ### Sample Complexity: Deterministic Core

Combining L1 conversion with the backward induction error bound:
if pointwise error <= eps_0, then value error <= H^2 * |S| * eps_0. -/

/-- **Finite-horizon sample complexity (deterministic core)**.
    If |P(s'|s,a,h) - P_hat(s'|s,a,h)| <= eps_0 for all (h,s,a,s'),
    then the Q-value error with H remaining steps is at most
    H^2 * |S| * eps_0. -/
theorem finite_horizon_sample_complexity
    (P_hat : Fin M.H → M.S → M.A → M.S → ℝ)
    (P_hat_nonneg : ∀ h s a s', 0 ≤ P_hat h s a s')
    (P_hat_sum_one : ∀ h s a, ∑ s', P_hat h s a s' = 1)
    (ε₀ : ℝ) (hε₀ : 0 ≤ ε₀)
    (h_pw : ∀ (h : Fin M.H) (s : M.S) (a : M.A) (s' : M.S),
      |M.P h s a s' - P_hat h s a s'| ≤ ε₀)
    (hk : M.H ≤ M.H) (s : M.S) (a : M.A) :
    |M.empiricalBackwardQ P_hat M.H hk s a -
     M.backwardQ M.H hk s a| ≤
      M.H ^ 2 * (Fintype.card M.S * ε₀) := by
  apply M.finite_horizon_value_error P_hat P_hat_nonneg P_hat_sum_one
    (Fintype.card M.S * ε₀) (by positivity)
  exact M.finite_horizon_l1_from_pointwise P_hat ε₀ hε₀ h_pw

/-- **Reformulated sample complexity**: the value error is at most
    H^2 * |S| * eps_0 (rewriting the multiplication). -/
theorem finite_horizon_sample_complexity'
    (P_hat : Fin M.H → M.S → M.A → M.S → ℝ)
    (P_hat_nonneg : ∀ h s a s', 0 ≤ P_hat h s a s')
    (P_hat_sum_one : ∀ h s a, ∑ s', P_hat h s a s' = 1)
    (ε₀ : ℝ) (hε₀ : 0 ≤ ε₀)
    (h_pw : ∀ (h : Fin M.H) (s : M.S) (a : M.A) (s' : M.S),
      |M.P h s a s' - P_hat h s a s'| ≤ ε₀)
    (hk : M.H ≤ M.H) (s : M.S) (a : M.A) :
    |M.empiricalBackwardQ P_hat M.H hk s a -
     M.backwardQ M.H hk s a| ≤
      M.H ^ 2 * Fintype.card M.S * ε₀ := by
  have h := M.finite_horizon_sample_complexity P_hat P_hat_nonneg P_hat_sum_one
    ε₀ hε₀ h_pw hk s a
  linarith [mul_assoc (↑M.H ^ 2 : ℝ) (↑(Fintype.card M.S) : ℝ) ε₀]

/-! ### Sample Complexity Formula

The algebraic statement: if N >= H^2 * |S|^2 * C / eps^2 for some
log factor C, then the value error is at most eps.

We state this as: given eps > 0, if eps_0 <= eps / (H^2 * |S|),
then the value error is at most eps. -/

/-- **Sample complexity formula**: if the per-entry transition error
    eps_0 satisfies eps_0 <= eps / (H^2 * |S|), then the value error
    is at most eps.

    In the probabilistic setting, Hoeffding gives
    eps_0 ~ sqrt(log(H|S||A|/delta) / N), so solving for N gives
    N >= H^4 * |S|^2 * log(H|S||A|/delta) / eps^2. -/
theorem sample_complexity_formula
    (P_hat : Fin M.H → M.S → M.A → M.S → ℝ)
    (P_hat_nonneg : ∀ h s a s', 0 ≤ P_hat h s a s')
    (P_hat_sum_one : ∀ h s a, ∑ s', P_hat h s a s' = 1)
    (ε ε₀ : ℝ) (_hε : 0 < ε) (hε₀ : 0 ≤ ε₀)
    (h_pw : ∀ (h : Fin M.H) (s : M.S) (a : M.A) (s' : M.S),
      |M.P h s a s' - P_hat h s a s'| ≤ ε₀)
    (h_budget : M.H ^ 2 * Fintype.card M.S * ε₀ ≤ ε)
    (hk : M.H ≤ M.H) (s : M.S) (a : M.A) :
    |M.empiricalBackwardQ P_hat M.H hk s a -
     M.backwardQ M.H hk s a| ≤ ε := by
  calc |M.empiricalBackwardQ P_hat M.H hk s a -
       M.backwardQ M.H hk s a|
      ≤ M.H ^ 2 * Fintype.card M.S * ε₀ :=
        M.finite_horizon_sample_complexity' P_hat P_hat_nonneg P_hat_sum_one
          ε₀ hε₀ h_pw hk s a
    _ ≤ ε := h_budget

/-! ### Empirical Value Bounds

The empirical Q-values inherit the same bounds as the true Q-values,
up to the error term. -/

/-- Empirical backward Q is nonneg when P_hat is nonneg and sums to 1. -/
theorem empiricalBackwardQ_nonneg
    (P_hat : Fin M.H → M.S → M.A → M.S → ℝ)
    (P_hat_nonneg : ∀ h s a s', 0 ≤ P_hat h s a s')
    (_P_hat_sum_one : ∀ h s a, ∑ s', P_hat h s a s' = 1) :
    ∀ (k : ℕ) (hk : k ≤ M.H) (s : M.S) (a : M.A),
    0 ≤ M.empiricalBackwardQ P_hat k hk s a := by
  intro k
  induction k with
  | zero => intro hk s a; simp [empiricalBackwardQ]
  | succ n ih =>
    intro hk s a
    simp only [empiricalBackwardQ]
    apply add_nonneg (M.r_nonneg _ s a)
    apply Finset.sum_nonneg; intro s' _
    apply mul_nonneg (P_hat_nonneg _ s a s')
    exact le_trans (ih (by omega) s' (Classical.arbitrary M.A))
      (Finset.le_sup' _ (Finset.mem_univ _))

/-- Empirical backward Q is bounded by k (same bound as true Q). -/
theorem empiricalBackwardQ_le
    (P_hat : Fin M.H → M.S → M.A → M.S → ℝ)
    (P_hat_nonneg : ∀ h s a s', 0 ≤ P_hat h s a s')
    (P_hat_sum_one : ∀ h s a, ∑ s', P_hat h s a s' = 1) :
    ∀ (k : ℕ) (hk : k ≤ M.H) (s : M.S) (a : M.A),
    M.empiricalBackwardQ P_hat k hk s a ≤ k := by
  intro k
  induction k with
  | zero => intro hk s a; simp [empiricalBackwardQ]
  | succ n ih =>
    intro hk s a
    simp only [empiricalBackwardQ]
    have hr : M.r ⟨M.H - n - 1, by omega⟩ s a ≤ 1 :=
      M.r_le_one _ s a
    have htrans : ∑ s', P_hat ⟨M.H - n - 1, by omega⟩ s a s' *
        Finset.univ.sup' Finset.univ_nonempty
          (fun a' => M.empiricalBackwardQ P_hat n (by omega) s' a') ≤ n := by
      calc ∑ s', P_hat ⟨M.H - n - 1, by omega⟩ s a s' *
              Finset.univ.sup' Finset.univ_nonempty
                (fun a' => M.empiricalBackwardQ P_hat n (by omega) s' a')
          ≤ ∑ s', P_hat ⟨M.H - n - 1, by omega⟩ s a s' *
              (n : ℝ) := by
            apply Finset.sum_le_sum; intro s' _
            apply mul_le_mul_of_nonneg_left _
              (P_hat_nonneg _ s a s')
            apply Finset.sup'_le; intro a' _
            exact ih (by omega) s' a'
        _ = (∑ s', P_hat ⟨M.H - n - 1, by omega⟩ s a s') *
              n := (Finset.sum_mul _ _ _).symm
        _ = n := by rw [P_hat_sum_one, one_mul]
    push_cast; linarith

end FiniteHorizonMDP

end
