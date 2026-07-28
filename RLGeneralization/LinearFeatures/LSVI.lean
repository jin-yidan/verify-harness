/-
# LSVI and Approximate Dynamic Programming

Formalizes approximate backward induction with bounded Bellman
residuals.

## Main Results

* `approx_dp_error` - If the Bellman residual
  at each step is bounded by η, then the Q-function error grows
  linearly: |Q̂_h(s,a) - Q*_h(s,a)| ≤ (H-h) · η

* `policy_value_gap` - The greedy policy π̂
  w.r.t. approximate Q-functions has value gap
  V*_0(s) - V^{π̂}_0(s) ≤ 2H²η

## Key Insight

This is the RL core of the LSVI guarantee. The regression
side (SLT library) provides small Bellman residuals as input, and
this lemma converts them into policy-quality guarantees. The proof
is pure backward induction — no probability or regression needed.

## References

* [Agarwal et al., *RL: Theory and Algorithms*]
-/

import RLGeneralization.MDP.FiniteHorizon

open Finset BigOperators

noncomputable section

namespace FiniteHorizonMDP

variable (M : FiniteHorizonMDP)

/-! ### Approximate Q-Functions with Bounded Residuals -/

/-- An approximate Q-function sequence with bounded Bellman
    residuals at each step. This models the output of LSVI
    (Algorithm 1) or any approximate backward induction.

    The key property: at each step h with k remaining steps,
    |Q̂_h(s,a) - (T_h Q̂_{h+1})(s,a)| ≤ η

    where T_h is the exact Bellman operator at step h. -/
structure ApproxBackwardQ where
  /-- Approximate Q-function with k remaining steps -/
  Q_hat : (k : ℕ) → (hk : k ≤ M.H) → M.S → M.A → ℝ
  /-- Terminal condition: Q̂_H = 0 -/
  terminal : ∀ (hk : 0 ≤ M.H) s a, Q_hat 0 hk s a = 0
  /-- Bellman residual bound: |Q̂_h - T_h Q̂_{h+1}| ≤ η -/
  η : ℝ
  hη : 0 ≤ η
  residual_bound : ∀ (k : ℕ) (hk : k + 1 ≤ M.H) (s : M.S) (a : M.A),
    |Q_hat (k + 1) hk s a -
      (M.r ⟨M.H - k - 1, by omega⟩ s a +
       ∑ s', M.P ⟨M.H - k - 1, by omega⟩ s a s' *
         Finset.univ.sup' Finset.univ_nonempty
           (fun a' => Q_hat k (by omega) s' a'))| ≤ η

/-! ### Approximate DP Error Bound -/

/-- Approximate dynamic-programming error bound.

  If Q̂ has Bellman residual ≤ η at each step, then:
    |Q̂_h(s,a) - Q*_h(s,a)| ≤ k · η
  where k = H - h is the number of remaining steps.

  Proof by backward induction on k:
  - k = 0: Both Q̂_H = Q*_H = 0, so error = 0 ≤ 0.
  - k → k+1: |Q̂ - Q*| = |Q̂ - T Q̂ + T Q̂ - T Q*|
             ≤ η + |T Q̂ - T Q*|
             ≤ η + max|Q̂_prev - Q*_prev| (monotonicity)
             ≤ η + k·η = (k+1)·η -/
theorem approx_dp_error (approx : M.ApproxBackwardQ) :
    ∀ (k : ℕ) (hk : k ≤ M.H) (s : M.S) (a : M.A),
    |approx.Q_hat k hk s a - M.backwardQ k hk s a| ≤
      k * approx.η := by
  intro k
  induction k with
  | zero =>
    intro hk s a
    simp [approx.terminal, backwardQ]
  | succ n ih =>
    intro hk s a
    -- |Q̂ - Q*| ≤ |Q̂ - T_h Q̂| + |T_h Q̂ - T_h Q*|
    -- ≤ η + sup|Q̂_prev - Q*_prev|  (by contraction)
    -- ≤ η + n·η = (n+1)·η
    set Q_hat_val := approx.Q_hat (n + 1) hk s a
    set Q_star_val := M.backwardQ (n + 1) hk s a
    set T_Q_hat := M.r ⟨M.H - n - 1, by omega⟩ s a +
      ∑ s', M.P ⟨M.H - n - 1, by omega⟩ s a s' *
        Finset.univ.sup' Finset.univ_nonempty
          (fun a' => approx.Q_hat n (by omega) s' a')
    -- Step 1: |Q̂ - T_h Q̂| ≤ η (residual bound)
    have h_res : |Q_hat_val - T_Q_hat| ≤ approx.η :=
      approx.residual_bound n hk s a
    -- Step 2: |T_h Q̂ - T_h Q*| ≤ n·η
    -- T_h Q̂ - T_h Q* = ∑P(max Q̂_prev - max Q*_prev)
    have h_bellman : |T_Q_hat - Q_star_val| ≤ n * approx.η := by
      -- Both T_h Q̂ and Q* share the same reward term
      -- |T_h Q̂ - T_h Q*| = |∑P(sup Q̂ - sup Q*)| ≤ n·η
      -- Reward terms cancel, leaving ∑P·(sup Q̂ - sup Q*)
      have hdiff : ∀ s' : M.S,
          M.P ⟨M.H - n - 1, by omega⟩ s a s' *
            Finset.univ.sup' Finset.univ_nonempty
              (fun a' => approx.Q_hat n (by omega) s' a') -
          M.P ⟨M.H - n - 1, by omega⟩ s a s' *
            Finset.univ.sup' Finset.univ_nonempty
              (fun a' => M.backwardQ n (by omega) s' a') =
          M.P ⟨M.H - n - 1, by omega⟩ s a s' *
            (Finset.univ.sup' Finset.univ_nonempty
              (fun a' => approx.Q_hat n (by omega) s' a') -
             Finset.univ.sup' Finset.univ_nonempty
              (fun a' => M.backwardQ n (by omega) s' a')) :=
        fun s' => by ring
      -- T_Q_hat - Q_star_val = ∑P(sup Q̂ - sup Q*)
      change |T_Q_hat - Q_star_val| ≤ _
      have hexpand : T_Q_hat - Q_star_val =
          ∑ s', M.P ⟨M.H - n - 1, by omega⟩ s a s' *
            (Finset.univ.sup' Finset.univ_nonempty
              (fun a' => approx.Q_hat n (by omega) s' a') -
             Finset.univ.sup' Finset.univ_nonempty
              (fun a' => M.backwardQ n (by omega) s' a')) := by
        -- T_Q_hat = r + ∑P·supQ̂, Q_star = r + ∑P·supQ*
        -- Difference = ∑P·(supQ̂ - supQ*) after r cancels
        have hsum_sub :
            ∑ s', M.P ⟨M.H - n - 1, by omega⟩ s a s' *
              Finset.univ.sup' Finset.univ_nonempty
                (fun a' => approx.Q_hat n (by omega) s' a') -
            ∑ s', M.P ⟨M.H - n - 1, by omega⟩ s a s' *
              Finset.univ.sup' Finset.univ_nonempty
                (fun a' => M.backwardQ n (by omega) s' a') =
            ∑ s', M.P ⟨M.H - n - 1, by omega⟩ s a s' *
              (Finset.univ.sup' Finset.univ_nonempty
                (fun a' => approx.Q_hat n (by omega) s' a') -
               Finset.univ.sup' Finset.univ_nonempty
                (fun a' => M.backwardQ n (by omega) s' a')) := by
          rw [← Finset.sum_sub_distrib]
          congr 1; funext s'; exact hdiff s'
        simp only [T_Q_hat, Q_star_val, backwardQ]
        linarith [hsum_sub]
      rw [hexpand]
      -- |∑P(sup Q̂ - sup Q*)| ≤ n·η by weighted_sum + sup_sub_sup
      apply FiniteMDP.abs_weighted_sum_le_bound _ _
        (n * approx.η) (M.P_nonneg _ s a) (M.P_sum_one _ s a)
      intro s'
      calc |Finset.univ.sup' Finset.univ_nonempty
              (fun a' => approx.Q_hat n (by omega) s' a') -
            Finset.univ.sup' Finset.univ_nonempty
              (fun a' => M.backwardQ n (by omega) s' a')|
          ≤ Finset.univ.sup' Finset.univ_nonempty
              (fun a' => |approx.Q_hat n (by omega) s' a' -
                M.backwardQ n (by omega) s' a'|) :=
            FiniteMDP.abs_sup_sub_sup_le _ _
        _ ≤ n * approx.η := by
            apply Finset.sup'_le; intro a' _
            exact ih (by omega) s' a'
    -- Step 3: Triangle inequality
    -- Triangle: |Q̂ - Q*| ≤ |Q̂ - TQ̂| + |TQ̂ - Q*| ≤ η + n·η
    have h_tri : |Q_hat_val - Q_star_val| ≤
        |Q_hat_val - T_Q_hat| + |T_Q_hat - Q_star_val| := by
      calc |Q_hat_val - Q_star_val|
          = |(Q_hat_val - T_Q_hat) + (T_Q_hat - Q_star_val)| := by
            congr 1; ring
        _ ≤ |Q_hat_val - T_Q_hat| + |T_Q_hat - Q_star_val| :=
            abs_add_le _ _
    calc |Q_hat_val - Q_star_val|
        ≤ approx.η + n * approx.η := by linarith
      _ = (↑(n + 1) : ℝ) * approx.η := by push_cast; ring

/-! ### Policy Gap Bound -/

/-- **Greedy-action gap from approximate DP**.

  If the approximate Q-function has error ≤ kη at step k
  (from `approx_dp_error`), then the greedy action â w.r.t. Q̂
  satisfies:
    max_a Q*_k(s,a) - Q*_k(s, â) ≤ 2kη

  This is a corollary of `approx_dp_error` and is used as
  a building block in the full policy-gap proof
  (`policy_value_gap`) which bounds V*_h(s) - V^π̂_h(s) ≤ 2H²η. -/
theorem approx_dp_policy_gap (approx : M.ApproxBackwardQ)
    (k : ℕ) (hk : k ≤ M.H) (s : M.S)
    -- â is the greedy action w.r.t. Q̂
    (a_hat : M.A)
    (h_greedy : ∀ a, approx.Q_hat k hk s a ≤
      approx.Q_hat k hk s a_hat) :
    Finset.univ.sup' Finset.univ_nonempty
      (fun a => M.backwardQ k hk s a) -
    M.backwardQ k hk s a_hat ≤ 2 * k * approx.η := by
  -- Q*(s, a*) ≤ Q̂(s, a*) + kη  (error bound for a*)
  -- Q̂(s, a*) ≤ Q̂(s, â)         (greedy)
  -- Q̂(s, â) ≤ Q*(s, â) + kη     (error bound for â)
  -- So Q*(s, a*) ≤ Q*(s, â) + 2kη
  have herr := M.approx_dp_error approx
  -- sup Q*(s,·) ≤ Q*(s,â) + 2kη
  suffices h : Finset.univ.sup' Finset.univ_nonempty
      (fun a => M.backwardQ k hk s a) ≤
      M.backwardQ k hk s a_hat + 2 * k * approx.η by linarith
  apply Finset.sup'_le; intro a' _
  have h1 : M.backwardQ k hk s a' ≤
      approx.Q_hat k hk s a' + k * approx.η := by
    linarith [abs_le.mp (herr k hk s a')]
  have h2 : approx.Q_hat k hk s a' ≤
      approx.Q_hat k hk s a_hat := h_greedy a'
  have h3 : approx.Q_hat k hk s a_hat ≤
      M.backwardQ k hk s a_hat + k * approx.η := by
    linarith [abs_le.mp (herr k hk s a_hat)]
  linarith

/-! ### Full Policy Value Gap -/

/-- **Per-state greedy-action gap** (corollary of `approx_dp_policy_gap`).

  Wraps `approx_dp_policy_gap` with a function-valued greedy selector:
    max_a Q*_k(s,a) - Q*_k(s, â(s)) ≤ 2kη

  This is an intermediate result. The full policy value gap
  V*_H - V^π̂_H ≤ 2H²η is proved below as `policy_value_gap`. -/
theorem approx_dp_value_gap (approx : M.ApproxBackwardQ)
    (k : ℕ) (hk : k ≤ M.H) (s : M.S)
    -- Greedy actions at each step
    (a_hat : M.S → M.A)
    (h_greedy : ∀ s a,
      approx.Q_hat k hk s a ≤ approx.Q_hat k hk s (a_hat s)) :
    Finset.univ.sup' Finset.univ_nonempty
      (fun a => M.backwardQ k hk s a) -
    M.backwardQ k hk s (a_hat s) ≤ 2 * k * approx.η :=
  M.approx_dp_policy_gap approx k hk s (a_hat s)
    (h_greedy s)

/-! ### Greedy Policy Value Function -/

/-- The greedy action at step k w.r.t. approximate Q-function Q̂_k.
    â_k(s) = argmax_a Q̂_k(s,a).
    We use `Finset.univ.sup'` via classical choice. -/
def greedyAction (approx : M.ApproxBackwardQ)
    (k : ℕ) (hk : k ≤ M.H) (s : M.S) : M.A :=
  (Finset.univ.exists_mem_eq_sup' Finset.univ_nonempty
    (fun a => approx.Q_hat k hk s a)).choose

theorem greedyAction_is_sup (approx : M.ApproxBackwardQ)
    (k : ℕ) (hk : k ≤ M.H) (s : M.S) :
    approx.Q_hat k hk s (M.greedyAction approx k hk s) =
    Finset.univ.sup' Finset.univ_nonempty
      (fun a => approx.Q_hat k hk s a) :=
  (Finset.univ.exists_mem_eq_sup' Finset.univ_nonempty
    (fun a => approx.Q_hat k hk s a)).choose_spec.2.symm

/-- **Greedy action achieves the sup of Q̂**.

  The greedy action a_hat = argmax_a Q̂_k(s,a) satisfies
  Q̂_k(s,a) <= Q̂_k(s, a_hat) for all actions a. This is a
  direct consequence of `greedyAction_is_sup` and the definition
  of `Finset.sup'`. Used as a building block in the policy gap
  bound `approx_dp_policy_gap`. -/
theorem greedyAction_spec (approx : M.ApproxBackwardQ)
    (k : ℕ) (hk : k ≤ M.H) (s : M.S) :
    ∀ a, approx.Q_hat k hk s a ≤
      approx.Q_hat k hk s (M.greedyAction approx k hk s) := by
  intro a
  rw [M.greedyAction_is_sup approx k hk s]
  exact Finset.le_sup' _ (Finset.mem_univ a)

/-- Value function of the greedy policy w.r.t. Q̂.

    V^π̂_k(s) = r_h(s, â_k(s)) + Σ P(s'|s, â_k(s)) · V^π̂_{k-1}(s')

    where â_k(s) = argmax_a Q̂_k(s,a) and k is remaining steps.
    At k = 0 (terminal), V^π̂ = 0. -/
def greedyValueFn (approx : M.ApproxBackwardQ) :
    (k : ℕ) → (hk : k ≤ M.H) → M.S → ℝ
  | 0, _, _ => 0
  | k + 1, hk, s =>
    let h : Fin M.H := ⟨M.H - k - 1, by omega⟩
    let â := M.greedyAction approx (k + 1) hk s
    M.r h s â + ∑ s', M.P h s â s' *
      greedyValueFn approx k (by omega) s'

/-! ### Per-Step Value Gap Bound -/

/-- The optimal value function: V*_k(s) = max_a Q*_k(s,a). -/
def optimalValueFn (k : ℕ) (hk : k ≤ M.H) (s : M.S) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun a => M.backwardQ k hk s a)

/-! ### Main Policy Value Gap Bound -/

/-- **Policy value gap, tight form**.

  If the Bellman residual at each step is bounded by eta, the
  greedy policy pi_hat (argmax_a Q̂_h(s,a)) has value gap:

    V*_k(s) - V^{pi_hat}_k(s) <= k(k+1)eta

  for k remaining steps. At k = H this gives H(H+1)eta <= 2H^2 eta.

  Proved by backward induction: the greedy-action gap contributes
  2(k+1)eta (from `approx_dp_policy_gap`) and future terms
  contribute k(k+1)eta by IH, summing to (k+1)(k+2)eta.

  **Caveat**: This is the tight k(k+1) bound, intermediate for
  the final `policy_value_gap` which relaxes it to 2H^2 eta. -/
theorem policy_value_gap_linear (approx : M.ApproxBackwardQ) :
    ∀ (k : ℕ) (hk : k ≤ M.H) (s : M.S),
    M.optimalValueFn k hk s -
    M.greedyValueFn approx k hk s ≤
      k * (k + 1) * approx.η := by
  intro k
  induction k with
  | zero =>
    intro hk s
    simp [optimalValueFn, greedyValueFn, backwardQ]
  | succ n ih =>
    intro hk s
    -- Let â = greedy action at this step
    set â := M.greedyAction approx (n + 1) hk s
    -- V*_{n+1}(s) = sup_a Q*_{n+1}(s,a)
    -- Q*_{n+1}(s,â) = r(s,â) + Σ P · V*_n
    -- V^π̂_{n+1}(s) = r(s,â) + Σ P · V^π̂_n
    -- Gap = (V* - Q*(â)) + (Q*(â) - V^π̂)
    --     = (V* - Q*(â)) + Σ P (V*_n - V^π̂_n)

    -- First: V* - V^π̂ = (V* - Q*(â)) + Σ P (V*_n - V^π̂_n)
    -- where Q*(â) = r(s,â) + Σ P · V*_n(s')
    have hdecomp :
        M.optimalValueFn (n + 1) hk s -
        M.greedyValueFn approx (n + 1) hk s =
        (M.optimalValueFn (n + 1) hk s -
          M.backwardQ (n + 1) hk s â) +
        ∑ s', M.P ⟨M.H - n - 1, by omega⟩ s â s' *
          (M.optimalValueFn n (by omega) s' -
           M.greedyValueFn approx n (by omega) s') := by
      -- V^π̂(s) = r(s,â) + Σ P V^π̂_n  and  Q*(s,â) = r(s,â) + Σ P V*_n
      -- So Q*(s,â) - V^π̂(s) = Σ P (V*_n - V^π̂_n)
      -- Therefore V* - V^π̂ = (V* - Q*) + (Q* - V^π̂) = (V* - Q*) + Σ P (V*_n - V^π̂_n)
      have h_Q_star : M.backwardQ (n + 1) hk s â =
          M.r ⟨M.H - n - 1, by omega⟩ s â +
          ∑ s', M.P ⟨M.H - n - 1, by omega⟩ s â s' *
            M.optimalValueFn n (by omega) s' := by
        simp [backwardQ, optimalValueFn]
      have h_V_pi : M.greedyValueFn approx (n + 1) hk s =
          M.r ⟨M.H - n - 1, by omega⟩ s â +
          ∑ s', M.P ⟨M.H - n - 1, by omega⟩ s â s' *
            M.greedyValueFn approx n (by omega) s' := by
        simp [greedyValueFn, â]
      -- Q*(â) - V^π̂ = Σ P (V*_n - V^π̂_n)
      have h_diff : M.backwardQ (n + 1) hk s â -
          M.greedyValueFn approx (n + 1) hk s =
          ∑ s', M.P ⟨M.H - n - 1, by omega⟩ s â s' *
            (M.optimalValueFn n (by omega) s' -
             M.greedyValueFn approx n (by omega) s') := by
        rw [h_Q_star, h_V_pi, add_sub_add_left_eq_sub]
        rw [← Finset.sum_sub_distrib]
        congr 1; ext s'
        ring
      linarith
    -- Part 1: greedy gap ≤ 2(n+1)η
    have h_greedy_gap :
        M.optimalValueFn (n + 1) hk s -
        M.backwardQ (n + 1) hk s â ≤
        2 * (↑(n + 1) : ℝ) * approx.η := by
      -- optimalValueFn = sup Q* and approx_dp_policy_gap gives sup Q* - Q*(â) ≤ 2kη
      unfold optimalValueFn
      exact M.approx_dp_policy_gap approx (n + 1) hk s â
        (M.greedyAction_spec approx (n + 1) hk s)
    -- Part 2: Σ P · (V*_n - V^π̂_n) ≤ n(n+1)η
    have h_future :
        ∑ s', M.P ⟨M.H - n - 1, by omega⟩ s â s' *
          (M.optimalValueFn n (by omega) s' -
           M.greedyValueFn approx n (by omega) s') ≤
        ↑n * (↑n + 1) * approx.η := by
      calc ∑ s', M.P ⟨M.H - n - 1, by omega⟩ s â s' *
              (M.optimalValueFn n (by omega) s' -
               M.greedyValueFn approx n (by omega) s')
          ≤ ∑ s', M.P ⟨M.H - n - 1, by omega⟩ s â s' *
              (↑n * (↑n + 1) * approx.η) := by
            apply Finset.sum_le_sum; intro s' _
            apply mul_le_mul_of_nonneg_left (ih (by omega) s')
              (M.P_nonneg _ s _ s')
        _ = (∑ s', M.P ⟨M.H - n - 1, by omega⟩ s â s') *
              (↑n * (↑n + 1) * approx.η) :=
            (Finset.sum_mul _ _ _).symm
        _ = ↑n * (↑n + 1) * approx.η := by
            rw [M.P_sum_one, one_mul]
    -- Combine: 2(n+1)η + n(n+1)η = (n+1)(n+2)η
    rw [hdecomp]
    calc (M.optimalValueFn (n + 1) hk s -
            M.backwardQ (n + 1) hk s â) +
          ∑ s', M.P ⟨M.H - n - 1, by omega⟩ s â s' *
            (M.optimalValueFn n (by omega) s' -
             M.greedyValueFn approx n (by omega) s')
        ≤ 2 * (↑(n + 1) : ℝ) * approx.η +
          ↑n * (↑n + 1) * approx.η := add_le_add h_greedy_gap h_future
      _ = (↑(n + 1) : ℝ) * ((↑(n + 1) : ℝ) + 1) * approx.η := by
          push_cast; ring

/-- Final `2H^2 η` greedy-policy value-gap bound.

  V*_H(s) - V^{π̂}_H(s) ≤ 2H²η

  This uses the loose upper bound `H(H+1) ≤ 2H²` to simplify
  the tighter linear-in-`H(H+1)` estimate proved above. -/
theorem policy_value_gap (approx : M.ApproxBackwardQ)
    (s : M.S) :
    M.optimalValueFn M.H le_rfl s -
    M.greedyValueFn approx M.H le_rfl s ≤
      2 * (M.H : ℝ) ^ 2 * approx.η := by
  calc M.optimalValueFn M.H le_rfl s -
        M.greedyValueFn approx M.H le_rfl s
      ≤ (M.H : ℝ) * ((M.H : ℝ) + 1) * approx.η :=
        M.policy_value_gap_linear approx M.H le_rfl s
    _ ≤ 2 * (M.H : ℝ) ^ 2 * approx.η := by
        -- H(H+1) ≤ 2H² follows from H ≤ H² for all H : ℕ
        have hη := approx.hη
        -- We need H*(H+1)*η ≤ 2*H^2*η.
        -- First prove H*(H+1) ≤ 2*H^2 in ℝ, then multiply by η ≥ 0.
        have hH : (0 : ℝ) ≤ (M.H : ℝ) := Nat.cast_nonneg M.H
        have key : (M.H : ℝ) * ((M.H : ℝ) + 1) ≤
            2 * (M.H : ℝ) ^ 2 := by
          -- H(H+1) = H^2+H ≤ 2H^2 iff H ≤ H^2, which holds for all H : ℕ.
          -- Case split: H = 0 (trivial) or H ≥ 1 (then H*1 ≤ H*H).
          by_cases hH0 : M.H = 0
          · simp [hH0]
          · have h1H : (1 : ℝ) ≤ (M.H : ℝ) := by
              exact_mod_cast Nat.one_le_iff_ne_zero.mpr hH0
            nlinarith [mul_le_mul_of_nonneg_left h1H hH]
        exact mul_le_mul_of_nonneg_right key hη

end FiniteHorizonMDP

end
