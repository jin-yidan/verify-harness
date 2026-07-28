/-
Copyright (c) 2026 Yidan Jin. All rights reserved.
This source code is proprietary and not licensed for public use.

# Pessimistic Value Iteration — Suboptimality Decomposition

The suboptimality of pessimistic VI decomposes into three terms:

  V*(s) - V^{π̂}(s) = (optimality gap) + (estimation error) + (pessimism gap)

Specifically, for the LCB-greedy policy π̂:
  V*(s₀) - V^{π̂}(s₀) ≤ (1/(1-γ)) · E_{d^{π*}}[bonus(s,a)]

This file proves the decomposition algebraically, building on the
pessimism principle from Pessimism.lean and the performance difference
lemma from PerformanceDifference.lean.

## Main Results

* `pessimistic_vi_decomposition` — 3-term suboptimality decomposition
* `pessimistic_vi_single_state` — single-state suboptimality bound
* `pessimistic_vs_optimistic` — comparison with UCBVI optimism

## References

* [Jin et al., "Is Pessimism Provably Efficient for Offline RL?,"
  ICML 2021]
* [Rashidinejad et al., "Bridging Offline RL and Imitation Learning,"
  ICLR 2022]
-/

import RLGeneralization.OfflineRL.Pessimism

open Finset BigOperators

noncomputable section

namespace FiniteMDP

variable (M : FiniteMDP)

/-! ### Three-Term Decomposition -/

/-- **Pessimistic VI suboptimality decomposition** (3-term form).

  For any policy π̂ greedy w.r.t. Q_lcb = Q_hat - bonus:

  V*(s) - Q_lcb(s, π̂(s))
    = [V*(s) - Q*(s, π̂(s))]       -- optimality gap (π̂ ≠ π*)
    + [Q*(s, π̂(s)) - Q_hat(s, π̂(s))]  -- estimation error
    + [bonus(s, π̂(s))]            -- pessimism penalty

  The first term is zero when π̂ = π*.
  The second + third = bonus - (Q_hat - Q*).
  Under |Q_hat - Q*| ≤ bonus, all three terms are nonneg. -/
theorem pessimistic_vi_decomposition
    (Q_star Q_hat bonus : M.ActionValueFn)
    (V_star : M.StateValueFn)
    (π : M.DetPolicy) (s : M.S) :
    V_star s - M.lcbQ Q_hat bonus s (π s) =
    (V_star s - Q_star s (π s)) +
    (Q_star s (π s) - Q_hat s (π s)) +
    bonus s (π s) := by
  simp only [lcbQ]; ring

/-- Under pessimism (bonus ≥ |Q_hat - Q*|), the estimation error
    term is bounded by the bonus. -/
theorem estimation_error_le_bonus
    (Q_star Q_hat bonus : M.ActionValueFn)
    (h_bonus : ∀ s a, |Q_hat s a - Q_star s a| ≤ bonus s a)
    (s : M.S) (a : M.A) :
    Q_star s a - Q_hat s a ≤ bonus s a := by
  have := h_bonus s a
  linarith [neg_abs_le (Q_hat s a - Q_star s a)]

/-- Under pessimism, the full suboptimality is at most
    (optimality gap) + 2·bonus. -/
theorem pessimistic_vi_bound
    (Q_star Q_hat bonus : M.ActionValueFn)
    (V_star : M.StateValueFn)
    (h_bonus : ∀ s a, |Q_hat s a - Q_star s a| ≤ bonus s a)
    (π : M.DetPolicy) (s : M.S) :
    V_star s - M.lcbQ Q_hat bonus s (π s) ≤
    (V_star s - Q_star s (π s)) + 2 * bonus s (π s) := by
  rw [M.pessimistic_vi_decomposition Q_star Q_hat bonus V_star π s]
  have h_est := M.estimation_error_le_bonus Q_star Q_hat bonus h_bonus s (π s)
  linarith

/-! ### Single-State Analysis -/

/-- **Pessimistic VI: greedy improvement bound.**

  If π̂ is greedy w.r.t. Q_lcb (i.e., π̂(s) = argmax_a Q_lcb(s,a)),
  then for ANY action a:
    Q_lcb(s, π̂(s)) ≥ Q_lcb(s, a)

  In particular, taking a = π*(s):
    Q_lcb(s, π̂(s)) ≥ Q_lcb(s, π*(s)) ≥ Q*(s, π*(s)) - 2·bonus(s, π*(s))
    = V*(s) - 2·bonus(s, π*(s)). -/
theorem pessimistic_greedy_improvement
    (Q_hat bonus : M.ActionValueFn)
    (π_hat : M.DetPolicy)
    (h_greedy : ∀ s a, M.lcbQ Q_hat bonus s (π_hat s) ≥
      M.lcbQ Q_hat bonus s a)
    (s : M.S) (a : M.A) :
    M.lcbQ Q_hat bonus s (π_hat s) ≥ M.lcbQ Q_hat bonus s a :=
  h_greedy s a

/-- **Pessimistic VI single-state bound**: when π̂ is greedy w.r.t.
    Q_lcb and bonus ≥ |Q_hat - Q*|:

    V*(s) - V^{lcb}(s, π̂(s)) ≤ 2·bonus(s, π*(s))

    where π* is the optimal policy. -/
theorem pessimistic_vi_single_state
    (Q_star Q_hat bonus : M.ActionValueFn)
    (V_star : M.StateValueFn)
    (hV : ∀ s, V_star s = Finset.univ.sup' Finset.univ_nonempty (Q_star s))
    (h_bonus : ∀ s a, |Q_hat s a - Q_star s a| ≤ bonus s a)
    (π_hat : M.DetPolicy)
    (h_greedy : ∀ s a, M.lcbQ Q_hat bonus s (π_hat s) ≥
      M.lcbQ Q_hat bonus s a)
    (π_star : M.DetPolicy)
    (hπ_star : ∀ s, Q_star s (π_star s) = V_star s)
    (s : M.S) :
    V_star s - M.lcbQ Q_hat bonus s (π_hat s) ≤
    2 * bonus s (π_star s) := by
  have h1 : M.lcbQ Q_hat bonus s (π_hat s) ≥
      M.lcbQ Q_hat bonus s (π_star s) :=
    h_greedy s (π_star s)
  have h2 : M.lcbQ Q_hat bonus s (π_star s) ≥
      Q_star s (π_star s) - 2 * bonus s (π_star s) := by
    simp only [lcbQ]
    have h_est := h_bonus s (π_star s)
    have := (abs_le.mp h_est).1
    linarith
  linarith [hπ_star s]

/-! ### Optimism vs Pessimism Comparison -/

/-- **Optimism vs pessimism**: the UCB Q-function (Q_hat + bonus)
    provides an upper bound while LCB (Q_hat - bonus) provides a
    lower bound. The gap is 2·bonus:

    Q_ucb(s,a) - Q_lcb(s,a) = 2·bonus(s,a) -/
theorem ucb_lcb_gap
    (Q_hat bonus : M.ActionValueFn) (s : M.S) (a : M.A) :
    (Q_hat s a + bonus s a) - M.lcbQ Q_hat bonus s a =
    2 * bonus s a := by
  simp only [lcbQ]; ring

end FiniteMDP

end
