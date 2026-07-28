/-
# UCB Value Iteration (UCBVI)

Definitions for the UCBVI algorithm and the algebraic core of its
finite-horizon regret analysis.

## Main Definitions

* `UCBVIBonus` - The exploration bonus β_h(s,a)
* `regret` - Cumulative regret over K episodes

## References

* [Agarwal et al., *RL: Theory and Algorithms*]
-/

import RLGeneralization.MDP.FiniteHorizon
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset BigOperators

noncomputable section

namespace FiniteHorizonMDP

variable (M : FiniteHorizonMDP)

/-! ### Exploration Bonus -/

-- [UNUSED]
/-- Visit count N_h(s,a) = number of times (s,a) visited at step h
    across episodes 1,...,k-1. -/
def visitCount (episodes : ℕ) (history : Fin episodes →
    Fin M.H → M.S × M.A) (h : Fin M.H) (s : M.S) (a : M.A) : ℕ :=
  (Finset.univ.filter (fun ep =>
    (history ep h).1 = s ∧ (history ep h).2 = a)).card

-- [UNUSED]
/-- UCBVI exploration bonus:
    `β_h(s,a) = c · H · √(log(SAHK/δ) / max(N_h(s,a), 1))`. -/
def ucbBonus (c H_val : ℝ) (log_term : ℝ) (n : ℕ) : ℝ :=
  c * H_val * Real.sqrt (log_term / max n 1)

/-! ### Regret -/

/-- Per-episode regret: V*_0(s_0) - V^{π_k}_0(s_0)
    where π_k is the greedy policy w.r.t. Q̂^k. -/
def episodeRegret (V_star_0 : M.S → ℝ)
    (V_policy_0 : M.S → ℝ) (s_0 : M.S) : ℝ :=
  V_star_0 s_0 - V_policy_0 s_0

/-- Cumulative regret over K episodes:
    R_K = ∑_{k=1}^K (V*_0(s_0^k) - V^{π_k}_0(s_0^k)) -/
def cumulativeRegret (K : ℕ)
    (V_star_0 : M.S → ℝ)
    (V_policies : Fin K → M.S → ℝ)
    (starts : Fin K → M.S) : ℝ :=
  ∑ k : Fin K, M.episodeRegret V_star_0 (V_policies k) (starts k)

/-- Cumulative regret is nonneg when V* ≥ V^π (optimality). -/
theorem cumulativeRegret_nonneg (K : ℕ)
    (V_star_0 : M.S → ℝ)
    (V_policies : Fin K → M.S → ℝ)
    (starts : Fin K → M.S)
    (h_opt : ∀ k s, V_policies k s ≤ V_star_0 s) :
    0 ≤ M.cumulativeRegret K V_star_0 V_policies starts := by
  unfold cumulativeRegret episodeRegret
  apply Finset.sum_nonneg
  intro k _
  linarith [h_opt k (starts k)]

/-! ### Per-Step Value Gap -/

/-- **Per-step value gap nonnegativity**.

  V*_k(s) - Q*_k(s,a) ≥ 0 for all a, since V*_k = max_a Q*_k.

  This is the pointwise ingredient for the one-episode regret
  decomposition. The full telescoping decomposition
  V*_0(s₀) - V^π_0(s₀) = ∑_h E[...] is NOT proved here. -/
theorem per_step_value_gap_nonneg
    (k : ℕ) (hk : k ≤ M.H) (s : M.S) (a : M.A) :
    Finset.univ.sup' Finset.univ_nonempty
      (fun a' => M.backwardQ k hk s a') -
    M.backwardQ k hk s a ≥ 0 := by
  linarith [Finset.le_sup' (fun a' => M.backwardQ k hk s a')
    (Finset.mem_univ a)]

/-! ### Regret Decomposition

  The one-episode regret decomposition is the core identity used in
  the UCBVI regret analysis. For a deterministic policy π and the
  optimal value V*, the regret at step k decomposes into:
    - an "advantage" term: V*_k(s) - Q*_k(s, π(s)), and
    - a future term: Σ P(s'|s, π(s)) · [V*_{k-1}(s') - V^π_{k-1}(s')].

  This is the core algebraic identity and is also the same
  decomposition used in the simulation lemma / performance difference
  lemma throughout this repository.
-/

/-- Optimal value function: V*_k(s) = max_a Q*_k(s,a).
    (Local copy for UCBVI; same as in LSVI.lean.) -/
def optValFn (k : ℕ) (hk : k ≤ M.H) (s : M.S) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun a => M.backwardQ k hk s a)

/-- Value function of a deterministic policy π.
    V^π with 0 remaining steps = 0 (terminal).
    V^π with k+1 remaining steps = r_h(s,π(s)) + Σ P(s'|s,π(s)) V^π_k(s'). -/
def policyValueFn (π : Fin M.H → M.S → M.A) :
    (k : ℕ) → (hk : k ≤ M.H) → M.S → ℝ
  | 0, _, _ => 0
  | k + 1, hk, s =>
    let h : Fin M.H := ⟨M.H - k - 1, by omega⟩
    M.r h s (π h s) + ∑ s', M.P h s (π h s) s' *
      policyValueFn π k (by omega) s'

/-- Terminal condition for the policy value function. -/
theorem policyValueFn_zero (π : Fin M.H → M.S → M.A)
    (hk : 0 ≤ M.H) (s : M.S) :
    M.policyValueFn π 0 hk s = 0 := rfl

/-- **One-step regret decomposition**.

  V*_{k+1}(s) - V^π_{k+1}(s)
    = [V*_{k+1}(s) - Q*_{k+1}(s, π(s))]
    + Σ_{s'} P(s'|s, π(s)) · [V*_k(s') - V^π_k(s')]

  The first term is the "advantage" of the optimal policy over π
  at state s; it is nonneg because V* = max Q*.
  The second term propagates the regret from future steps.

  This is the key algebraic identity underlying the regret
  decomposition used in the UCBVI analysis. -/
theorem regret_decomposition_step
    (π : Fin M.H → M.S → M.A)
    (k : ℕ) (hk : k + 1 ≤ M.H) (s : M.S) :
    M.optValFn (k + 1) hk s -
    M.policyValueFn π (k + 1) hk s =
    (M.optValFn (k + 1) hk s -
      M.backwardQ (k + 1) hk s (π ⟨M.H - k - 1, by omega⟩ s)) +
    ∑ s', M.P ⟨M.H - k - 1, by omega⟩ s
        (π ⟨M.H - k - 1, by omega⟩ s) s' *
      (M.optValFn k (by omega) s' -
       M.policyValueFn π k (by omega) s') := by
  -- Q*_{k+1}(s, π(s)) = r(s,π(s)) + Σ P V*_k
  -- V^π_{k+1}(s)     = r(s,π(s)) + Σ P V^π_k
  -- So Q*(s,π(s)) - V^π(s) = Σ P (V*_k - V^π_k)
  -- Therefore: V* - V^π = (V* - Q*(π(s))) + Σ P (V*_k - V^π_k)
  set a_pi := π ⟨M.H - k - 1, by omega⟩ s
  have h_Q_star : M.backwardQ (k + 1) hk s a_pi =
      M.r ⟨M.H - k - 1, by omega⟩ s a_pi +
      ∑ s', M.P ⟨M.H - k - 1, by omega⟩ s a_pi s' *
        M.optValFn k (by omega) s' := by
    unfold backwardQ optValFn; rfl
  have h_V_pi : M.policyValueFn π (k + 1) hk s =
      M.r ⟨M.H - k - 1, by omega⟩ s a_pi +
      ∑ s', M.P ⟨M.H - k - 1, by omega⟩ s a_pi s' *
        M.policyValueFn π k (by omega) s' := by
    simp only [policyValueFn]; rfl
  -- Q*(a_pi) - V^pi = sum P (V*_k - V^pi_k)
  have h_diff : M.backwardQ (k + 1) hk s a_pi -
      M.policyValueFn π (k + 1) hk s =
      ∑ s', M.P ⟨M.H - k - 1, by omega⟩ s a_pi s' *
        (M.optValFn k (by omega) s' -
         M.policyValueFn π k (by omega) s') := by
    rw [h_Q_star, h_V_pi, add_sub_add_left_eq_sub]
    rw [← Finset.sum_sub_distrib]
    congr 1; ext s'; ring
  -- V* - V^pi = (V* - Q*(a_pi)) + (Q*(a_pi) - V^pi)
  linarith

/-- The advantage term in the regret decomposition is nonneg:
    V*_{k}(s) - Q*_{k}(s, a) ≥ 0 for any action a.

    This is a restatement of `per_step_value_gap_nonneg` using
    `optValFn`. -/
theorem advantage_nonneg
    (k : ℕ) (hk : k ≤ M.H) (s : M.S) (a : M.A) :
    0 ≤ M.optValFn k hk s - M.backwardQ k hk s a := by
  unfold optValFn
  linarith [Finset.le_sup' (fun a' => M.backwardQ k hk s a')
    (Finset.mem_univ a)]

/-- **Regret nonnegativity from decomposition**.

  V*_k(s) - V^π_k(s) ≥ 0, proved by induction using the
  one-step decomposition. Each step contributes a nonneg
  advantage term, and future terms are nonneg by IH.

  This gives an alternative proof of backward induction
  optimality via the regret decomposition. -/
theorem regret_nonneg_inductive
    (π : Fin M.H → M.S → M.A) :
    ∀ (k : ℕ) (hk : k ≤ M.H) (s : M.S),
    0 ≤ M.optValFn k hk s - M.policyValueFn π k hk s := by
  intro k
  induction k with
  | zero =>
    intro hk s
    simp [optValFn, policyValueFn, backwardQ]
  | succ n ih =>
    intro hk s
    -- Use the one-step decomposition
    rw [M.regret_decomposition_step π n hk s]
    apply add_nonneg
    · -- Advantage term is nonneg
      exact M.advantage_nonneg (n + 1) hk s
        (π ⟨M.H - n - 1, by omega⟩ s)
    · -- Future term: Σ P · (nonneg) ≥ 0
      apply Finset.sum_nonneg; intro s' _
      apply mul_nonneg (M.P_nonneg _ _ _ s')
      exact ih (by omega) s'

/-- **Uniform advantage bound**.

  If the per-step advantage satisfies V*_k(s) - Q*_k(s, pi(s)) <= epsilon
  uniformly over all steps k and states s, then:

    V*_k(s) - V^pi_k(s) <= k * epsilon

  Proved by induction using `regret_decomposition_step`. Each step
  contributes at most epsilon from the advantage, and the future
  terms are bounded by the inductive hypothesis weighted by
  transition probabilities (which sum to 1).

  **Caveat**: This is the deterministic algebraic ingredient for
  the full UCBVI regret proof. The full analysis replaces epsilon with the
  sum of exploration bonuses along the trajectory. -/
theorem regret_from_uniform_advantage_bound
    (π : Fin M.H → M.S → M.A)
    (ε : ℝ)
    (h_adv : ∀ (j : ℕ) (hj : j + 1 ≤ M.H) (s : M.S),
      M.optValFn (j + 1) hj s -
      M.backwardQ (j + 1) hj s
        (π ⟨M.H - j - 1, by omega⟩ s) ≤ ε) :
    ∀ (k : ℕ) (hk : k ≤ M.H) (s : M.S),
    M.optValFn k hk s -
    M.policyValueFn π k hk s ≤ k * ε := by
  intro k
  induction k with
  | zero =>
    intro hk s
    simp [optValFn, policyValueFn, backwardQ]
  | succ n ih =>
    intro hk s
    -- Decompose via the one-step identity
    rw [M.regret_decomposition_step π n hk s]
    -- Advantage term ≤ ε
    have h1 : M.optValFn (n + 1) hk s -
        M.backwardQ (n + 1) hk s
          (π ⟨M.H - n - 1, by omega⟩ s) ≤ ε :=
      h_adv n hk s
    -- Future term ≤ n · ε
    have h2 : ∑ s', M.P ⟨M.H - n - 1, by omega⟩ s
          (π ⟨M.H - n - 1, by omega⟩ s) s' *
        (M.optValFn n (by omega) s' -
         M.policyValueFn π n (by omega) s') ≤ n * ε := by
      calc ∑ s', M.P ⟨M.H - n - 1, by omega⟩ s
              (π ⟨M.H - n - 1, by omega⟩ s) s' *
            (M.optValFn n (by omega) s' -
             M.policyValueFn π n (by omega) s')
          ≤ ∑ s', M.P ⟨M.H - n - 1, by omega⟩ s
              (π ⟨M.H - n - 1, by omega⟩ s) s' *
            (↑n * ε) := by
            apply Finset.sum_le_sum; intro s' _
            apply mul_le_mul_of_nonneg_left (ih (by omega) s')
              (M.P_nonneg _ _ _ s')
        _ = (∑ s', M.P ⟨M.H - n - 1, by omega⟩ s
              (π ⟨M.H - n - 1, by omega⟩ s) s') *
            (↑n * ε) := (Finset.sum_mul _ _ _).symm
        _ = ↑n * ε := by rw [M.P_sum_one, one_mul]
    -- Combine: ε + n·ε = (n+1)·ε
    calc (M.optValFn (n + 1) hk s -
            M.backwardQ (n + 1) hk s
              (π ⟨M.H - n - 1, by omega⟩ s)) +
          ∑ s', M.P ⟨M.H - n - 1, by omega⟩ s
              (π ⟨M.H - n - 1, by omega⟩ s) s' *
            (M.optValFn n (by omega) s' -
             M.policyValueFn π n (by omega) s')
        ≤ ε + ↑n * ε := add_le_add h1 h2
      _ = (↑(n + 1) : ℝ) * ε := by push_cast; ring

/-- **Episode regret bound for UCBVI**.

  If the UCBVI exploration bonus ensures that at each step h the
  advantage gap V*(s) - Q*(s,π(s)) ≤ ε, then the per-episode
  regret V*_H(s) - V^π_H(s) ≤ H · ε.

  In the full UCBVI analysis, ε is replaced by the
  sum of exploration bonuses along the trajectory, yielding the
  O(√(H³SAK)) cumulative regret bound. -/
theorem episode_regret_bound
    (π : Fin M.H → M.S → M.A) (s₀ : M.S)
    (ε : ℝ)
    (h_adv : ∀ (j : ℕ) (hj : j + 1 ≤ M.H) (s : M.S),
      M.optValFn (j + 1) hj s -
      M.backwardQ (j + 1) hj s
        (π ⟨M.H - j - 1, by omega⟩ s) ≤ ε) :
    M.optValFn M.H le_rfl s₀ -
    M.policyValueFn π M.H le_rfl s₀ ≤ M.H * ε :=
  M.regret_from_uniform_advantage_bound π ε h_adv M.H le_rfl s₀

/-! ### Optimism and UCBVI Regret Bound

  The UCBVI regret analysis proceeds in three steps:

  1. **Optimism**: The UCB bonuses ensure Q̂_h^k(s,a) ≥ Q*_h(s,a)
     with high probability.

  2. **Per-episode regret ≤ sum of bonuses**: Under optimism, the
     greedy policy π_k w.r.t. Q̂^k satisfies
       V*_H(s) - V^{π_k}_H(s) ≤ ∑_h bonus_h^k(s_h, a_h).

  3. **Total bonus control**: By the pigeonhole / Cauchy-Schwarz
     argument on visit counts,
       ∑_k ∑_h bonus ≤ O(√(H³·|S|·|A|·K)).

  We formalize the optimism property as a hypothesis, prove the
  regret-to-bonus reduction, and state the full regret wrapper. -/

/-- **Optimism hypothesis**.

  The UCB Q-values upper-bound Q* at every episode, step,
  state, and action.  In the full proof this follows from the
  exploration bonus being at least the estimation error;
  here we take it as a hypothesis. -/
def isOptimistic
    (Q_ucb : ℕ → Fin M.H → M.S → M.A → ℝ) : Prop :=
  ∀ (k : ℕ) (h : Fin M.H) (s : M.S) (a : M.A),
    M.backwardQ (M.H - h.val) (by omega) s a ≤ Q_ucb k h s a

/-- **Cumulative regret bounded by total bonuses**.

  If each episode's regret is bounded by the sum of bonuses
  (hypothesis `h_per_ep`), then cumulative regret over K episodes
  is bounded by the total bonus sum:
    Regret(K) ≤ ∑_{k} ∑_{h} bonus_k_h -/
theorem cumulative_regret_le_total_bonuses
    (K : ℕ)
    (V_star_0 : M.S → ℝ)
    (V_policies : Fin K → M.S → ℝ)
    (starts : Fin K → M.S)
    (bonus : Fin K → Fin M.H → ℝ)
    (h_per_ep : ∀ k : Fin K,
      V_star_0 (starts k) - V_policies k (starts k) ≤
      ∑ h : Fin M.H, bonus k h) :
    M.cumulativeRegret K V_star_0 V_policies starts ≤
    ∑ k : Fin K, ∑ h : Fin M.H, bonus k h := by
  unfold cumulativeRegret episodeRegret
  exact Finset.sum_le_sum (fun k _ => h_per_ep k)

/-- **Total bonus bound** (pigeonhole + Cauchy-Schwarz).

  The UCBVI bonus at step h, state s, action a in episode k is
    β = c · H · √(log(HSAK/δ) / N_h^k(s,a)).

  By the pigeonhole argument on visit counts (Lemma B.5):
    ∑_k ∑_h β_h^k(s_h^k, a_h^k) ≤ c' · √(H³ · |S| · |A| · K · log(...))

  We state this as a hypothesis for the final regret wrapper. -/
def totalBonusBound
    (bonus : Fin K → Fin M.H → ℝ)
    (C : ℝ) (δ : ℝ) : Prop :=
  ∑ k : Fin K, ∑ h : Fin M.H, bonus k h ≤
    C * Real.sqrt (M.H ^ 3 * (Fintype.card M.S) * (Fintype.card M.A) *
      K * Real.log (M.H * (Fintype.card M.S) * (Fintype.card M.A) * K / δ))

/-- [WRAPPER] **Algebraic core of the UCBVI regret proof**.

  Takes h_per_ep (per-episode regret <= sum of bonuses) and
  h_bonus (total bonus bound) as hypotheses, then chains them
  to derive: Regret(K) ≤ C · √(H³·|S|·|A|·K·log(HSAK/δ)).

  Both hypotheses require probability theory not present here
  (Hoeffding/Azuma for h_per_ep, pigeonhole/Cauchy-Schwarz for h_bonus). -/
theorem ucbvi_regret_from_bonus_hypotheses
    (K : ℕ)
    (V_star_0 : M.S → ℝ)
    (V_policies : Fin K → M.S → ℝ)
    (starts : Fin K → M.S)
    (bonus : Fin K → Fin M.H → ℝ)
    (C : ℝ) (δ : ℝ) (_hδ : 0 < δ)
    -- Hypothesis 1: per-episode regret ≤ sum of bonuses (from optimism)
    (h_per_ep : ∀ k : Fin K,
      V_star_0 (starts k) - V_policies k (starts k) ≤
      ∑ h : Fin M.H, bonus k h)
    -- Hypothesis 2: total bonus bound (from pigeonhole/Cauchy-Schwarz)
    (h_bonus : M.totalBonusBound bonus C δ) :
    M.cumulativeRegret K V_star_0 V_policies starts ≤
    C * Real.sqrt (M.H ^ 3 * (Fintype.card M.S) * (Fintype.card M.A) *
      K * Real.log (M.H * (Fintype.card M.S) * (Fintype.card M.A) * K / δ)) := by
  calc M.cumulativeRegret K V_star_0 V_policies starts
      ≤ ∑ k : Fin K, ∑ h : Fin M.H, bonus k h :=
        M.cumulative_regret_le_total_bonuses K V_star_0 V_policies starts
          bonus h_per_ep
    _ ≤ C * Real.sqrt (M.H ^ 3 * (Fintype.card M.S) * (Fintype.card M.A) *
          K * Real.log (M.H * (Fintype.card M.S) * (Fintype.card M.A) * K / δ)) :=
        h_bonus

/-! ### Optimism Implies Per-Episode Regret Bound

  The key new result: under the optimism hypothesis (Q* ≤ Q̂) and a
  greedy policy (π picks argmax Q̂), the per-episode regret is bounded
  by the sum of "optimism gaps" Q̂(h,s,π(s)) - Q*(h,s,π(s)).

  This discharges the `h_per_ep` hypothesis from `ucbvi_regret_from_bonus_hypotheses`
  using `isOptimistic`, reducing the UCBVI proof to two ingredients:
  1. Optimism (from concentration + bonus ≥ estimation error)
  2. Total bonus control (from pigeonhole/Cauchy-Schwarz)

  **Proof**: Induction on remaining steps k, using `regret_decomposition_step`.
  At each step:
  - V*(s) ≤ max_a Q̂(s,a) = Q̂(s,π(s)) by optimism + greedy
  - So advantage V*(s) - Q*(s,π(s)) ≤ Q̂(s,π(s)) - Q*(s,π(s)) ≤ gap_bound
  - Future term weighted by P sums to 1, absorbing the IH

  **Reference**: Boucheron et al., *Concentration Inequalities* Ch. 2
  provides the Hoeffding/Bernstein bounds that justify the bonus ≥ error
  condition needed for optimism in the full probabilistic proof.
-/

/-- **Regret bound from optimism gap**.

  Generalization of `regret_from_uniform_advantage_bound` to non-uniform
  per-step bounds. Under optimism (Q* ≤ Q̂) and a greedy policy (π picks
  argmax Q̂):

    V*_k(s) - V^π_k(s) ≤ ∑_{j < k} gap_bound(j)

  where `gap_bound(j)` is a uniform-over-states upper bound on the
  optimism gap Q̂(h,s,π(s)) - Q*(h,s,π(s)) at remaining-step index j.

  This is the core algebraic step that converts optimism into a
  per-episode regret bound. -/
theorem regret_from_optimism_gap
    (π : Fin M.H → M.S → M.A)
    (Q_ucb : Fin M.H → M.S → M.A → ℝ)
    -- Optimism: Q* ≤ Q_ucb at every step/state/action
    (h_opt : ∀ (j : ℕ) (hj : j + 1 ≤ M.H) (s : M.S) (a : M.A),
      M.backwardQ (j + 1) hj s a ≤
      Q_ucb ⟨M.H - j - 1, by omega⟩ s a)
    -- Greedy: π picks the action maximizing Q_ucb
    (h_greedy : ∀ (h : Fin M.H) (s : M.S) (a : M.A),
      Q_ucb h s a ≤ Q_ucb h s (π h s))
    -- Per-step upper bound on the optimism gap (uniform over states)
    (gap_bound : ℕ → ℝ)
    (h_gap : ∀ (j : ℕ) (hj : j + 1 ≤ M.H) (s : M.S),
      Q_ucb ⟨M.H - j - 1, by omega⟩ s
        (π ⟨M.H - j - 1, by omega⟩ s) -
      M.backwardQ (j + 1) hj s
        (π ⟨M.H - j - 1, by omega⟩ s) ≤ gap_bound j) :
    ∀ (k : ℕ) (hk : k ≤ M.H) (s : M.S),
    M.optValFn k hk s -
    M.policyValueFn π k hk s ≤
    Finset.sum (Finset.range k) gap_bound := by
  intro k
  induction k with
  | zero =>
    intro hk s
    simp [optValFn, policyValueFn, backwardQ]
  | succ n ih =>
    intro hk s
    -- Decompose: V* - V^π = advantage + Σ P · (V*_next - V^π_next)
    rw [M.regret_decomposition_step π n hk s]
    -- Advantage: V*(n+1,s) - Q*(n+1,s,π(s)) ≤ gap_bound(n)
    have h_adv : M.optValFn (n + 1) hk s -
        M.backwardQ (n + 1) hk s
          (π ⟨M.H - n - 1, by omega⟩ s) ≤ gap_bound n := by
      -- V*(s) = max_a Q*(s,a) ≤ Q̂(s,π(s)) by optimism + greedy
      have h_opt_val : M.optValFn (n + 1) hk s ≤
          Q_ucb ⟨M.H - n - 1, by omega⟩ s
            (π ⟨M.H - n - 1, by omega⟩ s) := by
        unfold optValFn
        apply Finset.sup'_le; intro a _
        exact le_trans (h_opt n hk s a)
          (h_greedy ⟨M.H - n - 1, by omega⟩ s a)
      linarith [h_gap n hk s]
    -- Future: Σ P · (V*_next - V^π_next) ≤ Σ_{j<n} gap_bound(j)
    have h_fut : ∑ s', M.P ⟨M.H - n - 1, by omega⟩ s
          (π ⟨M.H - n - 1, by omega⟩ s) s' *
        (M.optValFn n (by omega) s' -
         M.policyValueFn π n (by omega) s') ≤
        Finset.sum (Finset.range n) gap_bound := by
      calc ∑ s', M.P ⟨M.H - n - 1, by omega⟩ s
              (π ⟨M.H - n - 1, by omega⟩ s) s' *
            (M.optValFn n (by omega) s' -
             M.policyValueFn π n (by omega) s')
          ≤ ∑ s', M.P ⟨M.H - n - 1, by omega⟩ s
              (π ⟨M.H - n - 1, by omega⟩ s) s' *
            Finset.sum (Finset.range n) gap_bound := by
            apply Finset.sum_le_sum; intro s' _
            apply mul_le_mul_of_nonneg_left (ih (by omega) s')
              (M.P_nonneg _ _ _ s')
        _ = (∑ s', M.P ⟨M.H - n - 1, by omega⟩ s
              (π ⟨M.H - n - 1, by omega⟩ s) s') *
            Finset.sum (Finset.range n) gap_bound :=
            (Finset.sum_mul _ _ _).symm
        _ = Finset.sum (Finset.range n) gap_bound := by
            rw [M.P_sum_one, one_mul]
    -- Combine: gap_bound(n) + Σ_{j<n} = Σ_{j<n+1}
    linarith [Finset.sum_range_succ gap_bound n]

/-- **Per-episode regret from optimism**.

  If Q̂ is optimistic (Q* ≤ Q̂) and π is the greedy policy w.r.t. Q̂,
  then the per-episode regret V*_H(s) - V^π_H(s) is bounded by the
  sum of optimism gaps over all H steps:

    V*_H(s₀) - V^π_H(s₀) ≤ ∑_{h} gap_bound(h)

  This is the composition of `regret_from_optimism_gap` at k = H,
  bridging the `isOptimistic` hypothesis to the `h_per_ep` hypothesis
  of `ucbvi_regret_from_bonus_hypotheses`. -/
theorem episode_regret_from_optimism
    (π : Fin M.H → M.S → M.A) (s₀ : M.S)
    (Q_ucb : Fin M.H → M.S → M.A → ℝ)
    (h_opt : ∀ (j : ℕ) (hj : j + 1 ≤ M.H) (s : M.S) (a : M.A),
      M.backwardQ (j + 1) hj s a ≤
      Q_ucb ⟨M.H - j - 1, by omega⟩ s a)
    (h_greedy : ∀ (h : Fin M.H) (s : M.S) (a : M.A),
      Q_ucb h s a ≤ Q_ucb h s (π h s))
    (gap_bound : ℕ → ℝ)
    (h_gap : ∀ (j : ℕ) (hj : j + 1 ≤ M.H) (s : M.S),
      Q_ucb ⟨M.H - j - 1, by omega⟩ s
        (π ⟨M.H - j - 1, by omega⟩ s) -
      M.backwardQ (j + 1) hj s
        (π ⟨M.H - j - 1, by omega⟩ s) ≤ gap_bound j) :
    M.optValFn M.H le_rfl s₀ -
    M.policyValueFn π M.H le_rfl s₀ ≤
    Finset.sum (Finset.range M.H) gap_bound :=
  M.regret_from_optimism_gap π Q_ucb h_opt h_greedy
    gap_bound h_gap M.H le_rfl s₀

/-! ### Composition Theorems

  These theorems compose the ingredients already proved above into
  end-to-end UCBVI regret bounds. Each theorem eliminates one or more
  hypotheses from `ucbvi_regret_from_bonus_hypotheses` by chaining
  algebraic lemmas in this file.

  Composition chain:
  1. `ucbvi_optimism_from_bonus`:
     bonus ≥ 0  ∧  Q* + bonus ≤ Q_ucb  →  Q* ≤ Q_ucb
  2. `ucbvi_full_regret_composition`:
     Chains optimism → per-episode regret → cumulative regret → final bound.
  3. `ucbvi_regret_self_contained`:
     Takes only the most primitive hypotheses and derives the full bound.
-/

/-- **Optimism from bonus dominance**.

  If the exploration bonus dominates the estimation error at every (h,s,a),
  meaning Q*(h,s,a) + bonus(h,s,a) ≤ Q_ucb(h,s,a) and bonus ≥ 0, then
  the UCB Q-values are optimistic: Q* ≤ Q_ucb.

  This is the algebraic bridge between concentration inequalities
  (which give bonus ≥ |estimation error|) and the regret analysis
  (which needs Q* ≤ Q_ucb). -/
theorem ucbvi_optimism_from_bonus
    (bonus : Fin M.H → M.S → M.A → ℝ)
    (Q_ucb : Fin M.H → M.S → M.A → ℝ)
    -- Q_ucb dominates Q* + bonus at every (j, s, a)
    (h_Qucb : ∀ (j : ℕ) (hj : j + 1 ≤ M.H) (s : M.S) (a : M.A),
      M.backwardQ (j + 1) hj s a + bonus ⟨M.H - j - 1, by omega⟩ s a
      ≤ Q_ucb ⟨M.H - j - 1, by omega⟩ s a)
    -- Bonus is nonneg
    (h_bonus_nonneg : ∀ h s a, 0 ≤ bonus h s a) :
    -- Conclusion: Q* ≤ Q_ucb (the optimism condition for regret_from_optimism_gap)
    ∀ (j : ℕ) (hj : j + 1 ≤ M.H) (s : M.S) (a : M.A),
    M.backwardQ (j + 1) hj s a ≤
    Q_ucb ⟨M.H - j - 1, by omega⟩ s a := by
  intro j hj s a
  have hb := h_bonus_nonneg ⟨M.H - j - 1, by omega⟩ s a
  linarith [h_Qucb j hj s a]

/-- **Full UCBVI regret composition**.

  Composes all ingredients into the complete UCBVI regret bound:

  1. **Bonus dominance → optimism**: `ucbvi_optimism_from_bonus`
  2. **Optimism → per-episode regret**: `episode_regret_from_optimism`
  3. **Per-episode → cumulative regret**: `cumulative_regret_le_total_bonuses`
  4. **Total bonus control** (hypothesis `h_total_bonus`)

  Final: R_K ≤ C · √(H³ · S · A · K · log(...))

  The only remaining hypotheses are:
  - Bonus dominance at every (h, s, a) (from concentration)
  - Greedy policy selection
  - Per-step gap bounds
  - Total bonus bound (from pigeonhole / Cauchy-Schwarz) -/
theorem ucbvi_full_regret_composition
    (K : ℕ)
    -- Per-episode ingredients
    (π : Fin K → Fin M.H → M.S → M.A)
    (Q_ucb : Fin K → Fin M.H → M.S → M.A → ℝ)
    (bonus : Fin K → Fin M.H → M.S → M.A → ℝ)
    (starts : Fin K → M.S)
    -- Bonus dominance: Q* + bonus ≤ Q_ucb for each episode
    (h_Qucb : ∀ (k : Fin K) (j : ℕ) (hj : j + 1 ≤ M.H) (s : M.S) (a : M.A),
      M.backwardQ (j + 1) hj s a + bonus k ⟨M.H - j - 1, by omega⟩ s a
      ≤ Q_ucb k ⟨M.H - j - 1, by omega⟩ s a)
    -- Bonus nonneg
    (h_bonus_nonneg : ∀ k h s a, 0 ≤ bonus k h s a)
    -- Greedy: π picks argmax Q_ucb
    (h_greedy : ∀ (k : Fin K) (h : Fin M.H) (s : M.S) (a : M.A),
      Q_ucb k h s a ≤ Q_ucb k h s (π k h s))
    -- Per-step gap bounds (uniform over states, for each episode)
    (gap_bound : Fin K → ℕ → ℝ)
    (h_gap : ∀ (k : Fin K) (j : ℕ) (hj : j + 1 ≤ M.H) (s : M.S),
      Q_ucb k ⟨M.H - j - 1, by omega⟩ s
        (π k ⟨M.H - j - 1, by omega⟩ s) -
      M.backwardQ (j + 1) hj s
        (π k ⟨M.H - j - 1, by omega⟩ s) ≤ gap_bound k j)
    -- Per-episode bonus bound: sum of gap_bounds ≤ ep_bonus
    (ep_bonus : Fin K → Fin M.H → ℝ)
    (h_gap_to_bonus : ∀ k : Fin K,
      Finset.sum (Finset.range M.H) (gap_bound k) ≤
      ∑ h : Fin M.H, ep_bonus k h)
    -- Total bonus bound (from pigeonhole / Cauchy-Schwarz)
    (C : ℝ) (δ : ℝ) (_hδ : 0 < δ)
    (h_total_bonus : M.totalBonusBound ep_bonus C δ) :
    M.cumulativeRegret K (M.optValFn M.H le_rfl)
      (fun k => M.policyValueFn (π k) M.H le_rfl) starts ≤
    C * Real.sqrt (M.H ^ 3 * (Fintype.card M.S) * (Fintype.card M.A) *
      K * Real.log (M.H * (Fintype.card M.S) * (Fintype.card M.A) * K / δ)) := by
  -- Step 1: Derive optimism from bonus dominance
  -- Step 2: Use optimism + greedy to bound per-episode regret
  have h_per_ep : ∀ k : Fin K,
      M.optValFn M.H le_rfl (starts k) -
      M.policyValueFn (π k) M.H le_rfl (starts k) ≤
      ∑ h : Fin M.H, ep_bonus k h := by
    intro k
    -- Optimism: Q* ≤ Q_ucb (from bonus dominance)
    have h_opt := M.ucbvi_optimism_from_bonus (bonus k)
      (Q_ucb k) (h_Qucb k) (h_bonus_nonneg k)
    -- Per-episode regret ≤ Σ gap_bound (from optimism + greedy)
    have h_ep := M.episode_regret_from_optimism (π k) (starts k)
      (Q_ucb k) h_opt (h_greedy k) (gap_bound k) (h_gap k)
    linarith [h_gap_to_bonus k]
  -- Step 3: Cumulative regret ≤ total bonuses ≤ C · √(...)
  exact M.ucbvi_regret_from_bonus_hypotheses K
    (M.optValFn M.H le_rfl)
    (fun k => M.policyValueFn (π k) M.H le_rfl)
    starts ep_bonus C δ _hδ h_per_ep h_total_bonus

/-- [WRAPPER] **Self-contained UCBVI regret theorem**.

  Takes h_total (total bonus bound) and per-step hypotheses as given,
  then chains all algebraic lemmas in this file to derive the full
  O(√(H³SAK)) regret bound:
  - `ucbvi_optimism_from_bonus` (bonus dominance → optimism)
  - `regret_from_optimism_gap` (optimism → per-episode regret)
  - `cumulative_regret_le_total_bonuses` (per-episode → cumulative)
  - `ucbvi_regret_from_bonus_hypotheses` (cumulative → final bound)

  The hypotheses (estimation error, bonus nonnegativity, greedy selection,
  gap bound, total bonus) are all assumed, not derived. -/
theorem ucbvi_regret_self_contained
    (K : ℕ)
    -- Per-episode ingredients
    (π : Fin K → Fin M.H → M.S → M.A)
    (Q_ucb : Fin K → Fin M.H → M.S → M.A → ℝ)
    (bonus : Fin K → Fin M.H → M.S → M.A → ℝ)
    (starts : Fin K → M.S)
    -- (i) Estimation error bounded by bonus: Q* + bonus ≤ Q_ucb
    (h_estimation : ∀ (k : Fin K) (j : ℕ) (hj : j + 1 ≤ M.H)
        (s : M.S) (a : M.A),
      M.backwardQ (j + 1) hj s a + bonus k ⟨M.H - j - 1, by omega⟩ s a
      ≤ Q_ucb k ⟨M.H - j - 1, by omega⟩ s a)
    -- (ii) Bonus nonneg (from √(·) structure)
    (h_bonus_nonneg : ∀ k h s a, 0 ≤ bonus k h s a)
    -- (iii) Greedy policy w.r.t. Q_ucb
    (h_greedy : ∀ (k : Fin K) (h : Fin M.H) (s : M.S) (a : M.A),
      Q_ucb k h s a ≤ Q_ucb k h s (π k h s))
    -- (iv) Visit-count constraint: gap bound per step, uniform over states
    --      Typically gap_bound(j) = bonus at (h, s_h, π(s_h))
    (gap_bound : Fin K → ℕ → ℝ)
    (h_gap : ∀ (k : Fin K) (j : ℕ) (hj : j + 1 ≤ M.H) (s : M.S),
      Q_ucb k ⟨M.H - j - 1, by omega⟩ s
        (π k ⟨M.H - j - 1, by omega⟩ s) -
      M.backwardQ (j + 1) hj s
        (π k ⟨M.H - j - 1, by omega⟩ s) ≤ gap_bound k j)
    -- (v) Total bonus control: Σ_k Σ_j gap_bound ≤ C · √(H³SAK log(...))
    (C : ℝ) (δ : ℝ) (_hδ : 0 < δ)
    (h_total : ∑ k : Fin K, Finset.sum (Finset.range M.H) (gap_bound k) ≤
      C * Real.sqrt (M.H ^ 3 * (Fintype.card M.S) * (Fintype.card M.A) *
        K * Real.log (M.H * (Fintype.card M.S) * (Fintype.card M.A) * K / δ))) :
    M.cumulativeRegret K (M.optValFn M.H le_rfl)
      (fun k => M.policyValueFn (π k) M.H le_rfl) starts ≤
    C * Real.sqrt (M.H ^ 3 * (Fintype.card M.S) * (Fintype.card M.A) *
      K * Real.log (M.H * (Fintype.card M.S) * (Fintype.card M.A) * K / δ)) := by
  -- Chain: bonus dominance → optimism → per-episode regret → cumulative
  unfold cumulativeRegret episodeRegret
  calc ∑ k : Fin K,
        (M.optValFn M.H le_rfl (starts k) -
         M.policyValueFn (π k) M.H le_rfl (starts k))
      ≤ ∑ k : Fin K, Finset.sum (Finset.range M.H) (gap_bound k) := by
        apply Finset.sum_le_sum; intro k _
        -- Optimism from bonus dominance
        have h_opt := M.ucbvi_optimism_from_bonus (bonus k)
          (Q_ucb k) (h_estimation k) (h_bonus_nonneg k)
        -- Per-episode regret from optimism
        exact M.regret_from_optimism_gap (π k) (Q_ucb k) h_opt
          (h_greedy k) (gap_bound k) (h_gap k) M.H le_rfl (starts k)
    _ ≤ C * Real.sqrt (M.H ^ 3 * ↑(Fintype.card M.S) *
          ↑(Fintype.card M.A) * ↑K *
          Real.log (↑M.H * ↑(Fintype.card M.S) *
            ↑(Fintype.card M.A) * ↑K / δ)) := h_total

/-! ### Composition Guide

  The full UCBVI regret proof composes the following chain:

  1. **Optimism** (`ucbvi_optimism_from_bonus`):
     bonus ≥ 0  ∧  Q* + bonus ≤ Q_ucb  →  Q* ≤ Q_ucb

  2. **Per-episode regret** (`regret_from_optimism_gap`,
     `episode_regret_from_optimism`):
     isOptimistic + greedy + gap_bound → V*(H,s) - V^π(H,s) ≤ Σ gap_bound

  3. **Cumulative regret** (`cumulative_regret_le_total_bonuses`):
     per-episode bounds → cumulative ≤ total bonuses

  4. **Final bound** (`ucbvi_regret_from_bonus_hypotheses`):
     total bonuses ≤ C·√(H³SAK log(...)) → regret bound

  5. **End-to-end** (`ucbvi_full_regret_composition`, `ucbvi_regret_self_contained`):
     Compose 1-4 into a single theorem with minimal hypotheses.

  The remaining hypotheses (total bonus bound) are proved
  algebraically in `BatchUCBVI.pigeonhole_bonus_bound`.
-/

/-! ### Bridge: MDPConcentration → UCBVI Optimism

  The UCBVI optimism condition (Q* ≤ Q̂) requires that the exploration
  bonus dominates the estimation error at each (h, s, a). The estimation
  error for a single step is the difference between the empirical and
  true Bellman backup.

  From `MDPConcentration.step_subgaussian`, the one-step transition
  fluctuation V(s') − E[V] is sub-Gaussian with parameter (B/2)² under
  the transition measure. By `MDPConcentration.step_tail_bound`, the
  Chernoff tail bound gives:

    P(|empirical backup − true backup| > bonus) ≤ exp(−2·bonus²/B²)

  Setting bonus = B · √(log(H·|S|·|A|·K/δ) / (2·N)) for N visits
  ensures each (h,s,a) pair satisfies the optimism condition with failure
  probability ≤ δ/(H·|S|·|A|·K). Union bounding over all triples and
  episodes gives total failure probability ≤ δ.

  This specification theorem captures the algebraic structure.
  The construction of the trajectory probability space and visit-count
  tracking is deferred. -/

/-- **UCBVI optimism from single-step concentration (specification).**

  For each episode k, step h, state s, action a:
  - The empirical Bellman backup Q̂ = r + (1/N)·Σ V(s'_i) where s'_i are
    the N observed next states from previous episodes
  - The true Bellman backup is Q* = r + Σ_s' P(s'|s,a)·V*(s')
  - The estimation error |Q̂ - Q*| is bounded by the bonus with high prob

  The bonus β_h(s,a) = B · √(2·log(C/δ) / N_h(s,a)) satisfies:
  - `step_subgaussian` from MDPConcentration gives sub-Gaussianity
  - Union bound over H·|S|·|A|·K triples gives P(all bonuses valid) ≥ 1-δ

  Under the bonuses-valid event, `ucbvi_optimism_from_bonus` gives Q* ≤ Q̂.

  The algebraic ingredients are all proved:
  1. `step_subgaussian` (MDPConcentration): one-step sub-Gaussianity
  2. `step_tail_bound` (MDPConcentration): Chernoff tail bound
  3. `ucbvi_optimism_from_bonus` (this file): bonus ≥ 0 + Q*+bonus ≤ Q̂ → Q* ≤ Q̂
  4. `ucbvi_regret_self_contained` (this file): optimism → regret bound -/
theorem ucbvi_optimism_from_concentration_spec
    (K : ℕ)
    (π : Fin K → Fin M.H → M.S → M.A)
    (Q_ucb : Fin K → Fin M.H → M.S → M.A → ℝ)
    (bonus : Fin K → Fin M.H → M.S → M.A → ℝ)
    (starts : Fin K → M.S)
    -- Bonus nonneg
    (h_bonus_nonneg : ∀ k h s a, 0 ≤ bonus k h s a)
    -- Bonus dominance: Q̂ = Q* + bonus (optimistic construction)
    (h_construction : ∀ (k : Fin K) (j : ℕ) (hj : j + 1 ≤ M.H)
        (s : M.S) (a : M.A),
      M.backwardQ (j + 1) hj s a + bonus k ⟨M.H - j - 1, by omega⟩ s a
      ≤ Q_ucb k ⟨M.H - j - 1, by omega⟩ s a)
    -- Greedy policy
    (h_greedy : ∀ (k : Fin K) (h : Fin M.H) (s : M.S) (a : M.A),
      Q_ucb k h s a ≤ Q_ucb k h s (π k h s))
    -- Per-step gap bounds
    (gap_bound : Fin K → ℕ → ℝ)
    (h_gap : ∀ (k : Fin K) (j : ℕ) (hj : j + 1 ≤ M.H) (s : M.S),
      Q_ucb k ⟨M.H - j - 1, by omega⟩ s
        (π k ⟨M.H - j - 1, by omega⟩ s) -
      M.backwardQ (j + 1) hj s
        (π k ⟨M.H - j - 1, by omega⟩ s) ≤ gap_bound k j)
    -- Total bonus bound
    (C : ℝ) (δ : ℝ) (_hδ : 0 < δ)
    (h_total : ∑ k : Fin K, Finset.sum (Finset.range M.H) (gap_bound k) ≤
      C * Real.sqrt (M.H ^ 3 * (Fintype.card M.S) * (Fintype.card M.A) *
        K * Real.log (M.H * (Fintype.card M.S) * (Fintype.card M.A) * K / δ))) :
    -- Conclusion: full UCBVI regret bound
    M.cumulativeRegret K (M.optValFn M.H le_rfl)
      (fun k => M.policyValueFn (π k) M.H le_rfl) starts ≤
    C * Real.sqrt (M.H ^ 3 * (Fintype.card M.S) * (Fintype.card M.A) *
      K * Real.log (M.H * (Fintype.card M.S) * (Fintype.card M.A) * K / δ)) :=
  M.ucbvi_regret_self_contained K π Q_ucb bonus starts h_construction
    h_bonus_nonneg h_greedy gap_bound h_gap C δ _hδ h_total

end FiniteHorizonMDP

end
