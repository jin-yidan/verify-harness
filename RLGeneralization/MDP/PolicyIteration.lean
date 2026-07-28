/-
# Policy Iteration

Formalizes contraction arguments that underlie policy iteration.

## Main Results

* `bellmanOptOp_monotone` - The Bellman optimality operator T is
  monotone: Q ≤ Q' implies TQ ≤ TQ' (elementwise).
* `sandwich_contraction` - Generic contraction: if
  TQ_old ≤ Q_new ≤ Q*, then ‖Q*-Q_new‖ ≤ γ·‖Q*-Q_old‖.
  (Captures the contraction step, without constructing the
  policy iteration sequence.)
* `policy_improvement_sandwich` - A genuine policy-iteration step
  satisfies `TQ_k ≤ Q_{k+1} ≤ Q*`.
* `policy_iteration_convergence` - Full policy-iteration convergence:
  if each `Q_k` evaluates `π_k` and `π_{k+1}` is greedy w.r.t. `Q_k`,
  then `‖Q* - Q_k‖ ≤ γ^k · ‖Q* - Q_0‖`.
* `sandwich_convergence` - Iterated sandwich convergence:
  ‖Q*-Q_k‖ ≤ γ^k·‖Q*-Q_0‖ for any sandwich sequence.
  (Captures the convergence rate, without constructing
  the policy iteration sequence.)

## References

* [Agarwal et al., *RL: Theory and Algorithms*][agarwal2026]
-/

import RLGeneralization.MDP.PerformanceDifference

open Finset BigOperators

noncomputable section

namespace FiniteMDP

variable (M : FiniteMDP)

/-! ### Value Reconstruction from Action Values -/

/-- The policy-weighted state-value function induced by an action-value function. -/
def valueFromQ (π : M.StochasticPolicy) (Q : M.ActionValueFn) : M.StateValueFn :=
  fun s => ∑ a, π.prob s a * Q s a

/-- If `Q` satisfies the Bellman evaluation equation for `π`, then the
policy-weighted action values satisfy the state-value Bellman equation. -/
theorem valueFromQ_isValueOf
    (π : M.StochasticPolicy)
    (Q : M.ActionValueFn)
    (hQ : M.isActionValueOf Q π) :
    M.isValueOf (M.valueFromQ π Q) π := by
  intro s
  dsimp [FiniteMDP.isValueOf, valueFromQ,
    FiniteMDP.expectedReward, FiniteMDP.expectedNextValue]
  calc
    ∑ a, π.prob s a * Q s a
      = ∑ a, π.prob s a *
          (M.r s a + M.γ * ∑ s', M.P s a s' *
            (∑ a', π.prob s' a' * Q s' a')) := by
            apply Finset.sum_congr rfl
            intro a _
            rw [hQ s a]
    _ = ∑ a, π.prob s a * M.r s a +
          ∑ a, π.prob s a *
            (M.γ * ∑ s', M.P s a s' *
              ∑ a', π.prob s' a' * Q s' a') := by
            simp_rw [mul_add]
            rw [Finset.sum_add_distrib]
    _ = ∑ a, π.prob s a * M.r s a +
          M.γ * ∑ a, π.prob s a *
            (∑ s', M.P s a s' *
              ∑ a', π.prob s' a' * Q s' a') := by
            congr 1
            have hscale :
                ∀ a, π.prob s a *
                  (M.γ * ∑ s', M.P s a s' * ∑ a', π.prob s' a' * Q s' a') =
                  M.γ * (π.prob s a *
                    ∑ s', M.P s a s' * ∑ a', π.prob s' a' * Q s' a') := by
              intro a
              ring
            simp_rw [hscale]
            exact (Finset.mul_sum _ _ _).symm

/-! ### Greedy Improvement Helpers -/

/-- The Bellman Q-evaluation operator is monotone. -/
theorem bellmanEvalOpQ_monotone (π : M.StochasticPolicy)
    (Q Q' : M.ActionValueFn)
    (hQQ' : ∀ s a, Q s a ≤ Q' s a) :
    ∀ s a, M.bellmanEvalOpQ π Q s a ≤ M.bellmanEvalOpQ π Q' s a := by
  intro s a
  unfold bellmanEvalOpQ
  have hinner : ∀ s',
      ∑ a', π.prob s' a' * Q s' a' ≤
        ∑ a', π.prob s' a' * Q' s' a' := by
    intro s'
    exact Finset.sum_le_sum (fun a' _ =>
      mul_le_mul_of_nonneg_left (hQQ' s' a') (π.prob_nonneg s' a'))
  have hsum :
      ∑ s', M.P s a s' * (∑ a', π.prob s' a' * Q s' a') ≤
        ∑ s', M.P s a s' * (∑ a', π.prob s' a' * Q' s' a') := by
    exact Finset.sum_le_sum (fun s' _ =>
      mul_le_mul_of_nonneg_left (hinner s') (M.P_nonneg s a s'))
  linarith [mul_le_mul_of_nonneg_left hsum M.γ_nonneg]

/-- Under the greedy policy for `Q`, the expected advantage of `Q`
relative to any baseline policy-weighted average of `Q` is nonnegative. -/
theorem greedy_expectedAdvantage_nonneg
    (π : M.StochasticPolicy)
    (Q : M.ActionValueFn) :
    ∀ s, 0 ≤ M.expectedAdvantage (M.greedyStochasticPolicy Q) Q (M.valueFromQ π Q) s := by
  intro s
  have havg_le :
      M.valueFromQ π Q s ≤
        Finset.univ.sup' Finset.univ_nonempty (Q s) := by
    unfold valueFromQ
    exact weighted_sum_le_max (π.prob s) (Q s)
      (π.prob_nonneg s) (π.prob_sum_one s)
  have hgreedy :
      M.expectedAdvantage (M.greedyStochasticPolicy Q) Q (M.valueFromQ π Q) s =
        Finset.univ.sup' Finset.univ_nonempty (Q s) -
          M.valueFromQ π Q s := by
    unfold expectedAdvantage advantage valueFromQ greedyStochasticPolicy
    simp [M.greedyAction_eq_sup]
  rw [hgreedy]
  linarith

/-- Greedy evaluation of `Q` agrees with the Bellman optimality operator on `Q`. -/
theorem bellmanEvalOpQ_greedy_eq_bellmanOptOp
    (Q : M.ActionValueFn) :
    ∀ s a,
      M.bellmanEvalOpQ (M.greedyStochasticPolicy Q) Q s a =
        M.bellmanOptOp Q s a := by
  intro s a
  unfold bellmanEvalOpQ bellmanOptOp greedyStochasticPolicy
  simp [M.greedyAction_eq_sup]

/-- Greedy policy improvement is monotone at the state-value level:
the value of the greedy policy for `Q_old` dominates the value of the
policy whose action-value is `Q_old`. -/
theorem greedy_policy_value_improves
    (π : M.StochasticPolicy)
    (Q_old Q_new : M.ActionValueFn)
    (hQ_old : M.isActionValueOf Q_old π)
    (hQ_new : M.isActionValueOf Q_new (M.greedyStochasticPolicy Q_old)) :
    let V_old := M.valueFromQ π Q_old
    let V_new := M.valueFromQ (M.greedyStochasticPolicy Q_old) Q_new
    ∀ s, V_old s ≤ V_new s := by
  intro V_old V_new
  have hV_old : M.isValueOf V_old π := by
    simpa [V_old] using M.valueFromQ_isValueOf π Q_old hQ_old
  have hV_new : M.isValueOf V_new (M.greedyStochasticPolicy Q_old) := by
    simpa [V_new] using
      M.valueFromQ_isValueOf (M.greedyStochasticPolicy Q_old) Q_new hQ_new
  have hQ_old_eval :
      ∀ s a, Q_old s a = M.r s a + M.γ * ∑ s', M.P s a s' * V_old s' := by
    intro s a
    simpa [V_old, valueFromQ] using hQ_old s a
  have hres := M.pdl_one_step (M.greedyStochasticPolicy Q_old) π
    V_new V_old Q_old hV_new hV_old hQ_old_eval
  have hdrive_nonneg :
      ∀ s, 0 ≤ M.expectedAdvantage (M.greedyStochasticPolicy Q_old) Q_old V_old s := by
    simpa [V_old] using M.greedy_expectedAdvantage_nonneg π Q_old
  by_contra hneg
  push_neg at hneg
  set Δ : M.StateValueFn := fun s => V_new s - V_old s
  have ⟨s₀, _, hs₀_min⟩ := Finset.exists_min_image
    Finset.univ Δ Finset.univ_nonempty
  have hs₀_neg : Δ s₀ < 0 := by
    obtain ⟨s₁, hs₁⟩ := hneg
    exact lt_of_le_of_lt (hs₀_min s₁ (Finset.mem_univ _)) (by simpa [Δ] using hs₁)
  have hΔ_ge : Δ s₀ ≥
      M.γ * M.expectedNextValue (M.greedyStochasticPolicy Q_old) Δ s₀ := by
    have hstep : Δ s₀ =
        M.expectedAdvantage (M.greedyStochasticPolicy Q_old) Q_old V_old s₀ +
          M.γ * M.expectedNextValue (M.greedyStochasticPolicy Q_old) Δ s₀ := by
      simpa [Δ] using hres s₀
    have hnonneg := hdrive_nonneg s₀
    linarith
  have havg_ge :
      M.expectedNextValue (M.greedyStochasticPolicy Q_old) Δ s₀ ≥ Δ s₀ := by
    unfold expectedNextValue
    calc
      ∑ a, (M.greedyStochasticPolicy Q_old).prob s₀ a *
          ∑ s', M.P s₀ a s' * Δ s'
        ≥ ∑ a, (M.greedyStochasticPolicy Q_old).prob s₀ a *
            ∑ s', M.P s₀ a s' * Δ s₀ := by
            apply Finset.sum_le_sum
            intro a _
            apply mul_le_mul_of_nonneg_left
            · apply Finset.sum_le_sum
              intro s' _
              exact mul_le_mul_of_nonneg_left
                (hs₀_min s' (Finset.mem_univ s'))
                (M.P_nonneg s₀ a s')
            · exact (M.greedyStochasticPolicy Q_old).prob_nonneg s₀ a
      _ = Δ s₀ := by
          simp_rw [← Finset.sum_mul, M.P_sum_one s₀,
            one_mul, ← Finset.sum_mul,
            (M.greedyStochasticPolicy Q_old).prob_sum_one, one_mul]
  have hfinal : Δ s₀ ≥ M.γ * Δ s₀ :=
    le_trans (mul_le_mul_of_nonneg_left havg_ge M.γ_nonneg) hΔ_ge
  nlinarith [M.γ_lt_one, hs₀_neg]

/-! ### Genuine Policy Iteration Step -/

/-- A genuine policy-iteration step satisfies the sandwich inequality
`TQ_old ≤ Q_new ≤ Q*`. -/
theorem policy_improvement_sandwich
    (Q_old Q_new Q_star : M.ActionValueFn)
    (π_old : M.StochasticPolicy)
    (hQ_old : M.isActionValueOf Q_old π_old)
    (hQ_new : M.isActionValueOf Q_new (M.greedyStochasticPolicy Q_old))
    (hQ_star : ∀ s a, Q_star s a = M.bellmanOptOp Q_star s a) :
    (∀ s a, M.bellmanOptOp Q_old s a ≤ Q_new s a) ∧
    (∀ s a, Q_new s a ≤ Q_star s a) := by
  let π_new := M.greedyStochasticPolicy Q_old
  let V_old := M.valueFromQ π_old Q_old
  let V_new := M.valueFromQ π_new Q_new
  let V_star : M.StateValueFn :=
    fun s => Finset.univ.sup' Finset.univ_nonempty (Q_star s)
  have hV_new_ge_old : ∀ s, V_old s ≤ V_new s := by
    simpa [π_new, V_old, V_new] using
      M.greedy_policy_value_improves π_old Q_old Q_new hQ_old hQ_new
  have hQ_old_le_new : ∀ s a, Q_old s a ≤ Q_new s a := by
    intro s a
    have h_old : Q_old s a =
        M.r s a + M.γ * ∑ s', M.P s a s' * V_old s' := by
      simpa [V_old, valueFromQ] using hQ_old s a
    have h_new : Q_new s a =
        M.r s a + M.γ * ∑ s', M.P s a s' * V_new s' := by
      simpa [π_new, V_new, valueFromQ] using hQ_new s a
    have hsum :
        ∑ s', M.P s a s' * V_old s' ≤
          ∑ s', M.P s a s' * V_new s' := by
      exact Finset.sum_le_sum (fun s' _ =>
        mul_le_mul_of_nonneg_left (hV_new_ge_old s') (M.P_nonneg s a s'))
    linarith [mul_le_mul_of_nonneg_left hsum M.γ_nonneg, h_old, h_new]
  have hlower : ∀ s a, M.bellmanOptOp Q_old s a ≤ Q_new s a := by
    intro s a
    calc
      M.bellmanOptOp Q_old s a
        = M.bellmanEvalOpQ π_new Q_old s a := by
            symm
            exact M.bellmanEvalOpQ_greedy_eq_bellmanOptOp Q_old s a
      _ ≤ M.bellmanEvalOpQ π_new Q_new s a :=
            M.bellmanEvalOpQ_monotone π_new Q_old Q_new hQ_old_le_new s a
      _ = Q_new s a := by
            symm
            exact hQ_new s a
  have hopt := M.optimal_policy_exists Q_star hQ_star
  rcases hopt with ⟨hV_star, hV_star_dom⟩
  have hV_new : M.isValueOf V_new π_new := by
    simpa [π_new, V_new] using M.valueFromQ_isValueOf π_new Q_new hQ_new
  have hVnew_le_star : ∀ s, V_new s ≤ V_star s := hV_star_dom π_new V_new hV_new
  have hupper : ∀ s a, Q_new s a ≤ Q_star s a := by
    intro s a
    have h_new : Q_new s a =
        M.r s a + M.γ * ∑ s', M.P s a s' * V_new s' := by
      simpa [π_new, V_new, valueFromQ] using hQ_new s a
    have h_star : Q_star s a =
        M.r s a + M.γ * ∑ s', M.P s a s' * V_star s' := by
      rw [hQ_star s a]
      simp [bellmanOptOp, V_star]
    have hsum :
        ∑ s', M.P s a s' * V_new s' ≤
          ∑ s', M.P s a s' * V_star s' := by
      exact Finset.sum_le_sum (fun s' _ =>
        mul_le_mul_of_nonneg_left (hVnew_le_star s') (M.P_nonneg s a s'))
    linarith [mul_le_mul_of_nonneg_left hsum M.γ_nonneg, h_new, h_star]
  exact ⟨hlower, hupper⟩

/-! ### Monotonicity of the Bellman Optimality Operator -/

/-- **Monotonicity of T**.

  If Q(s,a) ≤ Q'(s,a) for all (s,a), then
  (TQ)(s,a) ≤ (TQ')(s,a) for all (s,a).

  This follows because max_a Q(s',a) ≤ max_a Q'(s',a)
  and transition probabilities are nonneg. -/
theorem bellmanOptOp_monotone (Q Q' : M.ActionValueFn)
    (h : ∀ s a, Q s a ≤ Q' s a) :
    ∀ s a, M.bellmanOptOp Q s a ≤ M.bellmanOptOp Q' s a := by
  intro s a
  simp only [bellmanOptOp]
  -- r + γ∑P·supQ ≤ r + γ∑P·supQ'
  have hsup_le : ∀ s', Finset.univ.sup' Finset.univ_nonempty
      (fun a' => Q s' a') ≤
      Finset.univ.sup' Finset.univ_nonempty
        (fun a' => Q' s' a') := by
    intro s'
    apply Finset.sup'_le; intro a' _
    exact le_trans (h s' a')
      (Finset.le_sup' (fun a' => Q' s' a') (Finset.mem_univ a'))
  have hsum_le : ∑ s', M.P s a s' *
      Finset.univ.sup' Finset.univ_nonempty (fun a' => Q s' a') ≤
      ∑ s', M.P s a s' *
        Finset.univ.sup' Finset.univ_nonempty (fun a' => Q' s' a') := by
    apply Finset.sum_le_sum; intro s' _
    exact mul_le_mul_of_nonneg_left (hsup_le s') (M.P_nonneg s a s')
  linarith [mul_le_mul_of_nonneg_left hsum_le M.γ_nonneg]

/-! ### Sandwich Contraction Lemma -/

/-- **Sandwich contraction**.

  Generic sandwich lemma: if L ≤ Q ≤ U with L = T(Q_old) and
  U = Q*, and ‖U - L‖_∞ ≤ d, then ‖TU - TL‖_∞ ≤ γd.
  More precisely: if T(Q_old) ≤ Q_new ≤ Q* elementwise, then
    ‖Q* - Q_new‖_∞ ≤ γ · ‖Q* - Q_old‖_∞

  Proof:
    0 ≤ Q* - Q_new ≤ Q* - TQ_old = TQ* - TQ_old
  Taking norms: ‖Q*-Q_new‖ ≤ ‖TQ*-TQ_old‖ ≤ γ‖Q*-Q_old‖

  **Caveat**: This isolates only the contraction step. A full
  policy-iteration proof also needs the earlier steps showing that
  policy iteration
  produces a sequence satisfying this sandwich, which requires
  policy evaluation and greedy improvement (not formalized). -/
theorem sandwich_contraction
    (Q_old Q_new Q_star : M.ActionValueFn)
    -- Q* is a fixed point of T
    (hQ_star : Q_star = M.bellmanOptOp Q_star)
    -- Sandwich: TQ_old ≤ Q_new ≤ Q*
    (h_lower : ∀ s a,
      M.bellmanOptOp Q_old s a ≤ Q_new s a)
    (h_upper : ∀ s a, Q_new s a ≤ Q_star s a) :
    M.supDistQ Q_new Q_star ≤
      M.γ * M.supDistQ Q_old Q_star := by
  -- Goal: sup |Q_new - Q*| ≤ γ sup |Q_old - Q*|
  -- Since Q_new ≤ Q* elementwise, |Q_new - Q*| = Q* - Q_new
  -- Since TQ_old ≤ Q_new, we have Q* - Q_new ≤ Q* - TQ_old
  -- Q* = TQ*, so Q* - TQ_old = TQ* - TQ_old
  -- By contraction: ‖TQ* - TQ_old‖ ≤ γ‖Q* - Q_old‖
  simp only [supDistQ, supNormQ]
  apply Finset.sup'_le; intro s _
  apply Finset.sup'_le; intro a _
  -- |Q_new s a - Q_star s a| = Q_star s a - Q_new s a
  --   (since Q_new ≤ Q_star)
  have h_diff : |Q_new s a - Q_star s a| =
      Q_star s a - Q_new s a := by
    rw [abs_of_nonpos (by linarith [h_upper s a])]; ring
  rw [h_diff]
  -- Q* s a - Q_new s a ≤ Q* s a - TQ_old s a
  --   = TQ* s a - TQ_old s a ≤ |TQ* s a - TQ_old s a|
  have h1 : Q_star s a - Q_new s a ≤
      Q_star s a - M.bellmanOptOp Q_old s a := by
    linarith [h_lower s a]
  have h2 : Q_star s a - M.bellmanOptOp Q_old s a =
      M.bellmanOptOp Q_star s a -
        M.bellmanOptOp Q_old s a := by
    rw [show Q_star s a = M.bellmanOptOp Q_star s a from
      congr_fun (congr_fun hQ_star s) a]
  -- |TQ* - TQ_old| ≤ sup |TQ* - TQ_old| ≤ γ sup |Q* - Q_old|
  calc Q_star s a - Q_new s a
      ≤ M.bellmanOptOp Q_star s a -
          M.bellmanOptOp Q_old s a := by linarith [h1, h2]
    _ ≤ |M.bellmanOptOp Q_star s a -
          M.bellmanOptOp Q_old s a| := le_abs_self _
    _ ≤ Finset.univ.sup' Finset.univ_nonempty (fun a =>
          |M.bellmanOptOp Q_star s a -
            M.bellmanOptOp Q_old s a|) :=
        Finset.le_sup' (fun a =>
          |M.bellmanOptOp Q_star s a -
            M.bellmanOptOp Q_old s a|)
          (Finset.mem_univ a)
    _ ≤ M.supDistQ (M.bellmanOptOp Q_star)
          (M.bellmanOptOp Q_old) := by
        simp only [supDistQ, supNormQ]
        exact Finset.le_sup' (fun s =>
          Finset.univ.sup' Finset.univ_nonempty (fun a =>
            |M.bellmanOptOp Q_star s a -
              M.bellmanOptOp Q_old s a|))
          (Finset.mem_univ s)
    _ ≤ M.γ * M.supDistQ Q_star Q_old :=
        M.bellmanOptOp_contraction Q_star Q_old
    _ = M.γ * M.supDistQ Q_old Q_star := by
        -- supDistQ is symmetric: |Q* - Q_old| = |Q_old - Q*|
        simp only [supDistQ, supNormQ]
        congr 1; congr 1; funext s; congr 1; funext a
        exact abs_sub_comm (Q_star s a) (Q_old s a)

/-! ### Iterated Sandwich Convergence -/

/-- **Sandwich convergence**.

  If a sandwich sequence contracts (i.e., T(Q_k) ≤ Q_{k+1} ≤ Q*
  at each step), then it converges geometrically:
    ‖Q* - Q_k‖_∞ ≤ γ^k · ‖Q* - Q_0‖_∞

  This captures the convergence rate for any
  sequence satisfying the sandwich property.

  **Caveat**: A full policy-iteration convergence theorem additionally constructs
  the policy iteration sequence and shows it satisfies the
  sandwich property. That construction requires:
  1. Policy evaluation (compute Q^π via Bellman equation)
  2. Greedy improvement (π_{k+1} = argmax Q^{π_k})
  3. The sandwich proof establishing the sandwich property
  None of these are formalized here. -/
theorem sandwich_convergence
    (Q_star : M.ActionValueFn)
    (hQ_star : Q_star = M.bellmanOptOp Q_star)
    -- Sequence of Q-functions from policy iteration
    (Q_seq : ℕ → M.ActionValueFn)
    -- Each step satisfies the sandwich
    (h_sandwich : ∀ k, (∀ s a,
      M.bellmanOptOp (Q_seq k) s a ≤ Q_seq (k + 1) s a) ∧
      (∀ s a, Q_seq (k + 1) s a ≤ Q_star s a))
    (k : ℕ) :
    M.supDistQ (Q_seq k) Q_star ≤
      M.γ ^ k * M.supDistQ (Q_seq 0) Q_star := by
  induction k with
  | zero => simp
  | succ n ih =>
    calc M.supDistQ (Q_seq (n + 1)) Q_star
        ≤ M.γ * M.supDistQ (Q_seq n) Q_star :=
          M.sandwich_contraction (Q_seq n)
            (Q_seq (n + 1)) Q_star hQ_star
            (h_sandwich n).1 (h_sandwich n).2
      _ ≤ M.γ * (M.γ ^ n *
            M.supDistQ (Q_seq 0) Q_star) :=
          mul_le_mul_of_nonneg_left ih M.γ_nonneg
      _ = M.γ ^ (n + 1) *
            M.supDistQ (Q_seq 0) Q_star := by
          rw [pow_succ]; ring

/-! ### Full Policy Iteration Convergence -/

/-- Full policy-iteration convergence: if each `Q_k` evaluates `π_k`
and `π_{k+1}` is greedy with respect to `Q_k`, then the sequence
contracts geometrically to any Bellman-optimal fixed point `Q*`. -/
theorem policy_iteration_convergence
    (Q_star : M.ActionValueFn)
    (hQ_star : Q_star = M.bellmanOptOp Q_star)
    (π_seq : ℕ → M.StochasticPolicy)
    (Q_seq : ℕ → M.ActionValueFn)
    (h_eval : ∀ k, M.isActionValueOf (Q_seq k) (π_seq k))
    (h_greedy : ∀ k, π_seq (k + 1) = M.greedyStochasticPolicy (Q_seq k))
    (k : ℕ) :
    M.supDistQ (Q_seq k) Q_star ≤
      M.γ ^ k * M.supDistQ (Q_seq 0) Q_star := by
  have hQ_star_pt : ∀ s a, Q_star s a = M.bellmanOptOp Q_star s a := by
    intro s a
    exact congrFun (congrFun hQ_star s) a
  apply M.sandwich_convergence Q_star hQ_star Q_seq
  intro n
  have hstep := M.policy_improvement_sandwich
    (Q_seq n) (Q_seq (n + 1)) Q_star (π_seq n)
    (h_eval n)
    (by simpa [h_greedy n] using h_eval (n + 1))
    hQ_star_pt
  exact hstep

end FiniteMDP

end
