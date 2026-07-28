/-
# Resolvent Bound and Bellman Fixed Point Optimality

Formalizes three foundational resolvent and Bellman fixed-point results:

## Main Results

* `resolvent_bound` - If V satisfies the
  Bellman-like equation V = v + γP^πV, then ‖V‖ ≤ ‖v‖/(1-γ).
* `bellman_fixed_point_dominates` - If Q = TQ (fixed point of T), then the greedy value
  max_a Q(s,a) ≥ V^π(s) for any policy π.
* `crude_value_bound` - Deterministic model-error propagation through the resolvent.

## References

* [Agarwal et al., *RL: Theory and Algorithms*][agarwal2026]
-/

import RLGeneralization.MDP.SimulationLemma

open Finset BigOperators

noncomputable section

namespace FiniteMDP

variable (M : FiniteMDP)

/-! ### Resolvent Bound -/

/-- **Resolvent bound**.

  If V satisfies V(s) = v(s) + γ · P^π V(s) for some driving
  term v, then ‖(I - γP^π)⁻¹v‖_∞ ≤ ‖v‖_∞ / (1-γ).

  In matrix notation: V = (I - γP^π)⁻¹v, so this bounds the
  resolvent operator norm by 1/(1-γ).

  Proof sketch:
    v = V - γP^πV, so ‖v‖ ≥ ‖V‖ - γ‖V‖ = (1-γ)‖V‖.
  Rearranging: ‖V‖ ≤ ‖v‖/(1-γ).

  **Caveat**: We prove only the norm bound, not the matrix
  identity V = (I - γP^π)⁻¹v. The Lean formalization avoids
  matrix inverses entirely, working instead with the functional
  equation V = v + γP^πV as the hypothesis. -/
theorem resolvent_bound (π : M.StochasticPolicy)
    (V v : M.StateValueFn)
    -- V = v + γ P^π V  (i.e., V solves the resolvent equation)
    (hV : ∀ s, V s = v s +
      M.γ * M.expectedNextValue π V s) :
    ∀ s, |V s| ≤ M.supNormV v / (1 - M.γ) := by
  -- Same structure as value_bounded_by_Vmax
  set Vmax := M.supNormV v
  set D := M.supNormV V
  have h1g : (0 : ℝ) < 1 - M.γ := by linarith [M.γ_lt_one]
  -- Step 1: |V(s)| ≤ Vmax + γ D for each s
  have hstep : ∀ s, |V s| ≤ Vmax + M.γ * D := by
    intro s
    rw [hV s]
    calc |v s + M.γ * M.expectedNextValue π V s|
        ≤ |v s| + |M.γ * M.expectedNextValue π V s| :=
          abs_add_le _ _
      _ ≤ Vmax + M.γ * D := by
          apply add_le_add
          · exact Finset.le_sup' (fun s => |v s|)
              (Finset.mem_univ s)
          · rw [abs_mul, abs_of_nonneg M.γ_nonneg]
            apply mul_le_mul_of_nonneg_left _ M.γ_nonneg
            apply abs_weighted_sum_le_bound _ _ D
              (π.prob_nonneg s) (π.prob_sum_one s)
            intro a
            apply abs_weighted_sum_le_bound _ _ D
              (M.P_nonneg s a) (M.P_sum_one s a)
            intro s'
            exact Finset.le_sup' (fun s => |V s|)
              (Finset.mem_univ s')
  -- Step 2: D ≤ Vmax + γ D, so D ≤ Vmax/(1-γ)
  have hsup : D ≤ Vmax + M.γ * D :=
    Finset.sup'_le _ _ (fun s _ => hstep s)
  have hD : D ≤ Vmax / (1 - M.γ) := by
    rw [le_div_iff₀ h1g]; nlinarith
  -- Step 3: Pointwise
  intro s
  calc |V s| ≤ D :=
        Finset.le_sup' (fun s => |V s|) (Finset.mem_univ s)
    _ ≤ Vmax / (1 - M.γ) := hD

/-! ### Helper: Weighted Average ≤ Maximum -/

/-- Weighted average is at most the maximum (one-sided version
    of `abs_weighted_sum_le_bound`). -/
lemma weighted_sum_le_max {ι : Type*} [Fintype ι] [Nonempty ι]
    (w f : ι → ℝ) (hw_nonneg : ∀ i, 0 ≤ w i)
    (hw_sum : ∑ i, w i = 1) :
    ∑ i, w i * f i ≤
      Finset.univ.sup' Finset.univ_nonempty f := by
  calc ∑ i, w i * f i
      ≤ ∑ i, w i *
          Finset.univ.sup' Finset.univ_nonempty f := by
        apply Finset.sum_le_sum; intro i _
        exact mul_le_mul_of_nonneg_left
          (Finset.le_sup' f (Finset.mem_univ i))
          (hw_nonneg i)
    _ = (∑ i, w i) *
          Finset.univ.sup' Finset.univ_nonempty f :=
        (Finset.sum_mul _ _ _).symm
    _ = Finset.univ.sup' Finset.univ_nonempty f := by
        rw [hw_sum, one_mul]

/-! ### One-Sided Resolvent Bounds -/

/-- **One-sided resolvent bound** (upper).
  If V = v + γP^πV and v(s) ≤ B for all s, then V(s) ≤ B/(1-γ).
  Used for the component-wise value-comparison bounds. -/
theorem resolvent_upper (π : M.StochasticPolicy)
    (V v : M.StateValueFn) (B : ℝ)
    (hV : ∀ s, V s = v s + M.γ * M.expectedNextValue π V s)
    (hv : ∀ s, v s ≤ B) :
    ∀ s, V s ≤ B / (1 - M.γ) := by
  set D := Finset.univ.sup' Finset.univ_nonempty (fun s => V s)
  have h1g : (0 : ℝ) < 1 - M.γ := by linarith [M.γ_lt_one]
  -- V(s) ≤ B + γD for each s
  have hstep : ∀ s, V s ≤ B + M.γ * D := by
    intro s; rw [hV s]
    -- nextValue ≤ D (weighted avg ≤ max)
    have hnext : M.expectedNextValue π V s ≤ D := by
      unfold expectedNextValue
      exact le_trans
        (weighted_sum_le_max (π.prob s) _
          (π.prob_nonneg s) (π.prob_sum_one s))
        (Finset.sup'_le _ _ fun a _ =>
          weighted_sum_le_max (M.P s a) V
            (M.P_nonneg s a) (M.P_sum_one s a))
    linarith [hv s, mul_le_mul_of_nonneg_left hnext M.γ_nonneg]
  have hsup : D ≤ B + M.γ * D :=
    Finset.sup'_le _ _ (fun s _ => hstep s)
  have hD : D ≤ B / (1 - M.γ) := by
    rw [le_div_iff₀ h1g]; nlinarith
  intro s
  exact le_trans (Finset.le_sup' _ (Finset.mem_univ s)) hD

/-! ### Bellman Fixed Point Optimality -/

/-- **Bellman fixed point dominates policy values**.

  If Q is a fixed point of the Bellman optimality operator
  (Q = TQ), then V_Q(s) = max_a Q(s,a) dominates all policy
  values: V_Q(s) ≥ V^π(s) for every policy π and state s.

  Proof by minimum principle (avoids trajectory expectations):
  Let Δ(s) = V_Q(s) - V^π(s). From the Bellman equations:
    Δ(s) ≥ γ · P^π Δ(s)
  If min_s Δ(s) < 0, let s₀ achieve the minimum. Then
    Δ(s₀) ≥ γ·Δ(s₀) > Δ(s₀) since Δ(s₀) < 0 and γ < 1. □

  **Caveat**: This proves the dominance direction of Theorem
  1.7/1.8. A common presentation additionally constructs the optimal policy
  via trajectory arguments; we prove dominance algebraically
  via the minimum principle instead. -/
theorem bellman_fixed_point_dominates
    -- Q is a fixed point of T: Q = TQ
    (Q : M.ActionValueFn)
    (hQ : ∀ s a, Q s a = M.bellmanOptOp Q s a)
    -- V_Q(s) = max_a Q(s,a)
    (V_Q : M.StateValueFn)
    (hV_Q : ∀ s, V_Q s =
      Finset.univ.sup' Finset.univ_nonempty (Q s))
    -- π is any policy with value V^π
    (π : M.StochasticPolicy)
    (V_pi : M.StateValueFn)
    (hV_pi : M.isValueOf V_pi π) :
    ∀ s, V_pi s ≤ V_Q s := by
  -- Proof by minimum principle (avoids trajectories)
  by_contra h_neg
  push_neg at h_neg
  -- Find the state with minimum gap Δ(s) = V_Q(s) - V^π(s)
  set Δ := fun s => V_Q s - V_pi s
  have ⟨s₀, _, hs₀_min⟩ := Finset.exists_min_image
    Finset.univ Δ Finset.univ_nonempty
  have hs₀_neg : Δ s₀ < 0 := by
    obtain ⟨s₁, hs₁⟩ := h_neg
    exact lt_of_le_of_lt (hs₀_min s₁ (Finset.mem_univ _))
      (by linarith)
  -- Step 1: V_Q(s) ≥ bellmanEvalOp π V_Q s for all s
  -- (sup ≥ weighted avg, using Q(s,a) = r + γPV_Q)
  have hVQ_ge_bellman : ∀ s,
      V_Q s ≥ M.bellmanEvalOp π V_Q s := by
    intro s; rw [hV_Q s]; unfold bellmanEvalOp
    -- sup Q(s,·) ≥ ∑ π(a) Q(s,a)
    -- and ∑ π(a) Q(s,a) = expectedReward + γ expectedNextValue
    --                    = bellmanEvalOp π V_Q s
    -- when Q(s,a) = r + γPV_Q
    have hQ_eq : ∀ a, Q s a = M.r s a + M.γ *
        ∑ s', M.P s a s' * V_Q s' := by
      intro a; rw [hQ s a]; simp only [bellmanOptOp]
      simp_rw [← hV_Q]
    calc Finset.univ.sup' Finset.univ_nonempty (Q s)
        ≥ ∑ a, π.prob s a * Q s a :=
          weighted_sum_le_max (π.prob s) (Q s)
            (π.prob_nonneg s) (π.prob_sum_one s)
      _ = M.expectedReward π s +
          M.γ * M.expectedNextValue π V_Q s := by
          unfold expectedReward expectedNextValue
          simp_rw [hQ_eq, mul_add, Finset.sum_add_distrib]
          congr 1
          -- ∑ π(a) * (γ * ∑P V_Q) = γ * ∑ π(a) * ∑P V_Q
          have : ∀ x, π.prob s x *
              (M.γ * ∑ s', M.P s x s' * V_Q s') =
              M.γ * (π.prob s x *
                ∑ s', M.P s x s' * V_Q s') :=
            fun x => by ring
          simp_rw [this]; exact (Finset.mul_sum _ _ _).symm
  -- Step 2: Δ(s) ≥ γ · expectedNextValue π Δ s
  -- V_Q ≥ bellmanEvalOp π V_Q, V^π = bellmanEvalOp π V^π
  -- difference = γ (nextValue V_Q - nextValue V^π)
  have hΔ_ge : Δ s₀ ≥ M.γ *
      M.expectedNextValue π Δ s₀ := by
    have h1 := hVQ_ge_bellman s₀
    have h2 := hV_pi s₀
    -- bellmanEvalOp difference = γ · expectedNextValue Δ
    -- bellmanEvalOp difference = γ · expectedNextValue Δ
    -- (rewards cancel, leaving γ times transition diff)
    have hdiff : M.bellmanEvalOp π V_Q s₀ -
        M.bellmanEvalOp π V_pi s₀ =
        M.γ * (M.expectedNextValue π V_Q s₀ -
          M.expectedNextValue π V_pi s₀) := by
      simp only [bellmanEvalOp]; ring
    have hnext_eq : M.expectedNextValue π V_Q s₀ -
        M.expectedNextValue π V_pi s₀ =
        M.expectedNextValue π Δ s₀ := by
      unfold expectedNextValue
      rw [← Finset.sum_sub_distrib]
      congr 1; funext a; rw [← mul_sub]
      congr 1; rw [← Finset.sum_sub_distrib]
      congr 1; funext s'; ring
    -- V_pi s₀ = bellmanEvalOp π V_pi s₀ (from isValueOf)
    have h2_bell : M.bellmanEvalOp π V_pi s₀ = V_pi s₀ := by
      unfold bellmanEvalOp; linarith [hV_pi s₀]
    -- Chain: Δ ≥ bellman V_Q - bellman V_pi = γ nextV Δ
    have step1 : V_Q s₀ - V_pi s₀ ≥
        M.bellmanEvalOp π V_Q s₀ -
        M.bellmanEvalOp π V_pi s₀ := by linarith [h2_bell]
    have step2 : M.bellmanEvalOp π V_Q s₀ -
        M.bellmanEvalOp π V_pi s₀ =
        M.γ * M.expectedNextValue π Δ s₀ := by
      rw [hdiff, hnext_eq]
    linarith
  -- Step 3: expectedNextValue π Δ s₀ ≥ Δ s₀
  -- (weighted avg ≥ min, since Δ(s₀) = min Δ)
  have havg_ge : M.expectedNextValue π Δ s₀ ≥ Δ s₀ := by
    unfold expectedNextValue
    calc ∑ a, π.prob s₀ a * ∑ s', M.P s₀ a s' * Δ s'
        ≥ ∑ a, π.prob s₀ a *
            ∑ s', M.P s₀ a s' * Δ s₀ := by
          apply Finset.sum_le_sum; intro a _
          apply mul_le_mul_of_nonneg_left _
            (π.prob_nonneg s₀ a)
          apply Finset.sum_le_sum; intro s' _
          exact mul_le_mul_of_nonneg_left
            (hs₀_min s' (Finset.mem_univ s'))
            (M.P_nonneg s₀ a s')
      _ = Δ s₀ := by
          -- ∑ π(a) * (∑ P * Δ(s₀)) = ∑ π(a) * Δ(s₀) = Δ(s₀)
          simp_rw [← Finset.sum_mul, M.P_sum_one s₀,
            one_mul, ← Finset.sum_mul, π.prob_sum_one, one_mul]
  -- Contradiction: Δ(s₀) ≥ γ·avg ≥ γ·Δ(s₀) > Δ(s₀)
  have h_final : Δ s₀ ≥ M.γ * Δ s₀ :=
    le_trans (mul_le_mul_of_nonneg_left havg_ge M.γ_nonneg) hΔ_ge
  -- γ·x > x when x < 0 and γ < 1
  nlinarith [M.γ_lt_one, hs₀_neg]

/-! ### Crude Value Bound -/

/-- **Fixed-Policy Simulation Bound** (re-export of `simulation_lemma`).

  For a FIXED policy π, bounds ‖V^π_M - V^π_{M̂}‖ given
  model errors ε_R and ε_T.

  **This is NOT the optimality-gap statement**, which bounds the
  OPTIMAL value gap ‖Q* - Q̂*‖. That result
  additionally requires:
  - component-wise bounds using the resolvent
  - The fact that π̂* optimal in M̂ implies Q̂* ≥ Q̂^{π*}
  Neither is formalized here. -/
theorem crude_value_bound
    (M_hat : M.ApproxMDP)
    (π : M.StochasticPolicy)
    (V_M V_Mhat : M.StateValueFn)
    (hV_M : M.isValueOf V_M π)
    (hV_Mhat : ∀ s, V_Mhat s =
      (∑ a, π.prob s a * M_hat.r_hat s a) +
      M.γ * (∑ a, π.prob s a *
        ∑ s', M_hat.P_hat s a s' * V_Mhat s'))
    (B : ℝ) (hB : 0 ≤ B)
    (hV_Mhat_bound : ∀ s, |V_Mhat s| ≤ B)
    (ε_R : ℝ) (hε_R : M.rewardError M_hat ≤ ε_R)
    (ε_T : ℝ) (hε_T : M.transitionError M_hat ≤ ε_T) :
    ∀ s, |V_M s - V_Mhat s| ≤
      (ε_R + M.γ * B * ε_T) / (1 - M.γ) :=
  -- This is exactly our simulation_lemma
  M.simulation_lemma M_hat π V_M V_Mhat hV_M hV_Mhat
    B hB hV_Mhat_bound ε_R hε_R ε_T hε_T

/-! ### Greedy Stochastic Policy Construction -/

/-- The deterministic-greedy policy expressed as a `StochasticPolicy`.
    Puts probability 1 on `greedyAction Q s` and 0 elsewhere. -/
def greedyStochasticPolicy (Q : M.ActionValueFn) : M.StochasticPolicy where
  prob := fun s a => if a = M.greedyAction Q s then 1 else 0
  prob_nonneg := fun s a => by split <;> norm_num
  prob_sum_one := fun s => by
    have : ∀ a, (if a = M.greedyAction Q s then (1 : ℝ) else 0) =
      (if a = M.greedyAction Q s then 1 else 0) := fun _ => rfl
    trans ∑ a ∈ Finset.univ,
      (if a = M.greedyAction Q s then (1 : ℝ) else 0)
    · rfl
    · rw [Finset.sum_ite_eq']
      exact if_pos (Finset.mem_univ _)

/-- Helper: For a deterministic policy putting all weight on action `a₀`,
    `∑ a, (if a = a₀ then 1 else 0) * f a = f a₀`. -/
private lemma sum_ite_eq_eval {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a₀ : ι) (f : ι → ℝ) :
    ∑ a, (if a = a₀ then (1 : ℝ) else 0) * f a = f a₀ := by
  simp [Finset.sum_ite_eq' Finset.univ a₀, Finset.mem_univ]

/-- The expected reward under the greedy policy equals the reward
    at the greedy action. -/
lemma greedyPolicy_expectedReward (Q : M.ActionValueFn) (s : M.S) :
    M.expectedReward (M.greedyStochasticPolicy Q) s =
    M.r s (M.greedyAction Q s) := by
  unfold expectedReward greedyStochasticPolicy
  simp only
  exact sum_ite_eq_eval (M.greedyAction Q s) (M.r s)

/-- The expected next-state value under the greedy policy equals
    the transition-weighted sum at the greedy action. -/
lemma greedyPolicy_expectedNextValue (Q : M.ActionValueFn)
    (V : M.StateValueFn) (s : M.S) :
    M.expectedNextValue (M.greedyStochasticPolicy Q) V s =
    ∑ s', M.P s (M.greedyAction Q s) s' * V s' := by
  unfold expectedNextValue greedyStochasticPolicy
  simp only
  exact sum_ite_eq_eval (M.greedyAction Q s)
    (fun a => ∑ s', M.P s a s' * V s')

/-! ### Optimal Policy Existence -/

/-- **Optimal policy existence**.

  The greedy policy π*(s) = argmax_a Q*(s,a) w.r.t. the Bellman
  fixed point Q* achieves V* = V^{π*}, i.e., V*(s) = max_a Q*(s,a)
  is simultaneously the value of π* and the optimal value.

  The proof has two parts:
  1. **Greedy achieves the fixed point**: Since π* picks argmax,
     T^{π*}(V*) = V*, so V* is the value function of π*.
  2. **Dominance**: By `bellman_fixed_point_dominates`, V*(s) ≥
     V^π(s) for every policy π.

  **Caveat**: The standard optimal-policy-existence proof constructs π* and proves
  optimality in one sweep using trajectory arguments. Our proof
  is algebraic: Part 1 uses `greedyStochasticPolicy` (a
  deterministic policy encoded as a stochastic one), and Part 2
  invokes the minimum-principle argument from
  `bellman_fixed_point_dominates`. -/
theorem optimal_policy_exists
    (Q_star : M.ActionValueFn)
    (hQ_star : ∀ s a, Q_star s a = M.bellmanOptOp Q_star s a) :
    let V_star : M.StateValueFn :=
      fun s => Finset.univ.sup' Finset.univ_nonempty (Q_star s)
    let π_star := M.greedyStochasticPolicy Q_star
    -- Part 1: V* is the value function of π*
    M.isValueOf V_star π_star ∧
    -- Part 2: V* dominates all policy values
    (∀ (π : M.StochasticPolicy) (V_pi : M.StateValueFn),
      M.isValueOf V_pi π → ∀ s, V_pi s ≤ V_star s) := by
  intro V_star π_star
  constructor
  · -- Part 1: Show V_star satisfies Bellman equation for π_star
    -- i.e., V_star s = expectedReward π_star s + γ * expectedNextValue π_star V_star s
    intro s
    -- V_star s = Q_star s (greedyAction Q_star s)  [by greedyAction_eq_sup]
    have hV_eq : V_star s = Q_star s (M.greedyAction Q_star s) :=
      (M.greedyAction_eq_sup Q_star s).symm
    -- Q_star s a_star = r(s, a_star) + γ * ∑ s', P(s,a_star,s') * sup Q_star(s',·)
    --                  = r(s, a_star) + γ * ∑ s', P(s,a_star,s') * V_star(s')
    -- bellmanOptOp Q_star s a = r(s,a) + γ * ∑ s', P(s,a,s') * sup_{a'} Q_star(s',a')
    -- and sup_{a'} Q_star(s',a') = V_star s' by definition
    have hVstar_eq : ∀ s', Finset.univ.sup' Finset.univ_nonempty
        (fun a' => Q_star s' a') = V_star s' := fun _ => rfl
    have hQ_expand : Q_star s (M.greedyAction Q_star s) =
        M.r s (M.greedyAction Q_star s) +
        M.γ * ∑ s', M.P s (M.greedyAction Q_star s) s' * V_star s' := by
      conv_lhs => rw [hQ_star s (M.greedyAction Q_star s)]
      simp only [bellmanOptOp, hVstar_eq]
    -- Rewrite the RHS using greedy policy simplifications
    rw [M.greedyPolicy_expectedReward Q_star s,
        M.greedyPolicy_expectedNextValue Q_star V_star s]
    exact hV_eq.trans hQ_expand
  · -- Part 2: Dominance — direct from bellman_fixed_point_dominates
    intro π V_pi hV_pi s
    exact M.bellman_fixed_point_dominates Q_star hQ_star V_star
      (fun s' => rfl) π V_pi hV_pi s

/-! ### Bellman Q-Evaluation Operator Form

  In our finite MDP setting, the matrix identity
  `Q^π = (I - γP^π)⁻¹ r` is represented through:

  1. **Operator form**: Q^π satisfies (I - γP^π)Q = r, i.e.,
     Q(s,a) = r(s,a) + γ ∑_{s'} P(s'|s,a) ∑_{a'} π(a'|s') Q(s',a').
     This is exactly `isActionValueOf Q π`.

  2. **Uniqueness**: The Bellman evaluation operator for Q-values is a
     γ-contraction, so the fixed point is unique. Any two Q satisfying
     `isActionValueOf` for the same π must be equal.

  Together, these say Q^π is THE unique solution of the operator equation
  (I - γP^π)Q = r, which is the content of the matrix-inverse identity
  Q^π = (I - γP^π)⁻¹ r without requiring explicit matrix inverses.
-/

/-- The Bellman evaluation operator for action-value functions:
    (T^π_Q)(s,a) = r(s,a) + γ ∑_{s'} P(s'|s,a) ∑_{a'} π(a'|s') Q(s',a')

    Q is a fixed point of this operator iff `isActionValueOf Q π`. -/
def bellmanEvalOpQ (π : M.StochasticPolicy) (Q : M.ActionValueFn) :
    M.ActionValueFn :=
  fun s a => M.r s a + M.γ * ∑ s', M.P s a s' *
    (∑ a', π.prob s' a' * Q s' a')

/-- `isActionValueOf Q π` is equivalent to Q being a fixed point of
    the Bellman evaluation operator `bellmanEvalOpQ π`. -/
theorem isActionValueOf_iff_fixedPoint (π : M.StochasticPolicy)
    (Q : M.ActionValueFn) :
    M.isActionValueOf Q π ↔
    ∀ s a, Q s a = M.bellmanEvalOpQ π Q s a := by
  simp only [isActionValueOf, bellmanEvalOpQ]

/-- **Bellman Q-evaluation contraction**. The operator T^π_Q is a
    γ-contraction in the sup norm:
      ‖T^π_Q Q₁ - T^π_Q Q₂‖_∞ ≤ γ · ‖Q₁ - Q₂‖_∞

    Proof: The reward terms cancel, leaving
      |(T^π Q₁)(s,a) - (T^π Q₂)(s,a)|
        = γ |∑_{s'} P(s'|s,a) ∑_{a'} π(a'|s') (Q₁ - Q₂)(s',a')|
        ≤ γ · ‖Q₁ - Q₂‖_∞
    since P and π are stochastic (convex combination). -/
theorem bellmanEvalOpQ_contraction (π : M.StochasticPolicy)
    (Q₁ Q₂ : M.ActionValueFn) :
    M.supDistQ (M.bellmanEvalOpQ π Q₁) (M.bellmanEvalOpQ π Q₂) ≤
      M.γ * M.supDistQ Q₁ Q₂ := by
  -- Reduce to pointwise bound for each (s, a)
  suffices h : ∀ s a,
      |M.bellmanEvalOpQ π Q₁ s a - M.bellmanEvalOpQ π Q₂ s a| ≤
      M.γ * M.supDistQ Q₁ Q₂ by
    simp only [supDistQ, supNormQ]
    exact Finset.sup'_le _ _ (fun s _ =>
      Finset.sup'_le _ _ (fun a _ => h s a))
  intro s a
  set D := M.supDistQ Q₁ Q₂
  -- Reward terms cancel, leaving γ * (weighted difference)
  have hdiff : M.bellmanEvalOpQ π Q₁ s a -
      M.bellmanEvalOpQ π Q₂ s a =
      M.γ * (∑ s', M.P s a s' *
        (∑ a', π.prob s' a' * (Q₁ s' a' - Q₂ s' a'))) := by
    simp only [bellmanEvalOpQ]
    have hsplit : ∀ s',
        M.P s a s' * ∑ a', π.prob s' a' * (Q₁ s' a' - Q₂ s' a') =
        M.P s a s' * (∑ a', π.prob s' a' * Q₁ s' a') -
        M.P s a s' * (∑ a', π.prob s' a' * Q₂ s' a') := by
      intro s'
      rw [← mul_sub]; congr 1
      rw [← Finset.sum_sub_distrib]
      congr 1; funext a'; ring
    simp_rw [hsplit, Finset.sum_sub_distrib]; ring
  rw [hdiff, abs_mul, abs_of_nonneg M.γ_nonneg]
  apply mul_le_mul_of_nonneg_left _ M.γ_nonneg
  -- |∑ P · (∑ π · (Q₁-Q₂))| ≤ D
  apply abs_weighted_sum_le_bound _ _ D
    (M.P_nonneg s a) (M.P_sum_one s a)
  intro s'
  -- |∑ π(a'|s') · (Q₁-Q₂)(s',a')| ≤ D
  apply abs_weighted_sum_le_bound _ _ D
    (π.prob_nonneg s') (π.prob_sum_one s')
  intro a'
  -- |Q₁ s' a' - Q₂ s' a'| ≤ D
  exact le_trans
    (Finset.le_sup' (fun a => |Q₁ s' a - Q₂ s' a|)
      (Finset.mem_univ a'))
    (Finset.le_sup'
      (fun s => Finset.univ.sup' Finset.univ_nonempty
        (fun a => |Q₁ s a - Q₂ s a|))
      (Finset.mem_univ s'))

/-- **Uniqueness of policy action-values**.

  The action-value function Q^π is the UNIQUE solution of the
  Bellman evaluation equation:
    Q(s,a) = r(s,a) + γ ∑_{s'} P(s'|s,a) ∑_{a'} π(a'|s') Q(s',a')

  Equivalently, Q^π is the unique solution of (I - γP^π)Q = r.

  Proof by contraction: If Q₁ and Q₂ both satisfy the equation,
  then ‖Q₁ - Q₂‖ = ‖T^π Q₁ - T^π Q₂‖ ≤ γ‖Q₁ - Q₂‖.
  Since γ < 1, this forces ‖Q₁ - Q₂‖ = 0. -/
theorem bellman_eval_unique_fixed_point (π : M.StochasticPolicy)
    (Q₁ Q₂ : M.ActionValueFn)
    (hQ₁ : M.isActionValueOf Q₁ π)
    (hQ₂ : M.isActionValueOf Q₂ π) :
    ∀ s a, Q₁ s a = Q₂ s a := by
  -- Since Q₁ = T^π Q₁ and Q₂ = T^π Q₂, we have
  --   ‖Q₁ - Q₂‖ = ‖T^π Q₁ - T^π Q₂‖ ≤ γ · ‖Q₁ - Q₂‖
  -- With γ < 1, this forces ‖Q₁ - Q₂‖ ≤ 0, hence = 0.
  set D := M.supDistQ Q₁ Q₂
  -- Step 1: Pointwise, |Q₁ - Q₂| ≤ γD (by contraction + fixed point)
  have hpointwise : ∀ s a,
      |Q₁ s a - Q₂ s a| ≤ M.γ * D := by
    intro s a
    -- Q₁(s,a) - Q₂(s,a) = bellman(Q₁)(s,a) - bellman(Q₂)(s,a)
    -- Reward terms cancel, leaving γ * weighted difference
    have hdiff : Q₁ s a - Q₂ s a =
        M.γ * ∑ s', M.P s a s' *
          (∑ a', π.prob s' a' * (Q₁ s' a' - Q₂ s' a')) := by
      rw [hQ₁ s a, hQ₂ s a]
      have hsplit : ∀ s',
          M.P s a s' * ∑ a', π.prob s' a' * (Q₁ s' a' - Q₂ s' a') =
          M.P s a s' * (∑ a', π.prob s' a' * Q₁ s' a') -
          M.P s a s' * (∑ a', π.prob s' a' * Q₂ s' a') := by
        intro s'; rw [← mul_sub]; congr 1
        rw [← Finset.sum_sub_distrib]
        congr 1; funext a'; ring
      simp_rw [hsplit, Finset.sum_sub_distrib]; ring
    rw [hdiff, abs_mul, abs_of_nonneg M.γ_nonneg]
    apply mul_le_mul_of_nonneg_left _ M.γ_nonneg
    apply abs_weighted_sum_le_bound _ _ D
      (M.P_nonneg s a) (M.P_sum_one s a)
    intro s'
    apply abs_weighted_sum_le_bound _ _ D
      (π.prob_nonneg s') (π.prob_sum_one s')
    intro a'
    exact le_trans
      (Finset.le_sup' (fun a => |Q₁ s' a - Q₂ s' a|)
        (Finset.mem_univ a'))
      (Finset.le_sup'
        (fun s => Finset.univ.sup' Finset.univ_nonempty
          (fun a => |Q₁ s a - Q₂ s a|))
        (Finset.mem_univ s'))
  -- Step 2: D ≤ γD (take sup over pointwise bound)
  have hD_le : D ≤ M.γ * D := by
    simp only [D, supDistQ, supNormQ]
    exact Finset.sup'_le _ _ (fun s _ =>
      Finset.sup'_le _ _ (fun a _ => hpointwise s a))
  -- Step 3: D ≤ γD with γ < 1 implies D ≤ 0
  have hD_le_zero : D ≤ 0 := by nlinarith [M.γ_lt_one]
  -- Step 4: Pointwise equality from |Q₁ - Q₂| ≤ D ≤ 0
  intro s a
  have h_abs : |Q₁ s a - Q₂ s a| ≤ 0 := by
    calc |Q₁ s a - Q₂ s a|
        ≤ Finset.univ.sup' Finset.univ_nonempty
            (fun a' => |Q₁ s a' - Q₂ s a'|) :=
          Finset.le_sup' (fun a' => |Q₁ s a' - Q₂ s a'|)
            (Finset.mem_univ a)
      _ ≤ D := Finset.le_sup'
          (fun s' => Finset.univ.sup' Finset.univ_nonempty
            (fun a' => |Q₁ s' a' - Q₂ s' a'|))
          (Finset.mem_univ s)
      _ ≤ 0 := hD_le_zero
  have := abs_nonneg (Q₁ s a - Q₂ s a)
  have h0 : |Q₁ s a - Q₂ s a| = 0 := le_antisymm h_abs this
  linarith [abs_eq_zero.mp h0]

/-- Algebraic rearrangement of the Bellman Q-evaluation equation.

  For any Q satisfying `isActionValueOf Q π`, we have
    Q(s,a) - γ ∑_{s'} P(s'|s,a) ∑_{a'} π(a'|s') Q(s',a') = r(s,a)

  This is just the component-wise operator form of the Bellman equation,
  obtained by moving the discounted continuation term to the left-hand side. -/
theorem bellman_eval_operator_form (π : M.StochasticPolicy)
    (Q : M.ActionValueFn)
    (hQ : M.isActionValueOf Q π) :
    ∀ s a, Q s a - M.γ * ∑ s', M.P s a s' *
      (∑ a', π.prob s' a' * Q s' a') = M.r s a := by
  intro s a
  have := hQ s a
  linarith

/-- **Uniform bound on policy action-values** — ‖Q^π‖_∞ ≤ R_max / (1 - γ).

  Since Q^π = (I - γP^π)⁻¹ r and the resolvent operator norm is
  bounded by 1/(1-γ), we get ‖Q^π‖ ≤ ‖r‖/(1-γ) ≤ R_max/(1-γ). -/
theorem actionValue_bounded (π : M.StochasticPolicy)
    (Q : M.ActionValueFn)
    (hQ : M.isActionValueOf Q π) :
    ∀ s a, |Q s a| ≤ M.R_max / (1 - M.γ) := by
  -- Q satisfies Q(s,a) = r(s,a) + γ ∑ P · (∑ π · Q)
  -- This is a resolvent equation for Q viewed as a function of (s,a).
  -- We use the same contraction argument as resolvent_bound.
  set D := M.supNormQ Q
  have h1g : (0 : ℝ) < 1 - M.γ := by linarith [M.γ_lt_one]
  -- Step 1: |Q(s,a)| ≤ R_max + γ D for each (s,a)
  have hstep : ∀ s a, |Q s a| ≤ M.R_max + M.γ * D := by
    intro s a
    rw [hQ s a]
    calc |M.r s a + M.γ * ∑ s', M.P s a s' *
          (∑ a', π.prob s' a' * Q s' a')|
        ≤ |M.r s a| + |M.γ * ∑ s', M.P s a s' *
            (∑ a', π.prob s' a' * Q s' a')| :=
          abs_add_le _ _
      _ ≤ M.R_max + M.γ * D := by
          apply add_le_add
          · exact M.r_le_R_max s a
          · rw [abs_mul, abs_of_nonneg M.γ_nonneg]
            apply mul_le_mul_of_nonneg_left _ M.γ_nonneg
            apply abs_weighted_sum_le_bound _ _ D
              (M.P_nonneg s a) (M.P_sum_one s a)
            intro s'
            apply abs_weighted_sum_le_bound _ _ D
              (π.prob_nonneg s') (π.prob_sum_one s')
            intro a'
            exact le_trans
              (Finset.le_sup' (fun a => |Q s' a|)
                (Finset.mem_univ a'))
              (Finset.le_sup'
                (fun s => Finset.univ.sup' Finset.univ_nonempty
                  (fun a => |Q s a|))
                (Finset.mem_univ s'))
  -- Step 2: D ≤ R_max + γ D
  have hsup : D ≤ M.R_max + M.γ * D := by
    simp only [D, supNormQ]
    exact Finset.sup'_le _ _ (fun s _ =>
      Finset.sup'_le _ _ (fun a _ => hstep s a))
  -- Step 3: (1-γ)D ≤ R_max, so D ≤ R_max/(1-γ)
  have hD : D ≤ M.R_max / (1 - M.γ) := by
    rw [le_div_iff₀ h1g]; nlinarith
  -- Step 4: Pointwise
  intro s a
  calc |Q s a|
      ≤ Finset.univ.sup' Finset.univ_nonempty
          (fun a' => |Q s a'|) :=
        Finset.le_sup' (fun a' => |Q s a'|) (Finset.mem_univ a)
    _ ≤ D := Finset.le_sup'
        (fun s' => Finset.univ.sup' Finset.univ_nonempty
          (fun a' => |Q s' a'|))
        (Finset.mem_univ s)
    _ ≤ M.R_max / (1 - M.γ) := hD

end FiniteMDP

end
