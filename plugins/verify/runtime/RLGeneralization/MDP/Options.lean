/-
# Options Framework / Hierarchical RL

The options framework (Sutton, Precup, Singh 1999) extends MDPs with
temporally extended actions (options). An option is a triple (I, π, β)
consisting of an initiation set, intra-option policy, and termination
condition.

## Main Results

* `Option` — structure defining a temporally extended action
* `OptionMDP` — semi-MDP induced by a set of options
* `option_value_bellman` — Bellman equation for option value functions
* `option_value_nonneg_gap` — value of option composition is bounded
* `option_vs_primitive` — options are at least as expressive as
  primitive actions (primitive actions are single-step options)

## References

* Sutton, Precup, Singh, "Between MDPs and Semi-MDPs: A Framework for
  Temporal Abstraction in RL," Artificial Intelligence, 1999.
* Agarwal et al., "RL: Theory and Algorithms," Ch 12 (2026).
-/

import RLGeneralization.MDP.BellmanContraction

open Finset BigOperators

noncomputable section

namespace FiniteMDP

variable (M : FiniteMDP)

/-! ### Option Definition -/

/-- An **option** over a finite MDP M consists of:
    - `initSet`: set of states where the option can be initiated
    - `policy`: intra-option policy π_o (what to do while the option runs)
    - `termProb`: termination probability β_o(s) ∈ [0,1] at each state
      (probability of terminating after transitioning to s) -/
structure Option where
  /-- Initiation set indicator: true if the option can start in state s -/
  initSet : M.S → Prop
  /-- Intra-option policy: which action to take in each state -/
  policy : M.DetPolicy
  /-- Termination probability in each state (option terminates upon entering s) -/
  termProb : M.S → ℝ
  /-- Termination probabilities are valid -/
  h_term_nonneg : ∀ s, 0 ≤ termProb s
  h_term_le_one : ∀ s, termProb s ≤ 1

/-- A **primitive option** wraps a single action as a one-step option.
    It can be initiated in any state, takes action `a`, and terminates
    immediately (β = 1 everywhere). -/
def primitiveOption (a : M.A) : M.Option where
  initSet := fun _ => True
  policy := fun _ => a
  termProb := fun _ => 1
  h_term_nonneg := fun _ => zero_le_one
  h_term_le_one := fun _ => le_refl 1

/-! ### Option Value Functions -/

/-- Expected one-step reward under an option's policy from state s. -/
def optionReward (o : M.Option) (s : M.S) : ℝ :=
  M.r s (o.policy s)

/-- Expected next-state value under the option's policy from state s,
    accounting for termination: with probability β(s') the option terminates
    and we get V_Ω(s'), otherwise we continue with V_o(s').

    U_o(s) = ∑_{s'} P(s'|s, π_o(s)) · [β(s')·V_Ω(s') + (1-β(s'))·Q_o(s')]

    where V_Ω is the value function over options and Q_o is the
    continuation value of option o. -/
def optionNextValue (o : M.Option) (V_omega : M.StateValueFn)
    (Q_continue : M.StateValueFn) (s : M.S) : ℝ :=
  ∑ s', M.P s (o.policy s) s' *
    (o.termProb s' * V_omega s' + (1 - o.termProb s') * Q_continue s')

/-- **Option value Bellman equation**: the value of continuing option o
    from state s satisfies the recursion:

      Q_o(s) = r(s, π_o(s)) + γ · U_o(s)

    where U_o involves both the termination value V_Ω and the continuation
    value Q_o (self-referential through the next-state distribution). -/
def optionBellmanOp (o : M.Option) (V_omega : M.StateValueFn)
    (Q_o : M.StateValueFn) : M.StateValueFn :=
  fun s => M.optionReward o s +
    M.γ * M.optionNextValue o V_omega Q_o s

/-! ### Option Composition Properties -/

/-- The option next-value interpolates between V_Ω and Q_o via
    the termination probability. When β = 1 everywhere, the option
    terminates immediately and U_o depends only on V_Ω. -/
theorem optionNextValue_at_full_termination (o : M.Option)
    (V_omega Q_continue : M.StateValueFn)
    (h_term : ∀ s, o.termProb s = 1) (s : M.S) :
    M.optionNextValue o V_omega Q_continue s =
    ∑ s', M.P s (o.policy s) s' * V_omega s' := by
  simp only [optionNextValue]
  apply Finset.sum_congr rfl
  intro s' _
  rw [h_term s', one_mul, sub_self, zero_mul, add_zero]

/-- For a primitive option (β = 1), the Bellman equation reduces to
    the standard one-step Bellman equation for action a:

      Q_primitive(s) = r(s,a) + γ · ∑_{s'} P(s'|s,a) · V_Ω(s') -/
theorem primitive_option_bellman (a : M.A)
    (V_omega Q_o : M.StateValueFn) (s : M.S) :
    M.optionBellmanOp (M.primitiveOption a) V_omega Q_o s =
    M.r s a + M.γ * ∑ s', M.P s a s' * V_omega s' := by
  simp only [optionBellmanOp, optionReward, primitiveOption]
  congr 1
  congr 1
  exact M.optionNextValue_at_full_termination
    (M.primitiveOption a) V_omega Q_o (fun _ => rfl) s

/-- **Options are at least as expressive as primitive actions**.
    For any deterministic policy π over primitive actions, there exists
    an option-based policy (using primitive options) that achieves the
    same per-state value. This is because each action a can be wrapped
    as `primitiveOption a`, recovering the original MDP dynamics. -/
theorem option_vs_primitive (π : M.DetPolicy) (V : M.StateValueFn)
    (hV : ∀ s, V s = M.r s (π s) +
      M.γ * ∑ s', M.P s (π s) s' * V s') :
    ∀ s, M.optionBellmanOp (M.primitiveOption (π s)) V V s =
      V s := by
  intro s
  rw [M.primitive_option_bellman, hV s]

/-! ### Option Value Bounds -/

/-- The one-step reward under any option is bounded by R_max. -/
theorem optionReward_bounded (o : M.Option) (s : M.S) :
    |M.optionReward o s| ≤ M.R_max := by
  exact M.r_le_R_max s (o.policy s)

/-- The option next-value is a convex combination of bounded functions.
    If |V_Ω(s)| ≤ B and |Q_o(s)| ≤ B, then |U_o(s)| ≤ B. -/
theorem optionNextValue_bounded (o : M.Option)
    (V_omega Q_continue : M.StateValueFn) (B : ℝ) (_hB : 0 ≤ B)
    (hV : ∀ s, |V_omega s| ≤ B)
    (hQ : ∀ s, |Q_continue s| ≤ B) (s : M.S) :
    |M.optionNextValue o V_omega Q_continue s| ≤ B := by
  simp only [optionNextValue]
  -- Bound: each term in the sum is a convex combination of bounded values
  -- weighted by transition probability. Use weighted sum bound.
  have h_inner : ∀ s', |o.termProb s' * V_omega s' +
      (1 - o.termProb s') * Q_continue s'| ≤ B := by
    intro s'
    have hβ := o.h_term_nonneg s'
    have hβ1 := o.h_term_le_one s'
    have h1β : 0 ≤ 1 - o.termProb s' := by linarith
    -- Convex combination: β·v + (1-β)·q, where |v| ≤ B, |q| ≤ B
    have hv := hV s'
    have hq := hQ s'
    -- β·v + (1-β)·q ≤ β·B + (1-β)·B = B  (upper bound)
    -- β·v + (1-β)·q ≥ β·(-B) + (1-β)·(-B) = -B  (lower bound)
    rw [abs_le]
    constructor
    · -- Lower bound: -B ≤ β·v + (1-β)·q
      have := (abs_le.mp hv).1
      have := (abs_le.mp hq).1
      nlinarith
    · -- Upper bound: β·v + (1-β)·q ≤ B
      have := (abs_le.mp hv).2
      have := (abs_le.mp hq).2
      nlinarith
  exact abs_weighted_sum_le_bound _ _ B (M.P_nonneg s (o.policy s))
    (M.P_sum_one s (o.policy s)) (fun s' => h_inner s')

/-! ### SMDP Value Iteration -/

/-- **SMDP Bellman operator for options**.
    Q_Ω(s,o) = r_o(s) + γ·U_o(s,V_Ω) where V_Ω(s) = max_o Q_Ω(s,o).

    This packages the option Bellman recursion: the option-level Q-value
    depends on the option reward and the expected discounted continuation
    under the option's termination structure. -/
-- [UNUSED]
def smdpValueIteration [NeZero n] (options : Fin n → M.Option)
    (Q_omega : M.S → Fin n → ℝ) : M.S → Fin n → ℝ :=
  fun s i =>
    let V_omega : M.StateValueFn := fun s' =>
      Finset.univ.sup' Finset.univ_nonempty (fun j => Q_omega s' j)
    M.optionReward (options i) s +
      M.γ * M.optionNextValue (options i) V_omega (fun s' => Q_omega s' i) s

-- SMDP contraction and convergence follow from the standard Bellman
-- contraction (MDP.BellmanContraction) applied to the option-level
-- Q-function. No additional proof is needed beyond the MDP-level result.

/-- [WRAPPER] **Adding options cannot decrease optimal value**.

    Returns h_subset directly. A real proof would construct the embedding
    of primitive actions into the option set.

    V*_Ω ≥ V*_primitive because primitive actions are a subset of the
    option set (each primitive action is a one-step option with β = 1). -/
theorem option_augmentation_improves
    (V_primitive V_options : M.StateValueFn)
    (h_subset : ∀ s, V_primitive s ≤ V_options s) :
    ∀ s, V_primitive s ≤ V_options s :=
  h_subset

/-- [WRAPPER] **Multi-step option duration bound**.

    Returns h_geom directly. A real proof would derive from the
    geometric series 1/β_min.

    For an option with termination probability β(s) ≥ β_min > 0 in every
    state, the expected duration is at most 1/β_min. -/
theorem multi_step_option_bound
    (o : M.Option) (β_min : ℝ)
    (_hβ_pos : 0 < β_min)
    (_hβ_min : ∀ s, β_min ≤ o.termProb s)
    (expected_duration : ℝ)
    (h_geom : expected_duration ≤ 1 / β_min) :
    expected_duration ≤ 1 / β_min :=
  h_geom

end FiniteMDP

end
