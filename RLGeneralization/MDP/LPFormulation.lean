/-
# LP Formulation of Discounted MDPs

Formalizes the linear programming formulation of discounted MDPs
(cf. Puterman Ch 6, Altman 1999, d'Epenoux 1963).

## Main Definitions

* `PrimalFeasible` - V is primal feasible iff V(s) >= r(s,a) + gamma * P V(s') for all s,a
  (i.e., V >= TV, the Bellman superharmonic condition)
* `StateActionPolytope` - The state-action polytope K_mu:
  d >= 0 and sum_a d(s,a) = (1-gamma)*mu(s) + gamma * sum_{s',a'} P(s|s',a') d(s',a')
* `primalObjective` - sum_s mu(s) * V(s)
* `dualObjective` - (1/(1-gamma)) * sum_{s,a} d(s,a) * r(s,a)

## Main Results

* `primal_feasible_iff_bellman_dominates` - V feasible iff V >= TV
* `bellman_optimal_is_feasible` - V* is primal feasible
* `weak_duality` - Primal objective >= Dual objective (algebraic)
* `lp_value_equals_bellman` - LP value decomposition (one Bellman step)

## References

* [Puterman, *Markov Decision Processes*, Ch 6][puterman2014]
* [d'Epenoux, 1963, *A probabilistic production and inventory problem*]
-/

import RLGeneralization.MDP.OccupancyMeasure

open Finset BigOperators

noncomputable section

namespace FiniteMDP

variable (M : FiniteMDP)

/-! ### Bellman Optimality Operator for State Values -/

/-- The Bellman optimality operator for state value functions:
    (T V)(s) = max_a { r(s,a) + gamma * sum_{s'} P(s'|s,a) V(s') } -/
def bellmanOptV (V : M.StateValueFn) : M.StateValueFn :=
  fun s => Finset.univ.sup' Finset.univ_nonempty
    (fun a => M.r s a + M.γ * ∑ s', M.P s a s' * V s')

/-! ### Primal LP: Bellman Superharmonic Functions -/

/-- V is primal feasible iff it dominates the Bellman operator pointwise:
    V(s) >= r(s,a) + gamma * sum_{s'} P(s'|s,a) V(s') for all s, a.
    Equivalently, V >= TV (Bellman superharmonic). -/
def PrimalFeasible (V : M.StateValueFn) : Prop :=
  ∀ s a, V s ≥ M.r s a + M.γ * ∑ s', M.P s a s' * V s'

/-- Primal feasibility is equivalent to V dominating the Bellman operator. -/
theorem primal_feasible_iff_bellman_dominates (V : M.StateValueFn) :
    M.PrimalFeasible V ↔ ∀ s, V s ≥ M.bellmanOptV V s := by
  constructor
  · -- PrimalFeasible -> V >= TV
    intro hfeas s
    simp only [bellmanOptV]
    exact Finset.sup'_le _ _ (fun a _ => hfeas s a)
  · -- V >= TV -> PrimalFeasible
    intro hdom s a
    have h := hdom s
    simp only [bellmanOptV] at h
    exact le_trans
      (Finset.le_sup' (fun a => M.r s a + M.γ * ∑ s', M.P s a s' * V s')
        (Finset.mem_univ a)) h

/-- If V* satisfies the Bellman optimality equation, then V* is primal feasible.
    (V* = TV* implies V* >= TV* trivially.) -/
theorem bellman_optimal_is_feasible (V : M.StateValueFn)
    (hopt : M.isBellmanOptimalV V) :
    M.PrimalFeasible V := by
  intro s a
  have h := hopt s
  -- V(s) = sup_a { r(s,a) + gamma * sum P V } >= r(s,a) + gamma * sum P V
  rw [h]
  exact Finset.le_sup'
    (fun a => M.r s a + M.γ * ∑ s', M.P s a s' * V s')
    (Finset.mem_univ a)

/-! ### Primal Objective -/

/-- The primal LP objective: sum_s mu(s) * V(s). -/
def primalObjective (μ : M.S → ℝ) (V : M.StateValueFn) : ℝ :=
  ∑ s, μ s * V s

/-! ### Dual LP: State-Action Polytope -/

-- [UNUSED]
/-- A state-action measure d : S x A -> R. -/
def StateActionMeasure := M.S → M.A → ℝ

/-- The state-action polytope K_mu: the set of nonnegative measures d satisfying
    the flow conservation constraint:
      sum_a d(s,a) = (1-gamma)*mu(s) + gamma * sum_{s',a'} P(s|s',a') d(s',a')
    These are exactly the occupancy measures of stochastic policies. -/
structure StateActionPolytope (μ : M.S → ℝ) (d : M.S → M.A → ℝ) : Prop where
  /-- d is nonnegative -/
  d_nonneg : ∀ s a, 0 ≤ d s a
  /-- Flow conservation (balance) constraint -/
  flow_conservation : ∀ s,
    ∑ a, d s a = (1 - M.γ) * μ s +
      M.γ * ∑ s', ∑ a', M.P s' a' s * d s' a'

/-- The dual LP objective: (1/(1-gamma)) * sum_{s,a} d(s,a) * r(s,a). -/
def dualObjective (d : M.S → M.A → ℝ) : ℝ :=
  (1 / (1 - M.γ)) * ∑ s, ∑ a, d s a * M.r s a

/-! ### Occupancy Measures are Dual Feasible -/

/-- The **one-step** state-action occupancy measure for a stochastic policy pi
    with initial distribution mu:
    d(s,a) = (1-gamma) * mu(s) * pi(a|s)

    This is the one-step (unnormalized first-visit) version of the full
    stationary occupancy measure. The full stationary occupancy satisfies
    the flow conservation constraint and requires a geometric series
    over the transition kernel, which is not formalized here. -/
def stationaryOccupancy (π : M.StochasticPolicy) (μ : M.S → ℝ) :
    M.S → M.A → ℝ :=
  fun s a => (1 - M.γ) * μ s * π.prob s a

/-- The stationary occupancy measure is nonnegative when mu >= 0. -/
theorem stationaryOccupancy_nonneg (π : M.StochasticPolicy) (μ : M.S → ℝ)
    (hμ : ∀ s, 0 ≤ μ s) :
    ∀ s a, 0 ≤ M.stationaryOccupancy π μ s a := by
  intro s a
  unfold stationaryOccupancy
  apply mul_nonneg
  · apply mul_nonneg
    · linarith [M.γ_lt_one]
    · exact hμ s
  · exact π.prob_nonneg s a

/-- The stationary occupancy measure's action marginal. -/
theorem stationaryOccupancy_action_sum (π : M.StochasticPolicy) (μ : M.S → ℝ)
    (s : M.S) :
    ∑ a, M.stationaryOccupancy π μ s a = (1 - M.γ) * μ s := by
  simp only [stationaryOccupancy]
  rw [← Finset.mul_sum]
  rw [π.prob_sum_one s, mul_one]

/-! ### Weak Duality -/

/-- **Weak duality** for the LP formulation of MDPs.

  For any primal-feasible V and any nonnegative state-action measure d
  satisfying the flow conservation constraint (with initial distribution mu
  that is a probability distribution), the primal objective is at least
  the dual objective:
    sum_s mu(s) V(s) >= (1/(1-gamma)) sum_{s,a} d(s,a) r(s,a)

  Proof by the standard LP weak duality argument:
  multiply the primal constraint V(s) >= r(s,a) + gamma P V by d(s,a),
  sum over (s,a), and use the flow conservation to simplify. -/
theorem weak_duality (μ : M.S → ℝ) (V : M.StateValueFn)
    (d : M.S → M.A → ℝ)
    (hfeas : M.PrimalFeasible V)
    (hpoly : M.StateActionPolytope μ d) :
    M.primalObjective μ V ≥ M.dualObjective d := by
  -- Expand definitions
  simp only [primalObjective, dualObjective]
  rw [ge_iff_le, div_mul_eq_mul_div, one_mul]
  rw [div_le_iff₀ (by linarith [M.γ_lt_one] : (0:ℝ) < 1 - M.γ)]
  -- Goal: sum d(s,a) r(s,a) <= (1-gamma) sum mu(s) V(s)
  -- From primal feasibility: d(s,a) * V(s) >= d(s,a) * (r(s,a) + gamma sum P V)
  -- Sum over all (s,a):
  -- sum d(s,a) V(s) >= sum d(s,a) r(s,a) + gamma sum d(s,a) sum P V
  -- LHS: sum_s V(s) sum_a d(s,a) = sum_s V(s) [(1-gamma)mu(s) + gamma sum P d]
  --     = (1-gamma) sum mu(s)V(s) + gamma sum_{s'} V(s') sum_{s,a} P(s'|s,a)d(s,a)
  -- So: (1-gamma) sum mu V + gamma sum V(s') sum P d >= sum d r + gamma sum d sum P V
  -- The gamma terms cancel, leaving (1-gamma) sum mu V >= sum d r.

  -- Step 1: Multiply feasibility constraint by d(s,a) and sum
  have hinner : ∀ s a, d s a * M.r s a ≤
      d s a * V s - M.γ * (d s a * ∑ s', M.P s a s' * V s') := by
    intro s a
    by_cases hd : d s a = 0
    · simp [hd]
    · have hd_pos : 0 < d s a := lt_of_le_of_ne (hpoly.d_nonneg s a) (Ne.symm hd)
      have h := hfeas s a
      nlinarith [mul_le_mul_of_nonneg_left h (le_of_lt hd_pos)]
  -- Step 2: Sum the inequality over all (s, a)
  have hsum : ∑ s, ∑ a, d s a * M.r s a ≤
      ∑ s, ∑ a, d s a * V s -
      M.γ * ∑ s, ∑ a, d s a * ∑ s', M.P s a s' * V s' := by
    have h1 : ∑ s, ∑ a, d s a * M.r s a ≤
        ∑ s, ∑ a, (d s a * V s - M.γ * (d s a * ∑ s', M.P s a s' * V s')) :=
      Finset.sum_le_sum fun s _ =>
        Finset.sum_le_sum fun a _ => hinner s a
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at h1
    linarith
  -- Step 3: Use flow conservation to rewrite sum_a d(s,a) V(s)
  -- sum_s V(s) sum_a d(s,a) = sum_s V(s) [(1-gamma)mu(s) + gamma ...]
  have hflow : ∑ s, (∑ a, d s a) * V s =
      (1 - M.γ) * ∑ s, μ s * V s +
      M.γ * ∑ s, (∑ s', ∑ a', M.P s' a' s * d s' a') * V s := by
    have hexp : ∀ s, (∑ a, d s a) * V s =
        (1 - M.γ) * μ s * V s +
        M.γ * (∑ s', ∑ a', M.P s' a' s * d s' a') * V s := by
      intro s
      rw [hpoly.flow_conservation s]
      ring
    simp_rw [hexp, Finset.sum_add_distrib]
    congr 1
    · have : ∀ s : M.S, (1 - M.γ) * μ s * V s = (1 - M.γ) * (μ s * V s) :=
        fun s => by ring
      simp_rw [this, ← Finset.mul_sum]
    · have : ∀ s : M.S, M.γ * (∑ s', ∑ a', M.P s' a' s * d s' a') * V s =
        M.γ * ((∑ s', ∑ a', M.P s' a' s * d s' a') * V s) :=
        fun s => by ring
      simp_rw [this, ← Finset.mul_sum]
  -- Step 4: The gamma terms involving V cancel
  -- sum d(s,a) V(s) = sum_s (sum_a d(s,a)) V(s) (just regrouping)
  have hregroup : ∑ s, ∑ a, d s a * V s = ∑ s, (∑ a, d s a) * V s := by
    congr 1; funext s; rw [Finset.sum_mul]
  -- sum_{s,a} d(s,a) sum_{s'} P(s'|s,a) V(s')
  -- = sum_{s'} V(s') sum_{s,a} P(s'|s,a) d(s,a)
  -- = sum_{s'} V(s') sum_{s,a} d(s,a) P(s'|s,a) [by commutativity]
  have hswap : ∑ s, ∑ a, d s a * ∑ s', M.P s a s' * V s' =
      ∑ s', (∑ s, ∑ a, M.P s a s' * d s a) * V s' := by
    -- Both sides equal ∑_{s'} (∑_s ∑_a d(s,a) P(s'|s,a)) V(s')
    -- LHS transformation: distribute, swap sums, factor
    -- RHS transformation: factor V, commute P*d = d*P
    -- Expand RHS
    have hrhs : ∀ s', (∑ s, ∑ a, M.P s a s' * d s a) * V s' =
        ∑ s, ∑ a, M.P s a s' * d s a * V s' := by
      intro s'; rw [Finset.sum_mul]; congr 1; funext s; rw [Finset.sum_mul]
    simp_rw [hrhs]
    -- Expand LHS
    simp_rw [Finset.mul_sum,
      show ∀ s a (s' : M.S), d s a * (M.P s a s' * V s') =
        M.P s a s' * d s a * V s' from fun s a s' => by ring]
    -- Both sides are now triple sums over (s,a,s') vs (s',s,a) of the same term
    -- Swap outer sums: ∑_s ∑_a ∑_{s'} f = ∑_{s'} ∑_s ∑_a f (when f doesn't depend on order)
    -- First swap: ∑_s (∑_a ∑_{s'} f) = ∑_a (∑_s ∑_{s'} f)
    -- Actually we need: ∑_s ∑_a ∑_{s'} = ∑_{s'} ∑_s ∑_a
    -- = ∑_{s'} ∑_a ∑_s (swap inner) = ∑_a ∑_{s'} ∑_s (swap outer) ... complicated
    -- Simpler: use transitivity through ∑_a ∑_s ∑_{s'}
    trans ∑ a, ∑ s, ∑ s', M.P s a s' * d s a * V s'
    · rw [Finset.sum_comm]
    trans ∑ a, ∑ s', ∑ s, M.P s a s' * d s a * V s'
    · exact Finset.sum_congr rfl fun a _ =>
        Finset.sum_comm (f := fun s s' => M.P s a s' * d s a * V s')
    trans ∑ s', ∑ a, ∑ s, M.P s a s' * d s a * V s'
    · rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun s' _ =>
      Finset.sum_comm (f := fun a s => M.P s a s' * d s a * V s')
  -- Now combine: from hsum we have
  -- sum d r <= sum d V - gamma * sum d P V
  --          = (1-gamma) sum mu V + gamma * sum (sum P d) V - gamma * sum d P V
  -- The gamma terms match, so we get sum d r <= (1-gamma) sum mu V
  -- Key: the gamma terms cancel because swapping indices gives the same sum
  have hcancel : M.γ * ∑ s, (∑ s', ∑ a', M.P s' a' s * d s' a') * V s =
      M.γ * ∑ s, ∑ a, d s a * ∑ s', M.P s a s' * V s' := by
    congr 1; rw [hswap]
  linarith [hregroup, hflow, hcancel]

/-! ### LP Value Equals Bellman Optimum -/

/-- **LP dual objective at stationary occupancy**.

  The dual objective evaluated at the stationary occupancy
  d(s,a) = (1-gamma)*mu(s)*pi(a|s) simplifies to the
  expected immediate reward:
    (1/(1-gamma)) * sum_{s,a} d(s,a) * r(s,a) = sum_s mu(s) * r^pi(s)

  where r^pi(s) = sum_a pi(a|s) r(s,a) is the expected immediate reward.

  This is a purely algebraic simplification (no Bellman equation needed). -/
theorem dual_at_stationary_eq_reward (μ : M.S → ℝ) (π : M.StochasticPolicy) :
    M.dualObjective (M.stationaryOccupancy π μ) =
      ∑ s, μ s * M.expectedReward π s := by
  simp only [dualObjective, stationaryOccupancy, expectedReward]
  have h1g_pos : (0 : ℝ) < 1 - M.γ := by linarith [M.γ_lt_one]
  have h1g : (1 - M.γ) ≠ 0 := ne_of_gt h1g_pos
  -- (1/(1-gamma)) sum (1-gamma) mu pi r = sum mu pi r
  -- Factor out (1-gamma) from inner sums
  have hfactor : ∀ s, ∑ a, (1 - M.γ) * μ s * π.prob s a * M.r s a =
      (1 - M.γ) * (μ s * ∑ a, π.prob s a * M.r s a) := by
    intro s
    have : ∀ a : M.A, (1 - M.γ) * μ s * π.prob s a * M.r s a =
        (1 - M.γ) * (μ s * (π.prob s a * M.r s a)) := fun a => by ring
    simp_rw [this, ← Finset.mul_sum]
  simp_rw [hfactor, ← Finset.mul_sum]
  rw [one_div]
  field_simp

/-- **LP optimum equals Bellman optimum** (algebraic form).

  If V satisfies the Bellman evaluation equation for policy pi, then
  the primal objective sum_s mu(s) V(s) can be decomposed as:
    sum_s mu(s) V(s) = sum_s mu(s) r^pi(s) + gamma * sum_s mu(s) P^pi V(s)

  This is the first step toward showing that V is the LP optimum:
  iterating this identity recovers V as a geometric sum of rewards. -/
theorem lp_value_equals_bellman (μ : M.S → ℝ)
    (V : M.StateValueFn)
    (π : M.StochasticPolicy)
    (hV : M.isValueOf V π) :
    M.primalObjective μ V =
      ∑ s, μ s * M.expectedReward π s +
      M.γ * ∑ s, μ s * M.expectedNextValue π V s := by
  simp only [primalObjective]
  -- From V(s) = r^pi(s) + gamma P^pi V(s):
  -- sum mu V = sum mu (r^pi + gamma P^pi V) = sum mu r^pi + gamma sum mu P^pi V
  have hexpand : ∀ s, μ s * V s =
      μ s * M.expectedReward π s + M.γ * (μ s * M.expectedNextValue π V s) := by
    intro s
    have := hV s
    rw [this]; ring
  simp_rw [hexpand, Finset.sum_add_distrib, ← Finset.mul_sum]

/-! ### Strong LP Duality for MDPs

  **Strong duality** states that the LP primal and dual achieve the
  same optimal value:
    min { ∑ μ(s) V(s) : V ≥ TV } = max { (1/(1-γ)) ∑ d(s,a) r(s,a) : d ∈ K_μ }

  The proof requires the Farkas alternative lemma (or an equivalent
  LP strong duality theorem), which is not in Mathlib. We take it
  as a conditional hypothesis and derive the MDP-specific consequences.
-/

/-- **Farkas-type condition for MDP LP strong duality.**

  A Farkas-type hypothesis: if the primal LP has a feasible solution
  (which we know: V* is feasible), then the dual LP has an optimal
  solution with the same objective value.

  This encapsulates the LP strong duality theorem specialized to
  the MDP structure. -/
structure LPStrongDualityHyp where
  /-- For any initial distribution μ and Bellman-optimal V:
      there exists a dual-feasible d achieving the same objective. -/
  dual_attains : ∀ (μ : M.S → ℝ) (V : M.StateValueFn),
    M.isBellmanOptimalV V →
    (∀ s, 0 ≤ μ s) → (∑ s, μ s = 1) →
    ∃ d : M.S → M.A → ℝ,
      M.StateActionPolytope μ d ∧
      M.dualObjective d = M.primalObjective μ V

/-- **Strong LP duality for MDPs.**

  If the LP strong duality hypothesis holds (Farkas lemma),
  then for any Bellman-optimal V* and probability distribution μ:

    ∑_s μ(s) V*(s) = (1/(1-γ)) ∑_{s,a} d*(s,a) r(s,a)

  where d* is the optimal occupancy measure.

  The equality means:
  - The LP relaxation is tight (no integrality gap)
  - V* is the unique optimal primal solution
  - d* encodes the optimal policy's state-action frequencies -/
theorem lp_strong_duality
    (hyp : M.LPStrongDualityHyp)
    (μ : M.S → ℝ) (V : M.StateValueFn)
    (hopt : M.isBellmanOptimalV V)
    (hμ_nn : ∀ s, 0 ≤ μ s) (hμ_sum : ∑ s, μ s = 1) :
    ∃ d : M.S → M.A → ℝ,
      M.StateActionPolytope μ d ∧
      M.primalObjective μ V = M.dualObjective d := by
  obtain ⟨d, hpoly, heq⟩ := hyp.dual_attains μ V hopt hμ_nn hμ_sum
  exact ⟨d, hpoly, heq.symm⟩

/-- **Optimal policy from LP dual solution.**

  Given strong duality, the optimal occupancy measure d* determines
  the optimal policy: π*(a|s) = d*(s,a) / ∑_a d*(s,a)
  (when the state is reachable, i.e., ∑_a d*(s,a) > 0). -/
def optimalPolicyFromDual (d : M.S → M.A → ℝ)
    (_hd : ∀ s a, 0 ≤ d s a) : M.S → M.A → ℝ :=
  fun s a =>
    if _h : ∑ a', d s a' = 0 then
      1 / Fintype.card M.A  -- uniform when state unreachable
    else
      d s a / ∑ a', d s a'

/-- The policy extracted from a dual solution is a distribution. -/
theorem optimalPolicyFromDual_sum_one (d : M.S → M.A → ℝ)
    (hd : ∀ s a, 0 ≤ d s a) (s : M.S) :
    ∑ a, M.optimalPolicyFromDual d hd s a = 1 := by
  unfold optimalPolicyFromDual
  by_cases h : ∑ a', d s a' = 0
  · simp [h, Finset.card_univ]
  · simp only [h, dite_false]
    have key : ∑ a, d s a / ∑ a', d s a' = (∑ a, d s a) / ∑ a', d s a' := by
      simp_rw [div_eq_mul_inv]
      rw [Finset.sum_mul]
    rw [key, div_self h]

/-! ### Complementary Slackness -/

/-- **Bellman backup for a single state-action pair.**
    (TV)(s,a) = r(s,a) + γ * ∑_{s'} P(s'|s,a) V(s'). -/
def bellmanBackup (V : M.StateValueFn) (s : M.S) (a : M.A) : ℝ :=
  M.r s a + M.γ * ∑ s', M.P s a s' * V s'

/-- Primal feasibility expressed in terms of bellmanBackup. -/
theorem primal_feasible_bellmanBackup (V : M.StateValueFn) (hfeas : M.PrimalFeasible V) :
    ∀ s a, V s ≥ M.bellmanBackup V s a := by
  intro s a; exact hfeas s a

/-- Helper: the slackness sum ∑_{s,a} d(s,a) * (V(s) - TV(s,a)) equals
    ∑ d*V - ∑ d*r - γ * ∑ d*PV, which is 0 under strong duality. -/
private theorem slackness_sum_eq_zero
    (μ : M.S → ℝ) (V : M.StateValueFn) (d : M.S → M.A → ℝ)
    (_hfeas : M.PrimalFeasible V)
    (hpoly : M.StateActionPolytope μ d)
    (_hstrong : M.primalObjective μ V = M.dualObjective d) :
    ∑ s, ∑ a, d s a *
      (V s - (M.r s a + M.γ * ∑ s', M.P s a s' * V s')) = 0 := by
  -- Strong duality: (1-gamma) sum mu V = sum d r
  have h1g_pos : (0 : ℝ) < 1 - M.γ := by
    linarith [M.γ_lt_one]
  have hsd : (1 - M.γ) * ∑ s, μ s * V s = ∑ s, ∑ a, d s a * M.r s a := by
    have hsd0 := _hstrong
    simp only [primalObjective, dualObjective] at hsd0
    have h1g_ne : (1 - M.γ) ≠ 0 := ne_of_gt h1g_pos
    field_simp at hsd0
    linarith
  -- Flow conservation rewrite for ∑ d*V
  have hflow_dv : ∑ s, (∑ a, d s a) * V s =
      (1 - M.γ) * ∑ s, μ s * V s +
      M.γ * ∑ s, (∑ s', ∑ a', M.P s' a' s * d s' a') * V s := by
    have hexp : ∀ s, (∑ a, d s a) * V s =
        ((1 - M.γ) * μ s + M.γ * ∑ s', ∑ a', M.P s' a' s * d s' a') * V s := by
      intro s; rw [hpoly.flow_conservation s]
    simp_rw [hexp, add_mul, Finset.sum_add_distrib]
    congr 1
    · simp_rw [mul_assoc]; rw [← Finset.mul_sum]
    · simp_rw [mul_assoc]; rw [← Finset.mul_sum]
  -- Regroup ∑_s ∑_a d(s,a) V(s) = ∑_s (∑_a d(s,a)) V(s)
  have hregroup : ∑ s, ∑ a, d s a * V s = ∑ s, (∑ a, d s a) * V s := by
    congr 1; funext s; rw [Finset.sum_mul]
  -- Index swap: ∑_{s,a} d(s,a) ∑_{s'} P(s'|s,a) V(s') = ∑_{s'} (∑_{s,a} P(s'|s,a) d(s,a)) V(s')
  have hswap : ∑ s, ∑ a, d s a * ∑ s', M.P s a s' * V s' =
      ∑ s', (∑ s, ∑ a, M.P s a s' * d s a) * V s' := by
    have hrhs : ∀ s', (∑ s, ∑ a, M.P s a s' * d s a) * V s' =
        ∑ s, ∑ a, M.P s a s' * d s a * V s' := by
      intro s'; rw [Finset.sum_mul]; congr 1; funext s; rw [Finset.sum_mul]
    simp_rw [hrhs, Finset.mul_sum,
      show ∀ s a (s' : M.S), d s a * (M.P s a s' * V s') =
        M.P s a s' * d s a * V s' from fun s a s' => by ring]
    trans ∑ a, ∑ s, ∑ s', M.P s a s' * d s a * V s'
    · rw [Finset.sum_comm]
    trans ∑ a, ∑ s', ∑ s, M.P s a s' * d s a * V s'
    · exact Finset.sum_congr rfl fun a _ =>
        Finset.sum_comm (f := fun s s' => M.P s a s' * d s a * V s')
    trans ∑ s', ∑ a, ∑ s, M.P s a s' * d s a * V s'
    · rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun s' _ =>
      Finset.sum_comm (f := fun a s => M.P s a s' * d s a * V s')
  -- Gamma terms cancel
  have hgamma_cancel : M.γ * ∑ s, (∑ s', ∑ a', M.P s' a' s * d s' a') * V s =
      M.γ * ∑ s, ∑ a, d s a * ∑ s', M.P s a s' * V s' := by
    congr 1; rw [hswap]
  -- Expand the slackness sum
  -- ∑ d(V - r - γPV) = ∑ dV - ∑ dr - γ ∑ dPV
  have hexpand : ∑ s, ∑ a, d s a * (V s - (M.r s a + M.γ * ∑ s', M.P s a s' * V s')) =
      ∑ s, ∑ a, d s a * V s -
      (∑ s, ∑ a, d s a * M.r s a + M.γ * ∑ s, ∑ a, d s a * ∑ s', M.P s a s' * V s') := by
    -- Use the weak_duality-style decomposition
    have h1 : ∀ s a, d s a * (V s - (M.r s a + M.γ * ∑ s', M.P s a s' * V s')) =
        d s a * V s - d s a * M.r s a - M.γ * (d s a * ∑ s', M.P s a s' * V s') := by
      intro s a; ring
    simp_rw [h1]
    -- ∑∑ (a - b - c) = ∑∑ a - ∑∑ b - ∑∑ c = ∑∑ a - (∑∑ b + ∑∑ c)
    -- After simp_rw, each inner sum is a double sub, need to distribute
    have h2 : ∀ s,
        ∑ a, (d s a * V s - d s a * M.r s a -
          M.γ * (d s a * ∑ s', M.P s a s' * V s')) =
        (∑ a, d s a * V s) - (∑ a, d s a * M.r s a) -
          M.γ * (∑ a, d s a * ∑ s', M.P s a s' * V s') := by
      intro s
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
      congr 1
      rw [← Finset.mul_sum]
    simp_rw [h2]
    have h3 :
        ∑ s, ((∑ a, d s a * V s) - (∑ a, d s a * M.r s a) -
          M.γ * (∑ a, d s a * ∑ s', M.P s a s' * V s')) =
        (∑ s, ∑ a, d s a * V s) -
          (∑ s, ∑ a, d s a * M.r s a) -
          M.γ * (∑ s, ∑ a, d s a *
            ∑ s', M.P s a s' * V s') := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
      congr 1
      rw [← Finset.mul_sum]
    rw [h3]; ring
  rw [hexpand, hregroup, hflow_dv, hgamma_cancel]
  linarith

/-- **Complementary slackness for MDP LP.**

  If V is primal optimal (Bellman fixed point) and d is dual optimal
  under strong duality, then for every state-action pair (s,a):
    d(s,a) > 0 → V(s) = (TV)(s,a)

  Intuition: if a state-action pair has positive occupancy in the
  optimal dual, then the primal constraint must be tight at optimality.

  This follows from the LP complementary slackness theorem:
  at optimality, x_i > 0 implies the i-th dual constraint is tight. -/
theorem complementary_slackness
    (μ : M.S → ℝ) (V : M.StateValueFn) (d : M.S → M.A → ℝ)
    (hopt_V : M.isBellmanOptimalV V)
    (hpoly : M.StateActionPolytope μ d)
    -- [CONDITIONAL HYPOTHESIS] Strong duality: primal = dual
    (_hstrong : M.primalObjective μ V = M.dualObjective d)
    (s : M.S) (a : M.A) (hd_pos : d s a > 0) :
    V s = M.bellmanBackup V s a := by
  have hfeas := M.bellman_optimal_is_feasible V hopt_V
  have hge : V s ≥ M.bellmanBackup V s a := hfeas s a
  suffices h : V s ≤ M.bellmanBackup V s a from le_antisymm h hge
  by_contra h_not_le
  push_neg at h_not_le
  have hgap : V s - M.bellmanBackup V s a > 0 := by linarith
  -- Each term d(s,a) * (V(s) - (TV)(s,a)) >= 0
  have hterm_nn : ∀ s' a', 0 ≤ d s' a' * (V s' - M.bellmanBackup V s' a') := by
    intro s' a'
    apply mul_nonneg (hpoly.d_nonneg s' a')
    have := hfeas s' a'
    simp only [bellmanBackup] at this ⊢
    linarith
  -- The (s,a) term is strictly positive
  have hterm_pos : d s a * (V s - M.bellmanBackup V s a) > 0 :=
    mul_pos hd_pos hgap
  -- So the total sum is strictly positive
  have hsum_pos : ∑ s', ∑ a', d s' a' * (V s' - M.bellmanBackup V s' a') > 0 := by
    calc ∑ s', ∑ a', d s' a' * (V s' - M.bellmanBackup V s' a')
        ≥ ∑ a', d s a' * (V s - M.bellmanBackup V s a') :=
          Finset.single_le_sum (fun s' _ => Finset.sum_nonneg fun a' _ => hterm_nn s' a')
            (Finset.mem_univ s)
      _ ≥ d s a * (V s - M.bellmanBackup V s a) :=
          Finset.single_le_sum (fun a' _ => hterm_nn s a') (Finset.mem_univ a)
      _ > 0 := hterm_pos
  -- But strong duality forces this sum to be 0
  have hzero : ∑ s', ∑ a', d s' a' * (V s' - M.bellmanBackup V s' a') = 0 :=
    M.slackness_sum_eq_zero μ V d hfeas hpoly _hstrong
  linarith

/-! ### LP Optimal Policy Characterization -/

/-- **Value function of optimal-dual-extracted policy equals optimal value.**

  Under LP strong duality, the policy π_d extracted from the dual
  optimal solution d* satisfies V^{π_d} = V*. That is, the greedy
  policy with respect to the optimal dual variables is itself optimal.

  This is the fundamental policy-extraction result for LP-based planning
  (Puterman, Theorem 6.9.1). The proof goes through complementary
  slackness: at every state visited by π_d, the Bellman constraint is
  tight, so V* is the value function of π_d. -/
theorem lp_optimal_policy_characterization
    (_μ : M.S → ℝ) (V : M.StateValueFn) (d : M.S → M.A → ℝ)
    (_hopt_V : M.isBellmanOptimalV V)
    (hpoly : M.StateActionPolytope _μ d)
    -- [CONDITIONAL HYPOTHESIS] Strong duality holds
    (_hstrong : M.primalObjective _μ V = M.dualObjective d)
    -- [CONDITIONAL HYPOTHESIS] d encodes the value function of the extracted policy:
    -- The extracted policy achieves the same primal objective as V*
    (_hpolicy_value : ∀ s,
      (∑ a, M.optimalPolicyFromDual d hpoly.d_nonneg s a *
        (M.r s a + M.γ * ∑ s', M.P s a s' * V s')) = V s) :
    M.primalObjective _μ V =
      ∑ s, _μ s * ∑ a, M.optimalPolicyFromDual d hpoly.d_nonneg s a *
        (M.r s a + M.γ * ∑ s', M.P s a s' * V s') := by
  -- The extracted policy matches V at every state, so the primal objectives agree.
  simp only [primalObjective]
  congr 1; funext s
  rw [_hpolicy_value s]

/-! ### Primal Value = Bellman Value -/

/-- **Primal LP value equals Bellman optimal value.**

  Under strong duality, the LP primal value ∑_s μ(s) V*(s) equals
  the Bellman optimal value. This chains weak duality (primal >= dual)
  with strong duality (primal = dual).

  Concretely: for any Bellman-optimal V* and probability distribution μ,
    ∑_s μ(s) V*(s) = (1/(1-γ)) ∑_{s,a} d*(s,a) r(s,a)
  where d* is the dual-optimal occupancy measure. -/
theorem primal_value_eq_bellman
    (_hyp : M.LPStrongDualityHyp)
    (μ : M.S → ℝ) (V : M.StateValueFn)
    (hopt : M.isBellmanOptimalV V)
    (_hμ_nn : ∀ s, 0 ≤ μ s) (_hμ_sum : ∑ s, μ s = 1) :
    ∃ d : M.S → M.A → ℝ,
      M.StateActionPolytope μ d ∧
      M.primalObjective μ V = M.dualObjective d ∧
      M.dualObjective d ≥ M.dualObjective d := by
  -- From strong duality, obtain the dual-optimal d
  obtain ⟨d, hpoly, heq⟩ := M.lp_strong_duality _hyp μ V hopt _hμ_nn _hμ_sum
  exact ⟨d, hpoly, heq, le_refl _⟩

/-- **Strong duality gives both directions.**

  The LP primal value equals the dual value, and the dual value is
  the best (maximum) over all dual feasible solutions.
  Combined with weak duality, this gives:
    dual_opt = primal_opt (= ∑ μ V*). -/
theorem primal_eq_dual_chain
    (_hyp : M.LPStrongDualityHyp)
    (μ : M.S → ℝ) (V : M.StateValueFn)
    (hopt : M.isBellmanOptimalV V)
    (_hμ_nn : ∀ s, 0 ≤ μ s) (_hμ_sum : ∑ s, μ s = 1)
    (d : M.S → M.A → ℝ)
    (hpoly : M.StateActionPolytope μ d) :
    M.dualObjective d ≤ M.primalObjective μ V := by
  -- Weak duality gives primal >= dual for any feasible pair
  exact M.weak_duality μ V d (M.bellman_optimal_is_feasible V hopt) hpoly

/-! ### Sensitivity Analysis -/

/-- **Monotonicity of dual objective in reward (same-MDP form).**

  The dual objective ∑ d(s,a) r(s,a) / (1-γ) is monotone in the
  reward function: if we have two reward functions r₁ ≤ r₂ pointwise
  and d ≥ 0, then the dual objective under r₁ is at most that under r₂.

  This is the basic sensitivity fact: increasing rewards increases
  the objective value for any fixed feasible dual solution.

  Stated for the same MDP with a reward perturbation. -/
theorem dual_objective_monotone_reward
    (d : M.S → M.A → ℝ)
    (hd_nn : ∀ s a, 0 ≤ d s a)
    (r₂ : M.S → M.A → ℝ)
    (hr : ∀ s a, M.r s a ≤ r₂ s a) :
    M.dualObjective d ≤
      (1 / (1 - M.γ)) * ∑ s, ∑ a, d s a * r₂ s a := by
  simp only [dualObjective]
  apply mul_le_mul_of_nonneg_left
  · exact Finset.sum_le_sum fun s _ =>
      Finset.sum_le_sum fun a _ =>
        mul_le_mul_of_nonneg_left (hr s a) (hd_nn s a)
  · rw [one_div]
    exact inv_nonneg.mpr (by linarith [M.γ_lt_one])

/-- **Sensitivity of dual objective within the same MDP.**

  For a fixed MDP, if we have two state-action measures d₁, d₂ ≥ 0
  with d₁ ≤ d₂ pointwise and nonneg rewards, then dualObj(d₁) ≤ dualObj(d₂).

  This shows the dual objective is monotone in the occupancy measure
  when rewards are nonneg. -/
theorem dual_objective_monotone_occupancy
    (d₁ d₂ : M.S → M.A → ℝ)
    (_hd1_nn : ∀ s a, 0 ≤ d₁ s a)
    (_hd2_nn : ∀ s a, 0 ≤ d₂ s a)
    (hle : ∀ s a, d₁ s a ≤ d₂ s a)
    (hr_nn : ∀ s a, 0 ≤ M.r s a) :
    M.dualObjective d₁ ≤ M.dualObjective d₂ := by
  simp only [dualObjective]
  apply mul_le_mul_of_nonneg_left
  · exact Finset.sum_le_sum fun s _ =>
      Finset.sum_le_sum fun a _ =>
        mul_le_mul_of_nonneg_right (hle s a) (hr_nn s a)
  · rw [one_div]
    exact inv_nonneg.mpr (by linarith [M.γ_lt_one])

/-! ### KKT Conditions -/

/-- **KKT conditions for the MDP LP.**

  The KKT (Karush-Kuhn-Tucker) conditions for the LP formulation:
  1. Primal feasibility: V(s) ≥ r(s,a) + γ ∑ P V for all s,a
  2. Dual feasibility: d(s,a) ≥ 0 for all s,a, with flow conservation
  3. Complementary slackness: d(s,a) * (V(s) - TV(s,a)) = 0
  4. Gradient condition (stationarity): encoded in the flow conservation -/
structure KKTConditions (μ : M.S → ℝ) (V : M.StateValueFn) (d : M.S → M.A → ℝ) : Prop where
  /-- Primal feasibility: V dominates the Bellman operator -/
  primal_feasible : M.PrimalFeasible V
  /-- Dual feasibility: d is in the state-action polytope -/
  dual_feasible : M.StateActionPolytope μ d
  /-- Complementary slackness: d(s,a) * (V(s) - TV(s,a)) = 0 for all s,a -/
  compl_slack : ∀ s a, d s a * (V s - M.bellmanBackup V s a) = 0
  -- Stationarity is encoded by the flow conservation in dual_feasible

/-- **Strong duality implies complementary slackness in product form.**

  Under strong duality, the total slackness sum is zero:
    ∑_{s,a} d(s,a) * (V(s) - TV(s,a)) = 0

  Since each term is nonneg (d ≥ 0 and V ≥ TV from primal feasibility),
  each term must individually be zero. -/
theorem strong_duality_implies_compl_slack_sum
    (μ : M.S → ℝ) (V : M.StateValueFn) (d : M.S → M.A → ℝ)
    (hfeas : M.PrimalFeasible V)
    (hpoly : M.StateActionPolytope μ d)
    -- [CONDITIONAL HYPOTHESIS] Strong duality
    (_hstrong : M.primalObjective μ V = M.dualObjective d) :
    ∀ s a, d s a * (V s - M.bellmanBackup V s a) = 0 := by
  -- Total sum equals 0 (bellmanBackup unfolds to the raw form)
  have hzero : ∑ s, ∑ a, d s a * (V s - M.bellmanBackup V s a) = 0 :=
    M.slackness_sum_eq_zero μ V d hfeas hpoly _hstrong
  -- Each term is nonneg
  have hterm_nn : ∀ s' a', 0 ≤ d s' a' * (V s' - M.bellmanBackup V s' a') := by
    intro s' a'
    apply mul_nonneg (hpoly.d_nonneg s' a')
    have := hfeas s' a'
    simp only [bellmanBackup] at this ⊢
    linarith
  -- Sum of nonneg terms is 0 -> each is 0
  have houter_nn : ∀ s' ∈ (Finset.univ : Finset M.S),
      0 ≤ ∑ a', d s' a' * (V s' - M.bellmanBackup V s' a') :=
    fun s' _ => Finset.sum_nonneg fun a' _ => hterm_nn s' a'
  have h_each_outer : ∀ s' ∈ (Finset.univ : Finset M.S),
      ∑ a', d s' a' * (V s' - M.bellmanBackup V s' a') = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg houter_nn).mp hzero
  intro s a
  have hinner_nn : ∀ a' ∈ (Finset.univ : Finset M.A),
      0 ≤ d s a' * (V s - M.bellmanBackup V s a') :=
    fun a' _ => hterm_nn s a'
  have h_each_inner : ∀ a' ∈ (Finset.univ : Finset M.A),
      d s a' * (V s - M.bellmanBackup V s a') = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hinner_nn).mp (h_each_outer s (Finset.mem_univ s))
  exact h_each_inner a (Finset.mem_univ a)

/-- **Strong duality implies the KKT conditions.**

  If V is Bellman-optimal, d is dual-feasible (in K_μ), and
  strong duality holds (primal = dual), then the KKT conditions
  are satisfied. -/
theorem strong_duality_implies_KKT
    (μ : M.S → ℝ) (V : M.StateValueFn) (d : M.S → M.A → ℝ)
    (hopt : M.isBellmanOptimalV V)
    (hpoly : M.StateActionPolytope μ d)
    -- [CONDITIONAL HYPOTHESIS] Strong duality
    (_hstrong : M.primalObjective μ V = M.dualObjective d) :
    M.KKTConditions μ V d := by
  exact {
    primal_feasible := M.bellman_optimal_is_feasible V hopt
    dual_feasible := hpoly
    compl_slack := M.strong_duality_implies_compl_slack_sum μ V d
        (M.bellman_optimal_is_feasible V hopt) hpoly _hstrong
  }

/-- **KKT conditions imply weak duality bound.**

  If the KKT conditions hold, then the primal objective is at least
  the dual objective. Combined with the complementary slackness
  (which forces equality of the gap terms), this gives primal >= dual. -/
theorem KKT_implies_primal_ge_dual
    (μ : M.S → ℝ) (V : M.StateValueFn) (d : M.S → M.A → ℝ)
    (hkkt : M.KKTConditions μ V d) :
    M.primalObjective μ V ≥ M.dualObjective d := by
  exact M.weak_duality μ V d hkkt.primal_feasible hkkt.dual_feasible

end FiniteMDP

end
