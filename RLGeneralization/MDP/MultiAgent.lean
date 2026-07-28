/-
# Multi-Agent Reinforcement Learning

Formalizes Markov games (stochastic games): the multi-agent extension
of MDPs where N agents interact in a shared environment, each with
their own reward function. Key results include Nash equilibrium
definitions and the minimax theorem for two-player zero-sum games.

## Mathematical Background

A **Markov game** (Shapley 1953) is a tuple (N, S, {A_i}, P, {r_i}, γ) where:
- N agents with individual action spaces A_i
- Joint action a = (a_1, ..., a_N) determines transition and rewards
- P(s' | s, a) is the transition given joint action
- r_i(s, a) is agent i's reward

A **Nash equilibrium** is a joint policy where no agent can improve
their value by unilateral deviation.

## Main Definitions

* `MarkovGame` - Markov game (stochastic game) structure
* `JointPolicy` - Joint policy (one per agent)
* `NashEquilibrium` - Nash equilibrium condition
* `TwoPlayerZeroSum` - Two-player zero-sum game structure
* `payoff_le_max_row` - Weak duality: payoff <= max row value

## Approach

We work with finite games (finitely many states and actions per agent)
and a fixed finite number of agents. Nash equilibrium is defined as
a Prop. The minimax theorem for finite two-player zero-sum games
is stated algebraically.

## Blocked

- **Nash equilibrium existence**: requires Brouwer/Kakutani fixed-point
  theorem, which is not in Mathlib.
- **Correlated equilibrium**: requires LP characterization.
- **Learning dynamics**: fictitious play, no-regret convergence to
  coarse correlated equilibrium. Requires online learning theory.
- **Mean-field games**: continuous-agent limit. Requires measure theory
  on the space of distributions.

## References

* [Shapley, *Stochastic Games*, 1953]
* [Filar and Vrieze, *Competitive Markov Decision Processes*, 1997]
* [Shoham and Leyton-Brown, *Multiagent Systems*, 2009]
* [Zhang, Yang, Basar, *Multi-Agent Reinforcement Learning: A Selective Overview
  of Theories and Algorithms*, 2021]
-/

import RLGeneralization.MDP.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset BigOperators

noncomputable section

/-! ### Markov Game Structure -/

/-- A **Markov game** (stochastic game) with N agents.

    Each agent i has an individual action space. The joint action
    determines the transition and individual rewards. We index
    agents by `Fin N` and use a common action space for simplicity
    (heterogeneous action spaces can be embedded by padding). -/
structure MarkovGame (N : ℕ) where
  /-- State space (finite) -/
  S : Type
  /-- Action space per agent (finite, common for simplicity) -/
  A : Type
  [instFintypeS : Fintype S]
  [instFintypeA : Fintype A]
  [instDecEqS : DecidableEq S]
  [instDecEqA : DecidableEq A]
  [instNonemptyS : Nonempty S]
  [instNonemptyA : Nonempty A]
  /-- Transition probability: P(s' | s, joint_action) -/
  P : S → (Fin N → A) → S → ℝ
  /-- Reward for agent i: r_i(s, joint_action) -/
  r : Fin N → S → (Fin N → A) → ℝ
  /-- Discount factor γ ∈ [0, 1) -/
  γ : ℝ
  /-- P is nonneg -/
  P_nonneg : ∀ s a s', 0 ≤ P s a s'
  /-- P sums to 1 -/
  P_sum_one : ∀ s a, ∑ s', P s a s' = 1
  /-- Discount factor bounds -/
  γ_nonneg : 0 ≤ γ
  γ_lt_one : γ < 1

namespace MarkovGame

variable {N : ℕ} (G : MarkovGame N)

attribute [instance] MarkovGame.instFintypeS MarkovGame.instFintypeA
  MarkovGame.instDecEqS MarkovGame.instDecEqA
  MarkovGame.instNonemptyS MarkovGame.instNonemptyA

/-! ### Policies -/

/-- A **joint deterministic policy**: each agent maps states to actions. -/
def JointPolicy := Fin N → (G.S → G.A)

/-- Agent i's individual policy extracted from a joint policy. -/
def agentPolicy (π : G.JointPolicy) (i : Fin N) : G.S → G.A := π i

/-- The joint action at state s under joint policy π. -/
def jointAction (π : G.JointPolicy) (s : G.S) : Fin N → G.A :=
  fun i => π i s

/-! ### Value Functions -/

-- [UNUSED]
/-- **Expected immediate reward** for agent i at state s under joint policy π:
    r_i(s, π(s)). -/
def immediateReward (π : G.JointPolicy) (i : Fin N) (s : G.S) : ℝ :=
  G.r i s (G.jointAction π s)

/-- **Expected next-state value** under joint policy π at state s:
    ∑_{s'} P(s' | s, π(s)) · V(s'). -/
def expectedNextValue (π : G.JointPolicy) (s : G.S) (V : G.S → ℝ) : ℝ :=
  ∑ s', G.P s (G.jointAction π s) s' * V s'

/-- Expected next-state value is nonneg when V is nonneg. -/
theorem expectedNextValue_nonneg (π : G.JointPolicy) (s : G.S) (V : G.S → ℝ)
    (hV : ∀ s, 0 ≤ V s) :
    0 ≤ G.expectedNextValue π s V := by
  unfold expectedNextValue
  exact Finset.sum_nonneg fun s' _ =>
    mul_nonneg (G.P_nonneg s (G.jointAction π s) s') (hV s')

/-! ### Unilateral Deviation

Agent i deviates to policy π'_i while all other agents keep their
policies from π. This is the key concept for Nash equilibrium. -/

/-- **Unilateral deviation**: agent i plays π'_i while others keep π. -/
def unilateralDeviation (π : G.JointPolicy) (i : Fin N)
    (π'_i : G.S → G.A) : G.JointPolicy :=
  fun j => if j = i then π'_i else π j

/-- Unilateral deviation preserves other agents' policies. -/
theorem unilateral_deviation_other (π : G.JointPolicy) (i j : Fin N)
    (π'_i : G.S → G.A) (hij : j ≠ i) :
    G.agentPolicy (G.unilateralDeviation π i π'_i) j = G.agentPolicy π j := by
  unfold agentPolicy unilateralDeviation
  simp [hij]

/-- Unilateral deviation gives agent i the new policy. -/
theorem unilateral_deviation_self (π : G.JointPolicy) (i : Fin N)
    (π'_i : G.S → G.A) :
    G.agentPolicy (G.unilateralDeviation π i π'_i) i = π'_i := by
  unfold agentPolicy unilateralDeviation
  simp

/-! ### Nash Equilibrium -/

/-- A **Nash equilibrium** is a joint policy π* such that no agent
    can improve their value by unilateral deviation.

    Formally: for all agents i and all alternative policies π'_i,
    V_i^{π*}(s) ≥ V_i^{(π'_i, π*_{-i})}(s) for all s.

    We encode this using value function witnesses. -/
structure NashEquilibrium where
  /-- The equilibrium joint policy -/
  policy : G.JointPolicy
  /-- Value function for each agent under the equilibrium -/
  value : Fin N → G.S → ℝ
  /-- Nash condition: no agent can improve by unilateral deviation.
      For each agent i and deviation π'_i, the immediate reward plus
      discounted continuation under deviation is no better than the
      equilibrium value. -/
  nash_condition : ∀ (i : Fin N) (π'_i : G.S → G.A) (s : G.S),
    G.r i s (fun j => if j = i then π'_i s else policy j s) +
    G.γ * ∑ s', G.P s (fun j => if j = i then π'_i s else policy j s) s' *
      value i s' ≤
    value i s

/-! ### Two-Player Zero-Sum Games -/

/-- A **two-player zero-sum game**: a Markov game with N = 2 where
    r₁(s, a) + r₂(s, a) = 0 for all states and joint actions.

    Player 1 is the maximizer, player 2 is the minimizer. -/
structure TwoPlayerZeroSum where
  /-- The underlying 2-player Markov game -/
  game : MarkovGame 2
  /-- Zero-sum condition: r₁ + r₂ = 0 -/
  zero_sum : ∀ s a, game.r 0 s a + game.r 1 s a = 0

namespace TwoPlayerZeroSum

variable (G : TwoPlayerZeroSum)

/-- In a zero-sum game, player 2's reward is the negation of player 1's. -/
theorem r2_eq_neg_r1 (s : G.game.S) (a : Fin 2 → G.game.A) :
    G.game.r 1 s a = -G.game.r 0 s a := by
  linarith [G.zero_sum s a]

end TwoPlayerZeroSum

/-! ### Minimax Theorem (Finite Matrix Games)

For a finite two-player zero-sum **stage game** (no dynamics, single step),
the minimax theorem states:

  max_{π₁} min_{π₂} ∑ π₁(a₁) π₂(a₂) r(a₁, a₂)
  = min_{π₂} max_{π₁} ∑ π₁(a₁) π₂(a₂) r(a₁, a₂)

This is Von Neumann's minimax theorem (1928). The proof requires LP duality
or Brouwer's fixed-point theorem.

We state the algebraic structure: for finite matrices, the max-min ≤ min-max
direction is always true (weak duality). The equality (strong duality)
is stated as a hypothesis. -/

/-- **Matrix game payoff**: player 1 plays mixed strategy p over Fin m,
    player 2 plays mixed strategy q over Fin n, with payoff matrix R. -/
def matrixGamePayoff {m n : ℕ} (R : Fin m → Fin n → ℝ)
    (p : Fin m → ℝ) (q : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, p i * q j * R i j

/-- The payoff is bilinear: linear in p for fixed q. -/
theorem matrixGamePayoff_linear_p {m n : ℕ} (R : Fin m → Fin n → ℝ)
    (p₁ p₂ : Fin m → ℝ) (q : Fin n → ℝ) (c₁ c₂ : ℝ) :
    matrixGamePayoff R (fun i => c₁ * p₁ i + c₂ * p₂ i) q =
    c₁ * matrixGamePayoff R p₁ q + c₂ * matrixGamePayoff R p₂ q := by
  unfold matrixGamePayoff
  simp [add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]

/-- The payoff is bilinear: linear in `q` for fixed `p`. -/
theorem matrixGamePayoff_linear_q {m n : ℕ} (R : Fin m → Fin n → ℝ)
    (p : Fin m → ℝ) (q₁ q₂ : Fin n → ℝ) (c₁ c₂ : ℝ) :
    matrixGamePayoff R p (fun j => c₁ * q₁ j + c₂ * q₂ j) =
    c₁ * matrixGamePayoff R p q₁ + c₂ * matrixGamePayoff R p q₂ := by
  unfold matrixGamePayoff
  calc
    ∑ i, ∑ j, p i * (c₁ * q₁ j + c₂ * q₂ j) * R i j
        = ∑ i, ∑ j, (c₁ * (p i * q₁ j * R i j) + c₂ * (p i * q₂ j * R i j)) := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            ring
    _ = ∑ i, (c₁ * ∑ j, p i * q₁ j * R i j + c₂ * ∑ j, p i * q₂ j * R i j) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = c₁ * ∑ i, ∑ j, p i * q₁ j * R i j + c₂ * ∑ i, ∑ j, p i * q₂ j * R i j := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = c₁ * matrixGamePayoff R p q₁ + c₂ * matrixGamePayoff R p q₂ := by
            unfold matrixGamePayoff
            rfl

/-- **Weak duality** (max-min ≤ min-max direction): for any mixed strategies,
    the best response against the worst case is no better than the worst case
    against the best response.

    min_q max_i ∑_j q_j R_{ij} ≥ max_p min_j ∑_i p_i R_{ij}

    We prove the elementary form: for any fixed p and q,
    ∑_{ij} p_i q_j R_{ij} is between min_j(∑_i p_i R_{ij}) and
    max_i(∑_j q_j R_{ij}) when p, q are distributions. -/
theorem payoff_le_max_row {m n : ℕ} [Nonempty (Fin m)] [Nonempty (Fin n)]
    (R : Fin m → Fin n → ℝ)
    (p : Fin m → ℝ) (q : Fin n → ℝ)
    (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (_hq_nonneg : ∀ j, 0 ≤ q j) (_hq_sum : ∑ j, q j = 1) :
    matrixGamePayoff R p q ≤
    Finset.univ.sup' Finset.univ_nonempty (fun i => ∑ j, q j * R i j) := by
  unfold matrixGamePayoff
  calc ∑ i, ∑ j, p i * q j * R i j
      = ∑ i, p i * ∑ j, q j * R i j := by
        congr 1; ext i; rw [Finset.mul_sum]; congr 1; ext j; ring
    _ ≤ ∑ i, p i * Finset.univ.sup' Finset.univ_nonempty
          (fun i => ∑ j, q j * R i j) := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_left (Finset.le_sup' _ (Finset.mem_univ i))
          (hp_nonneg i)
    _ = (∑ i, p i) * Finset.univ.sup' Finset.univ_nonempty
          (fun i => ∑ j, q j * R i j) := by rw [Finset.sum_mul]
    _ = Finset.univ.sup' Finset.univ_nonempty
          (fun i => ∑ j, q j * R i j) := by rw [hp_sum, one_mul]

/-- Lower sandwich bound: the expected payoff is at least the smallest
    column payoff against the mixed strategy `p`. -/
theorem min_col_le_payoff {m n : ℕ} [Nonempty (Fin m)] [Nonempty (Fin n)]
    (R : Fin m → Fin n → ℝ)
    (p : Fin m → ℝ) (q : Fin n → ℝ)
    (_hp_nonneg : ∀ i, 0 ≤ p i) (_hp_sum : ∑ i, p i = 1)
    (hq_nonneg : ∀ j, 0 ≤ q j) (hq_sum : ∑ j, q j = 1) :
    Finset.univ.inf' Finset.univ_nonempty (fun j => ∑ i, p i * R i j) ≤
    matrixGamePayoff R p q := by
  unfold matrixGamePayoff
  calc Finset.univ.inf' Finset.univ_nonempty (fun j => ∑ i, p i * R i j)
      = (∑ j, q j) * Finset.univ.inf' Finset.univ_nonempty (fun j => ∑ i, p i * R i j) := by
          rw [hq_sum, one_mul]
    _ = ∑ j, q j * Finset.univ.inf' Finset.univ_nonempty (fun j => ∑ i, p i * R i j) := by
          rw [← Finset.sum_mul]
    _ ≤ ∑ j, q j * ∑ i, p i * R i j := by
          apply Finset.sum_le_sum
          intro j _
          apply mul_le_mul_of_nonneg_left
            (Finset.inf'_le _ (Finset.mem_univ j))
            (hq_nonneg j)
    _ = ∑ j, ∑ i, q j * (p i * R i j) := by
          congr 1
          ext j
          rw [Finset.mul_sum]
    _ = ∑ i, ∑ j, p i * q j * R i j := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          ring

/-- The matrix-game payoff lies between the minimum column payoff and
    the maximum row payoff. -/
theorem payoff_between_min_col_max_row {m n : ℕ} [Nonempty (Fin m)] [Nonempty (Fin n)]
    (R : Fin m → Fin n → ℝ)
    (p : Fin m → ℝ) (q : Fin n → ℝ)
    (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (hq_nonneg : ∀ j, 0 ≤ q j) (hq_sum : ∑ j, q j = 1) :
    Finset.univ.inf' Finset.univ_nonempty (fun j => ∑ i, p i * R i j) ≤
    matrixGamePayoff R p q ∧
    matrixGamePayoff R p q ≤
      Finset.univ.sup' Finset.univ_nonempty (fun i => ∑ j, q j * R i j) := by
  constructor
  · exact min_col_le_payoff R p q hp_nonneg hp_sum hq_nonneg hq_sum
  · exact payoff_le_max_row R p q hp_nonneg hp_sum hq_nonneg hq_sum

/-- Weak-duality corollary: for any mixed strategies `p` and `q`, the
    minimum column payoff against `p` is bounded above by the maximum
    row payoff against `q`. -/
theorem min_col_le_max_row {m n : ℕ} [Nonempty (Fin m)] [Nonempty (Fin n)]
    (R : Fin m → Fin n → ℝ)
    (p : Fin m → ℝ) (q : Fin n → ℝ)
    (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (hq_nonneg : ∀ j, 0 ≤ q j) (hq_sum : ∑ j, q j = 1) :
    Finset.univ.inf' Finset.univ_nonempty (fun j => ∑ i, p i * R i j) ≤
    Finset.univ.sup' Finset.univ_nonempty (fun i => ∑ j, q j * R i j) := by
  exact le_trans
    (min_col_le_payoff R p q hp_nonneg hp_sum hq_nonneg hq_sum)
    (payoff_le_max_row R p q hp_nonneg hp_sum hq_nonneg hq_sum)

/-! ### Cooperative vs Competitive

In cooperative games, agents share a common reward:
  r₁ = r₂ = ... = r_N

This reduces to a single-agent MDP with a larger action space.
In competitive games (zero-sum), the minimax framework applies. -/

-- [UNUSED]
/-- A **cooperative game** is a Markov game where all agents share the
    same reward function. -/
def isCooperative (G : MarkovGame N) : Prop :=
  ∀ i j : Fin N, ∀ s a, G.r i s a = G.r j s a

/-! ### Von Neumann Minimax Theorem

  For finite two-player zero-sum games:
    max_p min_q p^T R q = min_q max_p p^T R q

  The weak direction (≤) follows from our `min_col_le_max_row`.
  The strong direction (≥, i.e., equality) requires LP strong duality
  or Brouwer's fixed-point theorem, neither of which is in Mathlib.

  We state the minimax theorem as a conditional result, taking the
  existence of a saddle point as a hypothesis.
-/

/-- **Saddle-point condition**: strategies (p*, q*) form a saddle point
    if p* is optimal against q* and q* is optimal against p*. -/
structure SaddlePoint {m n : ℕ} (R : Fin m → Fin n → ℝ) where
  /-- Player 1's equilibrium strategy -/
  p : Fin m → ℝ
  /-- Player 2's equilibrium strategy -/
  q : Fin n → ℝ
  /-- p is a distribution -/
  p_nonneg : ∀ i, 0 ≤ p i
  p_sum : ∑ i, p i = 1
  /-- q is a distribution -/
  q_nonneg : ∀ j, 0 ≤ q j
  q_sum : ∑ j, q j = 1
  /-- Saddle-point inequality:
      for all distributions p', q':
      p'^T R q* ≤ p*^T R q* ≤ p*^T R q' -/
  saddle_le : ∀ (p' : Fin m → ℝ), (∀ i, 0 ≤ p' i) → ∑ i, p' i = 1 →
    matrixGamePayoff R p' q ≤ matrixGamePayoff R p q
  le_saddle : ∀ (q' : Fin n → ℝ), (∀ j, 0 ≤ q' j) → ∑ j, q' j = 1 →
    matrixGamePayoff R p q ≤ matrixGamePayoff R p q'

/-- **Von Neumann minimax theorem** (conditional on saddle-point existence).

  If a saddle point (p*, q*) exists, then:
    max_p min_q p^T R q = min_q max_p p^T R q = p*^T R q*

  More precisely: the minimax value equals the maximin value,
  and both equal the saddle-point payoff.

  We prove: for any distributions p and q,
    min_j (∑_i p_i R_{ij}) ≤ v* ≤ max_i (∑_j q_j R_{ij})
  where v* = p*^T R q* is the game value. -/
theorem von_neumann_minimax {m n : ℕ}
    [Nonempty (Fin m)] [Nonempty (Fin n)]
    (R : Fin m → Fin n → ℝ)
    (sp : SaddlePoint R)
    (p : Fin m → ℝ) (hp_nn : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (q : Fin n → ℝ) (hq_nn : ∀ j, 0 ≤ q j) (hq_sum : ∑ j, q j = 1) :
    -- Any player 1 strategy p: min column payoff ≤ game value
    Finset.univ.inf' Finset.univ_nonempty (fun j => ∑ i, p i * R i j) ≤
    matrixGamePayoff R sp.p sp.q ∧
    -- Any player 2 strategy q: game value ≤ max row payoff
    matrixGamePayoff R sp.p sp.q ≤
    Finset.univ.sup' Finset.univ_nonempty (fun i => ∑ j, q j * R i j) := by
  constructor
  · -- min_j (∑_i p_i R_{ij}) ≤ p^T R q* ≤ p*^T R q* = v*
    calc Finset.univ.inf' Finset.univ_nonempty (fun j => ∑ i, p i * R i j)
        ≤ matrixGamePayoff R p sp.q :=
          min_col_le_payoff R p sp.q hp_nn hp_sum sp.q_nonneg sp.q_sum
      _ ≤ matrixGamePayoff R sp.p sp.q := sp.saddle_le p hp_nn hp_sum
  · -- v* = p*^T R q* ≤ p*^T R q ≤ max_i (∑_j q_j R_{ij})
    calc matrixGamePayoff R sp.p sp.q
        ≤ matrixGamePayoff R sp.p q := sp.le_saddle q hq_nn hq_sum
      _ ≤ Finset.univ.sup' Finset.univ_nonempty (fun i => ∑ j, q j * R i j) :=
          payoff_le_max_row R sp.p q sp.p_nonneg sp.p_sum hq_nn hq_sum

/-- **Minimax equality** (conditional on saddle-point existence).

  If a saddle point exists for the payoff matrix R, then:
    max_p min_j (∑_i p_i R_{ij}) = min_q max_i (∑_j q_j R_{ij})

  Specifically, both equal the saddle-point payoff v* = p*^T R q*.
  This is the algebraic content of the Von Neumann minimax theorem.

  Proved given a saddle point `sp : SaddlePoint R`. The existence
  of such a saddle point follows from LP strong duality or Brouwer's
  fixed-point theorem (not formalized here). -/
theorem minimax_equality {m n : ℕ}
    [Nonempty (Fin m)] [Nonempty (Fin n)]
    (R : Fin m → Fin n → ℝ) (sp : SaddlePoint R) :
    -- The saddle-point payoff is sandwiched between maximin and minimax
    -- For the equilibrium strategies:
    -- min_j payoff against q* = v* = max_i payoff against p*
    Finset.univ.inf' Finset.univ_nonempty
      (fun j => ∑ i, sp.p i * R i j) =
    matrixGamePayoff R sp.p sp.q ∧
    matrixGamePayoff R sp.p sp.q =
    Finset.univ.sup' Finset.univ_nonempty
      (fun i => ∑ j, sp.q j * R i j) := by
  -- Helper: payoff against a pure column strategy e_j equals the column sum
  have pure_col : ∀ j : Fin n, matrixGamePayoff R sp.p (fun j' => if j' = j then 1 else 0) =
      ∑ i, sp.p i * R i j := by
    intro j
    simp only [matrixGamePayoff]
    apply Finset.sum_congr rfl; intro i _
    simp [Finset.sum_ite_eq', Finset.mem_univ, mul_comm]
  -- Helper: payoff against a pure row strategy e_i equals the row sum
  have pure_row : ∀ i : Fin m, matrixGamePayoff R (fun i' => if i' = i then 1 else 0) sp.q =
      ∑ j, sp.q j * R i j := by
    intro i
    simp only [matrixGamePayoff]
    simp [Finset.sum_ite_eq', Finset.mem_univ, mul_comm]
  constructor
  · -- min_j (∑_i p*_i R_{ij}) = v*
    apply le_antisymm
    · exact min_col_le_payoff R sp.p sp.q sp.p_nonneg sp.p_sum sp.q_nonneg sp.q_sum
    · -- v* ≤ min_j: for all q', v* ≤ p*^T R q', so v* ≤ min column
      apply Finset.le_inf'
      intro j _
      -- p*^T R q* ≤ p*^T R e_j = ∑_i p*_i R_{ij}
      have h := sp.le_saddle (fun j' => if j' = j then 1 else 0)
        (fun j' => by dsimp only; split_ifs <;> norm_num)
        (by simp [Finset.sum_ite_eq', Finset.mem_univ])
      rw [pure_col] at h
      exact h
  · -- v* = max_i (∑_j q*_j R_{ij})
    apply le_antisymm
    · exact payoff_le_max_row R sp.p sp.q sp.p_nonneg sp.p_sum sp.q_nonneg sp.q_sum
    · -- max_i (∑_j q*_j R_{ij}) ≤ v*: for all p', p'^T R q* ≤ v*
      apply Finset.sup'_le
      intro i _
      -- e_i^T R q* = ∑_j q*_j R_{ij} ≤ p*^T R q*
      have h := sp.saddle_le (fun i' => if i' = i then 1 else 0)
        (fun i' => by dsimp only; split_ifs <;> norm_num)
        (by simp [Finset.sum_ite_eq', Finset.mem_univ])
      rw [pure_row] at h
      exact h

end MarkovGame

end
