/-
# Monte Carlo Tree Search (MCTS) and UCT

Formalizes the core components and algebraic properties of Monte Carlo
Tree Search with Upper Confidence bounds applied to Trees (UCT).

## Main Definitions

* `MCTSNode` -- A tree node storing visit count N(s), total value W(s),
  and number of children.
* `mcts_value_estimate` -- Empirical mean Q_hat(s,a) = W(s,a) / N(s,a).
* `mcts_exploration_bonus` -- Exploration bonus c * sqrt(ln N(s) / N(s,a)).
* `uct_selection_score` -- UCT score = Q_hat + bonus.

## Main Results

* `mcts_value_bounded` -- Value estimates are bounded when returns are bounded.
* `mcts_bonus_decreasing` -- The exploration bonus decreases as N(s,a) grows.
* `mcts_effective_horizon_bound` -- Depth-limited MCTS return bounded by
  R_max * (1 - disc^H) / (1 - disc).
* `mcts_visit_ratio_bound` -- Pigeonhole: at least one root action has
  N(root,a) >= T / |A| visits.

## References

* Kocsis and Szepesv\'ari, "Bandit based Monte-Carlo Planning" (2006).
* Browne et al., "A Survey of MCTS Methods" (2012).
-/

import RLGeneralization.MDP.FiniteHorizon
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Finset BigOperators Real

noncomputable section

namespace FiniteMDP

variable (M : FiniteMDP)

/-! ### Tree Node Structure -/

/-- A node in the MCTS tree, storing visit statistics. -/
structure MCTSNode where
  /-- Visit count N(s) -- number of times this node has been visited -/
  visits : ℕ
  /-- Total accumulated value W(s) -- sum of returns through this node -/
  totalValue : ℝ
  /-- Number of child actions explored from this node -/
  numChildren : ℕ

/-! ### UCT Score Components -/

/-- Empirical mean value estimate: Q_hat(s,a) = W(s,a) / N(s,a).
    When N(s,a) = 0, returns 0 by convention (division by zero in reals). -/
def mcts_value_estimate (W_sa : ℝ) (N_sa : ℕ) : ℝ :=
  W_sa / N_sa

/-- Exploration bonus: bonus(s,a) = c * sqrt(ln N(s) / N(s,a)).
    The denominator uses max(N_sa, 1) to avoid division by zero. -/
def mcts_exploration_bonus (c : ℝ) (N_s : ℕ) (N_sa : ℕ) : ℝ :=
  c * Real.sqrt (Real.log N_s / (max N_sa 1 : ℕ))

/-- UCT selection score: UCT(s,a) = Q_hat(s,a) + c * sqrt(ln N(s) / N(s,a)).
    This is the UCB1 formula applied to tree nodes. -/
def uct_selection_score (W_sa : ℝ) (N_sa : ℕ) (c : ℝ) (N_s : ℕ) : ℝ :=
  mcts_value_estimate W_sa N_sa +
  mcts_exploration_bonus c N_s N_sa

/-! ### Value Estimate Boundedness -/

/-- **Value estimate bounded**: if every individual return through (s,a)
    is bounded in absolute value by V_max, and the total value W(s,a)
    satisfies |W(s,a)| <= N(s,a) * V_max, then the empirical mean
    |Q_hat(s,a)| <= V_max.

    This is the basic property that averaging bounded quantities
    yields a bounded mean. -/
theorem mcts_value_bounded
    (W_sa : ℝ) (N_sa : ℕ) (V_max : ℝ)
    (hN : 0 < (N_sa : ℝ))
    (hW : |W_sa| ≤ N_sa * V_max) :
    |mcts_value_estimate W_sa N_sa| ≤ V_max := by
  unfold mcts_value_estimate
  rw [abs_div, abs_of_pos hN]
  rw [div_le_iff₀ hN]
  linarith [mul_comm V_max (N_sa : ℝ)]

/-! ### Exploration Bonus Monotonicity -/

/-- **Exploration bonus decreasing**: for fixed parent visits N_s and
    exploration constant c >= 0, the exploration bonus decreases as
    the child visit count increases.

    Specifically, if N2 > N1 > 0 and c >= 0, then
    bonus(N2) <= bonus(N1).

    This captures the key UCT property: well-visited actions receive
    less exploration incentive. -/
theorem mcts_bonus_decreasing
    (c : ℝ) (hc : 0 ≤ c)
    (N_s : ℕ) (N₁ N₂ : ℕ)
    (hN₁ : 0 < N₁) (hN₂ : N₁ < N₂)
    (hlog_nonneg : 0 ≤ Real.log N_s) :
    mcts_exploration_bonus c N_s N₂ ≤
    mcts_exploration_bonus c N_s N₁ := by
  unfold mcts_exploration_bonus
  apply mul_le_mul_of_nonneg_left _ hc
  apply Real.sqrt_le_sqrt
  apply div_le_div_of_nonneg_left hlog_nonneg
  · have : (1 : ℝ) ≤ (max N₁ 1 : ℕ) := by exact_mod_cast Nat.le_max_right N₁ 1
    linarith
  · have h₁ : max N₁ 1 = N₁ := Nat.max_eq_left hN₁
    have h₂ : max N₂ 1 = N₂ := Nat.max_eq_left (le_trans hN₁ hN₂.le)
    simp only [h₁, h₂]
    exact_mod_cast hN₂.le

/-! ### Effective Horizon Bound -/

/-- **Depth-limited MCTS return bound**: for a depth-limited MCTS with
    horizon H, discount factor disc in [0,1), and per-step reward bounded
    by R_max, the total discounted return is bounded by
    R_max * (1 - disc^H) / (1 - disc).

    This is the finite geometric series bound that justifies depth-limited
    search: truncating at depth H loses at most the tail
    disc^H * R_max / (1-disc) of the infinite-horizon value. -/
private lemma geom_sum_mul_eq (disc : ℝ) :
    ∀ H : ℕ, (∑ h ∈ Finset.range H, disc ^ h) * (1 - disc) = 1 - disc ^ H := by
  intro H
  induction H with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, add_mul, ih]; ring

theorem mcts_effective_horizon_bound
    (R_max : ℝ) (_hR : 0 ≤ R_max)
    (disc : ℝ) (_hdisc_nonneg : 0 ≤ disc) (hdisc_lt : disc < 1)
    (H : ℕ)
    (G : ℝ)
    (hG : G ≤ ∑ h ∈ Finset.range H, disc ^ h * R_max) :
    G ≤ R_max * (1 - disc ^ H) / (1 - disc) := by
  have hd1 : (1 - disc) ≠ 0 := ne_of_gt (by linarith)
  have hsum : ∑ h ∈ Finset.range H, disc ^ h * R_max =
      R_max * ∑ h ∈ Finset.range H, disc ^ h := by
    rw [Finset.mul_sum]; congr 1; ext h; ring
  rw [hsum] at hG
  have hsuf : ∑ h ∈ Finset.range H, disc ^ h = (1 - disc ^ H) / (1 - disc) := by
    rw [eq_div_iff hd1]
    exact geom_sum_mul_eq disc H
  rw [hsuf] at hG
  linarith [mul_div_assoc R_max (1 - disc ^ H) (1 - disc)]

/-! ### Visit Ratio Bound (Pigeonhole) -/

/-- **Pigeonhole visit bound**: if UCT runs T iterations from the root
    and the root has num_actions actions, then at least one root-level action
    has been visited at least T / num_actions times (natural division).

    This follows from the pigeonhole principle: T visits distributed
    among num_actions actions means some action gets at least T / num_actions. -/
theorem mcts_visit_ratio_bound
    (num_actions : ℕ) (hA : 0 < num_actions)
    (T : ℕ)
    (visit_counts : Fin num_actions → ℕ)
    (hsum : ∑ a : Fin num_actions, visit_counts a = T) :
    ∃ a : Fin num_actions, T / num_actions ≤ visit_counts a := by
  by_contra h
  push_neg at h
  have hlt : ∑ a : Fin num_actions, visit_counts a <
      ∑ _a : Fin num_actions, (T / num_actions) := by
    apply Finset.sum_lt_sum
    · intro a _; exact le_of_lt (h a)
    · exact ⟨⟨0, hA⟩, Finset.mem_univ _, h ⟨0, hA⟩⟩
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, hsum] at hlt
  simp only [smul_eq_mul] at hlt
  have : T / num_actions * num_actions ≤ T := Nat.div_mul_le_self T num_actions
  linarith

end FiniteMDP

end
