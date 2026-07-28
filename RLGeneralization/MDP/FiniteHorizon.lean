/-
# Finite-Horizon Markov Decision Processes

Formalizes finite-horizon MDPs with time-dependent transitions together
with backward induction for optimal action values.

## Main Results

* `FiniteHorizonMDP` - Time-dependent MDP with horizon H
* `backwardQ` - Backward induction: exact Q* computation
* `backwardQ_nonneg` - Q values are nonnegative
* `backwardQ_le` - Q values bounded by remaining steps

## References

* [Agarwal et al., *RL: Theory and Algorithms*]
-/

import RLGeneralization.MDP.BellmanContraction

open Finset BigOperators

noncomputable section

/-! ### Finite-Horizon MDP Structure -/

/-- A finite-horizon MDP with time-dependent dynamics. -/
structure FiniteHorizonMDP where
  S : Type
  A : Type
  [instFintypeS : Fintype S]
  [instFintypeA : Fintype A]
  [instDecEqS : DecidableEq S]
  [instDecEqA : DecidableEq A]
  [instNonemptyS : Nonempty S]
  [instNonemptyA : Nonempty A]
  /-- Horizon -/
  H : ℕ
  /-- Time-dependent transition: P_h(s'|s,a) -/
  P : Fin H → S → A → S → ℝ
  /-- Time-dependent reward: r_h(s,a) -/
  r : Fin H → S → A → ℝ
  P_nonneg : ∀ h s a s', 0 ≤ P h s a s'
  P_sum_one : ∀ h s a, ∑ s', P h s a s' = 1
  r_nonneg : ∀ h s a, 0 ≤ r h s a
  r_le_one : ∀ h s a, r h s a ≤ 1

namespace FiniteHorizonMDP

attribute [instance] FiniteHorizonMDP.instFintypeS
  FiniteHorizonMDP.instFintypeA
  FiniteHorizonMDP.instDecEqS
  FiniteHorizonMDP.instDecEqA
  FiniteHorizonMDP.instNonemptyS
  FiniteHorizonMDP.instNonemptyA

/-! ### Backward Induction

  Exact computation of Q* via backward recursion:
    Q with 0 remaining steps = 0  (terminal)
    Q with k+1 remaining steps = r + P · max(Q with k remaining)

  This is parameterized by "remaining steps k" rather than
  "current step h" for clean structural recursion. The
  correspondence is: step h = H - k, so k remaining
  steps means we are at step H - k. -/

/-- Backward induction: Q-value with k remaining steps.
    `backwardQ M k` gives Q at step H-k. -/
def backwardQ (M : FiniteHorizonMDP) :
    (k : ℕ) → (hk : k ≤ M.H) → M.S → M.A → ℝ
  | 0, _, _, _ => 0
  | k + 1, hk, s, a =>
    let h : Fin M.H := ⟨M.H - k - 1, by omega⟩
    M.r h s a + ∑ s', M.P h s a s' *
      Finset.univ.sup' Finset.univ_nonempty
        (fun a' => backwardQ M k (by omega) s' a')

/-- Terminal condition: Q_H ≡ 0 (0 remaining steps). -/
theorem backwardQ_zero (M : FiniteHorizonMDP)
    (hk : 0 ≤ M.H) (s : M.S) (a : M.A) :
    M.backwardQ 0 hk s a = 0 := rfl

/-- Q values are nonnegative (rewards are nonneg, P ≥ 0). -/
theorem backwardQ_nonneg (M : FiniteHorizonMDP) :
    ∀ (k : ℕ) (hk : k ≤ M.H) (s : M.S) (a : M.A),
    0 ≤ M.backwardQ k hk s a := by
  intro k
  induction k with
  | zero => intro hk s a; simp [backwardQ]
  | succ n ih =>
    intro hk s a
    simp only [backwardQ]
    apply add_nonneg (M.r_nonneg _ s a)
    apply Finset.sum_nonneg; intro s' _
    apply mul_nonneg (M.P_nonneg _ s a s')
    -- sup' Q ≥ Q(s', any_a) ≥ 0
    exact le_trans (ih (by omega) s' (Classical.arbitrary M.A))
      (Finset.le_sup' _ (Finset.mem_univ _))

/-- **Value Bound**: `Q` with `k` remaining steps is at most `k`.
    This follows because each step contributes reward at most `1`. -/
theorem backwardQ_le (M : FiniteHorizonMDP) :
    ∀ (k : ℕ) (hk : k ≤ M.H) (s : M.S) (a : M.A),
    M.backwardQ k hk s a ≤ k := by
  intro k
  induction k with
  | zero => intro hk s a; simp [backwardQ]
  | succ n ih =>
    intro hk s a
    simp only [backwardQ]
    -- r ≤ 1 and ∑ P · max Q ≤ ∑ P · n = n
    have hr : M.r ⟨M.H - n - 1, by omega⟩ s a ≤ 1 :=
      M.r_le_one _ s a
    have htrans : ∑ s', M.P ⟨M.H - n - 1, by omega⟩ s a s' *
        Finset.univ.sup' Finset.univ_nonempty
          (fun a' => M.backwardQ n (by omega) s' a') ≤ n := by
      calc ∑ s', M.P ⟨M.H - n - 1, by omega⟩ s a s' *
              Finset.univ.sup' Finset.univ_nonempty
                (fun a' => M.backwardQ n (by omega) s' a')
          ≤ ∑ s', M.P ⟨M.H - n - 1, by omega⟩ s a s' *
              (n : ℝ) := by
            apply Finset.sum_le_sum; intro s' _
            apply mul_le_mul_of_nonneg_left _
              (M.P_nonneg _ s a s')
            apply Finset.sup'_le; intro a' _
            exact ih (by omega) s' a'
        _ = (∑ s', M.P ⟨M.H - n - 1, by omega⟩ s a s') *
              n := (Finset.sum_mul _ _ _).symm
        _ = n := by rw [M.P_sum_one, one_mul]
    push_cast; linarith

/-! ### Backward Induction Optimality -/

/-- **Backward induction dominates any evaluation**.

  For any function f(s) ≤ max_a Q*_{k}(s,a) and any action a:
    r_h(s,a) + ∑ P_h(s'|s,a) f(s') ≤ Q*_{k+1}(s,a)

  This is the one-step monotonicity that drives the backward
  induction optimality proof. By induction, any policy value
  V^π_h(s) ≤ max_a Q*_h(s,a) for all s,h. -/
theorem backwardQ_dominates_step (M : FiniteHorizonMDP)
    (k : ℕ) (hk : k + 1 ≤ M.H)
    (f : M.S → ℝ)
    (hf : ∀ s, f s ≤ Finset.univ.sup' Finset.univ_nonempty
      (fun a => M.backwardQ k (by omega) s a))
    (s : M.S) (a : M.A) :
    M.r ⟨M.H - k - 1, by omega⟩ s a +
    ∑ s', M.P ⟨M.H - k - 1, by omega⟩ s a s' * f s' ≤
    M.backwardQ (k + 1) hk s a := by
  -- backwardQ(k+1)(s,a) = r + ∑P max Q(k)
  -- So RHS = r + ∑P f ≤ r + ∑P max Q(k) = backwardQ(k+1)
  simp only [backwardQ]
  -- r + ∑P f ≤ r + ∑P (max Q) since f ≤ max Q pointwise
  have : ∑ s', M.P ⟨M.H - k - 1, by omega⟩ s a s' * f s' ≤
      ∑ s', M.P ⟨M.H - k - 1, by omega⟩ s a s' *
        Finset.univ.sup' Finset.univ_nonempty
          (fun a' => M.backwardQ k (by omega) s' a') := by
    apply Finset.sum_le_sum; intro s' _
    exact mul_le_mul_of_nonneg_left (hf s') (M.P_nonneg _ s a s')
  linarith

/-! ### Full Backward-Induction Optimality Statement -/

/-- Wrapper around the one-step backward-induction domination lemma.

  For any "policy value" that at each step satisfies
    V(s) = r_h(s,a) + ∑P V_next(s')
  for SOME action a, the backward induction value dominates:
    V(s) ≤ max_a Q*_k(s,a)

  This declaration is just the direct specialization of
  `backwardQ_dominates_step` to the supplied `V`. -/
theorem backwardQ_dominates_policy (M : FiniteHorizonMDP)
    (k : ℕ) (hk : k + 1 ≤ M.H)
    (V : M.S → ℝ)
    (hV : ∀ s, V s ≤ Finset.univ.sup' Finset.univ_nonempty
      (fun a => M.backwardQ k (by omega) s a))
    (s : M.S) (a : M.A) :
    M.r ⟨M.H - k - 1, by omega⟩ s a +
    ∑ s', M.P ⟨M.H - k - 1, by omega⟩ s a s' * V s' ≤
    M.backwardQ (k + 1) hk s a := by
  -- Q*_{k+1}(s,a) = r + ∑P · max Q*_k
  -- r + ∑P·V ≤ r + ∑P·max Q*_k  since V ≤ max Q*_k
  exact M.backwardQ_dominates_step k hk
    (fun s' => V s') hV s a

/-! ### Stochastic Policies and Value Functions -/

/-- A stochastic policy for a finite-horizon MDP:
    π_h(a|s) gives the probability of action a at state s at step h. -/
structure FHPolicy (M : FiniteHorizonMDP) where
  prob : Fin M.H → M.S → M.A → ℝ
  prob_nonneg : ∀ h s a, 0 ≤ prob h s a
  prob_sum_one : ∀ h s, ∑ a, prob h s a = 1

variable (M : FiniteHorizonMDP)

/-- Q-value under a fixed policy π at step h:
    Q^π_h(s,a) = r_h(s,a) + Σ_{s'} P_h(s'|s,a) V^π_{h+1}(s')

    We take Q as a parameter rather than computing it recursively,
    since the recursive definition requires the full value function. -/
def policyQValue (_π : FHPolicy M) (Q : Fin M.H → M.S → M.A → ℝ) :=
  Q

/-- **Per-step advantage difference**: the difference in Q-values
    under π evaluated at actions chosen by π vs π̄:

    δ_h(s) = Σ_a π_h(a|s)·Q^π_h(s,a) - Σ_a π̄_h(a|s)·Q^π_h(s,a)

    This is the per-step "improvement" of π over π̄ at state s. -/
def stepAdvDiff (π π_bar : FHPolicy M)
    (Q : Fin M.H → M.S → M.A → ℝ)
    (h : Fin M.H) (s : M.S) : ℝ :=
  ∑ a, π.prob h s a * Q h s a - ∑ a, π_bar.prob h s a * Q h s a

/-! ### Policy Difference U-Divergence

The **U-divergence** (Narang, Wagenmaker, Ratliff, Jamieson 2024)
measures the squared policy difference across timesteps:

  U(π, π̄) = Σ_h Σ_s w_h^π(s) · (Σ_a (π_h - π̄_h)(a|s) · Q^π_h(s,a))²

where w_h^π(s) is the state visitation probability under π at step h.

This is the second-moment analogue of the performance difference
lemma: while PDL gives V^π - V^π̄ = Σ_h E_{d^π}[advantage],
the U-divergence gives the squared version needed for policy
difference estimation.

By Cauchy-Schwarz: (V^π - V^π̄)² ≤ H · U(π, π̄).

Ref: Narang et al., "Sample Complexity Reduction via Policy
Difference Estimation," arXiv:2406.06856, Definition 1. -/

/-- **U-divergence** (policy difference complexity measure).

    U(π, π̄) = Σ_h Σ_s w_h(s) · δ_h(s)²

    where w_h is a state visitation weight and
    δ_h(s) = Σ_a (π_h - π̄_h)(a|s) · Q_h(s,a). -/
def policyDiffU (π π_bar : FHPolicy M)
    (Q : Fin M.H → M.S → M.A → ℝ)
    (w : Fin M.H → M.S → ℝ) : ℝ :=
  ∑ h, ∑ s, w h s * (stepAdvDiff M π π_bar Q h s) ^ 2

/-- **U-divergence is nonneg**: U(π, π̄) ≥ 0 when weights are nonneg. -/
theorem policyDiffU_nonneg (π π_bar : FHPolicy M)
    (Q : Fin M.H → M.S → M.A → ℝ)
    (w : Fin M.H → M.S → ℝ)
    (hw : ∀ h s, 0 ≤ w h s) :
    0 ≤ policyDiffU M π π_bar Q w := by
  apply Finset.sum_nonneg; intro h _
  apply Finset.sum_nonneg; intro s _
  exact mul_nonneg (hw h s) (sq_nonneg _)

/-- [CONDITIONAL] **Performance difference from U-divergence** (Cauchy-Schwarz).

    If the performance difference decomposes as
      V^π - V^π̄ = Σ_h Σ_s w_h(s) · δ_h(s)
    then by the weighted Cauchy-Schwarz inequality:
      (V^π - V^π̄)² ≤ W · U(π, π̄)
    where W = Σ_h Σ_s w_h(s) is the total weight.

    The Cauchy-Schwarz step is taken as hypothesis `h_cs`.
    Ref: Narang et al. 2024, proof of Theorem 1. -/
theorem performance_diff_le_U_divergence
    (π π_bar : FHPolicy M)
    (Q : Fin M.H → M.S → M.A → ℝ)
    (w : Fin M.H → M.S → ℝ)
    (_hw : ∀ h s, 0 ≤ w h s)
    (perf_diff : ℝ)
    (h_pdl : perf_diff = ∑ h, ∑ s, w h s * stepAdvDiff M π π_bar Q h s)
    (W : ℝ) (_hW : 0 < W)
    (_h_total_weight : ∑ h, ∑ s, w h s = W)
    (h_cs : (∑ h, ∑ s, w h s * stepAdvDiff M π π_bar Q h s) ^ 2 ≤
            W * ∑ h, ∑ s, w h s * (stepAdvDiff M π π_bar Q h s) ^ 2) :
    perf_diff ^ 2 ≤ W * policyDiffU M π π_bar Q w := by
  rw [h_pdl]; simp only [policyDiffU]; exact h_cs

/-- **U-divergence is zero iff policies agree on Q-weighted actions**.

    U(π, π̄) = 0 with positive weights iff for all h, s:
    Σ_a π_h(a|s)·Q_h(s,a) = Σ_a π̄_h(a|s)·Q_h(s,a). -/
theorem policyDiffU_eq_zero_iff
    (π π_bar : FHPolicy M)
    (Q : Fin M.H → M.S → M.A → ℝ)
    (w : Fin M.H → M.S → ℝ)
    (hw : ∀ h s, 0 < w h s) :
    policyDiffU M π π_bar Q w = 0 ↔
    ∀ h s, stepAdvDiff M π π_bar Q h s = 0 := by
  constructor
  · intro hU h s
    simp only [policyDiffU] at hU
    have := Finset.sum_eq_zero_iff_of_nonneg
      (fun h _ => Finset.sum_nonneg
        (fun s _ => mul_nonneg (le_of_lt (hw h s)) (sq_nonneg _)))
      |>.mp hU h (Finset.mem_univ _)
    have := Finset.sum_eq_zero_iff_of_nonneg
      (fun s _ => mul_nonneg (le_of_lt (hw h s)) (sq_nonneg _))
      |>.mp this s (Finset.mem_univ _)
    have hw_ne := ne_of_gt (hw h s)
    rcases mul_eq_zero.mp this with h1 | h2
    · exact absurd h1 hw_ne
    · exact pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp h2
  · intro h_zero
    simp only [policyDiffU]
    apply Finset.sum_eq_zero; intro h _
    apply Finset.sum_eq_zero; intro s _
    rw [h_zero h s, zero_pow (by norm_num : 2 ≠ 0), mul_zero]

end FiniteHorizonMDP

end
