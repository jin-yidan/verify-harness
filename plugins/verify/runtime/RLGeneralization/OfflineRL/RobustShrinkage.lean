/-
Copyright (c) 2026 Yidan Jin. All rights reserved.
This source code is proprietary and not licensed for public use.

# Range Shrinkage for Robust Value Functions

When using a pessimistic (robust) value function that penalizes
uncertain states, the effective range shrinks. The span
span(V) = max V - min V controls convergence in average-reward MDPs.

## Main Results

* `valueSpan_nonneg` — span(V) ≥ 0
* `valueSpan_const` — span(c) = 0
* `robustBellmanOp_le_bellmanOp` — pessimistic ≤ optimistic

## References

* [Iyengar, "Robust Dynamic Programming," Math OR 2005]
* [Panaganti and Kalathil, "Sample Complexity of Robust RL," 2022]
-/

import RLGeneralization.MDP.Basic

open Finset BigOperators

noncomputable section

variable {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]

/-! ### Span (Range) of Value Functions -/

/-- The **span** (range) of a value function:
    span(V) = max_s V(s) - min_s V(s). -/
def valueSpan (V : S → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty V -
  Finset.univ.inf' Finset.univ_nonempty V

/-- span(V) ≥ 0 always. -/
theorem valueSpan_nonneg (V : S → ℝ) : 0 ≤ valueSpan V := by
  unfold valueSpan
  obtain ⟨s₀⟩ := ‹Nonempty S›
  linarith [Finset.le_sup' V (Finset.mem_univ s₀),
            Finset.inf'_le V (Finset.mem_univ s₀)]

/-- span(c) = 0 for constant functions. -/
theorem valueSpan_const (c : ℝ) : valueSpan (fun _ : S => c) = 0 := by
  unfold valueSpan
  simp [Finset.sup'_const, Finset.inf'_const]

/-! ### Penalty Reduces Robust Value -/

/-- **Subtracting a constant preserves span**: span(V - c) = span(V). -/
theorem valueSpan_sub_const (V : S → ℝ) (c : ℝ) :
    valueSpan (fun s => V s - c) = valueSpan V := by
  unfold valueSpan
  have h_sup : Finset.univ.sup' Finset.univ_nonempty (fun s => V s - c) =
      Finset.univ.sup' Finset.univ_nonempty V - c := by
    apply le_antisymm
    · apply Finset.sup'_le; intro s _
      linarith [Finset.le_sup' V (Finset.mem_univ s)]
    · obtain ⟨s₀, _, hs₀⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty V
      rw [hs₀]
      linarith [Finset.le_sup' (fun s => V s - c) (Finset.mem_univ s₀)]
  have h_inf : Finset.univ.inf' Finset.univ_nonempty (fun s => V s - c) =
      Finset.univ.inf' Finset.univ_nonempty V - c := by
    apply le_antisymm
    · obtain ⟨s₀, _, hs₀⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty V
      rw [hs₀]
      linarith [Finset.inf'_le (fun s => V s - c) (Finset.mem_univ s₀)]
    · apply Finset.le_inf'; intro s _
      linarith [Finset.inf'_le V (Finset.mem_univ s)]
  rw [h_sup, h_inf]; ring

/-! ### Robust Bellman Operator -/

namespace FiniteMDP

variable (M : FiniteMDP)

/-- **Robust Bellman operator**: T_robust(V)(s) = max_a [r(s,a) +
    γ·E[V(s')] - penalty(s,a)]. -/
def robustBellmanOp (V : M.StateValueFn) (penalty : M.S → M.A → ℝ) :
    M.StateValueFn :=
  fun s => Finset.univ.sup' Finset.univ_nonempty
    (fun a => M.r s a + M.γ * ∑ s', M.P s a s' * V s' - penalty s a)

/-- The robust Bellman value is at most the standard Bellman value
    when penalty ≥ 0. -/
theorem robustBellmanOp_le_bellmanOp
    (V : M.StateValueFn) (penalty : M.S → M.A → ℝ)
    (h_nonneg : ∀ s a, 0 ≤ penalty s a) (s : M.S) :
    M.robustBellmanOp V penalty s ≤
    Finset.univ.sup' Finset.univ_nonempty
      (fun a => M.r s a + M.γ * ∑ s', M.P s a s' * V s') := by
  apply Finset.sup'_le
  intro a _
  calc M.r s a + M.γ * ∑ s', M.P s a s' * V s' - penalty s a
      ≤ M.r s a + M.γ * ∑ s', M.P s a s' * V s' := by linarith [h_nonneg s a]
    _ ≤ Finset.univ.sup' Finset.univ_nonempty
        (fun a => M.r s a + M.γ * ∑ s', M.P s a s' * V s') :=
      Finset.le_sup' (fun a => M.r s a + M.γ * ∑ s', M.P s a s' * V s')
        (Finset.mem_univ a)

/-- The gap between standard and robust Bellman is at most max penalty. -/
theorem bellman_robust_gap
    (V : M.StateValueFn) (penalty : M.S → M.A → ℝ)
    (pen_max : ℝ) (h_pen : ∀ s a, penalty s a ≤ pen_max) (s : M.S) :
    Finset.univ.sup' Finset.univ_nonempty
      (fun a => M.r s a + M.γ * ∑ s', M.P s a s' * V s') -
    M.robustBellmanOp V penalty s ≤ pen_max := by
  unfold robustBellmanOp
  obtain ⟨a₀, _, ha₀⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun a => M.r s a + M.γ * ∑ s', M.P s a s' * V s')
  rw [ha₀]
  calc M.r s a₀ + M.γ * ∑ s', M.P s a₀ s' * V s' -
        Finset.univ.sup' Finset.univ_nonempty
          (fun a => M.r s a + M.γ * ∑ s', M.P s a s' * V s' - penalty s a)
      ≤ M.r s a₀ + M.γ * ∑ s', M.P s a₀ s' * V s' -
        (M.r s a₀ + M.γ * ∑ s', M.P s a₀ s' * V s' - penalty s a₀) := by
        linarith [Finset.le_sup' (fun a =>
          M.r s a + M.γ * ∑ s', M.P s a s' * V s' - penalty s a)
          (Finset.mem_univ a₀)]
    _ = penalty s a₀ := by ring
    _ ≤ pen_max := h_pen s a₀

/-! ### R-Contamination Robust Bellman Theorems

The **R-contamination model**: the true transition kernel P' lies in
  U^R(P) = { (1-R)·P(·|s,a) + R·Q(·|s,a) : Q any distribution over S }
for contamination level R ∈ [0,1).

Key closed-form result: the adversary concentrates its R-fraction on argmin V,
giving  min_{P' ∈ U^R(P)} E_{P'}[V] = (1-R)·E_P[V] + R·min_s V(s).

References:
* [Iyengar, "Robust Dynamic Programming," Math OR 2005, §4.2]
* [Nilim and El Ghaoui, "Robust Control of MDPs," OR 2005]
-/

/-- **R-contamination worst-case lower bound**.

For any distribution Q (Q ≥ 0, ∑Q = 1) and contamination level R ≥ 0,
the R-contamination mixture with the infimum is a lower bound:

  (1-R)·E_P[V] + R·min V ≤ (1-R)·E_P[V] + R·E_Q[V]

This is because min V ≤ E_Q[V] for any distribution Q (the expectation
of V under a distribution is ≥ the minimum of V), and R ≥ 0 preserves
the inequality direction. Combined with the fact that equality is
achieved at the point mass on argmin V, this gives the closed form
for the worst-case R-contamination expectation. -/
theorem rContamination_worst_case
    (V : M.StateValueFn) (R : ℝ) (hR0 : 0 ≤ R)
    (s : M.S) (a : M.A)
    (Q : M.S → ℝ) (hQ_nonneg : ∀ s', 0 ≤ Q s') (hQ_sum : ∑ s', Q s' = 1) :
    (1 - R) * ∑ s', M.P s a s' * V s' +
      R * Finset.univ.inf' Finset.univ_nonempty V ≤
    (1 - R) * ∑ s', M.P s a s' * V s' + R * ∑ s', Q s' * V s' := by
  have h_min_le : Finset.univ.inf' Finset.univ_nonempty V ≤ ∑ s', Q s' * V s' := by
    have h_sum_const : ∑ s', Q s' * Finset.univ.inf' Finset.univ_nonempty V =
        Finset.univ.inf' Finset.univ_nonempty V := by
      rw [← Finset.sum_mul]; simp [hQ_sum]
    rw [← h_sum_const]
    apply Finset.sum_le_sum; intro s' _
    apply mul_le_mul_of_nonneg_left (Finset.inf'_le V (Finset.mem_univ s')) (hQ_nonneg s')
  linarith [mul_le_mul_of_nonneg_left h_min_le hR0]

/-- **R-contamination robust Bellman operator is ≤ standard Bellman**.

Define T^R(V)(s) = max_a [r(s,a) + γ·((1-R)·E_P[V] + R·min V)].
Since min V ≤ E_P[V] (expectation of V under a distribution is ≥ min V),
the robust value is pessimistic:
  T^R(V)(s) ≤ T(V)(s) = max_a [r(s,a) + γ·E_P[V]]. -/
theorem robustBellmanOp_rContamination
    (V : M.StateValueFn) (R : ℝ) (hR0 : 0 ≤ R) (hR1 : R < 1)
    (s : M.S) :
    Finset.univ.sup' Finset.univ_nonempty
      (fun a => M.r s a + M.γ *
        ((1 - R) * ∑ s', M.P s a s' * V s' +
         R * Finset.univ.inf' Finset.univ_nonempty V)) ≤
    Finset.univ.sup' Finset.univ_nonempty
      (fun a => M.r s a + M.γ * ∑ s', M.P s a s' * V s') := by
  apply Finset.sup'_le
  intro a _
  have h_min_le_exp : Finset.univ.inf' Finset.univ_nonempty V ≤
      ∑ s', M.P s a s' * V s' := by
    have h_sum_const : ∑ s' : M.S, M.P s a s' *
        Finset.univ.inf' Finset.univ_nonempty V =
        Finset.univ.inf' Finset.univ_nonempty V := by
      rw [← Finset.sum_mul]; simp [M.P_sum_one s a]
    rw [← h_sum_const]
    apply Finset.sum_le_sum; intro s' _
    apply mul_le_mul_of_nonneg_left (Finset.inf'_le V (Finset.mem_univ s'))
      (M.P_nonneg s a s')
  have h_combo : (1 - R) * ∑ s', M.P s a s' * V s' +
      R * Finset.univ.inf' Finset.univ_nonempty V ≤
      ∑ s', M.P s a s' * V s' := by
    have h1R : 0 ≤ 1 - R := by linarith
    nlinarith
  calc M.r s a + M.γ *
        ((1 - R) * ∑ s', M.P s a s' * V s' +
         R * Finset.univ.inf' Finset.univ_nonempty V)
      ≤ M.r s a + M.γ * ∑ s', M.P s a s' * V s' := by
        have := mul_le_mul_of_nonneg_left h_combo M.γ_nonneg
        linarith
    _ ≤ Finset.univ.sup' Finset.univ_nonempty
        (fun a => M.r s a + M.γ * ∑ s', M.P s a s' * V s') :=
      Finset.le_sup' (fun a' => M.r s a' + M.γ * ∑ s', M.P s a' s' * V s')
        (Finset.mem_univ a)

/-- **R-contamination range shrinkage (convex combination bound)**.

For any state and action, the robust next-state value
  (1-R)·E_P[V] + R·min V
lies in [min V, max V]. This is because it is a convex combination of
E_P[V] (which itself lies in [min V, max V]) and min V. -/
theorem rContamination_range_shrinkage
    (V : M.StateValueFn) (R : ℝ) (hR0 : 0 ≤ R) (hR1 : R < 1)
    (s : M.S) (a : M.A) :
    Finset.univ.inf' Finset.univ_nonempty V ≤
      (1 - R) * ∑ s', M.P s a s' * V s' +
       R * Finset.univ.inf' Finset.univ_nonempty V ∧
    (1 - R) * ∑ s', M.P s a s' * V s' +
       R * Finset.univ.inf' Finset.univ_nonempty V ≤
      Finset.univ.sup' Finset.univ_nonempty V := by
  set V_min := Finset.univ.inf' Finset.univ_nonempty V
  set V_max := Finset.univ.sup' Finset.univ_nonempty V
  set E_V := ∑ s', M.P s a s' * V s'
  have h1R : 0 ≤ 1 - R := by linarith
  have h_min_le_exp : V_min ≤ E_V := by
    have h_sum_const : ∑ s' : M.S, M.P s a s' * V_min = V_min := by
      rw [← Finset.sum_mul]; simp [M.P_sum_one s a]
    rw [← h_sum_const]
    apply Finset.sum_le_sum; intro s' _
    apply mul_le_mul_of_nonneg_left (Finset.inf'_le V (Finset.mem_univ s'))
      (M.P_nonneg s a s')
  have h_exp_le_max : E_V ≤ V_max := by
    have h_sum_const : ∑ s' : M.S, M.P s a s' * V_max = V_max := by
      rw [← Finset.sum_mul]; simp [M.P_sum_one s a]
    rw [← h_sum_const]
    apply Finset.sum_le_sum; intro s' _
    apply mul_le_mul_of_nonneg_left (Finset.le_sup' V (Finset.mem_univ s'))
      (M.P_nonneg s a s')
  constructor
  · -- Lower bound: V_min ≤ (1-R)·E_V + R·V_min
    nlinarith
  · -- Upper bound: (1-R)·E_V + R·V_min ≤ V_max
    nlinarith

end FiniteMDP

end
