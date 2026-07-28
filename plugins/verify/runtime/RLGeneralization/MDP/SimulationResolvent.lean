/-
# Exact Simulation Resolvent Identity

Proves the exact resolvent form of the simulation lemma:
  V^π_M(s) - V^π_M̂(s) = ∑_{s'} d̂^π(s, s') · driving(s')
where d̂^π is the discounted visitation under the approximate model.

The proof uses the same limit-uniqueness technique as pdl_occupancy_form.

## References

* [Agarwal et al., *RL: Theory and Algorithms*][agarwal2026]
-/

import RLGeneralization.Generalization.ComponentWise
import Mathlib.Analysis.SpecificLimits.Normed

open Finset BigOperators

noncomputable section

namespace FiniteMDP

variable (M : FiniteMDP)

/-! ### Approximate-Model Transition Powers

These are defined directly on M, parameterized by M_hat's kernel,
to avoid type-compatibility issues with constructing a new FiniteMDP. -/

/-- t-step transition under the approximate kernel P̂. -/
def approxTransitionPow (P_hat : M.S → M.A → M.S → ℝ)
    (π : M.StochasticPolicy) : ℕ → M.S → M.S → ℝ
  | 0 => fun s s' => if s = s' then 1 else 0
  | t + 1 => fun s s' =>
    ∑ s'', approxTransitionPow P_hat π t s s'' *
      (∑ a, π.prob s'' a * P_hat s'' a s')

/-- Approximate transition powers are nonneg. -/
lemma approxTransitionPow_nonneg
    {P_hat : M.S → M.A → M.S → ℝ}
    (hP : ∀ s a s', 0 ≤ P_hat s a s')
    (π : M.StochasticPolicy) (t : ℕ) (s s' : M.S) :
    0 ≤ approxTransitionPow M P_hat π t s s' := by
  induction t generalizing s s' with
  | zero => simp [approxTransitionPow]; split <;> norm_num
  | succ n ih =>
    simp only [approxTransitionPow]
    exact Finset.sum_nonneg fun s'' _ =>
      mul_nonneg (ih s s'')
        (Finset.sum_nonneg fun a _ => mul_nonneg (π.prob_nonneg s'' a) (hP s'' a s'))

/-- Approximate transition powers sum to 1. -/
lemma approxTransitionPow_sum_one
    {P_hat : M.S → M.A → M.S → ℝ}
    (hP_sum : ∀ s a, ∑ s', P_hat s a s' = 1)
    (π : M.StochasticPolicy) (t : ℕ) (s : M.S) :
    ∑ s', approxTransitionPow M P_hat π t s s' = 1 := by
  induction t generalizing s with
  | zero => simp [approxTransitionPow, Finset.sum_ite_eq, Finset.mem_univ]
  | succ n ih =>
    simp only [approxTransitionPow]
    -- ∑_{s'} ∑_{s''} P̂^n(s,s'') · (∑_a π(a|s'') P̂(s'|s'',a))
    -- = ∑_{s''} P̂^n(s,s'') · ∑_{s'} (∑_a π(a|s'') P̂(s'|s'',a))
    -- = ∑_{s''} P̂^n(s,s'') · 1 = 1
    trans ∑ s'', approxTransitionPow M P_hat π n s s''
    · rw [Finset.sum_comm]
      congr 1; ext s''
      rw [← Finset.mul_sum]
      conv_rhs => rw [← mul_one (approxTransitionPow M P_hat π n s s'')]
      congr 1
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, hP_sum, mul_one, π.prob_sum_one]
    · exact ih s

/-- Approximate discounted visitation. -/
noncomputable def approxDiscountedVisitation
    (P_hat : M.S → M.A → M.S → ℝ)
    (π : M.StochasticPolicy) (s₀ s' : M.S) : ℝ :=
  ∑' t, M.γ ^ t * approxTransitionPow M P_hat π t s₀ s'

/-- Summability of the approximate geometric-transition series. -/
lemma summable_approx_geometric
    {P_hat : M.S → M.A → M.S → ℝ}
    (hP : ∀ s a s', 0 ≤ P_hat s a s')
    (hP_sum : ∀ s a, ∑ s', P_hat s a s' = 1)
    (π : M.StochasticPolicy) (s₀ s' : M.S) :
    Summable (fun t => M.γ ^ t * approxTransitionPow M P_hat π t s₀ s') := by
  apply Summable.of_nonneg_of_le
  · intro t; exact mul_nonneg (pow_nonneg M.γ_nonneg t)
      (approxTransitionPow_nonneg M hP π t s₀ s')
  · intro t
    apply mul_le_of_le_one_right (pow_nonneg M.γ_nonneg t)
    calc approxTransitionPow M P_hat π t s₀ s'
        ≤ ∑ s'', approxTransitionPow M P_hat π t s₀ s'' :=
          Finset.single_le_sum
            (fun s'' _ => approxTransitionPow_nonneg M hP π t s₀ s'')
            (Finset.mem_univ s')
      _ = 1 := approxTransitionPow_sum_one M hP_sum π t s₀
  · exact summable_geometric_of_lt_one M.γ_nonneg M.γ_lt_one

/-- Finite Fubini for the approximate transition:
    ∑ P̂^n · (∑_a π P̂ W) = ∑ P̂^{n+1} · W.
    This is pure sum reordering. -/
private lemma approxTP_fubini
    (P_hat : M.S → M.A → M.S → ℝ)
    (π : M.StochasticPolicy) (n : ℕ) (s₀ : M.S) (f : M.S → ℝ) :
    ∑ s', approxTransitionPow M P_hat π n s₀ s' *
      (∑ a, π.prob s' a * ∑ s'', P_hat s' a s'' * f s'') =
    ∑ s'', approxTransitionPow M P_hat π (n + 1) s₀ s'' * f s'' := by
  change _ = ∑ s'', (∑ s', approxTransitionPow M P_hat π n s₀ s' *
    (∑ a, π.prob s' a * P_hat s' a s'')) * f s''
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  conv_lhs => arg 2; ext s'; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro s'' _
  apply Finset.sum_congr rfl; intro s' _
  apply Finset.sum_congr rfl; intro a _; ring

/-! ### Exact Simulation Resolvent Identity -/

/-- **Exact simulation identity (resolvent form).**

  V^π_M(s₀) - V^π_M̂(s₀) = ∑_{s'} d̂^π(s₀, s') · driving(s')

  where d̂^π uses the APPROXIMATE model's transitions and
  driving(s') = γ ∑_a π(a|s') ∑_{s''} (P-P̂)(s'') V_M(s'').

  The existing `simulation_lemma` (Kearns-Singh inequality) is a
  corollary: bound |driving| ≤ γ·V_max·ε_T and apply d̂ sums to
  (1-γ)⁻¹ to recover the norm bound. -/
theorem simulation_resolvent_identity (M_hat : M.ApproxMDP)
    (π : M.StochasticPolicy)
    (V_M V_Mhat : M.StateValueFn)
    (hV_M : M.isValueOf V_M π)
    (hV_Mhat : ∀ s, V_Mhat s =
      (∑ a, π.prob s a * M_hat.r_hat s a) +
      M.γ * (∑ a, π.prob s a *
        ∑ s', M_hat.P_hat s a s' * V_Mhat s'))
    (h_same_r : ∀ s a, M.r s a = M_hat.r_hat s a)
    (s₀ : M.S) :
    let driving := fun s' => ∑ a, π.prob s' a * M.γ *
      ∑ s'', (M.P s' a s'' - M_hat.P_hat s' a s'') * V_M s''
    V_M s₀ - V_Mhat s₀ =
      ∑ s', approxDiscountedVisitation M M_hat.P_hat π s₀ s' *
        driving s' := by
  intro driving
  set W := fun s => V_M s - V_Mhat s
  have h_gap := M.value_gap_resolvent M_hat π V_M V_Mhat hV_M hV_Mhat h_same_r
  set E_hat := fun (t : ℕ) (f : M.S → ℝ) (s : M.S) =>
    ∑ s', approxTransitionPow M M_hat.P_hat π t s s' * f s'
  -- Swap: ∑_t γ^t E_hat(t,f,s) = ∑_s' partial(T,s')·f(s')
  have h_swap : ∀ T, ∑ t ∈ range T, M.γ ^ t * E_hat t driving s₀ =
      ∑ s', (∑ t ∈ range T,
        M.γ ^ t * approxTransitionPow M M_hat.P_hat π t s₀ s') *
        driving s' := by
    intro T; simp only [E_hat]
    conv_lhs =>
      arg 2; ext t; rw [Finset.mul_sum]; arg 2; ext s';
      rw [show M.γ ^ t * (approxTransitionPow M M_hat.P_hat π t s₀ s' *
        driving s') = (M.γ ^ t *
        approxTransitionPow M M_hat.P_hat π t s₀ s') *
        driving s' from by ring]
    rw [Finset.sum_comm]
    congr 1; ext s'; rw [← Finset.sum_mul]
  -- Truncated identity
  have h_trunc : ∀ T, W s₀ = ∑ t ∈ range T,
      M.γ ^ t * E_hat t driving s₀ +
      M.γ ^ T * E_hat T W s₀ := by
    intro T; induction T with
    | zero =>
      simp [E_hat, approxTransitionPow, Finset.sum_ite_eq, Finset.mem_univ]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      -- Need: γ^n * E_hat(n,W) = γ^n * E_hat(n,driving) + γ^{n+1} * E_hat(n+1,W)
      -- From W = driving + γ P̂^π W, expand and distribute.
      simp only [E_hat] at *
      have h_expand : ∀ s', approxTransitionPow M M_hat.P_hat π n s₀ s' * W s' =
          approxTransitionPow M M_hat.P_hat π n s₀ s' * driving s' +
          M.γ * (approxTransitionPow M M_hat.P_hat π n s₀ s' *
            (∑ a, π.prob s' a * ∑ s'', M_hat.P_hat s' a s'' * W s'')) := by
        intro s'; rw [show W s' = driving s' + M.γ *
          (∑ a, π.prob s' a * ∑ s'', M_hat.P_hat s' a s'' * W s'') from h_gap s']; ring
      simp only [h_expand, Finset.sum_add_distrib]
      rw [← Finset.mul_sum,
          M.approxTP_fubini M_hat.P_hat π n s₀ W,
          pow_succ]
      ring
  -- Partial sum convergence
  have h_conv : ∀ s', Filter.Tendsto
      (fun T => ∑ t ∈ range T,
        M.γ ^ t * approxTransitionPow M M_hat.P_hat π t s₀ s')
      Filter.atTop
      (nhds (approxDiscountedVisitation M M_hat.P_hat π s₀ s')) :=
    fun s' => (summable_approx_geometric M M_hat.P_hat_nonneg
      M_hat.P_hat_sum_one π s₀ s').hasSum.tendsto_sum_nat
  have h_sum_conv : Filter.Tendsto
      (fun T => ∑ s', (∑ t ∈ range T,
        M.γ ^ t * approxTransitionPow M M_hat.P_hat π t s₀ s') *
        driving s')
      Filter.atTop
      (nhds (∑ s', approxDiscountedVisitation M M_hat.P_hat π s₀ s' *
        driving s')) :=
    tendsto_finset_sum _ fun s' _ => (h_conv s').mul_const _
  -- Remainder → 0
  have h_rem : Filter.Tendsto
      (fun T => M.γ ^ T * E_hat T W s₀) Filter.atTop (nhds 0) := by
    set B := univ.sup' univ_nonempty (fun s => |W s|) with hB_def
    have hB_bound : ∀ T, |M.γ ^ T * E_hat T W s₀| ≤ M.γ ^ T * B := by
      intro T
      rw [abs_mul, abs_of_nonneg (pow_nonneg M.γ_nonneg T)]
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg M.γ_nonneg T)
      calc |∑ s', approxTransitionPow M M_hat.P_hat π T s₀ s' * W s'|
          ≤ ∑ s', |approxTransitionPow M M_hat.P_hat π T s₀ s' * W s'| :=
            abs_sum_le_sum_abs _ _
        _ = ∑ s', approxTransitionPow M M_hat.P_hat π T s₀ s' * |W s'| := by
            congr 1; ext s'
            rw [abs_mul, abs_of_nonneg
              (approxTransitionPow_nonneg M M_hat.P_hat_nonneg π T s₀ s')]
        _ ≤ ∑ s', approxTransitionPow M M_hat.P_hat π T s₀ s' * B := by
            apply Finset.sum_le_sum; intro s' _
            exact mul_le_mul_of_nonneg_left
              (Finset.le_sup' (fun s => |W s|) (mem_univ s'))
              (approxTransitionPow_nonneg M M_hat.P_hat_nonneg π T s₀ s')
        _ = B := by
            rw [← Finset.sum_mul,
              approxTransitionPow_sum_one M M_hat.P_hat_sum_one π T s₀,
              one_mul]
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hγ := tendsto_pow_atTop_nhds_zero_of_lt_one M.γ_nonneg M.γ_lt_one
    have hB_nn : 0 ≤ B := le_trans (abs_nonneg _)
      (Finset.le_sup' (fun s => |W s|) (mem_univ s₀))
    obtain ⟨T₀, hT₀⟩ := Metric.tendsto_atTop.mp hγ (ε / (B + 1))
      (div_pos hε (by linarith))
    exact ⟨T₀, fun T hT => by
      rw [Real.dist_eq, sub_zero]
      specialize hT₀ T hT
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (pow_nonneg M.γ_nonneg T)] at hT₀
      calc |M.γ ^ T * E_hat T W s₀|
          ≤ M.γ ^ T * B := hB_bound T
        _ ≤ M.γ ^ T * (B + 1) := by
            apply mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg M.γ_nonneg T)
        _ < ε / (B + 1) * (B + 1) := by
            apply mul_lt_mul_of_pos_right hT₀ (by linarith)
        _ = ε := div_mul_cancel₀ ε (by linarith)⟩
  -- Limit uniqueness
  suffices h : V_M s₀ - V_Mhat s₀ =
      ∑ s', approxDiscountedVisitation M M_hat.P_hat π s₀ s' *
        driving s' from h
  set f := fun T =>
    ∑ s', (∑ t ∈ range T,
      M.γ ^ t * approxTransitionPow M M_hat.P_hat π t s₀ s') *
      driving s' + M.γ ^ T * E_hat T W s₀
  have hf1 : Filter.Tendsto f Filter.atTop (nhds (W s₀)) :=
    Filter.Tendsto.congr (fun T => by simp only [f]; rw [← h_swap]; exact h_trunc T)
      tendsto_const_nhds
  have hf2 : Filter.Tendsto f Filter.atTop
      (nhds (∑ s', approxDiscountedVisitation M M_hat.P_hat π s₀ s' *
        driving s')) := by
    simp only [f]; simpa [add_zero] using
      Filter.Tendsto.add h_sum_conv h_rem
  exact tendsto_nhds_unique hf1 hf2

/-! ### Q-Function Level Resolvent Identity -/

/-- **Q-function resolvent decomposition.**

  Q*(s,a) - Q̂*(s,a) = γ ∑_{s'} (P - P̂)(s'|s,a) · V*(s')
                     + γ ∑_{s'} P̂(s'|s,a) · (V* - V̂*)(s')

  The first term is the direct one-step transition error at (s,a).
  The second term is the propagated value error through P̂.
  Combined with `simulation_resolvent_identity` for V*-V̂*, this gives
  the corresponding Q-level resolvent comparison formula. -/
theorem q_gap_decomposition (M_hat : M.ApproxMDP)
    (Q_star : M.ActionValueFn) (V_star : M.StateValueFn)
    (Q_hat_star : M.ActionValueFn) (V_hat_star : M.StateValueFn)
    -- Q* satisfies Bellman in M
    (hQ : ∀ s a, Q_star s a =
      M.r s a + M.γ * ∑ s', M.P s a s' * V_star s')
    -- Q̂* satisfies Bellman in M̂
    (hQ_hat : ∀ s a, Q_hat_star s a =
      M_hat.r_hat s a + M.γ * ∑ s', M_hat.P_hat s a s' * V_hat_star s')
    -- Same rewards
    (h_same_r : ∀ s a, M.r s a = M_hat.r_hat s a)
    (s : M.S) (a : M.A) :
    Q_star s a - Q_hat_star s a =
      M.γ * ∑ s', (M.P s a s' - M_hat.P_hat s a s') * V_star s' +
      M.γ * ∑ s', M_hat.P_hat s a s' * (V_star s' - V_hat_star s') := by
  rw [hQ s a, hQ_hat s a, h_same_r s a]
  -- r̂ + γ∑PV* - (r̂ + γ∑P̂V̂*) = γ∑(P-P̂)V* + γ∑P̂(V*-V̂*)
  have h_split : ∀ s', M.P s a s' * V_star s' - M_hat.P_hat s a s' * V_hat_star s' =
      (M.P s a s' - M_hat.P_hat s a s') * V_star s' +
      M_hat.P_hat s a s' * (V_star s' - V_hat_star s') := fun _ => by ring
  simp only [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib, ← mul_sub]
  simp_rw [h_split, Finset.sum_add_distrib]
  ring

end FiniteMDP

end
