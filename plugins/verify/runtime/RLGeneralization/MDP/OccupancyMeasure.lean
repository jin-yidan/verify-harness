/-
# Occupancy Measure and Performance-Difference Lemma

Defines truncated and infinite-horizon state-visitation weights via
transition-matrix powers. Proves the truncated performance-difference
identity, remainder vanishing, and the exact infinite-horizon
occupancy-measure form of the Kakade-Langford PDL.

## Main Definitions

* `truncatedOccupancy` - Truncated occupancy: (1-γ)∑_{t=0}^{T-1} γ^t (P^π)^t
* `expectedReturn` - Truncated expected return: ∑_{t=0}^{T-1} γ^t r^π(s_t)
* `discountedVisitation` - Unnormalized occupancy: ∑_{t≥0} γ^t (P^π)^t(s₀,s),
  sums to 1/(1-γ) over states.
* `stateOccupancy` - Normalized occupancy: (1-γ) · discountedVisitation,
  a proper distribution over states (sums to 1).

## Main Results

* `truncated_pdl` - Truncated PDL: exact telescoping identity for
  finite-horizon prefix, with a γ^T remainder term.
* `pdl_remainder_vanishes` - The γ^T remainder vanishes as T → ∞.
* `pdl_occupancy_form` - Kakade-Langford PDL (unnormalized occupancy):
  V^π - V^{π'} = ∑_s d_unnorm(s) · E_π[A^{π'}(s)].
* `pdl_normalized` - Kakade-Langford PDL (normalized form):
  V^π - V^{π'} = (1/(1-γ)) · ∑_s d^π(s) · E_π[A^{π'}(s)].

## References

* [Agarwal et al., *RL: Theory and Algorithms*]
-/

import RLGeneralization.MDP.PerformanceDifference
import Mathlib.Analysis.SpecificLimits.Normed

open Finset BigOperators

noncomputable section

namespace FiniteMDP

variable (M : FiniteMDP)

/-! ### Transition Matrix Powers -/

/-- The t-step transition probability under policy π:
    (P^π)^t(s, s') = probability of reaching s' from s in t steps. -/
def transitionPow : M.StochasticPolicy → ℕ → M.S → M.S → ℝ
  | _, 0 => fun s s' => if s = s' then 1 else 0
  | π, t + 1 => fun s s' =>
    ∑ s'', transitionPow π t s s'' *
      (∑ a, π.prob s'' a * M.P s'' a s')

/-- transitionPow 0 is the identity. -/
@[simp]
theorem transitionPow_zero (π : M.StochasticPolicy) (s s' : M.S) :
    M.transitionPow π 0 s s' = if s = s' then 1 else 0 := rfl

/-- transitionPow sums to 1 (it's a stochastic matrix). -/
theorem transitionPow_sum_one (π : M.StochasticPolicy)
    (t : ℕ) (s : M.S) :
    ∑ s', M.transitionPow π t s s' = 1 := by
  induction t with
  | zero =>
    simp only [transitionPow]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  | succ n ih =>
    simp only [transitionPow]
    -- ∑_{s'} ∑_{s''} P^n(s,s'') ∑_a π(a|s'') P(s'|s'',a)
    -- = ∑_{s''} P^n(s,s'') ∑_a π(a|s'') ∑_{s'} P(s'|s'',a)
    -- = ∑_{s''} P^n(s,s'') ∑_a π(a|s'') · 1  = ∑_{s''} P^n(s,s'') = 1
    -- Swap sums: ∑_{s'} ∑_{s''} f(s'',s') = ∑_{s''} ∑_{s'} f(s'',s')
    rw [Finset.sum_comm]
    -- Now: ∑_{s''} ∑_{s'} P^n(s,s'') * (∑_a π(a|s'') * P(s'|s'',a))
    -- Factor P^n out of inner sum
    simp_rw [← Finset.mul_sum]
    -- ∑_{s''} P^n(s,s'') * ∑_{s'} (∑_a π(a|s'') * P(s'|s'',a))
    -- Inner sum: ∑_{s'} ∑_a π(a) P(s'|s'',a) = ∑_a π(a) ∑_{s'} P(s'|s'',a)
    --          = ∑_a π(a) * 1 = 1
    have hinner : ∀ s'',
        ∑ s', ∑ a, π.prob s'' a * M.P s'' a s' = 1 := by
      intro s''
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, M.P_sum_one, mul_one,
        π.prob_sum_one]
    simp_rw [hinner, mul_one]
    exact ih

/-- transitionPow has nonneg entries. -/
theorem transitionPow_nonneg (π : M.StochasticPolicy)
    (t : ℕ) : ∀ s s', 0 ≤ M.transitionPow π t s s' := by
  induction t with
  | zero => intro s s'; simp only [transitionPow]; split_ifs <;> norm_num
  | succ n ih =>
    intro s s'
    simp only [transitionPow]
    apply Finset.sum_nonneg; intro s'' _
    exact mul_nonneg (ih s s'')
      (Finset.sum_nonneg fun a _ =>
        mul_nonneg (π.prob_nonneg s'' a) (M.P_nonneg s'' a s'))

/-! ### Truncated Occupancy Measure -/

/-- Truncated discounted occupancy measure (T steps):
    d^π_{T,s₀}(s) = (1-γ) ∑_{t=0}^{T-1} γ^t (P^π)^t(s₀, s)
    As T → ∞, this converges to the true occupancy measure. -/
def truncatedOccupancy (π : M.StochasticPolicy)
    (T : ℕ) (s₀ s : M.S) : ℝ :=
  (1 - M.γ) * ∑ t ∈ range T,
    M.γ ^ t * M.transitionPow π t s₀ s

/-- Truncated occupancy is nonneg. -/
theorem truncatedOccupancy_nonneg (π : M.StochasticPolicy)
    (T : ℕ) (s₀ s : M.S) :
    0 ≤ M.truncatedOccupancy π T s₀ s := by
  unfold truncatedOccupancy
  apply mul_nonneg (by linarith [M.γ_lt_one])
  apply Finset.sum_nonneg; intro t _
  exact mul_nonneg (pow_nonneg M.γ_nonneg t)
    (M.transitionPow_nonneg π t s₀ s)

/-! ### Expected Value under Transition Powers -/

/-- Expected value of f after t steps under policy π from state s₀:
    ∑_{s'} (P^π)^t(s₀, s') * f(s') -/
def expectedUnderPow (π : M.StochasticPolicy)
    (t : ℕ) (f : M.S → ℝ) (s₀ : M.S) : ℝ :=
  ∑ s', M.transitionPow π t s₀ s' * f s'

/-- Expected value at step 0 is just f(s₀). -/
theorem expectedUnderPow_zero (π : M.StochasticPolicy)
    (f : M.S → ℝ) (s₀ : M.S) :
    M.expectedUnderPow π 0 f s₀ = f s₀ := by
  simp [expectedUnderPow, transitionPow, Finset.sum_ite_eq,
    Finset.mem_univ]

/-- One-step recursion: E_{(P^π)^{t+1}}[f] = E_{(P^π)^t}[P^π f]. -/
theorem expectedUnderPow_succ (π : M.StochasticPolicy)
    (t : ℕ) (f : M.S → ℝ) (s₀ : M.S) :
    M.expectedUnderPow π (t + 1) f s₀ =
    M.expectedUnderPow π t
      (fun s => M.expectedNextValue π f s) s₀ := by
  simp only [expectedUnderPow, expectedNextValue, transitionPow]
  -- Goal: ∑_{s'} (∑_{s''} P^t(s₀,s'') · ∑_a π P(s'|s'',a)) · f(s')
  --     = ∑_{s''} P^t(s₀,s'') · (∑_a π(a|s'') · ∑_{s'} P(s'|s'',a) · f(s'))
  -- Distribute f into the inner sum
  simp_rw [Finset.sum_mul]
  -- Now each term is P^t · (∑_a π P) · f = P^t · ∑_a π · P · f
  rw [Finset.sum_comm]
  congr 1; funext s''
  -- Factor P^t out and rearrange sums
  have hfact : ∀ s'',
      ∑ s', (M.transitionPow π t s₀ s'' *
        ∑ a, π.prob s'' a * M.P s'' a s') * f s' =
      M.transitionPow π t s₀ s'' *
        (∑ a, π.prob s'' a *
          ∑ s', M.P s'' a s' * f s') := by
    intro s''
    have : ∀ s', (M.transitionPow π t s₀ s'' *
        ∑ a, π.prob s'' a * M.P s'' a s') * f s' =
        M.transitionPow π t s₀ s'' *
          ((∑ a, π.prob s'' a * M.P s'' a s') * f s') :=
      fun s' => by ring
    simp_rw [this, ← Finset.mul_sum]
    congr 1
    -- ∑_{s'} (∑_a π P(s')) · f(s') = ∑_a π · ∑_{s'} P(s') · f(s')
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    congr 1; funext a
    have : ∀ x, π.prob s'' a * M.P s'' a x * f x =
        π.prob s'' a * (M.P s'' a x * f x) := fun x => by ring
    simp_rw [this, ← Finset.mul_sum]
  simp_rw [hfact]

/-! ### Truncated Performance Difference Lemma -/

/-- **Truncated performance-difference identity**.

  For policies π, π' with value functions V^π, V^{π'} and
  action-value Q^{π'}, the truncated identity:

    V^π(s₀) - V^{π'}(s₀) =
      ∑_{t=0}^{T-1} γ^t · E_{(P^π)^t(s₀)}[E_π[A^{π'}]]
      + γ^T · E_{(P^π)^T(s₀)}[V^π - V^{π'}]

  As T -> infinity, the remainder γ^T term vanishes (see
  `pdl_remainder_vanishes`), recovering the infinite-horizon identity.

  **Caveat**: This is expressed using `expectedUnderPow`
  (transition-power weighted expectations), NOT an explicit
  occupancy-measure object d^π. The full occupancy-measure form
  would require packaging d^π
  as a proper distribution. -/
theorem truncated_pdl
    (π π' : M.StochasticPolicy)
    (V_pi V_pi' : M.StateValueFn)
    (Q_pi' : M.ActionValueFn)
    (hV_pi : M.isValueOf V_pi π)
    (_hV_pi' : M.isValueOf V_pi' π')
    (hQ_pi' : ∀ s a, Q_pi' s a =
      M.r s a + M.γ * ∑ s', M.P s a s' * V_pi' s')
    (T : ℕ) (s₀ : M.S) :
    V_pi s₀ - V_pi' s₀ =
      ∑ t ∈ range T, M.γ ^ t *
        M.expectedUnderPow π t
          (M.expectedAdvantage π Q_pi' V_pi') s₀ +
      M.γ ^ T * M.expectedUnderPow π T
        (fun s => V_pi s - V_pi' s) s₀ := by
  -- Proof by induction on T (telescoping)
  induction T with
  | zero =>
    simp [expectedUnderPow_zero]
  | succ n ih =>
    -- Split the sum: ∑_{t=0}^n = ∑_{t=0}^{n-1} + term at n
    rw [Finset.sum_range_succ]
    rw [ih]
    -- Need: γ^n E_n[W] = γ^n E_n[adv] + γ^{n+1} E_{n+1}[W]
    -- where W = V^π - V^{π'}, adv = expectedAdvantage
    -- Key: E_n[W] = E_n[adv] + γ E_{n+1}[W]
    -- from pdl_one_step + expectedUnderPow_succ
    -- Abbreviations for readability (let, not set, to avoid unfolding issues)
    let W := fun s => V_pi s - V_pi' s
    let adv := M.expectedAdvantage π Q_pi' V_pi'
    -- E_n[W] = E_n[adv + γP^πW] (by pdl_one_step pointwise)
    --        = E_n[adv] + γ E_n[P^πW] (linearity)
    --        = E_n[adv] + γ E_{n+1}[W] (by expectedUnderPow_succ)
    have hpdl := M.pdl_one_step π π' V_pi V_pi' Q_pi'
      hV_pi _hV_pi' hQ_pi'
    -- E_n[W] splits by linearity
    have hlin : M.expectedUnderPow π n W s₀ =
        M.expectedUnderPow π n adv s₀ +
        M.γ * M.expectedUnderPow π n
          (M.expectedNextValue π W) s₀ := by
      simp only [expectedUnderPow]
      -- W(s') = adv(s') + γ·nextValue(W)(s') by pdl_one_step
      -- So P^n · W = P^n · adv + P^n · γ·nextValue(W)
      have hsplit : ∀ s',
          M.transitionPow π n s₀ s' * W s' =
          M.transitionPow π n s₀ s' * adv s' +
          M.γ * (M.transitionPow π n s₀ s' *
            M.expectedNextValue π W s') := by
        intro s'
        have hpdl_s := hpdl s'
        -- P^n · W = P^n · (adv + γ nextV W) = P^n · adv + γ P^n · nextV W
        rw [show W s' = adv s' + M.γ *
            M.expectedNextValue π W s' from hpdl_s]; ring
      simp_rw [hsplit, Finset.sum_add_distrib, ← Finset.mul_sum]
    -- E_n[P^πW] = E_{n+1}[W]
    have hsucc :
        M.expectedUnderPow π n (M.expectedNextValue π W) s₀ =
        M.expectedUnderPow π (n + 1) W s₀ :=
      (M.expectedUnderPow_succ π n W s₀).symm
    -- Combine: γ^n E_n[W] = γ^n E_n[adv] + γ^{n+1} E_{n+1}[W]
    -- γ^n · E_n[W] = γ^n · (E_n[adv] + γ E_{n+1}[W])
    --              = γ^n E_n[adv] + γ^{n+1} E_{n+1}[W]
    have h1 : M.γ ^ n * M.expectedUnderPow π n W s₀ =
        M.γ ^ n * M.expectedUnderPow π n adv s₀ +
        M.γ ^ (n + 1) * M.expectedUnderPow π (n + 1) W s₀ := by
      rw [hlin, hsucc, pow_succ]; ring
    linarith

/-! ### Toward the Exact Infinite-Horizon PDL -/

/-- **Remainder bound for truncated PDL**.
  The remainder γ^T · E_T[V^π-V^{π'}] is bounded by
  γ^T · 2·V_max, which → 0 as T → ∞. -/
theorem truncated_pdl_remainder_bound
    (π π' : M.StochasticPolicy)
    (V_pi V_pi' : M.StateValueFn)
    (Q_pi' : M.ActionValueFn)
    (hV_pi : M.isValueOf V_pi π)
    (hV_pi' : M.isValueOf V_pi' π')
    (_hQ_pi' : ∀ s a, Q_pi' s a =
      M.r s a + M.γ * ∑ s', M.P s a s' * V_pi' s')
    (T : ℕ) (s₀ : M.S) :
    |M.γ ^ T * M.expectedUnderPow π T
      (fun s => V_pi s - V_pi' s) s₀| ≤
    M.γ ^ T * (2 * M.V_max) := by
  rw [abs_mul, abs_of_nonneg (pow_nonneg M.γ_nonneg T)]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg M.γ_nonneg T)
  -- |E_T[V^π - V^{π'}]| ≤ 2·V_max
  unfold expectedUnderPow
  apply abs_weighted_sum_le_bound _ _ (2 * M.V_max)
    (M.transitionPow_nonneg π T s₀)
    (M.transitionPow_sum_one π T s₀)
  intro s'
  -- |V^π(s') - V^{π'}(s')| ≤ |V^π(s')| + |V^{π'}(s')| ≤ 2V_max
  calc |V_pi s' - V_pi' s'|
      ≤ |V_pi s'| + |V_pi' s'| := by
        have h1 : V_pi s' - V_pi' s' = V_pi s' + -V_pi' s' := sub_eq_add_neg _ _
        rw [h1]; exact (abs_add_le _ _).trans (by rw [abs_neg])
    _ ≤ M.V_max + M.V_max := by
        apply add_le_add
        · exact M.value_bounded_by_Vmax V_pi π hV_pi s'
        · exact M.value_bounded_by_Vmax V_pi' π' hV_pi' s'
    _ = 2 * M.V_max := by ring

/-- **Remainder vanishing for the truncated performance-difference identity**.

  The remainder term γ^T · E_{(P^π)^T(s₀)}[V^π - V^{π'}]
  from `truncated_pdl` tends to zero as T → ∞.

  Formally: for any ε > 0, there exists T₀ such that for
  T ≥ T₀, |γ^T · E_T[V^π - V^{π'}]| < ε.

  This is the convergence ingredient; the actual limit identity
  is packaged as `exact_pdl_limit` below. -/
theorem pdl_remainder_vanishes
    (π π' : M.StochasticPolicy)
    (V_pi V_pi' : M.StateValueFn)
    (Q_pi' : M.ActionValueFn)
    (hV_pi : M.isValueOf V_pi π)
    (hV_pi' : M.isValueOf V_pi' π')
    (hQ_pi' : ∀ s a, Q_pi' s a =
      M.r s a + M.γ * ∑ s', M.P s a s' * V_pi' s')
    (s₀ : M.S) (ε : ℝ) (hε : 0 < ε) :
    ∃ T₀ : ℕ, ∀ T, T₀ ≤ T →
      |M.γ ^ T * M.expectedUnderPow π T
        (fun s => V_pi s - V_pi' s) s₀| < ε := by
  -- γ^T · 2V_max → 0 since γ < 1
  -- Choose T₀ such that γ^T₀ · 2V_max < ε
  -- γ^T · 2V_max → 0 since γ^T → 0 (γ < 1)
  -- Use remainder bound + geometric convergence
  have h_rem := M.truncated_pdl_remainder_bound π π' V_pi V_pi'
    Q_pi' hV_pi hV_pi' hQ_pi'
  -- γ^T → 0
  have hγ_abs : |M.γ| < 1 := by
    rw [abs_of_nonneg M.γ_nonneg]; exact M.γ_lt_one
  have hγ_tend := tendsto_pow_atTop_nhds_zero_of_abs_lt_one hγ_abs
  have hε' : 0 < ε / (2 * M.V_max + 1) :=
    div_pos hε (by linarith [M.V_max_pos])
  rw [Metric.tendsto_atTop] at hγ_tend
  obtain ⟨T₀, hT₀⟩ := hγ_tend (ε / (2 * M.V_max + 1)) hε'
  use T₀
  intro T hT
  calc |M.γ ^ T * M.expectedUnderPow π T
        (fun s => V_pi s - V_pi' s) s₀|
      ≤ M.γ ^ T * (2 * M.V_max) := h_rem T s₀
    _ < ε := by
        have hγT := hT₀ T hT
        simp only [Real.dist_eq, sub_zero,
          abs_of_nonneg (pow_nonneg M.γ_nonneg T)] at hγT
        -- hγT : M.γ ^ T < ε / (2 * V_max + 1)
        -- Goal: M.γ ^ T * (2 * V_max) < ε
        have hV := M.V_max_pos
        have h2V1 : (0 : ℝ) < 2 * M.V_max + 1 := by linarith
        -- γ^T < ε/(2V+1), so γ^T·(2V+1) < ε
        have := (lt_div_iff₀ h2V1).mp hγT
        -- γ^T·(2V) ≤ γ^T·(2V+1) < ε
        linarith [mul_nonneg (pow_nonneg M.γ_nonneg T) (by linarith : (0:ℝ) ≤ 1)]

/-- **Performance-difference identity, limit form**.

  V^π(s₀) - V^{π'}(s₀) = lim_{T→∞} ∑_{t=0}^{T-1} γ^t E_t[A^{π'}(s_t, a_t)]

  This follows from `truncated_pdl` (the truncated identity)
  and `pdl_remainder_vanishes` (the remainder → 0).

  Formally: for any ε > 0, there exists T₀ such that for T ≥ T₀,
  |V^π(s₀) - V^{π'}(s₀) - ∑_{t<T} γ^t E_t[adv(s₀)]| < ε. -/
theorem exact_pdl_limit
    (π π' : M.StochasticPolicy)
    (V_pi V_pi' : M.StateValueFn)
    (Q_pi' : M.ActionValueFn)
    (hV_pi : M.isValueOf V_pi π)
    (hV_pi' : M.isValueOf V_pi' π')
    (hQ_pi' : ∀ s a, Q_pi' s a =
      M.r s a + M.γ * ∑ s', M.P s a s' * V_pi' s')
    (s₀ : M.S) (ε : ℝ) (hε : 0 < ε) :
    ∃ T₀ : ℕ, ∀ T, T₀ ≤ T →
      |V_pi s₀ - V_pi' s₀ -
        ∑ t ∈ range T, M.γ ^ t *
          M.expectedUnderPow π t
            (M.expectedAdvantage π Q_pi' V_pi') s₀| < ε := by
  -- From pdl_remainder_vanishes, the remainder → 0
  obtain ⟨T₀, hT₀⟩ := M.pdl_remainder_vanishes π π' V_pi V_pi'
    Q_pi' hV_pi hV_pi' hQ_pi' s₀ ε hε
  exact ⟨T₀, fun T hT => by
    -- From truncated_pdl, the difference equals the remainder
    have hpdl := M.truncated_pdl π π' V_pi V_pi' Q_pi'
      hV_pi hV_pi' hQ_pi' T s₀
    -- V_pi s₀ - V_pi' s₀ - ∑ = γ^T · E_T[W]
    have heq : V_pi s₀ - V_pi' s₀ -
        ∑ t ∈ range T, M.γ ^ t *
          M.expectedUnderPow π t
            (M.expectedAdvantage π Q_pi' V_pi') s₀ =
        M.γ ^ T * M.expectedUnderPow π T
          (fun s => V_pi s - V_pi' s) s₀ := by linarith
    rw [heq]
    exact hT₀ T hT⟩

/-! ### Infinite-Horizon Occupancy Measure -/

/-- Each transition-power entry is bounded by 1 (since the row sums to 1
    and entries are nonneg). -/
lemma transitionPow_le_one (π : M.StochasticPolicy) (t : ℕ)
    (s₀ s : M.S) : M.transitionPow π t s₀ s ≤ 1 := by
  calc M.transitionPow π t s₀ s
      ≤ ∑ s', M.transitionPow π t s₀ s' :=
        Finset.single_le_sum (f := fun s' => M.transitionPow π t s₀ s')
          (fun s' _ => M.transitionPow_nonneg π t s₀ s') (Finset.mem_univ s)
    _ = 1 := M.transitionPow_sum_one π t s₀

/-- The geometric-transition series is summable for each fixed (s₀, s). -/
lemma summable_geometric_transitionPow (π : M.StochasticPolicy)
    (s₀ s : M.S) :
    Summable (fun t => M.γ ^ t * M.transitionPow π t s₀ s) := by
  apply Summable.of_nonneg_of_le
  · intro t; exact mul_nonneg (pow_nonneg M.γ_nonneg t)
      (M.transitionPow_nonneg π t s₀ s)
  · intro t; exact mul_le_of_le_one_right (pow_nonneg M.γ_nonneg t)
      (M.transitionPow_le_one π t s₀ s)
  · exact summable_geometric_of_lt_one M.γ_nonneg M.γ_lt_one

/-- **Discounted state-visitation weight** (unnormalized occupancy):
    `d(s₀, s) = ∑_{t=0}^∞ γ^t · P(s_t = s | π, s₀)`.
    Sums to `1/(1-γ)` over the state space.

    The normalized occupancy measure is `(1-γ) · discountedVisitation`. -/
noncomputable def discountedVisitation (π : M.StochasticPolicy)
    (s₀ s : M.S) : ℝ :=
  ∑' t, M.γ ^ t * M.transitionPow π t s₀ s

/-- Discounted visitation is nonneg. -/
lemma discountedVisitation_nonneg (π : M.StochasticPolicy)
    (s₀ s : M.S) : 0 ≤ M.discountedVisitation π s₀ s :=
  tsum_nonneg fun t => mul_nonneg (pow_nonneg M.γ_nonneg t)
    (M.transitionPow_nonneg π t s₀ s)

/-- **The discounted visitation weights sum to `1/(1-γ)` over states.** -/
theorem discountedVisitation_sum (π : M.StochasticPolicy) (s₀ : M.S) :
    ∑ s, M.discountedVisitation π s₀ s = (1 - M.γ)⁻¹ := by
  simp only [discountedVisitation]
  -- Swap finite sum over states and tsum over time:
  --   ∑_s ∑'_t f(t,s) = ∑'_t ∑_s f(t,s)
  rw [(Summable.tsum_finsetSum
    (fun s _ => M.summable_geometric_transitionPow π s₀ s)).symm]
  -- ∑_s γ^t * P^t(s₀,s) = γ^t * ∑_s P^t(s₀,s) = γ^t
  have h_simp : ∀ t, ∑ s, M.γ ^ t * M.transitionPow π t s₀ s =
      M.γ ^ t := by
    intro t
    rw [← Finset.mul_sum]
    simp [M.transitionPow_sum_one π t s₀]
  simp_rw [h_simp]
  exact tsum_geometric_of_lt_one M.γ_nonneg M.γ_lt_one

/-- The normalized occupancy measure `(1-γ) · discountedVisitation` sums to 1. -/
theorem occupancyMeasure_sum_one (π : M.StochasticPolicy) (s₀ : M.S) :
    (1 - M.γ) * ∑ s, M.discountedVisitation π s₀ s = 1 := by
  rw [M.discountedVisitation_sum π s₀]
  exact mul_inv_cancel₀ (ne_of_gt (sub_pos.mpr M.γ_lt_one))

/-! ### Normalized Occupancy Definitions

We use the **normalized**
discounted state-visitation distribution:
  `d^π_{s₀}(s) := (1-γ) ∑_{t≥0} γ^t Pr(s_t = s | s₀, π)`
which sums to 1 over states, and the state-action occupancy:
  `d^π_{s₀}(s, a) := d^π_{s₀}(s) · π(a|s)`
The corresponding PDL is then:
`V^π - V^π' = (1/(1-γ)) E_{(s,a)~d^π}[A^π'(s,a)]`. -/

/-- **Normalized discounted state-visitation distribution**.
    `d^π_{s₀}(s) = (1-γ) ∑_{t≥0} γ^t Pr(s_t = s | s₀, π)`.
    Sums to 1 over states (`occupancyMeasure_sum_one`). -/
noncomputable def stateOccupancy (π : M.StochasticPolicy)
    (s₀ s : M.S) : ℝ :=
  (1 - M.γ) * M.discountedVisitation π s₀ s

-- [UNUSED]
/-- **State-action occupancy measure**.
    `d^π_{s₀}(s, a) = d^π_{s₀}(s) · π(a|s)`. -/
noncomputable def stateActionOccupancy (π : M.StochasticPolicy)
    (s₀ : M.S) (s : M.S) (a : M.A) : ℝ :=
  M.stateOccupancy π s₀ s * π.prob s a

/-- The normalized state occupancy sums to 1 over states. -/
theorem stateOccupancy_sum_one (π : M.StochasticPolicy) (s₀ : M.S) :
    ∑ s, M.stateOccupancy π s₀ s = 1 := by
  simp only [stateOccupancy, ← Finset.mul_sum]
  exact M.occupancyMeasure_sum_one π s₀

/-- The state occupancy is nonneg. -/
lemma stateOccupancy_nonneg (π : M.StochasticPolicy) (s₀ s : M.S) :
    0 ≤ M.stateOccupancy π s₀ s :=
  mul_nonneg (sub_pos.mpr M.γ_lt_one).le (M.discountedVisitation_nonneg π s₀ s)

/-! ### Performance-Difference Lemma -/

/-- **Kakade-Langford PDL (unnormalized occupancy form)**.

  V^π(s₀) - V^{π'}(s₀) = ∑_s d_unnorm(s₀, s) · E_π[A^{π'}(s)]

  where `d_unnorm = discountedVisitation = ∑_{t≥0} γ^t P^t(s₀, s)` is the
  unnormalized state-visitation weight (sums to `(1-γ)⁻¹`). -/
theorem pdl_occupancy_form
    (π π' : M.StochasticPolicy)
    (V_pi V_pi' : M.StateValueFn)
    (Q_pi' : M.ActionValueFn)
    (hV_pi : M.isValueOf V_pi π)
    (hV_pi' : M.isValueOf V_pi' π')
    (hQ_pi' : ∀ s a, Q_pi' s a =
      M.r s a + M.γ * ∑ s', M.P s a s' * V_pi' s')
    (s₀ : M.S) :
    V_pi s₀ - V_pi' s₀ =
      ∑ s, M.discountedVisitation π s₀ s *
        M.expectedAdvantage π Q_pi' V_pi' s := by
  set adv := M.expectedAdvantage π Q_pi' V_pi'
  -- Prove directly using limit uniqueness
  suffices h : V_pi s₀ - V_pi' s₀ =
      ∑ s, M.discountedVisitation π s₀ s * adv s by
    exact h
  -- Swap finite sums: ∑_t γ^t E_t[adv](s₀) = ∑_s (∑_t γ^t P^t(s₀,s)) · adv(s)
  have h_swap : ∀ T, ∑ t ∈ range T, M.γ ^ t *
      M.expectedUnderPow π t adv s₀ =
      ∑ s, (∑ t ∈ range T, M.γ ^ t *
        M.transitionPow π t s₀ s) * adv s := by
    intro T; simp only [expectedUnderPow]
    -- Convert both sides to ∑_t ∑_s γ^t * P^t(s₀,s) * adv(s)
    conv_lhs =>
      arg 2; ext t; rw [Finset.mul_sum]; arg 2; ext s; rw [show
        M.γ ^ t * (M.transitionPow π t s₀ s * adv s) =
        M.γ ^ t * M.transitionPow π t s₀ s * adv s from by ring]
    conv_rhs =>
      arg 2; ext s; rw [Finset.sum_mul]
    exact Finset.sum_comm
  -- Proof via limits: partial sums → tsum and remainder → 0.
  -- partial(T,s) = ∑_{t<T} γ^t P^t(s₀,s) → discountedVisitation π s₀ s  [HasSum]
  -- ∑_s partial(T,s)·adv(s) → ∑_s d(s)·adv(s)  [tendsto_finset_sum]
  -- V-V' = ∑_s partial(T,s)·adv(s) + γ^T·rem(T)  [truncated_pdl + h_swap]
  -- γ^T·rem(T) → 0  [pdl_remainder_vanishes]
  -- So V-V' = ∑_s d(s)·adv(s) + 0, giving c = 0.
  -- Formally: two sequences summing to V-V', one converges to ∑d·adv, other to 0.
  have h_conv_partial : ∀ s, Filter.Tendsto
      (fun T => ∑ t ∈ range T, M.γ ^ t * M.transitionPow π t s₀ s)
      Filter.atTop (nhds (M.discountedVisitation π s₀ s)) :=
    fun s => (M.summable_geometric_transitionPow π s₀ s).hasSum.tendsto_sum_nat
  -- ∑_s partial(T,s)*adv(s) → ∑_s d(s)*adv(s)
  have h_sum_conv : Filter.Tendsto
      (fun T => ∑ s, (∑ t ∈ range T,
        M.γ ^ t * M.transitionPow π t s₀ s) * adv s)
      Filter.atTop
      (nhds (∑ s, M.discountedVisitation π s₀ s * adv s)) :=
    tendsto_finset_sum _ fun s _ => (h_conv_partial s).mul_const _
  -- γ^T·rem(T) → 0
  have h_rem_conv : Filter.Tendsto
      (fun T => M.γ ^ T * M.expectedUnderPow π T
        (fun s => V_pi s - V_pi' s) s₀)
      Filter.atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨T₀, hT₀⟩ := M.pdl_remainder_vanishes π π' V_pi V_pi'
      Q_pi' hV_pi hV_pi' hQ_pi' s₀ ε hε
    exact ⟨T₀, fun T hT => by
      rw [Real.dist_eq, sub_zero]; exact hT₀ T hT⟩
  -- V-V' = partial_sum(T) + γ^T·rem(T) for all T (from truncated_pdl + h_swap)
  have h_decomp : ∀ T, V_pi s₀ - V_pi' s₀ =
      ∑ s, (∑ t ∈ range T,
        M.γ ^ t * M.transitionPow π t s₀ s) * adv s +
      M.γ ^ T * M.expectedUnderPow π T
        (fun s => V_pi s - V_pi' s) s₀ := by
    intro T
    have := M.truncated_pdl π π' V_pi V_pi' Q_pi'
      hV_pi hV_pi' hQ_pi' T s₀
    rw [h_swap T] at this; linarith
  -- The sum of two convergent sequences converges to the sum of limits.
  -- ∑partial·adv + γ^T·rem → ∑d·adv + 0 = ∑d·adv
  -- But the LHS is constant = V-V' for all T.
  -- So V-V' = ∑d·adv, i.e., c = 0.
  have h_const : Filter.Tendsto
      (fun _ : ℕ => V_pi s₀ - V_pi' s₀) Filter.atTop
      (nhds (V_pi s₀ - V_pi' s₀)) := tendsto_const_nhds
  have h_limit := Filter.Tendsto.add h_sum_conv h_rem_conv
  -- h_limit: f(T) + g(T) → ∑d·adv + 0
  -- h_decomp: V-V' = f(T) + g(T) for all T
  -- h_const: V-V' → V-V'
  -- By uniqueness of limits: V-V' = ∑d·adv
  have h_limit' : Filter.Tendsto
      (fun T => ∑ s, (∑ t ∈ range T,
        M.γ ^ t * M.transitionPow π t s₀ s) * adv s +
        M.γ ^ T * M.expectedUnderPow π T
          (fun s => V_pi s - V_pi' s) s₀)
      Filter.atTop
      (nhds (∑ s, M.discountedVisitation π s₀ s * adv s)) := by
    have := Filter.Tendsto.add h_sum_conv h_rem_conv
    simp only [add_zero] at this; exact this
  -- The function f(T) = sum(T) + rem(T) converges to both V-V' and ∑d·adv.
  -- By uniqueness: V-V' = ∑d·adv.
  set f := fun T => ∑ s, (∑ t ∈ range T,
    M.γ ^ t * M.transitionPow π t s₀ s) * adv s +
    M.γ ^ T * M.expectedUnderPow π T
      (fun s => V_pi s - V_pi' s) s₀
  have hf1 : Filter.Tendsto f Filter.atTop
      (nhds (V_pi s₀ - V_pi' s₀)) :=
    Filter.Tendsto.congr (fun T => h_decomp T)
      tendsto_const_nhds
  have hf2 : Filter.Tendsto f Filter.atTop
      (nhds (∑ s, M.discountedVisitation π s₀ s * adv s)) := by
    simp only [f]; simpa [add_zero] using
      Filter.Tendsto.add h_sum_conv h_rem_conv
  exact tendsto_nhds_unique hf1 hf2

/-- **Kakade-Langford PDL (normalized form)**.

  V^π(s₀) - V^{π'}(s₀) = (1/(1-γ)) · ∑_s d^π(s₀, s) · E_π[A^{π'}(s)]

  where `d^π = stateOccupancy = (1-γ) · discountedVisitation` is the
  **normalized** discounted state-visitation distribution (sums to 1). -/
theorem pdl_normalized
    (π π' : M.StochasticPolicy)
    (V_pi V_pi' : M.StateValueFn)
    (Q_pi' : M.ActionValueFn)
    (hV_pi : M.isValueOf V_pi π)
    (hV_pi' : M.isValueOf V_pi' π')
    (hQ_pi' : ∀ s a, Q_pi' s a =
      M.r s a + M.γ * ∑ s', M.P s a s' * V_pi' s')
    (s₀ : M.S) :
    V_pi s₀ - V_pi' s₀ =
      (1 - M.γ)⁻¹ * ∑ s, M.stateOccupancy π s₀ s *
        M.expectedAdvantage π Q_pi' V_pi' s := by
  have h_pdl := M.pdl_occupancy_form π π' V_pi V_pi' Q_pi'
    hV_pi hV_pi' hQ_pi' s₀
  -- stateOccupancy = (1-γ) * discountedVisitation
  -- So (1-γ)⁻¹ * ∑ stateOccupancy * adv = (1-γ)⁻¹ * ∑ (1-γ) * d * adv
  --   = ∑ d * adv = pdl_occupancy_form RHS
  rw [h_pdl]; simp only [stateOccupancy]
  have h1g_ne : (1 - M.γ) ≠ 0 := ne_of_gt (sub_pos.mpr M.γ_lt_one)
  -- (1-γ)⁻¹ * ∑ (1-γ)*d*adv = (1-γ)⁻¹ * (1-γ) * ∑ d*adv = ∑ d*adv
  simp_rw [show ∀ s, (1 - M.γ) * M.discountedVisitation π s₀ s *
    M.expectedAdvantage π Q_pi' V_pi' s =
    (1 - M.γ) * (M.discountedVisitation π s₀ s *
      M.expectedAdvantage π Q_pi' V_pi' s) from fun s => by ring]
  rw [← Finset.mul_sum, inv_mul_cancel_left₀ h1g_ne]

end FiniteMDP

end
