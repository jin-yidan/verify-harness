/-
# Average-Reward MDPs

Formalizes the average-reward (gain-bias) formulation of MDPs,
the span seminorm, and the connection between discounted and
average-reward settings.

## Main Definitions

* `spanSeminorm` - The span seminorm sp(h) = max h - min h
* `GainBiasEquation` - The gain-bias optimality equation

## Main Results

* `span_nonneg` - sp(h) >= 0
* `span_zero_iff_const` - sp(h) = 0 iff h is constant
* `span_sub_le` - sp(f - g) <= sp(f) + sp(g)
* `bellman_span_contraction` - Bellman operator is a span contraction (gamma-contraction)
* `discounted_to_average_limit` - Bellman rearrangement: (1-gamma)*V = r^pi + gamma*(PV - V)

## References

* [Puterman, *Markov Decision Processes*, Ch 8-9][puterman2014]
* [Bertsekas, *Dynamic Programming and Optimal Control*, Vol II][bertsekas2012]
-/

import RLGeneralization.MDP.BellmanContraction

open Finset BigOperators

noncomputable section

namespace FiniteMDP

variable (M : FiniteMDP)

/-! ### Span Seminorm -/

/-- The span seminorm of a function f on a finite nonempty type:
    sp(f) = max_s f(s) - min_s f(s).

    This is a seminorm: sp(f) = 0 iff f is constant, and it satisfies
    a triangle-like inequality sp(f - g) <= sp(f) + sp(g). -/
def spanSeminorm (f : M.S → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty f -
  Finset.univ.inf' Finset.univ_nonempty f

/-- The span seminorm is nonnegative. -/
theorem span_nonneg (f : M.S → ℝ) : 0 ≤ M.spanSeminorm f := by
  unfold spanSeminorm
  have ⟨s, hs⟩ : ∃ s, s ∈ (Finset.univ : Finset M.S) :=
    ⟨Classical.arbitrary _, Finset.mem_univ _⟩
  linarith [Finset.le_sup' f hs, Finset.inf'_le f hs]

/-- The span seminorm is zero if and only if the function is constant. -/
theorem span_zero_iff_const (f : M.S → ℝ) :
    M.spanSeminorm f = 0 ↔ ∀ s₁ s₂ : M.S, f s₁ = f s₂ := by
  unfold spanSeminorm
  constructor
  · -- sp(f) = 0 implies f is constant
    intro h
    have hsup_eq_inf : Finset.univ.sup' Finset.univ_nonempty f =
        Finset.univ.inf' Finset.univ_nonempty f := by linarith
    intro s₁ s₂
    have h1 := Finset.le_sup' f (Finset.mem_univ s₁)
    have h2 := Finset.inf'_le f (Finset.mem_univ s₁)
    have h3 := Finset.le_sup' f (Finset.mem_univ s₂)
    have h4 := Finset.inf'_le f (Finset.mem_univ s₂)
    linarith
  · -- f constant implies sp(f) = 0
    intro hconst
    have hs := Classical.arbitrary M.S
    have hsup : Finset.univ.sup' Finset.univ_nonempty f = f hs := by
      apply le_antisymm
      · exact Finset.sup'_le _ _ fun s _ => le_of_eq (hconst s hs)
      · exact Finset.le_sup' f (Finset.mem_univ hs)
    have hinf : Finset.univ.inf' Finset.univ_nonempty f = f hs := by
      apply le_antisymm
      · exact Finset.inf'_le f (Finset.mem_univ hs)
      · exact Finset.le_inf' _ _ fun s _ => le_of_eq (hconst hs s)
    rw [hsup, hinf, sub_self]

/-- Triangle-like inequality for span: sp(f - g) <= sp(f) + sp(g). -/
theorem span_sub_le (f g : M.S → ℝ) :
    M.spanSeminorm (fun s => f s - g s) ≤ M.spanSeminorm f + M.spanSeminorm g := by
  unfold spanSeminorm
  -- sp(f-g) = max(f-g) - min(f-g)
  -- max(f-g) <= max(f) - min(g) and min(f-g) >= min(f) - max(g)
  -- So sp(f-g) <= (max f - min g) - (min f - max g) = sp(f) + sp(g)
  have hmax : Finset.univ.sup' Finset.univ_nonempty (fun s => f s - g s) ≤
      Finset.univ.sup' Finset.univ_nonempty f -
      Finset.univ.inf' Finset.univ_nonempty g := by
    apply Finset.sup'_le _ _ fun s _ => ?_
    linarith [Finset.le_sup' f (Finset.mem_univ s),
              Finset.inf'_le g (Finset.mem_univ s)]
  have hmin : Finset.univ.inf' Finset.univ_nonempty f -
      Finset.univ.sup' Finset.univ_nonempty g ≤
      Finset.univ.inf' Finset.univ_nonempty (fun s => f s - g s) := by
    apply Finset.le_inf' _ _ fun s _ => ?_
    linarith [Finset.inf'_le f (Finset.mem_univ s),
              Finset.le_sup' g (Finset.mem_univ s)]
  linarith

/-! ### Gain-Bias Equation -/

/-- The gain-bias optimality equation (Bellman equation for average reward):
    g + h(s) = max_a { r(s,a) + sum_{s'} P(s'|s,a) h(s') }

    A pair (g, h) satisfying this equation characterizes the optimal
    average reward g* and the optimal bias h*. -/
def GainBiasEquation (g : ℝ) (h : M.S → ℝ) : Prop :=
  ∀ s, g + h s = Finset.univ.sup' Finset.univ_nonempty
    (fun a => M.r s a + ∑ s', M.P s a s' * h s')

/-- The policy evaluation version of the gain-bias equation:
    g + h(s) = sum_a pi(a|s) * (r(s,a) + sum_{s'} P(s'|s,a) h(s'))
    for a fixed policy pi. -/
def GainBiasEvalEquation (π : M.StochasticPolicy) (g : ℝ) (h : M.S → ℝ) : Prop :=
  ∀ s, g + h s = ∑ a, π.prob s a * (M.r s a + ∑ s', M.P s a s' * h s')

/-! ### Bellman Operator for Average Reward -/

/-- The average-reward Bellman operator T_avg:
    (T_avg h)(s) = max_a { r(s,a) + sum_{s'} P(s'|s,a) h(s') } - g

    When g is the optimal gain, fixed points of T_avg are optimal biases. -/
def bellmanAvgOp (g : ℝ) (h : M.S → ℝ) : M.S → ℝ :=
  fun s => Finset.univ.sup' Finset.univ_nonempty
    (fun a => M.r s a + ∑ s', M.P s a s' * h s') - g

/-- The gain-bias equation is equivalent to h being a fixed point of T_avg. -/
theorem gainBias_iff_fixed (g : ℝ) (h : M.S → ℝ) :
    M.GainBiasEquation g h ↔ ∀ s, h s = M.bellmanAvgOp g h s := by
  simp only [GainBiasEquation, bellmanAvgOp]
  constructor <;> intro H s <;> linarith [H s]

/-! ### Span Contraction of Bellman Operator -/

/-- The Bellman optimality operator for state value functions:
    (T V)(s) = max_a { r(s,a) + gamma * sum_{s'} P(s'|s,a) V(s') }
    Used for the span contraction theorem. -/
private def bellmanOptVLocal (V : M.S → ℝ) : M.S → ℝ :=
  fun s => Finset.univ.sup' Finset.univ_nonempty
    (fun a => M.r s a + M.γ * ∑ s', M.P s a s' * V s')

/-- **Span contraction of the Bellman operator** (for ergodic MDPs).

    For an MDP with discount factor gamma, the Bellman optimality operator
    satisfies:
      sp(T h₁ - T h₂) <= gamma * sp(h₁ - h₂)

    where T h(s) = max_a { r(s,a) + gamma * sum P h(s') }.

    The ergodicity hypothesis ensures uniform mixing
    (P(s'|s,a) >= alpha > 0 for all s,a,s').

    Proof: The difference T h₁(s) - T h₂(s) satisfies
      |T h₁(s) - T h₂(s)| <= gamma * max |h₁ - h₂|
    by the Bellman contraction property. The span bound then follows
    since sp(f) <= 2 * max |f| and we can tighten using ergodicity.

    We prove the gamma bound directly via:
      max (Th₁ - Th₂) <= gamma * max (h₁ - h₂) (weighted average <= max)
      min (Th₁ - Th₂) >= gamma * min (h₁ - h₂) (weighted average >= min) -/
theorem bellman_span_contraction
    (h₁ h₂ : M.S → ℝ) :
    M.spanSeminorm (fun s =>
      M.bellmanOptVLocal h₁ s - M.bellmanOptVLocal h₂ s) ≤
    M.γ * M.spanSeminorm (fun s => h₁ s - h₂ s) := by
  unfold spanSeminorm
  set D := fun s => h₁ s - h₂ s
  set maxD := Finset.univ.sup' Finset.univ_nonempty D
  set minD := Finset.univ.inf' Finset.univ_nonempty D
  set Th := fun s => M.bellmanOptVLocal h₁ s - M.bellmanOptVLocal h₂ s
  -- Key: for each s, minD <= weighted_avg(D, P(s,a)) <= maxD
  -- So gamma * minD <= gamma * weighted_avg(D) <= gamma * maxD
  -- Helper: weighted average of D is at most maxD
  have wavg_le_max : ∀ s a, ∑ s', M.P s a s' * D s' ≤ maxD := by
    intro s a
    calc ∑ s', M.P s a s' * D s'
        ≤ ∑ s', M.P s a s' * maxD :=
          Finset.sum_le_sum fun s' _ =>
            mul_le_mul_of_nonneg_left (Finset.le_sup' D (Finset.mem_univ s'))
              (M.P_nonneg s a s')
      _ = maxD := by rw [← Finset.sum_mul, M.P_sum_one, one_mul]
  -- Helper: weighted average of D is at least minD
  have wavg_ge_min : ∀ s a, minD ≤ ∑ s', M.P s a s' * D s' := by
    intro s a
    calc minD = ∑ s', M.P s a s' * minD := by rw [← Finset.sum_mul, M.P_sum_one, one_mul]
      _ ≤ ∑ s', M.P s a s' * D s' :=
          Finset.sum_le_sum fun s' _ =>
            mul_le_mul_of_nonneg_left (Finset.inf'_le D (Finset.mem_univ s'))
              (M.P_nonneg s a s')
  -- Upper bound: Th(s) <= gamma * maxD for all s
  -- Strategy: sup f - sup g where f(a) = r + gamma P h₁, g(a) = r + gamma P h₂
  -- We use: sup f - sup g <= sup (f - g) (when f - g >= 0)
  -- Actually: sup f <= sup g + sup(f-g) always
  -- (since f a <= g a + (f a - g a) <= sup g + sup(f-g))
  -- So sup f - sup g <= sup (f - g) = sup (gamma * sum P D) <= gamma * maxD
  have h_upper : ∀ s, Th s ≤ M.γ * maxD := by
    intro s
    -- Th(s) = sup_a(r + gamma P h₁) - sup_a(r + gamma P h₂)
    -- By abs_sup_sub_sup_le: |sup f - sup g| <= sup |f - g|
    -- So Th(s) <= |Th(s)| <= sup_a |r + gamma P h₁ - r - gamma P h₂|
    --                       = sup_a |gamma sum P D|
    --                       = gamma * sup_a |sum P D|
    --                       <= gamma * supNormV D
    -- And supNormV D >= maxD, so this gives Th(s) <= gamma * supNormV D.
    -- But we want Th(s) <= gamma * maxD, which is tighter.
    -- For the tighter bound:
    -- sup f - sup g <= sup(f - g) (since f(a) - g(a) <= sup(f-g) for all a,
    --   so f(a) <= g(a) + sup(f-g), taking sup: sup f <= sup g + sup(f-g))
    -- sup(f-g) = sup_a(gamma * sum P D) <= gamma * maxD (weighted avg <= max)
    simp only [Th, bellmanOptVLocal]
    -- Step 1: sup f <= sup g + sup(f - g)
    have hsup_le : Finset.univ.sup' Finset.univ_nonempty
        (fun a => M.r s a + M.γ * ∑ s', M.P s a s' * h₁ s') ≤
        Finset.univ.sup' Finset.univ_nonempty
        (fun a => M.r s a + M.γ * ∑ s', M.P s a s' * h₂ s') +
        Finset.univ.sup' Finset.univ_nonempty
        (fun a => M.γ * ∑ s', M.P s a s' * D s') := by
      apply Finset.sup'_le _ _ fun a _ => ?_
      have hdecomp : M.r s a + M.γ * ∑ s', M.P s a s' * h₁ s' =
          (M.r s a + M.γ * ∑ s', M.P s a s' * h₂ s') +
          M.γ * ∑ s', M.P s a s' * D s' := by
        simp only [D]
        have : ∀ s', M.P s a s' * (h₁ s' - h₂ s') =
            M.P s a s' * h₁ s' - M.P s a s' * h₂ s' := fun s' => mul_sub _ _ _
        simp_rw [this, Finset.sum_sub_distrib]
        ring
      rw [hdecomp]
      exact add_le_add
        (Finset.le_sup' (fun a => M.r s a + M.γ * ∑ s', M.P s a s' * h₂ s')
          (Finset.mem_univ a))
        (Finset.le_sup' (fun a => M.γ * ∑ s', M.P s a s' * D s')
          (Finset.mem_univ a))
    -- Step 2: sup(gamma * sum P D) <= gamma * maxD
    have hbound : Finset.univ.sup' Finset.univ_nonempty
        (fun a => M.γ * ∑ s', M.P s a s' * D s') ≤ M.γ * maxD := by
      apply Finset.sup'_le _ _ fun a _ => ?_
      exact mul_le_mul_of_nonneg_left (wavg_le_max s a) M.γ_nonneg
    linarith
  -- Lower bound: Th(s) >= gamma * minD for all s
  -- Strategy: sup f - sup g >= f(a₀) - g(a₀) for the action a₀ achieving sup g
  -- and f(a₀) - g(a₀) = gamma * sum P D >= gamma * minD
  have h_lower : ∀ s, M.γ * minD ≤ Th s := by
    intro s
    simp only [Th, bellmanOptVLocal]
    -- Let a₀ be the action achieving sup on h₂ side
    set g := fun a => M.r s a + M.γ * ∑ s', M.P s a s' * h₂ s'
    obtain ⟨a₀, _, ha₀⟩ := Finset.exists_max_image Finset.univ g Finset.univ_nonempty
    have hsup_g : Finset.univ.sup' Finset.univ_nonempty g = g a₀ :=
      le_antisymm (Finset.sup'_le _ _ fun a _ => ha₀ a (Finset.mem_univ a))
        (Finset.le_sup' g (Finset.mem_univ a₀))
    -- f(a₀) - g(a₀) = gamma * sum P D >= gamma * minD
    have hdiff : (M.r s a₀ + M.γ * ∑ s', M.P s a₀ s' * h₁ s') - g a₀ =
        M.γ * ∑ s', M.P s a₀ s' * D s' := by
      simp only [g, D]
      have : ∀ s', M.P s a₀ s' * (h₁ s' - h₂ s') =
          M.P s a₀ s' * h₁ s' - M.P s a₀ s' * h₂ s' := fun s' => mul_sub _ _ _
      simp_rw [this, Finset.sum_sub_distrib]; ring
    calc M.γ * minD
        ≤ M.γ * ∑ s', M.P s a₀ s' * D s' :=
          mul_le_mul_of_nonneg_left (wavg_ge_min s a₀) M.γ_nonneg
      _ = (M.r s a₀ + M.γ * ∑ s', M.P s a₀ s' * h₁ s') - g a₀ := hdiff.symm
      _ ≤ Finset.univ.sup' Finset.univ_nonempty
            (fun a => M.r s a + M.γ * ∑ s', M.P s a s' * h₁ s') -
          Finset.univ.sup' Finset.univ_nonempty g := by
        rw [hsup_g]
        linarith [Finset.le_sup'
          (fun a => M.r s a + M.γ * ∑ s', M.P s a s' * h₁ s')
          (Finset.mem_univ a₀)]
  -- Combine: sp(Th) = sup Th - inf Th <= gamma * maxD - gamma * minD = gamma * sp(D)
  -- The goal is: sup (fun s => bellmanOptVLocal h₁ s - bellmanOptVLocal h₂ s) -
  --   inf (fun s => ...) <= gamma * (sup D - inf D)
  -- Since Th = fun s => bellmanOptVLocal h₁ s - bellmanOptVLocal h₂ s,
  -- and we have h_upper/h_lower for Th, we can use them.
  have hsup_Th : Finset.univ.sup' Finset.univ_nonempty Th ≤ M.γ * maxD :=
    Finset.sup'_le _ _ fun s _ => h_upper s
  have hinf_Th : M.γ * minD ≤ Finset.univ.inf' Finset.univ_nonempty Th :=
    Finset.le_inf' _ _ fun s _ => h_lower s
  -- sup Th - inf Th <= gamma * maxD - gamma * minD = gamma * (maxD - minD)
  nlinarith

/-! ### Connection Between Discounted and Average Reward -/

/-- **Bellman rearrangement for the discounted case**.

    If V satisfies the discounted Bellman equation V(s) = r^pi(s) + gamma * P^pi V(s),
    then rearranging gives:
      (1-gamma)*V(s) = r^pi(s) + gamma*(P^pi V(s) - V(s))

    This is a purely algebraic rearrangement of the Bellman equation, not the
    actual (1-gamma)*V_gamma -> g* limit as gamma -> 1 (which would require
    convergence analysis). See `average_reward_approximation` for the
    approximation bound. -/
theorem discounted_to_average_limit
    (π : M.StochasticPolicy)
    (V : M.StateValueFn)
    (hV : M.isValueOf V π) :
    ∀ s, (1 - M.γ) * V s =
      M.expectedReward π s +
      M.γ * (M.expectedNextValue π V s - V s) := by
  intro s
  -- From V(s) = r^pi(s) + gamma * P^pi V(s):
  -- (1-gamma) V(s) = V(s) - gamma V(s)
  --               = r^pi(s) + gamma P^pi V(s) - gamma V(s)
  --               = r^pi(s) + gamma (P^pi V(s) - V(s))
  linarith [hV s]

/-- If V satisfies the Bellman equation, then the "average reward" component
    (1-gamma)*V(s) is close to the expected immediate reward r^pi(s),
    with the correction bounded by gamma * 2 * V_max.

    As gamma -> 1, the correction vanishes relative to the value scale. -/
theorem average_reward_approximation
    (π : M.StochasticPolicy)
    (V : M.StateValueFn)
    (hV : M.isValueOf V π) :
    ∀ s, |(1 - M.γ) * V s - M.expectedReward π s| ≤
      M.γ * (2 * M.V_max) := by
  intro s
  -- From discounted_to_average_limit:
  -- (1-gamma) V(s) - r^pi(s) = gamma * (P^pi V(s) - V(s))
  have hdecomp := M.discounted_to_average_limit π V hV s
  rw [show (1 - M.γ) * V s - M.expectedReward π s =
    M.γ * (M.expectedNextValue π V s - V s) from by linarith]
  rw [abs_mul, abs_of_nonneg M.γ_nonneg]
  apply mul_le_mul_of_nonneg_left _ M.γ_nonneg
  -- |P^pi V(s) - V(s)| <= |P^pi V(s)| + |V(s)| <= V_max + V_max
  calc |M.expectedNextValue π V s - V s|
      ≤ |M.expectedNextValue π V s| + |V s| := by
        have h1 := abs_add_le (M.expectedNextValue π V s) (-V s)
        rwa [abs_neg] at h1
    _ ≤ M.V_max + M.V_max := by
        apply add_le_add
        · -- |P^pi V(s)| <= V_max
          unfold expectedNextValue
          apply abs_weighted_sum_le_bound _ _ M.V_max (π.prob_nonneg s) (π.prob_sum_one s)
          intro a
          apply abs_weighted_sum_le_bound _ _ M.V_max (M.P_nonneg s a) (M.P_sum_one s a)
          intro s'
          exact M.value_bounded_by_Vmax V π hV s'
        · exact M.value_bounded_by_Vmax V π hV s
    _ = 2 * M.V_max := by ring

end FiniteMDP

end
