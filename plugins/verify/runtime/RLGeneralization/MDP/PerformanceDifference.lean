/-
# Algebraic Policy Comparison via Resolvent

Proves auxiliary results related to (but NOT identical to) the
the standard infinite-horizon performance difference lemma.

The exact occupancy-measure identity is:
  V^π(μ) - V^{π'}(μ) = (1/(1-γ)) E_{d^π_μ}[A^{π'}]
which requires the occupancy measure d^π_μ (not formalized).

We instead prove a one-step Bellman identity and a resolvent
bound that are algebraic consequences of the Bellman equations.

## Key Insight

The trajectory-based proof uses telescoping:
  V^π - V^{π'} = E_τ[∑ γ^t A^{π'}(s_t,a_t)]

We instead observe that V^π - V^{π'} satisfies a Bellman-like
resolvent equation with "driving term" = expected advantage:
  (V^π - V^{π'})(s) = E_{a~π}[A^{π'}(s,a)] + γ P^π(V^π - V^{π'})(s)

This is purely algebraic (no trajectories, no measure theory).
Combined with `resolvent_bound`, it gives:
  ‖V^π - V^{π'}‖_∞ ≤ max_s |E_{a~π}[A^{π'}(s,a)]| / (1-γ)

## Main Results

* `pdl_one_step` - The one-step PDL identity (resolvent form)
* `pdl_bound` - Performance difference bound via resolvent

## References

* [Agarwal et al., *RL: Theory and Algorithms*][agarwal2026]
* [Kakade and Langford, 2002]
-/

import RLGeneralization.MDP.Resolvent

open Finset BigOperators

noncomputable section

namespace FiniteMDP

variable (M : FiniteMDP)

/-! ### Advantage Function -/

/-- The advantage of policy `π'` at `(s,a)`:
    `A^{π'}(s,a) = Q^{π'}(s,a) - V^{π'}(s)`. -/
def advantage (Q : M.ActionValueFn) (V : M.StateValueFn) :
    M.S → M.A → ℝ :=
  fun s a => Q s a - V s

/-- Expected advantage under policy π:
    E_{a~π(·|s)}[A^{π'}(s,a)] = ∑_a π(a|s) A^{π'}(s,a)
    This is the "driving term" in the resolvent form of the PDL. -/
def expectedAdvantage (π : M.StochasticPolicy)
    (Q : M.ActionValueFn) (V : M.StateValueFn)
    (s : M.S) : ℝ :=
  ∑ a, π.prob s a * M.advantage Q V s a

/-! ### One-Step PDL Identity (Resolvent Form) -/

/-- **One-step Bellman identity for V^π - V^{π'}**.

  For any two policies π, π' with value functions V^π, V^{π'}
  and action-value Q^{π'}, the one-step identity:

    V^π(s) - V^{π'}(s) = E_{a~π}[A^{π'}(s,a)]
                        + γ · P^π(V^π - V^{π'})(s)

  where A^{π'}(s,a) = Q^{π'}(s,a) - V^{π'}(s) is the advantage.

  This says the policy gap satisfies a Bellman-like resolvent
  equation with the expected advantage as the "driving term."
  The full performance-difference identity
  (V^π - V^{π'} = (1/(1-γ)) E_{d^π}[A^{π'}]) follows by
  unrolling via the resolvent (I - γP^π)⁻¹.

  **Caveat**: This is NOT the same as the occupancy-measure identity. It is a
  one-step Bellman decomposition that serves as the building
  block; the infinite-horizon
  occupancy-measure form obtained by iterating this identity. -/
theorem pdl_one_step
    (π π' : M.StochasticPolicy)
    (V_pi V_pi' : M.StateValueFn)
    (Q_pi' : M.ActionValueFn)
    -- V^π satisfies Bellman for π
    (hV_pi : M.isValueOf V_pi π)
    -- V^{π'} satisfies Bellman for π'
    (_hV_pi' : M.isValueOf V_pi' π')
    -- Q^{π'}(s,a) = r(s,a) + γ ∑ P(s'|s,a) V^{π'}(s')
    (hQ_pi' : ∀ s a, Q_pi' s a =
      M.r s a + M.γ * ∑ s', M.P s a s' * V_pi' s') :
    ∀ s, V_pi s - V_pi' s =
      M.expectedAdvantage π Q_pi' V_pi' s +
      M.γ * M.expectedNextValue π
        (fun s => V_pi s - V_pi' s) s := by
  intro s
  -- Strategy: show both sides equal
  --   expectedReward π s + γ nextValue π V_pi s - V_pi' s
  -- LHS = V_pi s - V_pi' s = (by Bellman) above expression
  -- RHS = expectedAdvantage + γ nextValue(V_pi - V_pi')
  --     = (same expression after expansion and cancellation)

  -- Step 1: LHS via Bellman
  have hLHS : V_pi s - V_pi' s = M.expectedReward π s +
      M.γ * M.expectedNextValue π V_pi s - V_pi' s := by
    rw [hV_pi s]
  -- Step 2: nextValue is linear (distribute over subtraction)
  have hNextLin : M.expectedNextValue π
      (fun s => V_pi s - V_pi' s) s =
      M.expectedNextValue π V_pi s -
      M.expectedNextValue π V_pi' s := by
    unfold expectedNextValue
    rw [← Finset.sum_sub_distrib]
    congr 1; funext a; rw [← mul_sub]
    congr 1; rw [← Finset.sum_sub_distrib]
    congr 1; funext s'; ring
  -- Step 3: expectedAdvantage expands using Q = r + γPV'
  have hAdvExp : M.expectedAdvantage π Q_pi' V_pi' s =
      M.expectedReward π s +
      M.γ * M.expectedNextValue π V_pi' s -
      V_pi' s := by
    -- ∑ π(a)(Q(s,a) - V') = (∑ π Q) - V'
    --   = (∑ π(r + γPV')) - V' = expReward + γ nextV V' - V'
    simp only [expectedAdvantage, advantage]
    have h1 : ∑ a, π.prob s a * (Q_pi' s a - V_pi' s) =
        (∑ a, π.prob s a * Q_pi' s a) - V_pi' s := by
      simp_rw [mul_sub, Finset.sum_sub_distrib,
        ← Finset.sum_mul, π.prob_sum_one, one_mul]
    have h2 : ∑ a, π.prob s a * Q_pi' s a =
        M.expectedReward π s +
        M.γ * M.expectedNextValue π V_pi' s := by
      simp only [expectedReward, expectedNextValue]
      simp_rw [hQ_pi', mul_add, Finset.sum_add_distrib]
      congr 1
      have : ∀ a, π.prob s a *
          (M.γ * ∑ s', M.P s a s' * V_pi' s') =
          M.γ * (π.prob s a *
            ∑ s', M.P s a s' * V_pi' s') :=
        fun a => by ring
      simp_rw [this]; exact (Finset.mul_sum _ _ _).symm
    linarith [h1, h2]
  -- Step 4: Combine RHS
  have hRHS : M.expectedAdvantage π Q_pi' V_pi' s +
      M.γ * M.expectedNextValue π
        (fun s => V_pi s - V_pi' s) s =
      M.expectedReward π s +
      M.γ * M.expectedNextValue π V_pi s -
      V_pi' s := by
    rw [hNextLin, hAdvExp]; ring
  linarith [hLHS, hRHS]

/-! ### PDL Bound via Resolvent -/

/-- **Resolvent bound for V^π - V^{π'}**.

  Combines `pdl_one_step` with `resolvent_bound` to obtain:

    ‖V^π - V^{π'}‖_∞ ≤ ‖E_π[A^{π'}]‖_∞ / (1-γ)

  where A^{π'}(s,a) = Q^{π'}(s,a) - V^{π'}(s) is the advantage
  and E_π[A^{π'}](s) = ∑_a π(a|s) A^{π'}(s,a).

  This is a quantitative performance-difference bound: the policy
  gap is controlled by the maximum expected advantage, amplified
  by the effective horizon 1/(1-γ).

  **Caveat**: This is NOT the occupancy-measure identity but an
  equivalent norm bound. A trajectory-based proof derives
  this via trajectory telescoping; we derive it algebraically
  via the resolvent (I - γP^π)⁻¹. -/
theorem pdl_bound
    (π π' : M.StochasticPolicy)
    (V_pi V_pi' : M.StateValueFn)
    (Q_pi' : M.ActionValueFn)
    (hV_pi : M.isValueOf V_pi π)
    (hV_pi' : M.isValueOf V_pi' π')
    (hQ_pi' : ∀ s a, Q_pi' s a =
      M.r s a + M.γ * ∑ s', M.P s a s' * V_pi' s') :
    ∀ s, |V_pi s - V_pi' s| ≤
      M.supNormV (M.expectedAdvantage π Q_pi' V_pi') /
        (1 - M.γ) := by
  -- V^π - V^{π'} satisfies the resolvent equation
  -- W = b + γ P^π W where b = expectedAdvantage
  -- So resolvent_bound gives ‖W‖ ≤ ‖b‖/(1-γ)
  exact M.resolvent_bound π
    (fun s => V_pi s - V_pi' s)
    (M.expectedAdvantage π Q_pi' V_pi')
    (M.pdl_one_step π π' V_pi V_pi' Q_pi'
      hV_pi hV_pi' hQ_pi')

end FiniteMDP

end
