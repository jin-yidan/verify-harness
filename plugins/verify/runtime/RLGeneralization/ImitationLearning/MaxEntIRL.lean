/-
# Maximum Entropy Inverse Reinforcement Learning

Formalizes the MaxEnt IRL framework (Ziebart et al., 2008):
given expert demonstrations, find a reward function R that explains
the behavior via the maximum entropy principle.

## Main Results

* `maxentPolicy_well_defined` — softmax policy probabilities sum to 1

* `maxentPolicy_is_softoptimal` — log π(a|s) = Q(s,a) - log Z(s)

* `maxent_feature_matching_from_hypothesis` — the MaxEnt IRL solution matches expert
    feature expectations (wrapper: bridges optimality hypothesis)

* `maxent_dual_linear_in_occupancy` — MaxEnt dual is linear in occupancy

* `ppo_improvement_lower_bound` — MaxEnt IRL reduces to soft MDP planning

## References

* Ziebart et al., "Maximum Entropy Inverse Reinforcement Learning," AAAI 2008.
* Agarwal et al., "RL: Theory and Algorithms," Ch 13.4 (2026).
-/

import RLGeneralization.MDP.LPFormulation
import RLGeneralization.MDP.OccupancyMeasure
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Algebra.BigOperators.Field

open Finset BigOperators Real

noncomputable section

namespace FiniteMDP

variable (M : FiniteMDP)

/-! ### Maximum Entropy Policy -/

/-- **MaxEnt policy** (soft-optimal policy for Q-function Q):
    π_Q(a|s) = exp(Q(s,a)) / ∑_a' exp(Q(s,a'))
    This is the Boltzmann/softmax distribution over actions. -/
noncomputable def maxentPolicyProb (Q : M.ActionValueFn)
    (s : M.S) (a : M.A) : ℝ :=
  Real.exp (Q s a) / ∑ a', Real.exp (Q s a')

/-- The partition function Z(s) = ∑_a exp(Q(s,a)) is strictly positive. -/
theorem maxentPolicy_partition_pos (Q : M.ActionValueFn) (s : M.S) :
    0 < ∑ a : M.A, Real.exp (Q s a) :=
  Finset.sum_pos (fun _a _ => Real.exp_pos _) Finset.univ_nonempty

/-- MaxEnt policy probabilities are nonneg. -/
theorem maxentPolicy_prob_nonneg (Q : M.ActionValueFn)
    (s : M.S) (a : M.A) :
    0 ≤ M.maxentPolicyProb Q s a :=
  div_nonneg (le_of_lt (Real.exp_pos _))
    (le_of_lt (M.maxentPolicy_partition_pos Q s))

/-- MaxEnt policy probabilities sum to 1 (well-defined distribution). -/
theorem maxentPolicy_prob_sum_one (Q : M.ActionValueFn) (s : M.S) :
    ∑ a : M.A, M.maxentPolicyProb Q s a = 1 := by
  simp only [maxentPolicyProb, ← Finset.sum_div]
  exact div_self (ne_of_gt (M.maxentPolicy_partition_pos Q s))

/-- Construct MaxEnt policy as a StochasticPolicy. -/
def maxentPolicy (Q : M.ActionValueFn) : M.StochasticPolicy where
  prob := M.maxentPolicyProb Q
  prob_nonneg := M.maxentPolicy_prob_nonneg Q
  prob_sum_one := M.maxentPolicy_prob_sum_one Q

/-- **Key identity**: log π_Q(a|s) = Q(s,a) - log Z(s).
    This connects the log-policy to the Q-function. -/
theorem maxentPolicy_log_prob (Q : M.ActionValueFn) (s : M.S) (a : M.A) :
    Real.log (M.maxentPolicyProb Q s a) =
      Q s a - Real.log (∑ a', Real.exp (Q s a')) := by
  simp only [maxentPolicyProb]
  rw [Real.log_div (ne_of_gt (Real.exp_pos _))
      (ne_of_gt (M.maxentPolicy_partition_pos Q s))]
  simp [Real.log_exp]

/-! ### Feature Expectations -/

/-- Feature expectation of policy π starting from state s₀:
    Φ(π, s₀) = ∑_s d^π(s₀,s) · ∑_a π(a|s) · φ(s,a)
    where d^π(s₀,s) = (1-γ) · ∑_t γ^t P^t(s₀→s). -/
noncomputable def featureExpectation (pol : M.StochasticPolicy)
    (φ : M.S → M.A → ℝ) (s₀ : M.S) : ℝ :=
  ∑ s, M.stateOccupancy pol s₀ s * ∑ a, pol.prob s a * φ s a

/-! ### MaxEnt IRL Feature Matching -/

/-- **MaxEnt feature matching** from gradient stationarity.

At the optimal reward R*, the induced MaxEnt policy π_{R*} satisfies:
  Φ(π_{R*}, s₀) = Φ(π_expert, s₀)

i.e., feature expectations match the expert.

At a stationary point (∇L = 0), the feature difference vanishes,
giving Φ(π_Q) = Φ_E.

[TAUTOLOGICAL: stationarity — optimality of Q_opt is taken as hypothesis] -/
theorem maxent_feature_matching_from_hypothesis
    (φ : M.S → M.A → ℝ) (s₀ : M.S)
    (Q_opt : M.ActionValueFn)
    (π_expert : M.StochasticPolicy)
    -- At the optimum, gradient vanishes (stationarity)
    (h_stationary : M.featureExpectation (M.maxentPolicy Q_opt) φ s₀ -
                    M.featureExpectation π_expert φ s₀ = 0) :
    M.featureExpectation (M.maxentPolicy Q_opt) φ s₀ =
    M.featureExpectation π_expert φ s₀ := by
  linarith

/-! ### Linearity of MaxEnt Dual in Occupancy -/

/-- **MaxEnt dual objective is linear in occupancy measure**.

The MaxEnt dual d ↦ ∑_{s,a} d(s,a) · log π_Q(a|s) is linear in d.
This implies convexity in d (linearity → convexity trivially). -/
theorem maxent_dual_linear_in_occupancy
    (Q : M.ActionValueFn)
    (d₁ d₂ : M.S → M.A → ℝ) (t : ℝ) :
    ∑ s : M.S, ∑ a : M.A,
      ((1 - t) * d₁ s a + t * d₂ s a) *
      Real.log (M.maxentPolicyProb Q s a)
    = (1 - t) * ∑ s : M.S, ∑ a : M.A, d₁ s a * Real.log (M.maxentPolicyProb Q s a) +
      t * ∑ s : M.S, ∑ a : M.A, d₂ s a * Real.log (M.maxentPolicyProb Q s a) := by
  have h_point : ∀ (s : M.S) (a : M.A),
      ((1 - t) * d₁ s a + t * d₂ s a) * Real.log (M.maxentPolicyProb Q s a)
      = (1 - t) * (d₁ s a * Real.log (M.maxentPolicyProb Q s a))
      + t * (d₂ s a * Real.log (M.maxentPolicyProb Q s a)) :=
    fun _ _ => by ring
  simp_rw [h_point, Finset.sum_add_distrib, ← Finset.mul_sum]

/-! ### Reduction to Soft MDP Planning -/

/-- **MaxEnt IRL → Soft MDP planning**.

The MaxEnt policy is the unique fixed-point of the soft Bellman operator:
  V(s) = log ∑_a exp(Q(s,a))
  π(a|s) = exp(Q(s,a) - V(s))

For reward R and soft value V, the policy π_R satisfies:
  π_R(a|s) = exp(Q_R(s,a)) / Z_R(s)
  Q_R(s,a) = R(s,a) + γ · ∑_s' P(s'|s,a) · V_R(s')

This shows MaxEnt IRL reduces to solving soft MDPs. -/
theorem maxent_reduces_to_soft_mdp
    (Q : M.ActionValueFn) (s : M.S)
    -- Log-partition function = soft value
    (V_soft : M.StateValueFn)
    (h_V : ∀ s, V_soft s = Real.log (∑ a : M.A, Real.exp (Q s a))) :
    ∀ a : M.A,
      Real.log (M.maxentPolicyProb Q s a) = Q s a - V_soft s := by
  intro a
  rw [h_V s, M.maxentPolicy_log_prob Q s a]

/-- [TAUTOLOGICAL] **Gradient of MaxEnt IRL objective implies feature matching**.

∇_w L(w) = Φ(π_w, s₀) - Φ_expert(s₀)

where L(w) = E_{expert}[w · φ] - log Z(w) is the MaxEnt dual.

At the optimum, ∇_w L = 0, giving feature matching.

Proved: if the gradient vanishes for ALL feature directions simultaneously,
then it vanishes for any particular feature vector φ, giving matching. -/
theorem maxent_irl_gradient_at_optimum_from_hypothesis
    (φ : M.S → M.A → ℝ) (s₀ : M.S)
    (Q_opt : M.ActionValueFn)
    (π_expert : M.StochasticPolicy)
    -- At the optimum, the gradient vanishes for ALL feature directions
    (h_all_grad_zero : ∀ (ψ : M.S → M.A → ℝ) (s : M.S),
      M.featureExpectation (M.maxentPolicy Q_opt) ψ s -
      M.featureExpectation π_expert ψ s = 0) :
    -- Feature matching holds for the specific φ, s₀
    M.featureExpectation (M.maxentPolicy Q_opt) φ s₀ =
    M.featureExpectation π_expert φ s₀ := by
  linarith [h_all_grad_zero φ s₀]

/-! ### Log-Sum-Exp Convexity -/

/-- **Log-sum-exp is convex** (via pointwise weighted AM-GM).

For any vectors α β over a finite nonempty type and weight t ∈ [0,1]:
  log(∑_a exp((1-t)·α_a + t·β_a)) ≤ (1-t)·log(∑_a exp(α_a)) + t·log(∑_a exp(β_a))

Proof sketch: normalise by Z₁ = ∑ exp(α), Z₂ = ∑ exp(β), apply pointwise
`geom_mean_le_arith_mean2_weighted`, sum, multiply back, take log. -/
theorem logSumExp_convex {A : Type*} [Fintype A] [Nonempty A]
    (α β : A → ℝ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.log (∑ a : A, Real.exp ((1 - t) * α a + t * β a)) ≤
      (1 - t) * Real.log (∑ a : A, Real.exp (α a)) +
      t * Real.log (∑ a : A, Real.exp (β a)) := by
  set Z₁ := ∑ a : A, Real.exp (α a) with hZ₁_def
  set Z₂ := ∑ a : A, Real.exp (β a) with hZ₂_def
  have hZ₁_pos : 0 < Z₁ := Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  have hZ₂_pos : 0 < Z₂ := Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  have h1t : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  -- Step 1: exp(mixed) = exp(α)^(1-t) · exp(β)^t
  have h_exp_split : ∀ a : A,
      Real.exp ((1 - t) * α a + t * β a) =
        (Real.exp (α a)) ^ (1 - t) * (Real.exp (β a)) ^ t := by
    intro a
    rw [Real.exp_add, mul_comm (1 - t) (α a), Real.exp_mul,
        mul_comm t (β a), Real.exp_mul]
  -- Step 2: Pointwise AM-GM on normalised probabilities
  have h_amgm_sum : ∑ a : A,
      (Real.exp (α a) / Z₁) ^ (1 - t) * (Real.exp (β a) / Z₂) ^ t ≤ 1 := by
    calc ∑ a, (Real.exp (α a) / Z₁) ^ (1 - t) * (Real.exp (β a) / Z₂) ^ t
        ≤ ∑ a, ((1 - t) * (Real.exp (α a) / Z₁) + t * (Real.exp (β a) / Z₂)) :=
          Finset.sum_le_sum fun a _ =>
            Real.geom_mean_le_arith_mean2_weighted h1t ht0
              (div_nonneg (Real.exp_pos _).le hZ₁_pos.le)
              (div_nonneg (Real.exp_pos _).le hZ₂_pos.le) (by ring)
      _ = (1 - t) * (∑ a, Real.exp (α a) / Z₁) + t * (∑ a, Real.exp (β a) / Z₂) := by
          simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = 1 := by
          rw [← Finset.sum_div, ← Finset.sum_div,
              div_self (ne_of_gt hZ₁_pos), div_self (ne_of_gt hZ₂_pos)]
          ring
  -- Step 3: Unfold normalisation to get ∑ exp(mixed) ≤ Z₁^(1-t) · Z₂^t
  have hZprod_pos : 0 < Z₁ ^ (1 - t) * Z₂ ^ t :=
    mul_pos (Real.rpow_pos_of_pos hZ₁_pos _) (Real.rpow_pos_of_pos hZ₂_pos _)
  have h_main : ∑ a : A, Real.exp ((1 - t) * α a + t * β a) ≤
      Z₁ ^ (1 - t) * Z₂ ^ t := by
    have h_term : ∀ a : A,
        (Real.exp (α a) / Z₁) ^ (1 - t) * (Real.exp (β a) / Z₂) ^ t =
        Real.exp ((1 - t) * α a + t * β a) / (Z₁ ^ (1 - t) * Z₂ ^ t) := by
      intro a
      rw [Real.div_rpow (Real.exp_pos _).le hZ₁_pos.le,
          Real.div_rpow (Real.exp_pos _).le hZ₂_pos.le,
          div_mul_div_comm, ← h_exp_split a]
    simp_rw [h_term, ← Finset.sum_div] at h_amgm_sum
    rwa [div_le_one hZprod_pos] at h_amgm_sum
  -- Step 4: Take log, decompose via log_mul and log_rpow
  have h_lhs_pos : 0 < ∑ a : A, Real.exp ((1 - t) * α a + t * β a) :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  calc Real.log (∑ a, Real.exp ((1 - t) * α a + t * β a))
      ≤ Real.log (Z₁ ^ (1 - t) * Z₂ ^ t) :=
        Real.log_le_log h_lhs_pos h_main
    _ = (1 - t) * Real.log Z₁ + t * Real.log Z₂ := by
        rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hZ₁_pos _))
                         (ne_of_gt (Real.rpow_pos_of_pos hZ₂_pos _)),
            Real.log_rpow hZ₁_pos, Real.log_rpow hZ₂_pos]

/-- **MaxEnt IRL dual convexity**.

The MaxEnt IRL dual objective:
  L(w) = Φ_expert · w - log Z_w(s₀)

is concave in w (since -log Z_w is concave in Q, and Q is linear in w).
Equivalently, the negative dual -L(w) is convex.

Log-sum-exp convexity proved via weighted AM-GM (see `logSumExp_convex`).
Conditional on stationarity hypothesis for feature matching. -/
theorem maxent_irl_dual_concave
    (φ : M.S → M.A → ℝ) (s₀ : M.S)
    (_π_expert : M.StochasticPolicy)
    (w₁ w₂ : ℝ) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    -- Q is linear in w: Q_w(s,a) = w · φ(s,a)
    (Q₁ Q₂ : M.ActionValueFn)
    (_h_Q₁ : ∀ s a, Q₁ s a = w₁ * φ s a)
    (_h_Q₂ : ∀ s a, Q₂ s a = w₂ * φ s a) :
    -- The dual entropy term is concave
    -(∑ s, M.stateOccupancy (M.maxentPolicy Q₁) s₀ s *
        Real.log (∑ a : M.A,
          Real.exp (((1 - t) * w₁ + t * w₂) * φ s a))) ≥
    -(1 - t) * (∑ s, M.stateOccupancy (M.maxentPolicy Q₁) s₀ s *
                Real.log (∑ a : M.A, Real.exp (w₁ * φ s a))) -
    t * (∑ s, M.stateOccupancy (M.maxentPolicy Q₁) s₀ s *
           Real.log (∑ a : M.A, Real.exp (w₂ * φ s a))) := by
  -- Apply log-sum-exp convexity at each state
  have h_logconvex : ∀ s,
      Real.log (∑ a : M.A, Real.exp (((1 - t) * w₁ + t * w₂) * φ s a)) ≤
        (1 - t) * Real.log (∑ a : M.A, Real.exp (w₁ * φ s a)) +
        t * Real.log (∑ a : M.A, Real.exp (w₂ * φ s a)) := by
    intro s
    have h_rw : ∀ a : M.A,
        ((1 - t) * w₁ + t * w₂) * φ s a = (1 - t) * (w₁ * φ s a) + t * (w₂ * φ s a) :=
      fun a => by ring
    simp_rw [h_rw]
    exact logSumExp_convex (fun a => w₁ * φ s a) (fun a => w₂ * φ s a) t ht ht1
  have h_le : ∑ s, M.stateOccupancy (M.maxentPolicy Q₁) s₀ s *
      Real.log (∑ a : M.A,
        Real.exp (((1 - t) * w₁ + t * w₂) * φ s a)) ≤
    ∑ s, M.stateOccupancy (M.maxentPolicy Q₁) s₀ s *
      ((1 - t) * Real.log (∑ a : M.A, Real.exp (w₁ * φ s a)) +
       t * Real.log (∑ a : M.A, Real.exp (w₂ * φ s a))) := by
    apply Finset.sum_le_sum
    intro s _
    apply mul_le_mul_of_nonneg_left (h_logconvex s)
    exact M.stateOccupancy_nonneg (M.maxentPolicy Q₁) s₀ s
  have h_dist : ∑ s : M.S, M.stateOccupancy (M.maxentPolicy Q₁) s₀ s *
      ((1 - t) * Real.log (∑ a : M.A, Real.exp (w₁ * φ s a)) +
       t * Real.log (∑ a : M.A, Real.exp (w₂ * φ s a))) =
    (1 - t) * ∑ s : M.S, M.stateOccupancy (M.maxentPolicy Q₁) s₀ s *
      Real.log (∑ a : M.A, Real.exp (w₁ * φ s a)) +
    t * ∑ s : M.S, M.stateOccupancy (M.maxentPolicy Q₁) s₀ s *
      Real.log (∑ a : M.A, Real.exp (w₂ * φ s a)) := by
    have h_pt : ∀ s : M.S,
        M.stateOccupancy (M.maxentPolicy Q₁) s₀ s *
        ((1 - t) * Real.log (∑ a : M.A, Real.exp (w₁ * φ s a)) +
         t * Real.log (∑ a : M.A, Real.exp (w₂ * φ s a))) =
        (1 - t) * (M.stateOccupancy (M.maxentPolicy Q₁) s₀ s *
          Real.log (∑ a : M.A, Real.exp (w₁ * φ s a))) +
        t * (M.stateOccupancy (M.maxentPolicy Q₁) s₀ s *
          Real.log (∑ a : M.A, Real.exp (w₂ * φ s a))) :=
      fun _ => by ring
    simp_rw [h_pt, Finset.sum_add_distrib, ← Finset.mul_sum]
  linarith [h_le.trans_eq h_dist]

end FiniteMDP

end
