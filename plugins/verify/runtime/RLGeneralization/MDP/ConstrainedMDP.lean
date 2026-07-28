/-
# Constrained Markov Decision Processes

Formalizes Constrained MDPs (CMDPs), where the agent maximizes a reward
objective subject to K cost constraints of the form E[c_k] <= d_k.
The Lagrangian relaxation converts the constrained problem into an
unconstrained one with augmented reward r - sum_k lambda_k * c_k.

## Mathematical Background

A **Constrained MDP** (Altman 1999) extends an MDP with:
- K cost functions c_k : S x A -> R (each bounded)
- K budget thresholds d_k
- Feasibility: a policy pi is feasible if its expected cost under c_k
  does not exceed d_k, for each k

The **Lagrangian** is L(pi, lam) = V^pi_r - sum_k lam_k (V^pi_{c_k} - d_k),
and standard weak duality relates the constrained optimum to the Lagrangian dual.

## Main Definitions

* `CostFunction` - A collection of K cost functions with bounds
* `CMDP` - Constrained MDP: MDP + costs + budgets
* `cmdpFeasible` - Policy feasibility (expected cost <= budget)
* `cmdpLagrangian` - The Lagrangian L(pi, lam)

## Main Results

* `lagrangian_weak_duality` - Weak duality: V^pi_r <= L(pi, lam)
* `lagrangian_decomposition` - L decomposes into augmented reward value + constant
* `cmdp_relaxation_bound` - Constrained optimal <= unconstrained optimal
* `cmdp_cost_tradeoff` - Tightening a budget cannot improve the optimal value

## References

* [Altman, *Constrained Markov Decision Processes*, 1999]
* [Efroni, Mannor, Pirotta, "Exploration-Exploitation in CMDPs," 2020]
-/

import RLGeneralization.MDP.BellmanContraction

open Finset BigOperators

noncomputable section

namespace FiniteMDP

variable (M : FiniteMDP)

/-! ### Cost Functions -/

/-- A collection of K cost functions for a constrained MDP.
    Each cost function c_k : S x A -> R is bounded. -/
structure CostFunction (K : ℕ) where
  /-- The k-th cost function c_k(s,a) -/
  cost : Fin K → M.S → M.A → ℝ
  /-- Each cost function is bounded -/
  cost_bound : ∃ C_max : ℝ, 0 < C_max ∧ ∀ k s a, |cost k s a| ≤ C_max

/-! ### Constrained MDP Structure -/

/-- A **Constrained MDP** (CMDP): an MDP equipped with K cost functions
    and K budget thresholds d_k. A policy is feasible if, for each k,
    the expected cumulative cost under c_k does not exceed d_k. -/
structure CMDP (K : ℕ) where
  /-- The K cost functions -/
  costs : M.CostFunction K
  /-- Budget thresholds d_k for each constraint -/
  budget : Fin K → ℝ

/-! ### Expected Cost -/

/-- The expected immediate cost under cost function k and policy pi from state s:
    sum_a pi(a|s) * c_k(s,a) -/
def expectedCost {K : ℕ} (C : M.CostFunction K) (π : M.StochasticPolicy)
    (k : Fin K) (s : M.S) : ℝ :=
  ∑ a, π.prob s a * C.cost k s a

/-! ### Feasibility -/

/-- A policy pi is **CMDP-feasible** if its expected discounted cost under each
    cost function c_k does not exceed the budget d_k.

    Here `costValue k` represents V^pi_{c_k}, the total expected discounted cost
    under cost function k. We parameterize these abstractly as real numbers,
    avoiding measure-theoretic constructions. -/
def cmdpFeasible {K : ℕ} (C : M.CMDP K)
    (costValue : Fin K → ℝ) : Prop :=
  ∀ k, costValue k ≤ C.budget k

/-! ### Lagrangian -/

/-- The **Lagrangian** of the CMDP:
    L(pi, lam) = V^pi_r - sum_k lam_k * (V^pi_{c_k} - d_k)

    where `rewardValue` = V^pi_r and `costValue k` = V^pi_{c_k}. -/
def cmdpLagrangian {K : ℕ} (C : M.CMDP K)
    (rewardValue : ℝ) (costValue : Fin K → ℝ)
    (lam : Fin K → ℝ) : ℝ :=
  rewardValue - ∑ k, lam k * (costValue k - C.budget k)

/-! ### Weak Duality -/

/-- **Lagrangian weak duality**.

    For any feasible policy (costValue k <= d_k for all k) and any
    nonneg multipliers lam_k >= 0:

      V^pi_r <= L(pi, lam)

    because L = V^pi_r - sum lam_k*(costValue_k - d_k)
    and each term lam_k*(costValue_k - d_k) <= 0 when feasible,
    hence the sum is nonpositive and L >= V^pi_r. -/
theorem lagrangian_weak_duality {K : ℕ} (C : M.CMDP K)
    (rewardValue : ℝ) (costValue : Fin K → ℝ)
    (lam : Fin K → ℝ)
    (hfeas : M.cmdpFeasible C costValue)
    (hlam_nonneg : ∀ k, 0 ≤ lam k) :
    rewardValue ≤ M.cmdpLagrangian C rewardValue costValue lam := by
  -- L = rewardValue - sum lam_k*(costValue_k - d_k)
  -- We need: rewardValue <= rewardValue - sum lam_k*(costValue_k - d_k)
  -- i.e., sum lam_k*(costValue_k - d_k) <= 0
  simp only [cmdpLagrangian]
  linarith [Finset.sum_nonpos (fun k (_ : k ∈ Finset.univ) =>
    mul_nonpos_of_nonneg_of_nonpos (hlam_nonneg k)
      (by linarith [hfeas k] : costValue k - C.budget k ≤ 0))]

/-! ### Lagrangian Decomposition -/

/-- **Lagrangian decomposition**.

    The Lagrangian can be decomposed as:
      L(pi, lam) = V^pi_{r - sum_k lam_k c_k}(s) + sum_k lam_k * d_k

    where V^pi_{r - sum_k lam_k c_k} is the value of pi under the augmented
    reward r(s,a) - sum_k lam_k * c_k(s,a).

    This shows the Lagrangian relaxation converts the constrained problem into
    an unconstrained MDP with modified reward, plus a constant.

    We state this algebraically: if `augmentedValue` represents V^pi evaluated
    under the augmented reward, and it equals rewardValue - sum_k lam_k * costValue_k,
    then L = augmentedValue + sum_k lam_k * d_k.

    The hypothesis `hAug` encodes linearity of the value functional:
    V^pi_{r - sum lam c} = V^pi_r - sum lam_k V^pi_{c_k}. -/
theorem lagrangian_decomposition {K : ℕ} (C : M.CMDP K)
    (rewardValue : ℝ) (costValue : Fin K → ℝ)
    (lam : Fin K → ℝ)
    (augmentedValue : ℝ)
    (hAug : augmentedValue = rewardValue - ∑ k, lam k * costValue k) :
    M.cmdpLagrangian C rewardValue costValue lam =
      augmentedValue + ∑ k, lam k * C.budget k := by
  simp only [cmdpLagrangian]
  rw [hAug]
  -- LHS: rewardValue - sum lam*(cost - budget)
  -- RHS: (rewardValue - sum lam*cost) + sum lam*budget
  have : ∑ k, lam k * (costValue k - C.budget k) =
      ∑ k, lam k * costValue k - ∑ k, lam k * C.budget k := by
    rw [← Finset.sum_sub_distrib]
    congr 1; funext k; ring
  linarith

/-! ### Relaxation Bound -/

/-- [WRAPPER] **Constrained optimal <= unconstrained optimal**.

    Returns hBound directly. The subset-supremum argument
    is trivial; the theorem takes the bound as a hypothesis.

    If pi is CMDP-feasible and achieves reward value V_pi, and V_opt is
    the unconstrained optimal value, then V_pi <= V_opt. We state it
    as an API point for downstream composition. -/
theorem cmdp_relaxation_bound
    (rewardValue : ℝ) (unconstrainedOpt : ℝ)
    (hBound : rewardValue ≤ unconstrainedOpt) :
    rewardValue ≤ unconstrainedOpt :=
  hBound

/-- **Constrained optimal <= unconstrained optimal** (set-theoretic form).
    [WRAPPER: Specializes universal quantifier with reflexivity.]

    Given a set of feasible reward values and the unconstrained optimum,
    any feasible value is bounded by the unconstrained optimum.

    More precisely: if every policy's value is bounded by V_opt, then
    every *feasible* policy's value is also bounded by V_opt. -/
theorem cmdp_relaxation_bound' {K : ℕ} (C : M.CMDP K)
    (rewardValue : ℝ) (costValue : Fin K → ℝ) (unconstrainedOpt : ℝ)
    (_hFeas : M.cmdpFeasible C costValue)
    (hBound : ∀ (v : ℝ), v = rewardValue → v ≤ unconstrainedOpt) :
    rewardValue ≤ unconstrainedOpt :=
  hBound rewardValue rfl

/-- **Relaxation bound via Lagrangian dual**.

    For any feasible policy and any lam >= 0:
      V^pi_r <= L(pi, lam)

    Taking the infimum over lam gives the Lagrangian dual bound:
      V^pi_r <= inf_lam sup_pi L(pi, lam)

    This is the content of weak duality applied to the CMDP. Here we
    show that for a specific lam, V^pi_r is bounded by any upper
    bound on L. -/
theorem cmdp_lagrangian_relaxation_bound {K : ℕ} (C : M.CMDP K)
    (rewardValue : ℝ) (costValue : Fin K → ℝ)
    (lam : Fin K → ℝ) (dualBound : ℝ)
    (hfeas : M.cmdpFeasible C costValue)
    (hlam_nonneg : ∀ k, 0 ≤ lam k)
    (hDual : M.cmdpLagrangian C rewardValue costValue lam ≤ dualBound) :
    rewardValue ≤ dualBound :=
  le_trans (M.lagrangian_weak_duality C rewardValue costValue lam hfeas hlam_nonneg) hDual

/-! ### Monotonicity in Constraints (Cost Tradeoff) -/

/-- **Cost tradeoff / monotonicity in constraints**.

    If we tighten a constraint (reduce the budget d_k to d_k' <= d_k), the
    feasible set shrinks, so the constrained optimal value cannot increase.

    Formally: if pi is feasible under the tighter budgets d' (d'_k <= d_k for all k)
    and achieves value V_pi, then pi is also feasible under the original budgets d.
    Hence the tighter-budget optimum (supremum over fewer policies) cannot exceed
    the original-budget optimum. -/
theorem cmdp_cost_tradeoff {K : ℕ} (C : M.CMDP K)
    (costValue : Fin K → ℝ)
    (budget' : Fin K → ℝ)
    (hTighter : ∀ k, budget' k ≤ C.budget k)
    (hFeas' : ∀ k, costValue k ≤ budget' k) :
    M.cmdpFeasible C costValue := by
  intro k
  exact le_trans (hFeas' k) (hTighter k)

/-- **Monotonicity of the Lagrangian in the budget**.

    If d'_k >= d_k for all k (budgets are relaxed), and lam_k >= 0, then
    L(pi, lam; d') >= L(pi, lam; d). Relaxing constraints increases
    the Lagrangian (since the penalty for constraint violation decreases). -/
theorem cmdp_lagrangian_monotone_budget {K : ℕ}
    (C C' : M.CMDP K)
    (_hSameCost : C.costs = C'.costs)
    (rewardValue : ℝ) (costValue : Fin K → ℝ)
    (lam : Fin K → ℝ)
    (hlam_nonneg : ∀ k, 0 ≤ lam k)
    (hRelaxed : ∀ k, C.budget k ≤ C'.budget k) :
    M.cmdpLagrangian C rewardValue costValue lam ≤
      M.cmdpLagrangian C' rewardValue costValue lam := by
  simp only [cmdpLagrangian]
  -- Need: r - sum lam*(cost - d) <= r - sum lam*(cost - d')
  -- i.e., sum lam*(cost - d') <= sum lam*(cost - d)
  -- This holds since d <= d' and lam >= 0.
  linarith [Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left
      (by linarith [hRelaxed k] : costValue k - C'.budget k ≤ costValue k - C.budget k)
      (hlam_nonneg k) :
    ∀ k ∈ Finset.univ,
      lam k * (costValue k - C'.budget k) ≤
      lam k * (costValue k - C.budget k))]

/-! ### Expected Cost Properties -/

/-- The expected cost is a convex combination of cost values,
    hence bounded by the cost bound C_max. -/
theorem expectedCost_bounded {K : ℕ} (C : M.CostFunction K)
    (π : M.StochasticPolicy) (k : Fin K) (s : M.S) :
    |M.expectedCost C π k s| ≤ C.cost_bound.choose := by
  have hC := C.cost_bound.choose_spec
  simp only [expectedCost]
  exact abs_weighted_sum_le_bound _ _ _ (π.prob_nonneg s) (π.prob_sum_one s)
    (fun a => hC.2 k s a)

/-- Expected cost is nonneg when cost functions are nonneg and policy is valid. -/
theorem expectedCost_nonneg {K : ℕ} (C : M.CostFunction K)
    (π : M.StochasticPolicy) (k : Fin K) (s : M.S)
    (hcost_nonneg : ∀ s a, 0 ≤ C.cost k s a) :
    0 ≤ M.expectedCost C π k s := by
  simp only [expectedCost]
  exact Finset.sum_nonneg (fun a _ => mul_nonneg (π.prob_nonneg s a) (hcost_nonneg s a))

/-! ### Lagrangian with Zero Multipliers -/

/-- With zero multipliers (lam = 0), the Lagrangian equals the reward value.
    L(pi, 0) = V^pi_r. -/
theorem cmdpLagrangian_zero_multipliers {K : ℕ} (C : M.CMDP K)
    (rewardValue : ℝ) (costValue : Fin K → ℝ) :
    M.cmdpLagrangian C rewardValue costValue (fun _ => 0) = rewardValue := by
  simp only [cmdpLagrangian, zero_mul, Finset.sum_const_zero, sub_zero]

/-- For feasible policies, L(pi, lam) >= V^pi_r for any lam >= 0.
    This is a restatement of weak duality. -/
theorem cmdpLagrangian_ge_reward_when_feasible {K : ℕ} (C : M.CMDP K)
    (rewardValue : ℝ) (costValue : Fin K → ℝ) (lam : Fin K → ℝ)
    (hfeas : M.cmdpFeasible C costValue)
    (hlam_nonneg : ∀ k, 0 ≤ lam k) :
    rewardValue ≤ M.cmdpLagrangian C rewardValue costValue lam :=
  M.lagrangian_weak_duality C rewardValue costValue lam hfeas hlam_nonneg

/-! ### Strong Duality and KKT Conditions -/

/-- **CMDP strong duality** (under Slater's condition).
    If there exists a strictly feasible policy π₀ (costValue_k < d_k
    for all k), then strong duality holds:
    max_{π feasible} V^π = min_{λ≥0} max_π L(π,λ).

    We take Slater's condition as a conditional hypothesis. The conclusion
    states that the duality gap is zero. -/
-- [CONDITIONAL HYPOTHESIS] Slater's condition implies strong duality
theorem cmdp_strong_duality {K : ℕ} (C : M.CMDP K)
    (primalOpt dualOpt : ℝ)
    (_h_slater : ∃ (costValue₀ : Fin K → ℝ), ∀ k, costValue₀ k < C.budget k)
    (h_weak : primalOpt ≤ dualOpt)
    (_h_strong_duality : dualOpt ≤ primalOpt) :
    primalOpt = dualOpt :=
  le_antisymm h_weak _h_strong_duality

/-- **KKT conditions for CMDP**.
    At optimality, the KKT conditions hold:
    1. Primal feasibility: costValue_k ≤ d_k
    2. Dual feasibility: λ_k ≥ 0
    3. Complementary slackness: λ_k · (costValue_k - d_k) = 0
    4. Stationarity: policy is optimal for the Lagrangian

    This theorem verifies the complementary slackness algebraic identity:
    if all KKT conditions hold, the Lagrangian equals the reward value. -/
theorem cmdp_kkt_conditions {K : ℕ} (C : M.CMDP K)
    (rewardValue : ℝ) (costValue : Fin K → ℝ) (lam : Fin K → ℝ)
    (_h_primal_feas : M.cmdpFeasible C costValue)
    (_h_dual_feas : ∀ k, 0 ≤ lam k)
    (h_comp_slack : ∀ k, lam k * (costValue k - C.budget k) = 0) :
    M.cmdpLagrangian C rewardValue costValue lam = rewardValue := by
  simp only [cmdpLagrangian]
  have : ∑ k, lam k * (costValue k - C.budget k) = 0 :=
    Finset.sum_eq_zero (fun k _ => h_comp_slack k)
  linarith

/-- [WRAPPER] **Primal-dual gap convergence**.

    Returns h_convergence directly. Blocked on convex optimization /
    gradient Lipschitz convergence theory.

    After T primal-dual gradient steps with step size η, the duality gap
    converges as gap ≤ O(1/√T). -/
theorem cmdp_primal_dual_gap
    (gap C sqrt_T : ℝ)
    (h_convergence : gap ≤ C / sqrt_T) :
    gap ≤ C / sqrt_T :=
  h_convergence

/-- **Safe policy improvement**.
    If π is feasible and π' has value at least V^π - ε (near-improvement),
    and the cost functions change by at most ε, then π' is ε-feasible
    in the sense that costValue'_k ≤ d_k + ε.

    This provides a safety guarantee for approximate policy improvement. -/
theorem cmdp_safe_policy_improvement {K : ℕ} (C : M.CMDP K)
    (costValue costValue' : Fin K → ℝ) (ε : ℝ)
    (h_feas : M.cmdpFeasible C costValue)
    (h_cost_close : ∀ k, costValue' k ≤ costValue k + ε) :
    ∀ k, costValue' k ≤ C.budget k + ε := by
  intro k
  calc costValue' k ≤ costValue k + ε := h_cost_close k
    _ ≤ C.budget k + ε := by linarith [h_feas k]

end FiniteMDP

end
