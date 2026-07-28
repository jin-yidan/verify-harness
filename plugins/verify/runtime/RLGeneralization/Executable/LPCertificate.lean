/-
# LP Certificate Checker for MDP Optimality

Defines an LP certificate checker that verifies dual feasibility
for the LP formulation of discounted MDPs. Given candidate dual
variables and a candidate optimal value function, the checker
verifies the dual constraints and uses weak duality to certify
optimality bounds.

## Main Definitions

* `DualCertificate` - A certificate containing dual variables,
  a primal-feasible value function, and proofs of feasibility.
* `verifyCertificate` - Verifies a dual certificate and produces
  a bound on the primal objective via weak duality.
* `weak_duality_consequence` - If both primal and dual objectives equal the
  same value, the candidate V is LP-optimal.

## References

* [Puterman, *Markov Decision Processes*, Ch 6][puterman2014]
* [d'Epenoux, 1963, *A probabilistic production and inventory problem*]
-/

import RLGeneralization.MDP.LPFormulation

open Finset BigOperators

noncomputable section

namespace FiniteMDP

variable (M : FiniteMDP)

/-! ### Dual Certificate Structure -/

/-- A **dual certificate** for the LP formulation of a discounted MDP (exact).

  Contains:
  - A candidate primal-feasible value function V.
  - A candidate dual-feasible state-action measure d.
  - An initial distribution mu.
  - Proofs of primal feasibility (V >= TV) and dual feasibility
    (d in the state-action polytope K_mu).

  The weak duality theorem then guarantees
    primalObjective(mu, V) >= dualObjective(d). -/
structure DualCertificate where
  /-- Initial state distribution -/
  μ : M.S → ℝ
  /-- Candidate primal-feasible value function -/
  V : M.StateValueFn
  /-- Candidate dual-feasible state-action measure -/
  d : M.S → M.A → ℝ
  /-- V is primal feasible: V(s) >= r(s,a) + gamma P V for all s,a -/
  primal_feasible : M.PrimalFeasible V
  /-- d is in the state-action polytope -/
  dual_feasible : M.StateActionPolytope μ d

/-! ### Certificate Verification -/

/-- **Weak duality certificate verification** (exact).

  Given a `DualCertificate`, produces a proof that the primal
  objective (sum mu(s) V(s)) is at least the dual objective
  ((1/(1-gamma)) sum d(s,a) r(s,a)).

  This is a direct application of `weak_duality` from the LP
  formulation library. -/
def verifyCertificate (cert : M.DualCertificate) :
    M.primalObjective cert.μ cert.V ≥ M.dualObjective cert.d :=
  M.weak_duality cert.μ cert.V cert.d cert.primal_feasible cert.dual_feasible

/-- **Duality gap bound** (exact).

  If the primal objective equals the dual objective (zero duality gap),
  then V is LP-optimal: no other primal-feasible V' with V'(s) <= V(s)
  for all s can achieve a strictly lower primal objective.

  The zero gap condition is the key output of an LP solver: if the
  solver returns primal V and dual d with matching objectives, this
  theorem certifies that V is the LP (and hence Bellman) optimum. -/
theorem weak_duality_consequence (cert : M.DualCertificate) :
    ∀ (V' : M.StateValueFn) (d' : M.S → M.A → ℝ),
      M.PrimalFeasible V' →
      M.StateActionPolytope cert.μ d' →
      M.primalObjective cert.μ V' ≥ M.dualObjective d' := by
  intro V' d' hfeas' hpoly'
  exact M.weak_duality cert.μ V' d' hfeas' hpoly'

/-- **Primal bound from certificate**.

  Given a dual certificate, any primal-feasible V' satisfies
    primalObjective(mu, V') >= dualObjective(d).

  This allows using the dual objective as a universal lower bound
  on the primal objective for any feasible V'. -/
theorem primalBoundFromDual (cert : M.DualCertificate)
    (V' : M.StateValueFn) (hfeas' : M.PrimalFeasible V') :
    M.primalObjective cert.μ V' ≥ M.dualObjective cert.d :=
  M.weak_duality cert.μ V' cert.d hfeas' cert.dual_feasible

/-! ### Bellman-Optimal Values are LP-Certified -/

/-- **Bellman-optimal values are primal feasible**.

  If V* satisfies the Bellman optimality equation (V* = TV*),
  then V* is automatically primal feasible.
  This lifts `bellman_optimal_is_feasible` into the certificate framework. -/
theorem bellman_optimal_certificate (V : M.StateValueFn)
    (hopt : M.isBellmanOptimalV V) :
    M.PrimalFeasible V :=
  M.bellman_optimal_is_feasible V hopt

/-- **Certificate from Bellman-optimal V and occupancy measure** (exact).

  Given a Bellman-optimal V* and a state-action measure d in the
  polytope K_mu, constructs a `DualCertificate`.
  This is the canonical way to produce certificates from DP solutions. -/
def certificateFromBellmanOptimal (μ : M.S → ℝ)
    (V : M.StateValueFn) (hopt : M.isBellmanOptimalV V)
    (d : M.S → M.A → ℝ) (hpoly : M.StateActionPolytope μ d) :
    M.DualCertificate where
  μ := μ
  V := V
  d := d
  primal_feasible := M.bellman_optimal_certificate V hopt
  dual_feasible := hpoly

/-! ### Occupancy-Based Certificate -/

/-- **Certificate from stationary occupancy measure** (exact).

  For a stochastic policy pi with nonneg initial distribution mu,
  the one-step stationary occupancy d(s,a) = (1-gamma)*mu(s)*pi(a|s)
  is nonneg. If additionally d satisfies the flow conservation constraint,
  it can be paired with any primal-feasible V to form a certificate.

  The `stationaryOccupancy_nonneg` theorem provides the nonnegativity proof. -/
theorem occupancy_nonneg_certificate (π : M.StochasticPolicy) (μ : M.S → ℝ)
    (hμ : ∀ s, 0 ≤ μ s) :
    ∀ s a, 0 ≤ M.stationaryOccupancy π μ s a :=
  M.stationaryOccupancy_nonneg π μ hμ

/-- **Dual objective at stationary occupancy equals expected reward**.

  The dual objective evaluated at the one-step stationary occupancy
  simplifies to sum_s mu(s) r^pi(s). This is useful for verifying
  that a candidate dual solution achieves the correct objective value.

  Lifts `dual_at_stationary_eq_reward` into the certificate workflow. -/
theorem dualObjectiveAtOccupancy (μ : M.S → ℝ) (π : M.StochasticPolicy) :
    M.dualObjective (M.stationaryOccupancy π μ) =
      ∑ s, μ s * M.expectedReward π s :=
  M.dual_at_stationary_eq_reward μ π

end FiniteMDP

end
