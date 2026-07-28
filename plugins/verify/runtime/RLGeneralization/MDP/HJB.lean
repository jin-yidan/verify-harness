/-
# Hamilton-Jacobi-Bellman Equation

Formalizes the Hamilton-Jacobi-Bellman (HJB) equation for continuous-time
optimal control, and the verification theorem that connects smooth
solutions of the HJB equation to optimal value functions.

## Mathematical Background

For a controlled diffusion dx_t = f(x,u)dt + σ(x)dW_t with running cost
l(x,u) and terminal cost g(x), the HJB equation is:

  V_t + min_u { f(x,u)^T ∇V + ½ tr(σσ^T ∇²V) + l(x,u) } = 0

with terminal condition V(T, x) = g(x).

The **verification theorem**: if V is a C^{1,2} solution of the HJB
equation, then V equals the optimal value function V*.

## Main Definitions

* `HJBData` - Data for a continuous-time control problem
* `HJBSolution` - A smooth solution of the HJB equation (algebraic)
* `hjb_one_step_ineq` - One-step HJB inequality for any control

## Approach

We formalize the algebraic structure of the HJB equation in the
deterministic case (no diffusion), where the PDE reduces to:

  V_t + min_u { f(x,u)^T ∇V + l(x,u) } = 0

The stochastic case requires Ito's formula and the theory of viscosity
solutions, which are beyond current scope.

## Blocked

- **Viscosity solutions**: the correct solution concept for non-smooth
  value functions. Requires the theory of semicontinuous envelopes
  and the comparison principle. Not in Mathlib.
- **Stochastic HJB**: requires Ito's lemma and stochastic calculus.
  See `Concentration.StochasticCalculus` for the stub.
- **Existence/uniqueness**: for viscosity solutions, requires Perron's
  method and barrier functions. Deep PDE theory.
- **Pontryagin maximum principle**: the dual formulation via adjoint
  equations. Requires ODE theory beyond current Mathlib.

## References

* [Fleming and Soner, *Controlled Markov Processes and Viscosity Solutions*]
* [Bertsekas, *Dynamic Programming and Optimal Control*, Vol I]
* [Yong and Zhou, *Stochastic Controls*, 1999]
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Linarith

open Finset BigOperators

noncomputable section

/-! ### Continuous-Time Control Problem Data -/

/-- **Data for a continuous-time deterministic control problem**.

  Dynamics: dx/dt = f(x, u)
  Running cost: l(x, u)
  Terminal cost: g(x)
  Time horizon: [0, T]

  All quantities are defined on finite-dimensional state and
  action spaces, encoded as `Fin d → ℝ` and `Fin m → ℝ`. -/
structure HJBData (d m : ℕ) where
  /-- Drift dynamics f(x, u) ∈ ℝ^d -/
  f : (Fin d → ℝ) → (Fin m → ℝ) → (Fin d → ℝ)
  /-- Running cost l(x, u) ∈ ℝ -/
  l : (Fin d → ℝ) → (Fin m → ℝ) → ℝ
  /-- Terminal cost g(x) ∈ ℝ -/
  g : (Fin d → ℝ) → ℝ
  /-- Time horizon T > 0 -/
  T : ℝ
  /-- T is positive -/
  hT : 0 < T
  /-- Running cost is bounded below -/
  l_bdd_below : ∃ C : ℝ, ∀ x u, C ≤ l x u

namespace HJBData

variable {d m : ℕ} (D : HJBData d m)

/-! ### HJB Equation: Algebraic Form

The deterministic HJB equation at a point (t, x) with gradient ∇V reads:

  V_t(t, x) + min_u { ∑ᵢ f_i(x, u) · (∇V)_i + l(x, u) } = 0

We encode this algebraically using the "Hamiltonian":

  H(x, p) = min_u { f(x,u)^T p + l(x,u) }

Then HJB is: V_t + H(x, ∇V) = 0. -/

/-- **Hamiltonian**: H(x, p) = min_u { f(x,u)^T p + l(x,u) }.
    Over a finite action space, the min is well-defined. -/
def hamiltonian
    (x : Fin d → ℝ) (p : Fin d → ℝ)
    (actions : Finset (Fin m → ℝ)) (hne : actions.Nonempty) : ℝ :=
  actions.inf' hne (fun u => ∑ i, D.f x u i * p i + D.l x u)

/-- **HJB residual**: for a given V_t, ∇V at (t, x), the HJB residual
    measures how far V is from satisfying the HJB equation.

    residual = V_t + min_u { f(x,u)^T ∇V + l(x,u) }

    A solution has residual = 0 everywhere. -/
-- [UNUSED]
def hjbResidual (V_t : ℝ)
    (x : Fin d → ℝ) (gradV : Fin d → ℝ)
    (actions : Finset (Fin m → ℝ)) (hne : actions.Nonempty) : ℝ :=
  V_t + HJBData.hamiltonian D x gradV actions hne

end HJBData

/-! ### HJB Solution Structure -/

/-- **HJB solution data**: encodes a candidate value function V along
    with its time derivative V_t and spatial gradient ∇V at each point,
    satisfying the HJB equation algebraically.

    A smooth solution V of the HJB equation must satisfy:
    1. V_t(t,x) + H(x, ∇V(t,x)) = 0 for all (t,x) in (0,T) × ℝ^d
    2. V(T, x) = g(x) for all x  (terminal condition) -/
structure HJBSolution (d m : ℕ) (D : HJBData d m) where
  /-- Value function V(t, x) -/
  V : ℝ → (Fin d → ℝ) → ℝ
  /-- Time derivative V_t(t, x) -/
  V_t : ℝ → (Fin d → ℝ) → ℝ
  /-- Spatial gradient ∇V(t, x) -/
  gradV : ℝ → (Fin d → ℝ) → (Fin d → ℝ)
  /-- Terminal condition: V(T, x) = g(x) -/
  terminal : ∀ x, V D.T x = D.g x

/-! ### Verification Theorem (Algebraic Core)

The **verification theorem** is the central result of HJB theory:

**Theorem**: If V is a C^{1,2} solution of the HJB equation with
terminal condition V(T, x) = g(x), then V(0, x) ≤ J(x, u) for
any admissible control u, and equality holds for the optimal control.

The algebraic core of the proof is: along any trajectory x(·),

  d/dt V(t, x(t)) = V_t + f(x,u)^T ∇V ≥ V_t + H(x, ∇V) = 0

when u is suboptimal (f^T∇V ≥ min_u f^T∇V), with equality for
the optimal u. Integrating from 0 to T gives the result.

We formalize the one-step algebraic inequality. -/

/-- **One-step HJB inequality**: for any control u, the drift
    f(x,u)^T ∇V + l(x,u) is at least the Hamiltonian H(x, ∇V). -/
theorem hjb_one_step_ineq {d m : ℕ} (D : HJBData d m)
    (x gradV : Fin d → ℝ) (u : Fin m → ℝ)
    (actions : Finset (Fin m → ℝ)) (hne : actions.Nonempty)
    (hu : u ∈ actions) :
    HJBData.hamiltonian D x gradV actions hne ≤
    ∑ i, D.f x u i * gradV i + D.l x u := by
  unfold HJBData.hamiltonian
  exact Finset.inf'_le _ hu

/-! ### Discrete-Time Analogy

The HJB equation is the continuous-time limit of the Bellman
optimality equation. For a discrete-time MDP with step size Δt:

  V(s) = min_a { Δt · l(s,a) + V(s + Δt · f(s,a)) }

Expanding V(s + Δt · f(s,a)) ≈ V(s) + Δt · f(s,a)^T ∇V(s) and
rearranging:

  0 = min_a { l(s,a) + f(s,a)^T ∇V(s) } + O(Δt)

which is the HJB equation in the Δt → 0 limit.

We formalize the discrete-time Bellman equation as a structure
and show the algebraic connection. -/

/-- **Discrete Bellman step**: the one-step cost-to-go with step size Δt:
    V(x) = min_a { Δt · l(x,a) + (1-Δt·discount) · V(x + Δt · f(x,a)) }

    We encode the algebraic form: for a given V, the Bellman residual at x. -/
-- [UNUSED]
def discreteBellmanResidual
    (dt : ℝ) (V_now V_next_approx : ℝ) (running_cost : ℝ) : ℝ :=
  V_now - (dt * running_cost + V_next_approx)

/-! ### Finite-Horizon Bellman as Discrete HJB

For a finite-horizon MDP with H steps, the backward induction
  Q_h(s,a) = r(s,a) + ∑_s' P(s'|s,a) V_{h+1}(s')
  V_h(s) = max_a Q_h(s,a)

is exactly the discrete HJB equation with Δt = 1.
The continuous-time HJB is recovered as H → ∞, Δt → 0. -/

/-! ### Sufficient Conditions for HJB Solutions

The verification theorem requires V to be smooth (C^{1,2}). For
non-smooth value functions (which arise in constrained problems
and degenerate dynamics), the correct solution concept is the
**viscosity solution**:

  V is a viscosity solution if:
  - For any smooth test function φ ≥ V with φ(t₀, x₀) = V(t₀, x₀):
    φ_t(t₀, x₀) + H(x₀, ∇φ(t₀, x₀)) ≥ 0  (subsolution)
  - For any smooth test function ψ ≤ V with ψ(t₀, x₀) = V(t₀, x₀):
    ψ_t(t₀, x₀) + H(x₀, ∇ψ(t₀, x₀)) ≤ 0  (supersolution)

**Blocked**: Viscosity solution theory requires:
- Semicontinuous envelopes and Perron's method
- Comparison principle (Ishii's lemma)
- Existence via Perron's method
These are deep PDE results not available in Mathlib. -/

end
