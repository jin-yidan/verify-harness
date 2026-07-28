/-
# Linear Quadratic Regulator (LQR)

Formalizes basic linear-quadratic regulator infrastructure: quadratic
costs, Riccati solutions, and the closed-loop Bellman identity wrapper.

## Main Definitions

* `LQRInstance` - An LQR problem with dynamics x_{t+1} = Ax + Bu + w,
    cost x^T Q x + u^T R u
* `RiccatiSolution` - A solution P to the discrete algebraic Riccati equation

## References

* [Agarwal et al., *RL: Theory and Algorithms*]
* [Anderson and Moore, *Optimal Control*, 1990]
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open Matrix

noncomputable section

/-! ### LQR Instance -/

/-- A discrete-time Linear Quadratic Regulator instance.

  Dynamics: x_{t+1} = A * x_t + B * u_t + w_t
  Stage cost: c(x, u) = x^T Q x + u^T R u

  where A in R^{n x n}, B in R^{n x m}.
  Positive-semidefiniteness of Q and positive-definiteness of R are
  encoded directly via quadratic form conditions on dotProduct. -/
structure LQRInstance (n m : Nat) where
  /-- State dynamics matrix A in R^{n x n} -/
  A : Matrix (Fin n) (Fin n) Real
  /-- Control input matrix B in R^{n x m} -/
  B : Matrix (Fin n) (Fin m) Real
  /-- State cost matrix Q in R^{n x n}, Q >= 0 -/
  Q : Matrix (Fin n) (Fin n) Real
  /-- Control cost matrix R in R^{m x m}, R > 0 -/
  R : Matrix (Fin m) (Fin m) Real
  /-- Q is positive semidefinite: x^T Q x >= 0 for all x -/
  Q_psd : forall x : Fin n -> Real, 0 <= dotProduct x (Q.mulVec x)
  /-- R is positive definite: x^T R x > 0 for all nonzero x -/
  R_pd : forall x : Fin m -> Real, x ≠ 0 -> 0 < dotProduct x (R.mulVec x)

namespace LQRInstance

variable {n m : Nat} (L : LQRInstance n m)

/-! ### Stage Cost -/

/-- The stage cost `c(x, u) = x^T Q x + u^T R u`. -/
def stageCost (x : Fin n -> Real) (u : Fin m -> Real) : Real :=
  dotProduct x (L.Q.mulVec x) + dotProduct u (L.R.mulVec u)

/-- Stage cost is nonnegative, since `Q >= 0` and `R > 0`. -/
theorem stageCost_nonneg (x : Fin n -> Real) (u : Fin m -> Real) :
    0 <= L.stageCost x u := by
  unfold stageCost
  apply add_nonneg (L.Q_psd x)
  by_cases hu : u = 0
  · subst hu; simp [dotProduct, mulVec]
  · exact le_of_lt (L.R_pd u hu)

/-! ### Discrete Algebraic Riccati Equation

  The optimal value function V*(x) = x^T P x where P solves the
  discrete algebraic Riccati equation (DARE):

    P = Q + A^T P A - A^T P B (R + B^T P B)^{-1} B^T P A

  The optimal control gain is:
    K* = -(R + B^T P B)^{-1} B^T P A
  giving the optimal policy u* = K* x. -/

/-- A solution to the discrete algebraic Riccati equation.
    P satisfies: P = Q + A^T P A - A^T P B (R + B^T P B)^{-1} B^T P A -/
structure RiccatiSolution where
  /-- The solution matrix P in R^{n x n} -/
  P : Matrix (Fin n) (Fin n) Real
  /-- P is positive semidefinite -/
  P_psd : forall x : Fin n -> Real, 0 <= dotProduct x (P.mulVec x)
  /-- P satisfies the DARE -/
  riccati_eq : P = L.Q + L.A.transpose * P * L.A -
    L.A.transpose * P * L.B *
      (L.R + L.B.transpose * P * L.B)⁻¹ *
      (L.B.transpose * P * L.A)

/-- The optimal control gain `K* = -(R + B^T P B)^{-1} B^T P A`. -/
def optimalGain (sol : L.RiccatiSolution) :
    Matrix (Fin m) (Fin n) Real :=
  -((L.R + L.B.transpose * sol.P * L.B)⁻¹ *
    (L.B.transpose * sol.P * L.A))

end LQRInstance

end
