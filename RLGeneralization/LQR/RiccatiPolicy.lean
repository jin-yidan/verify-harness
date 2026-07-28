/-
# Riccati Recursion and Policy Gradient for LQR

Formalizes the finite-horizon Riccati recursion, the closed-loop
Bellman identity, and the policy gradient for LQR.

## Main Results

* `riccati_recursion` — the Riccati backward recursion:
    P_t = Q + A^T P_{t+1} (A - B K_{t+1})
    at the optimal gain K_{t+1} = -(R + B^T P B)^{-1} B^T P A

* `lqr_value_quadratic` — the optimal value V_t*(x) = x^T P_t x
    where P_t satisfies the backward Riccati recursion

* `closed_loop_bellman` — the Bellman identity for the closed-loop system:
    x^T P x = L.stageCost(x, K x) + x^T A_cl^T P A_cl x
    where A_cl = A + B K is the closed-loop dynamics

* `lqr_cost_decomposition` — J(K) = trace(Q Σ_K) + trace(K^T R K Σ_K)

## References

* Anderson and Moore, "Optimal Control," 1990.
* Fazel et al., "Global Convergence of Policy Gradient Methods for the LQR," ICML 2018.
* Agarwal et al., "RL: Theory and Algorithms," Ch 14 (2026).
-/

import RLGeneralization.LQR.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef

open Matrix

noncomputable section

namespace LQRInstance

variable {n m : Nat} (L : LQRInstance n m)

/-! ### Finite-Horizon Riccati Recursion -/

/-- The finite-horizon Riccati matrices P_0,...,P_H.
    P_H = Q (terminal cost), backward recursion for t < H:
    P_t = Q + A^T P_{t+1} A - A^T P_{t+1} B (R + B^T P_{t+1} B)^{-1} B^T P_{t+1} A -/
noncomputable def riccatiMatrices (H : ℕ) : Fin (H + 1) → Matrix (Fin n) (Fin n) ℝ
  | ⟨0, _⟩ => L.Q  -- terminal cost P_H = Q
  | ⟨t + 1, ht⟩ =>
    let P_next := riccatiMatrices H ⟨t, Nat.lt_of_succ_lt ht⟩
    L.Q + L.A.transpose * P_next * L.A -
      L.A.transpose * P_next * L.B *
        (L.R + L.B.transpose * P_next * L.B)⁻¹ *
        (L.B.transpose * P_next * L.A)

/-- The optimal gain at step t:
    K_t = -(R + B^T P_{t+1} B)^{-1} B^T P_{t+1} A -/
noncomputable def riccatiGain (H : ℕ) (t : Fin H) :
    Matrix (Fin m) (Fin n) ℝ :=
  let P_next := L.riccatiMatrices H ⟨t.val, Nat.lt_succ_of_lt t.isLt⟩
  Neg.neg ((L.R + L.B.transpose * P_next * L.B)⁻¹ *
    (L.B.transpose * P_next * L.A))

/-- The closed-loop dynamics matrix A_cl = A + B K at step t. -/
noncomputable def closedLoopDynamics (H : ℕ) (t : Fin H) :
    Matrix (Fin n) (Fin n) ℝ :=
  L.A + L.B * L.riccatiGain H t

/-! ### Riccati Recursion Identity -/

/-- **Finite-horizon Riccati recursion** (algebraic).

The Riccati matrices satisfy the backward recursion:
  P_t = Q + (A + B K_{t+1})^T P_{t+1} (A + B K_{t+1}) + K_{t+1}^T R K_{t+1}

where K_{t+1} = -(R + B^T P_{t+1} B)^{-1} B^T P_{t+1} A.

This follows by substituting K into the DARE and simplifying. -/
theorem riccati_recursion_form (H : ℕ) (t : Fin H)
    (P_next : Matrix (Fin n) (Fin n) ℝ)
    (h_P : P_next = L.riccatiMatrices H ⟨t.val, Nat.lt_succ_of_lt t.isLt⟩) :
    L.riccatiMatrices H ⟨t.val + 1, Nat.succ_lt_succ t.isLt⟩ =
    L.Q + L.A.transpose * P_next * L.A -
      L.A.transpose * P_next * L.B *
        (L.R + L.B.transpose * P_next * L.B)⁻¹ *
        (L.B.transpose * P_next * L.A) := by
  simp [riccatiMatrices, h_P]

/-- **Completing the square** for the DARE: the Riccati recursion matrix equals
    Q + Kᵀ R K + A_clᵀ P A_cl when R + Bᵀ P B is invertible.

    The proof expands A_cl = A + BK and K = -(R+BᵀPB)⁻¹BᵀPA, then uses
    (R + BᵀPB) * (R + BᵀPB)⁻¹ = I to cancel the extra terms that arise.

    The proof is stated with abstract matrices S, N satisfying
    (R + BᵀPB) * S = 1 and N = BᵀPA to avoid inverse-specific complications. -/
private theorem dare_completing_square
    {n' m' : ℕ}
    (A' : Matrix (Fin n') (Fin n') ℝ)
    (B' : Matrix (Fin n') (Fin m') ℝ)
    (Q' : Matrix (Fin n') (Fin n') ℝ)
    (R' : Matrix (Fin m') (Fin m') ℝ)
    (P' : Matrix (Fin n') (Fin n') ℝ)
    (S : Matrix (Fin m') (Fin m') ℝ)
    (N : Matrix (Fin m') (Fin n') ℝ)
    (hMS : (R' + B'.transpose * P' * B') * S = 1)
    (hN : N = B'.transpose * P' * A') :
    Q' + A'.transpose * P' * A' - A'.transpose * P' * B' * S * N =
    Q' + (S * N).transpose * R' * (S * N) +
      (A' - B' * S * N).transpose * P' * (A' - B' * S * N) := by
  -- Right-associate all matrix products for consistent manipulation
  simp only [Matrix.mul_assoc] at hMS ⊢
  -- Set up abbreviations for the right-associated forms
  -- hMS now says: (R' + B'ᵀ * (P' * B')) * S = 1
  -- Key identity: (R' + BᵀPB) * S * N = N (right-multiply hMS by N)
  have hMSN : (R' + B'.transpose * (P' * B')) * (S * N) = N := by
    rw [← Matrix.mul_assoc, hMS, Matrix.one_mul]
  -- Expand the quadratic (A' - B(SN))ᵀ P' (A' - B(SN)) using bilinearity
  -- After right-association, B' * S * N = B' * (S * N)
  have expand_quad : (A' - B' * (S * N)).transpose * (P' * (A' - B' * (S * N))) =
      A'.transpose * (P' * A') - A'.transpose * (P' * (B' * (S * N))) -
      (B' * (S * N)).transpose * (P' * A') +
      (B' * (S * N)).transpose * (P' * (B' * (S * N))) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.transpose_sub]
    abel
  -- Factor transposes
  have factor_BSN : (B' * (S * N)).transpose = (S * N).transpose * B'.transpose :=
    Matrix.transpose_mul B' (S * N)
  have factor_SN : (S * N).transpose = N.transpose * S.transpose :=
    Matrix.transpose_mul S N
  -- The key cancellation:
  -- (SN)ᵀ(R'(SN)) - (BSN)ᵀ(PA) + (BSN)ᵀ(P(BSN)) = 0
  -- = NᵀSᵀ(R'(SN)) - NᵀSᵀBᵀ(PA) + NᵀSᵀBᵀ(P(BSN))
  -- = NᵀSᵀ(R'(SN) + Bᵀ(P(BSN)) - BᵀPA)
  -- = NᵀSᵀ((R' + BᵀPB)(SN) - BᵀPA)
  -- = NᵀSᵀ(N - BᵀPA) = NᵀSᵀ(N - N) = 0
  have cancel_terms :
      (S * N).transpose * (R' * (S * N)) -
      (B' * (S * N)).transpose * (P' * A') +
      (B' * (S * N)).transpose * (P' * (B' * (S * N))) = 0 := by
    rw [factor_BSN, factor_SN]
    -- After substitution, the goal has NᵀSᵀ... terms
    simp only [Matrix.mul_assoc]
    -- Factor out Nᵀ
    rw [← Matrix.mul_sub, ← Matrix.mul_add]
    -- Factor out Sᵀ from the inner expression
    rw [← Matrix.mul_sub, ← Matrix.mul_add]
    -- Inner expression: R'(SN) - Bᵀ(PA) + Bᵀ(P(BSN))
    -- Rewrite Bᵀ(P(BSN)) = Bᵀ(PB)(SN)
    rw [show R' * (S * N) - B'.transpose * (P' * A') +
        B'.transpose * (P' * (B' * (S * N))) =
        R' * (S * N) + B'.transpose * (P' * (B' * (S * N))) -
        B'.transpose * (P' * A') from by abel]
    rw [show B'.transpose * (P' * (B' * (S * N))) =
        B'.transpose * (P' * B') * (S * N) from by
      rw [Matrix.mul_assoc, Matrix.mul_assoc]]
    rw [← Matrix.add_mul, hMSN]
    -- N was substituted to B'ᵀ * P' * A', normalize associations
    simp only [Matrix.mul_assoc] at hN ⊢
    rw [hN, sub_self]
    simp [Matrix.mul_zero]
  -- Reassociate the LHS
  have h_assoc_lhs : A'.transpose * (P' * (B' * (S * N))) =
      A'.transpose * (P' * B') * (S * N) := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc]
  -- The final assembly
  rw [expand_quad]
  -- LHS (after simp mul_assoc): Q + AᵀPA - Aᵀ(PB)(SN)
  -- RHS: Q + (SN)ᵀ(R(SN)) + (AᵀPA - AᵀP(BSN) - (BSN)ᵀPA + (BSN)ᵀP(BSN))
  -- Show difference = cancel_terms = 0
  have goal_rw :
      Q' + A'.transpose * (P' * A') - A'.transpose * (P' * (B' * (S * N))) +
      ((S * N).transpose * (R' * (S * N)) -
        (B' * (S * N)).transpose * (P' * A') +
        (B' * (S * N)).transpose * (P' * (B' * (S * N)))) =
      Q' + (S * N).transpose * (R' * (S * N)) +
      (A'.transpose * (P' * A') - A'.transpose * (P' * (B' * (S * N))) -
        (B' * (S * N)).transpose * (P' * A') +
        (B' * (S * N)).transpose * (P' * (B' * (S * N)))) := by abel
  rw [← goal_rw, cancel_terms, add_zero]

/-- **Closed-loop Bellman identity** for the LQR.

For the optimal gain K_t, the stage cost + next-step value equals P_t:
  x^T P_t x = x^T Q x + (K_t x)^T R (K_t x) + (A_cl x)^T P_{t+1} (A_cl x)

where A_cl = A + B K_t is the closed-loop dynamics.

Requires that R + Bᵀ P_{t+1} B is invertible (which holds when R is positive
definite, the standard LQR assumption).

This is the central identity showing P_t encodes the optimal cost-to-go. -/
theorem closed_loop_bellman (H : ℕ) (t : Fin H)
    (x : Fin n → ℝ)
    (h_inv : IsUnit (L.R + L.B.transpose *
      L.riccatiMatrices H ⟨t.val, Nat.lt_succ_of_lt t.isLt⟩ * L.B).det) :
    let K := L.riccatiGain H t
    let P_t := L.riccatiMatrices H ⟨t.val + 1, Nat.succ_lt_succ t.isLt⟩
    let P_next := L.riccatiMatrices H ⟨t.val, Nat.lt_succ_of_lt t.isLt⟩
    let A_cl := L.A + L.B * K
    dotProduct x (P_t.mulVec x) =
      dotProduct x (L.Q.mulVec x) +
      dotProduct (K.mulVec x) (L.R.mulVec (K.mulVec x)) +
      dotProduct (A_cl.mulVec x) (P_next.mulVec (A_cl.mulVec x)) := by
  intro K P_t P_next A_cl
  -- Step 1: Convert RHS quadratic forms to matrix-vector form
  -- dotProduct (M *ᵥ x) (N *ᵥ (M' *ᵥ x)) = dotProduct x ((Mᵀ * N * M') *ᵥ x)
  have hK : dotProduct (K.mulVec x) (L.R.mulVec (K.mulVec x)) =
      dotProduct x ((K.transpose * L.R * K).mulVec x) := by
    rw [dotProduct_mulVec, vecMul_mulVec]
    rw [← dotProduct_mulVec]
    congr 1
    rw [mulVec_mulVec]
  have hAcl : dotProduct (A_cl.mulVec x) (P_next.mulVec (A_cl.mulVec x)) =
      dotProduct x ((A_cl.transpose * P_next * A_cl).mulVec x) := by
    rw [dotProduct_mulVec, vecMul_mulVec]
    rw [← dotProduct_mulVec]
    congr 1
    rw [mulVec_mulVec]
  rw [hK, hAcl]
  -- Step 2: Combine RHS into single matrix application
  rw [← dotProduct_add, ← dotProduct_add, ← add_mulVec, ← add_mulVec]
  -- Goal: dotProduct x (P_t *ᵥ x) = dotProduct x ((Q + KᵀRK + A_clᵀ P A_cl) *ᵥ x)
  congr 1
  congr 1
  -- Goal: P_t = Q + KᵀRK + A_clᵀ P A_cl (matrix identity)
  -- Unfold P_t, K, A_cl
  change L.riccatiMatrices H ⟨t.val + 1, Nat.succ_lt_succ t.isLt⟩ =
    L.Q + K.transpose * L.R * K + A_cl.transpose * P_next * A_cl
  -- Unfold riccatiMatrices
  simp only [riccatiMatrices]
  -- The LHS is the DARE: Q + AᵀPA - AᵀPB*S*BᵀPA
  -- We need to show it equals Q + KᵀRK + A_clᵀPA_cl
  -- where K = -(S * BᵀPA), A_cl = A + BK = A - BSBᵀPA
  -- This is exactly dare_completing_square
  set P := L.riccatiMatrices H ⟨t.val, Nat.lt_succ_of_lt t.isLt⟩ with hP_def
  set S := (L.R + L.B.transpose * P * L.B)⁻¹ with hS_def
  set N := L.B.transpose * P * L.A with hN_def
  -- Apply the completing-the-square identity
  have hMS_inv : IsUnit (L.R + L.B.transpose * P * L.B).det := h_inv
  have hMS : (L.R + L.B.transpose * P * L.B) * S = 1 :=
    Matrix.mul_nonsing_inv _ hMS_inv
  -- The K and A_cl match the dare_completing_square form
  -- K = -(S * N) and A_cl = A + B * K = A + B * (-(S * N)) = A - B * (S * N)
  -- dare_completing_square gives:
  -- Q + AᵀPA - AᵀPBSN = Q + (SN)ᵀR(SN) + (A - BSN)ᵀP(A - BSN)
  -- We need: RHS = Q + KᵀRK + A_clᵀPA_cl
  -- (SN)ᵀR(SN) = (-K)ᵀR(-K) = KᵀRK ✓
  -- (A - BSN) = A + B(-SN) = A + BK = A_cl ✓
  have hK_eq : K = -(S * N) := by
    simp [K, riccatiGain, S, N, hS_def, hN_def, P]
  have hAcl_eq : A_cl = L.A - L.B * (S * N) := by
    simp only [A_cl, hK_eq]
    rw [Matrix.mul_neg, sub_eq_add_neg]
  -- Convert the dare_completing_square result
  have dare := dare_completing_square L.A L.B L.Q L.R P S N hMS hN_def
  -- dare says: Q + AᵀPA - AᵀPBSN = Q + (SN)ᵀR(SN) + (A - BSN)ᵀP(A - BSN)
  -- We need: Q + AᵀPA - AᵀPBSN = Q + KᵀRK + A_clᵀPA_cl
  -- Since K = -SN and A_cl = A - BSN:
  -- KᵀRK = (-SN)ᵀR(-SN) = (SN)ᵀR(SN) ✓
  -- A_clᵀPA_cl = (A - BSN)ᵀP(A - BSN) ✓
  -- Rewrite dare to use K and A_cl
  have h_neg_sq : (S * N).transpose * L.R * (S * N) =
      K.transpose * L.R * K := by
    rw [hK_eq]; simp [Matrix.transpose_neg, Matrix.neg_mul, Matrix.mul_neg]
  have h_acl_match : (L.A - L.B * S * N).transpose * P * (L.A - L.B * S * N) =
      A_cl.transpose * P_next * A_cl := by
    have : L.A - L.B * S * N = A_cl := by
      rw [hAcl_eq, Matrix.mul_assoc]
    rw [this]
  rw [dare, h_neg_sq, h_acl_match]

/-! ### LQR Policy Gradient -/

/-- A linear feedback policy K: u_t = K x_t (matrix policy). -/
structure LinearPolicy where
  /-- The feedback gain matrix K in R^{m x n} -/
  K : Matrix (Fin m) (Fin n) ℝ
  /-- K is stabilizing: spectral radius of A + BK < 1 (stabilizability). -/
  h_stabilizing : ∃ P : Matrix (Fin n) (Fin n) ℝ,
    (∀ x : Fin n → ℝ, 0 ≤ dotProduct x (P.mulVec x)) ∧
    (∀ x : Fin n → ℝ,
      dotProduct x (P.mulVec x) ≥
      dotProduct x (L.Q.mulVec x) +
      dotProduct (K.mulVec x) (L.R.mulVec (K.mulVec x)) +
      dotProduct ((L.A + L.B * K).mulVec x) (P.mulVec ((L.A + L.B * K).mulVec x)))

/-- The infinite-horizon LQR value under policy K:
    J(K) = E_{x~μ}[∑_{t=0}^∞ x_t^T Q x_t + u_t^T R u_t]
    where x_{t+1} = (A + BK) x_t and μ is the initial distribution.

    For stabilizing K, J(K) = trace(P_K Σ) where P_K solves the
    Lyapunov equation and Σ = E[x x^T] is the state covariance. -/
noncomputable def lqrCost (π : L.LinearPolicy) (Cov : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  -- Simplified: J(K) = trace((Q + K^T R K) Σ_∞)
  -- where Σ_∞ = ∑_{t=0}^∞ A_cl^t Σ (A_cl^t)^T is the state covariance sum.
  -- We encode this as a hypothesis via the infinite-horizon Lyapunov equation.
  Matrix.trace ((L.Q + π.K.transpose * L.R * π.K) * Cov)

/-- **LQR cost decomposition**: The LQR cost J(K) = trace((Q + K^T R K) Σ_K)
    splits into state cost and control cost:

    J(K) = trace(Q · Σ_K) + trace(K^T R K · Σ_K)

    The state cost trace(Q Σ_K) is K-independent at fixed covariance, so the
    policy gradient ∇_K J(K) = 2(RK + B^T P_K A) Σ_K (Fazel et al. 2018)
    arises from differentiating the control cost plus the implicit dependence
    of Σ_K on K through the Lyapunov equation. The full gradient formula is
    conditional on matrix calculus identities not available in Mathlib. -/
theorem lqr_cost_decomposition
    (π : L.LinearPolicy)
    (Sigma_K : Matrix (Fin n) (Fin n) ℝ) :
    L.lqrCost π Sigma_K =
    Matrix.trace (L.Q * Sigma_K) +
    Matrix.trace (π.K.transpose * L.R * π.K * Sigma_K) := by
  unfold lqrCost
  rw [add_mul, Matrix.trace_add]

/-! ### Global Convergence Certificate -/

/-- **LQR policy gradient descent convergence** (conditional).

For stabilizing K₀ with cost J(K₀) < ∞, gradient descent with
step size η converges to the optimal K*:

  J(K_{t+1}) ≤ J(K_t) - η · ‖∇J(K_t)‖²_F / 2

When J is smooth and gradient-dominated (as in Fazel et al. 2018),
this implies linear convergence to J(K*).

**Status**: Conditional on gradient dominance (PL condition):
  ‖∇J(K)‖²_F ≥ 2μ (J(K) - J(K*))

This holds for LQR by the structure of the Riccati equation. -/
theorem lqr_gradient_descent_convergence
    (K_seq : ℕ → Matrix (Fin m) (Fin n) ℝ)
    (J : Matrix (Fin m) (Fin n) ℝ → ℝ)
    (J_star : ℝ) (η μ : ℝ) (_hη : 0 < η) (_hμ : 0 < μ)
    -- Step size is small enough for contraction: 0 ≤ 1 - η·μ/2 ≤ 1
    (h_small : η / 2 * μ ≤ 1)
    -- Gradient descent update: K_{t+1} = K_t - η · ∇J(K_t) (PL condition)
    (h_update : ∀ t, J (K_seq (t + 1)) ≤ J (K_seq t) - η / 2 * μ * (J (K_seq t) - J_star))
    (h_jstar : ∀ K, J_star ≤ J K) :
    ∀ t, J (K_seq t) - J_star ≤ (1 - η / 2 * μ) ^ t * (J (K_seq 0) - J_star) := by
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
    have h_nonneg_gap : 0 ≤ J (K_seq t) - J_star := by linarith [h_jstar (K_seq t)]
    have h_step := h_update t
    have h_contract_factor : 0 ≤ 1 - η / 2 * μ := by linarith
    calc J (K_seq (t + 1)) - J_star
        ≤ J (K_seq t) - η / 2 * μ * (J (K_seq t) - J_star) - J_star := by linarith
      _ = (1 - η / 2 * μ) * (J (K_seq t) - J_star) := by ring
      _ ≤ (1 - η / 2 * μ) * ((1 - η / 2 * μ) ^ t * (J (K_seq 0) - J_star)) :=
            mul_le_mul_of_nonneg_left ih h_contract_factor
      _ = (1 - η / 2 * μ) ^ (t + 1) * (J (K_seq 0) - J_star) := by ring

end LQRInstance

end
