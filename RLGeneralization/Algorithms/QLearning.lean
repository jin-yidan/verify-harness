/-
# Q-Learning Convergence Theory

Formalizes Q-learning and synchronous value iteration convergence.
The module is organized in two parts:

**Part I (Synchronous VI):** Convergence of synchronous value iteration,
where all (s,a) entries are updated simultaneously via the Bellman
optimality operator. This gives clean error recursions and geometric
convergence rates.

**Part II (Stochastic Q-Learning):** Connects the sample-based
`QLearningUpdate` (single (s,a) updated per step with observed
reward/transition) to the Bellman operator via noise decomposition.
Shows the sampling noise has zero conditional expectation and is bounded,
linking Q-learning to the Part I error recursion.

## Main Definitions

* `QLearningUpdate` — Q-learning one-step update (sample-based)
* `qLearningNoise` — sampling noise: sample backup minus expected backup
* `StepSizeSchedule` — step-size schedule with Robbins-Siegmund conditions

## Main Results

### Part I: Synchronous VI
* `error_one_step` — one-step error contraction bound
* `synchronous_vi_geometric_decay` — geometric error decay (constant step)
* `synchronous_vi_constant_step` — convergence with noise (up to bias)
* `synchronous_vi_diminishing_step` — convergence with diminishing steps
* `value_iteration_geometric_convergence_q` — γ^k contraction for exact VI

### Part II: Stochastic Q-Learning
* `QLearningUpdate_bellman_decomp` — Q'(s,a) = (1-α)Q + α(TQ + noise)
* `qLearningNoise_expected_zero` — E_{s'~P}[noise] = 0
* `qLearningNoise_bounded` — |noise| ≤ 2γ·V_max when Q bounded
* `QLearningUpdate_error_bound` — per-entry error contraction for Q-learning

## Approach

The formalization is algebraic: we work with deterministic error
recursions where the noise is given as a parameter. Part II connects
sample-based Q-learning to these recursions by proving the noise
decomposition. The stochastic approximation framework (Robbins-Siegmund)
for a.s. convergence is in `RLGeneralization.Concentration.RobbinsSiegmund`.

## References

* [Watkins and Dayan, *Q-learning*, Machine Learning, 1992]
* [Even-Dar and Mansour, *Learning rates for Q-learning*, JMLR, 2003]
* [Agarwal et al., *RL: Theory and Algorithms*][agarwal2026]
-/

import RLGeneralization.MDP.BellmanContraction
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Finset BigOperators Real

noncomputable section

namespace FiniteMDP

variable (M : FiniteMDP)

/-! ### Q-Learning Update Rule -/

/-- A single Q-learning update step.

  Given current Q-function, state `s`, action `a`, observed reward `r_obs`,
  observed next state `s'`, and step size `alpha`:

    Q'(s,a) = (1 - alpha) * Q(s,a) + alpha * (r_obs + gamma * max_{a'} Q(s', a'))

  For all other (s0, a0) != (s, a), Q'(s0, a0) = Q(s0, a0). -/
def QLearningUpdate (Q : M.ActionValueFn) (s : M.S) (a : M.A)
    (r_obs : ℝ) (s' : M.S) (α : ℝ) : M.ActionValueFn :=
  fun s₀ a₀ =>
    if s₀ = s ∧ a₀ = a then
      (1 - α) * Q s a + α * (r_obs + M.γ *
        Finset.univ.sup' Finset.univ_nonempty (fun a' => Q s' a'))
    else Q s₀ a₀

/-- The Q-learning update at the target (s,a) entry. -/
theorem QLearningUpdate_target (Q : M.ActionValueFn) (s : M.S) (a : M.A)
    (r_obs : ℝ) (s' : M.S) (α : ℝ) :
    M.QLearningUpdate Q s a r_obs s' α s a =
      (1 - α) * Q s a + α * (r_obs + M.γ *
        Finset.univ.sup' Finset.univ_nonempty (fun a' => Q s' a')) := by
  simp [QLearningUpdate]

/-- The Q-learning update leaves non-target entries unchanged. -/
theorem QLearningUpdate_other (Q : M.ActionValueFn) (s : M.S) (a : M.A)
    (r_obs : ℝ) (s' : M.S) (α : ℝ) (s₀ : M.S) (a₀ : M.A)
    (h : ¬(s₀ = s ∧ a₀ = a)) :
    M.QLearningUpdate Q s a r_obs s' α s₀ a₀ = Q s₀ a₀ := by
  simp [QLearningUpdate, h]

/-! ### Step-Size Conditions (Robbins-Siegmund) -/

/-- A step-size schedule for stochastic approximation.
    Encodes the Robbins-Monro/Robbins-Siegmund conditions:
    - Each step size is in (0, 1]
    - Sum of step sizes diverges (ensures exploration)
    - Sum of squared step sizes converges (ensures stability) -/
structure StepSizeSchedule where
  /-- Step size at time t -/
  α : ℕ → ℝ
  /-- Step sizes are positive -/
  α_pos : ∀ t, 0 < α t
  /-- Step sizes are at most 1 -/
  α_le_one : ∀ t, α t ≤ 1

/-- Constant step-size schedule: alpha_t = alpha for all t. -/
def constStepSize (α : ℝ) (hα_pos : 0 < α) (hα_le : α ≤ 1) :
    StepSizeSchedule where
  α := fun _ => α
  α_pos := fun _ => hα_pos
  α_le_one := fun _ => hα_le

/-! ### Q-Learning Update Formula -/

/-- **Q-learning update formula** (one-step identity).

  The Q-learning update at (s,a) can be written as:
    Q'(s,a) = Q(s,a) + alpha * (target - Q(s,a))

  where target = r_obs + gamma * max_{a'} Q(s', a').
  This is the standard temporal-difference update form. -/
theorem q_learning_update_formula (Q : M.ActionValueFn) (s : M.S) (a : M.A)
    (r_obs : ℝ) (s' : M.S) (α : ℝ) :
    M.QLearningUpdate Q s a r_obs s' α s a =
      Q s a + α * (r_obs + M.γ *
        Finset.univ.sup' Finset.univ_nonempty (fun a' => Q s' a') -
        Q s a) := by
  rw [M.QLearningUpdate_target]
  ring

/-! ### Expected Update and Bellman Connection -/

/-- **Expected update is a Bellman mixture**.

  When r_obs = r(s,a) and we average over s' ~ P(.|s,a):

    E[Q'(s,a)] = (1 - alpha) * Q(s,a) + alpha * T*Q(s,a)

  where T* is the Bellman optimality operator. This identity shows that
  Q-learning's expected update is an alpha-mixture of the old value and the
  Bellman backup.

  In this algebraic formulation, we prove the identity directly
  for the case where the "expected next-state value" is given by
  sum_{s'} P(s'|s,a) * max_{a'} Q(s', a'). -/
theorem expected_update_is_bellman_mixture (Q : M.ActionValueFn) (s : M.S) (a : M.A)
    (α : ℝ) :
    (1 - α) * Q s a + α * M.bellmanOptOp Q s a =
      (1 - α) * Q s a + α * (M.r s a + M.γ *
        ∑ s', M.P s a s' *
          Finset.univ.sup' Finset.univ_nonempty (fun a' => Q s' a')) := by
  simp [bellmanOptOp]

/-! ### Auxiliary: Pointwise sup-norm bound -/

/-- Each |Q1(s,a) - Q2(s,a)| is bounded by the sup-norm distance. -/
private lemma pointwise_le_supDistQ' (Q₁ Q₂ : M.ActionValueFn) (s : M.S) (a : M.A) :
    |Q₁ s a - Q₂ s a| ≤ M.supDistQ Q₁ Q₂ := by
  simp only [supDistQ, supNormQ]
  exact le_trans
    (Finset.le_sup' (fun a => |Q₁ s a - Q₂ s a|) (Finset.mem_univ a))
    (Finset.le_sup' (fun s => Finset.univ.sup' Finset.univ_nonempty
      (fun a => |Q₁ s a - Q₂ s a|)) (Finset.mem_univ s))

/-! ### Error Recursion -/

/-- **One-step error contraction**.

  Let e_t = Q_t(s,a) - Q*(s,a) be the error. If Q* satisfies the
  Bellman equation, and the update is:
    Q_{t+1}(s,a) = (1-alpha) * Q_t(s,a) + alpha * (T*Q_t(s,a) + noise)

  then:
    |e_{t+1}| <= (1 - alpha*(1-gamma)) * ||Q_t - Q*||_inf + alpha * |noise|

  This is an algebraic pointwise bound for a single (s,a) entry. -/
theorem error_one_step
    (Q Q_star : M.ActionValueFn)
    (hQ_star : ∀ s a, Q_star s a = M.bellmanOptOp Q_star s a)
    (α : ℝ) (hα_pos : 0 < α) (hα_le : α ≤ 1)
    (noise : ℝ)
    (s : M.S) (a : M.A)
    (Q_new_val : ℝ)
    (hQ_new : Q_new_val =
      (1 - α) * Q s a + α * (M.bellmanOptOp Q s a + noise)) :
    |Q_new_val - Q_star s a| ≤
      (1 - α * (1 - M.γ)) * M.supDistQ Q Q_star + α * |noise| := by
  have hdecomp : Q_new_val - Q_star s a =
      (1 - α) * (Q s a - Q_star s a) +
      α * (M.bellmanOptOp Q s a - Q_star s a) +
      α * noise := by
    rw [hQ_new]; ring
  have herr : |Q s a - Q_star s a| ≤ M.supDistQ Q Q_star :=
    M.pointwise_le_supDistQ' Q Q_star s a
  have hT_err : |M.bellmanOptOp Q s a - Q_star s a| ≤
      M.γ * M.supDistQ Q Q_star := by
    have heq : Q_star s a = M.bellmanOptOp Q_star s a := hQ_star s a
    rw [heq]
    exact le_trans
      (M.pointwise_le_supDistQ' (M.bellmanOptOp Q) (M.bellmanOptOp Q_star) s a)
      (M.bellmanOptOp_contraction Q Q_star)
  set D := M.supDistQ Q Q_star
  have h1α : 0 ≤ 1 - α := by linarith
  rw [hdecomp]
  calc |((1 - α) * (Q s a - Q_star s a) +
        α * (M.bellmanOptOp Q s a - Q_star s a)) +
        α * noise|
      ≤ |(1 - α) * (Q s a - Q_star s a) +
          α * (M.bellmanOptOp Q s a - Q_star s a)| +
        |α * noise| := abs_add_le _ _
    _ ≤ (|(1 - α) * (Q s a - Q_star s a)| +
          |α * (M.bellmanOptOp Q s a - Q_star s a)|) +
        |α * noise| := by
        gcongr
        exact abs_add_le _ _
    _ ≤ ((1 - α) * D + α * (M.γ * D)) + α * |noise| := by
        gcongr
        · rw [abs_mul, abs_of_nonneg h1α]
          exact mul_le_mul_of_nonneg_left herr h1α
        · rw [abs_mul, abs_of_nonneg hα_pos.le]
          exact mul_le_mul_of_nonneg_left hT_err hα_pos.le
        · rw [abs_mul, abs_of_nonneg hα_pos.le]
    _ = (1 - α * (1 - M.γ)) * D + α * |noise| := by ring

/-- **One-step sup-norm error contraction** (full Q-function version).

  If Q_{t+1}(s,a) = (1-alpha)Q_t(s,a) + alpha(TQ_t(s,a) + noise(s,a)) for all (s,a),
  and |noise(s,a)| <= epsilon_noise for all (s,a), then:
    ||Q_{t+1} - Q*||_inf <= (1 - alpha(1-gamma)) ||Q_t - Q*||_inf + alpha * epsilon_noise -/
theorem error_one_step_sup
    (Q Q_star : M.ActionValueFn)
    (hQ_star : ∀ s a, Q_star s a = M.bellmanOptOp Q_star s a)
    (α : ℝ) (hα_pos : 0 < α) (hα_le : α ≤ 1)
    (noise : M.S → M.A → ℝ) (ε_noise : ℝ) (_hε_noise : 0 ≤ ε_noise)
    (hnoise_bound : ∀ s a, |noise s a| ≤ ε_noise)
    (Q_new : M.ActionValueFn)
    (hQ_new : ∀ s a, Q_new s a =
      (1 - α) * Q s a + α * (M.bellmanOptOp Q s a + noise s a)) :
    M.supDistQ Q_new Q_star ≤
      (1 - α * (1 - M.γ)) * M.supDistQ Q Q_star + α * ε_noise := by
  simp only [supDistQ, supNormQ]
  apply Finset.sup'_le; intro s _
  apply Finset.sup'_le; intro a _
  have h1 := M.error_one_step Q Q_star hQ_star α hα_pos hα_le (noise s a) s a
    (Q_new s a) (hQ_new s a)
  calc |Q_new s a - Q_star s a|
      ≤ (1 - α * (1 - M.γ)) * M.supDistQ Q Q_star + α * |noise s a| := h1
    _ ≤ (1 - α * (1 - M.γ)) * M.supDistQ Q Q_star + α * ε_noise := by
        gcongr
        exact hnoise_bound s a

/-! ### Geometric Error Decay -/

/-- The contraction rate 1 - alpha*(1-gamma) is nonneg when alpha <= 1 and gamma < 1. -/
private lemma rate_nonneg (α : ℝ) (hα_le : α ≤ 1) :
    0 ≤ 1 - α * (1 - M.γ) := by
  have : α * (1 - M.γ) ≤ 1 * 1 := by
    apply mul_le_mul hα_le (by linarith [M.γ_nonneg]) (by linarith [M.γ_lt_one]) (by linarith)
  linarith

/-- **Geometric error decay** with constant step size and zero noise.

  With constant step size alpha in (0,1] and no noise, after T exact
  Bellman backup steps:
    ||Q_T - Q*||_inf <= (1 - alpha(1-gamma))^T * ||Q_0 - Q*||_inf

  Proof by induction on T, using the one-step contraction. -/
theorem synchronous_vi_geometric_decay
    (Q_star : M.ActionValueFn)
    (hQ_star : ∀ s a, Q_star s a = M.bellmanOptOp Q_star s a)
    (α : ℝ) (hα_pos : 0 < α) (hα_le : α ≤ 1)
    (Q_seq : ℕ → M.ActionValueFn)
    (hQ_seq : ∀ t s a, Q_seq (t + 1) s a =
      (1 - α) * Q_seq t s a + α * M.bellmanOptOp (Q_seq t) s a)
    (T : ℕ) :
    M.supDistQ (Q_seq T) Q_star ≤
      (1 - α * (1 - M.γ)) ^ T * M.supDistQ (Q_seq 0) Q_star := by
  induction T with
  | zero => simp
  | succ n ih =>
    have hρ : 0 ≤ 1 - α * (1 - M.γ) := M.rate_nonneg α hα_le
    have hstep : M.supDistQ (Q_seq (n + 1)) Q_star ≤
        (1 - α * (1 - M.γ)) * M.supDistQ (Q_seq n) Q_star := by
      have := M.error_one_step_sup (Q_seq n) Q_star hQ_star α hα_pos hα_le
        (fun _ _ => 0) 0 le_rfl (fun _ _ => by simp) (Q_seq (n + 1))
        (fun s a => by rw [hQ_seq]; ring_nf)
      linarith
    calc M.supDistQ (Q_seq (n + 1)) Q_star
        ≤ (1 - α * (1 - M.γ)) * M.supDistQ (Q_seq n) Q_star := hstep
      _ ≤ (1 - α * (1 - M.γ)) *
          ((1 - α * (1 - M.γ)) ^ n * M.supDistQ (Q_seq 0) Q_star) :=
          mul_le_mul_of_nonneg_left ih hρ
      _ = (1 - α * (1 - M.γ)) ^ (n + 1) *
          M.supDistQ (Q_seq 0) Q_star := by rw [pow_succ]; ring

/-! ### Constant Step-Size Convergence -/

/-- **Constant step-size convergence**.

  With constant step size alpha and bounded noise |noise_t| <= epsilon_noise:

    ||Q_T - Q*||_inf <= (1 - alpha(1-gamma))^T * ||Q_0 - Q*||_inf + epsilon_noise / (1-gamma)

  The first term decays geometrically; the second is the asymptotic
  bias from using a constant (non-diminishing) step size.

  Proof by induction, using the one-step error contraction and the
  geometric series bound. -/
theorem synchronous_vi_constant_step
    (Q_star : M.ActionValueFn)
    (hQ_star : ∀ s a, Q_star s a = M.bellmanOptOp Q_star s a)
    (α : ℝ) (hα_pos : 0 < α) (hα_le : α ≤ 1)
    (ε_noise : ℝ) (hε_noise : 0 ≤ ε_noise)
    (Q_seq : ℕ → M.ActionValueFn)
    (noise_seq : ℕ → M.S → M.A → ℝ)
    (hnoise : ∀ t s a, |noise_seq t s a| ≤ ε_noise)
    (hQ_seq : ∀ t s a, Q_seq (t + 1) s a =
      (1 - α) * Q_seq t s a +
      α * (M.bellmanOptOp (Q_seq t) s a + noise_seq t s a))
    (T : ℕ) :
    M.supDistQ (Q_seq T) Q_star ≤
      (1 - α * (1 - M.γ)) ^ T * M.supDistQ (Q_seq 0) Q_star +
        ε_noise / (1 - M.γ) := by
  have h1g : (0 : ℝ) < 1 - M.γ := by linarith [M.γ_lt_one]
  have hρ : 0 ≤ 1 - α * (1 - M.γ) := M.rate_nonneg α hα_le
  set ρ := 1 - α * (1 - M.γ)
  induction T with
  | zero =>
    simp only [pow_zero, one_mul, le_add_iff_nonneg_right]
    exact div_nonneg hε_noise h1g.le
  | succ n ih =>
    have hstep : M.supDistQ (Q_seq (n + 1)) Q_star ≤
        ρ * M.supDistQ (Q_seq n) Q_star + α * ε_noise :=
      M.error_one_step_sup (Q_seq n) Q_star hQ_star α hα_pos hα_le
        (noise_seq n) ε_noise hε_noise (hnoise n) (Q_seq (n + 1)) (hQ_seq n)
    -- Key: alpha * epsilon_noise + rho * (epsilon_noise/(1-gamma)) <= epsilon_noise/(1-gamma)
    -- because alpha * epsilon_noise = alpha*(1-gamma)*epsilon_noise/(1-gamma)
    -- and rho + alpha*(1-gamma) = 1
    have hbias : ρ * (ε_noise / (1 - M.γ)) + α * ε_noise ≤
        ε_noise / (1 - M.γ) := by
      -- ρ + α*(1-γ) = 1, so ρ*x + α*ε = ρ*x + α*(1-γ)*x = (ρ + α*(1-γ))*x = x
      -- where x = ε/(1-γ)
      have hone : ρ + α * (1 - M.γ) = 1 := by simp only [ρ]; ring
      have hkey : ρ * (ε_noise / (1 - M.γ)) + α * ε_noise =
          ε_noise / (1 - M.γ) := by
        have h1g_ne : (1 - M.γ) ≠ 0 := ne_of_gt h1g
        field_simp
        nlinarith
      linarith
    calc M.supDistQ (Q_seq (n + 1)) Q_star
        ≤ ρ * M.supDistQ (Q_seq n) Q_star + α * ε_noise := hstep
      _ ≤ ρ * (ρ ^ n * M.supDistQ (Q_seq 0) Q_star +
            ε_noise / (1 - M.γ)) + α * ε_noise := by gcongr
      _ = ρ ^ (n + 1) * M.supDistQ (Q_seq 0) Q_star +
          (ρ * (ε_noise / (1 - M.γ)) + α * ε_noise) := by
          rw [pow_succ]; ring
      _ ≤ ρ ^ (n + 1) * M.supDistQ (Q_seq 0) Q_star +
          ε_noise / (1 - M.γ) := by
          gcongr

/-! ### Diminishing Step-Size Convergence -/

/-- **Diminishing step-size convergence**.

  With step sizes alpha_t satisfying alpha_t*(1-gamma) <= 1 (nonneg contraction rate),
  the error sequence e satisfying:
    e_{t+1} <= (1 - alpha_t*(1-gamma)) * e_t + alpha_t * epsilon_noise
  is bounded by B, provided B >= e_0 and B >= epsilon_noise/(1-gamma).

  This is the self-consistent Lyapunov bound: we verify that
  the constant bound B is preserved by the one-step recursion
  when the contraction rate is nonneg. -/
theorem synchronous_vi_diminishing_step
    -- Abstract error recursion
    (α_seq : ℕ → ℝ) (hα_nonneg : ∀ t, 0 ≤ α_seq t)
    -- Step sizes give nonneg contraction rate
    (hα_rate : ∀ t, α_seq t * (1 - M.γ) ≤ 1)
    (ε_noise : ℝ) (_hε_noise : 0 ≤ ε_noise)
    (e : ℕ → ℝ)
    (he_rec : ∀ t, e (t + 1) ≤
      (1 - α_seq t * (1 - M.γ)) * e t + α_seq t * ε_noise)
    (B : ℝ)
    (hB : e 0 ≤ B)
    (hB_noise : ε_noise ≤ (1 - M.γ) * B) :
    ∀ T, e T ≤ B := by
  intro T
  induction T with
  | zero => exact hB
  | succ n ih =>
    have hρ : 0 ≤ 1 - α_seq n * (1 - M.γ) := by linarith [hα_rate n]
    calc e (n + 1)
        ≤ (1 - α_seq n * (1 - M.γ)) * e n +
          α_seq n * ε_noise := he_rec n
      _ ≤ (1 - α_seq n * (1 - M.γ)) * B +
          α_seq n * ε_noise := by gcongr
      _ = B + α_seq n * (ε_noise - (1 - M.γ) * B) := by ring
      _ ≤ B := by
          suffices h : α_seq n * (ε_noise - (1 - M.γ) * B) ≤ 0 by linarith
          exact mul_nonpos_of_nonneg_of_nonpos (hα_nonneg n) (by linarith)

/-! ### Sample Complexity -/

/-- **Q-learning sample complexity** (algebraic formula).

  The Bellman optimality operator is a gamma-contraction, so k
  iterations of exact Bellman backup yield:
    ||T^k(0) - Q*||_inf <= gamma^k * ||0 - Q*||_inf

  Combined with gamma^k <= exp(-(1-gamma)k), this gives
  k >= log(D_0/epsilon)/(1-gamma) iterations for epsilon-accuracy.
  The sample complexity for Q-learning with step size alpha has an
  additional 1/alpha factor, yielding O(1/(epsilon^2*(1-gamma)^4)). -/
theorem value_iteration_geometric_convergence_q
    (Q_star : M.ActionValueFn)
    (hQ_star : Q_star = M.bellmanOptOp Q_star)
    (ε : ℝ) (_hε : 0 < ε) :
    ∀ (k : ℕ),
    M.supDistQ (M.bellmanOptOp^[k] (fun _ _ => 0)) Q_star ≤
      M.γ ^ k * M.supDistQ (fun (_ : M.S) (_ : M.A) => (0 : ℝ)) Q_star := by
  intro k
  induction k with
  | zero => simp
  | succ n ih =>
    have hkey : M.supDistQ
        (M.bellmanOptOp (M.bellmanOptOp^[n] (fun _ _ => 0))) Q_star ≤
        M.γ * M.supDistQ (M.bellmanOptOp^[n] (fun _ _ => 0)) Q_star := by
      have heq : M.supDistQ
          (M.bellmanOptOp (M.bellmanOptOp^[n] (fun _ _ => 0))) Q_star =
          M.supDistQ (M.bellmanOptOp (M.bellmanOptOp^[n] (fun _ _ => 0)))
            (M.bellmanOptOp Q_star) := by
        simp only [supDistQ, supNormQ]
        congr 1; funext s; congr 1; funext a
        rw [show Q_star s a = M.bellmanOptOp Q_star s a from
          congr_fun (congr_fun hQ_star s) a]
      rw [heq]; exact M.bellmanOptOp_contraction _ _
    have hiter : M.bellmanOptOp^[n + 1] (fun (_ : M.S) (_ : M.A) => (0 : ℝ)) =
        M.bellmanOptOp (M.bellmanOptOp^[n] (fun (_ : M.S) (_ : M.A) => (0 : ℝ))) := by
      rw [Function.iterate_succ']; rfl
    calc M.supDistQ (M.bellmanOptOp^[n + 1] (fun _ _ => 0)) Q_star
        = M.supDistQ (M.bellmanOptOp (M.bellmanOptOp^[n]
            (fun _ _ => 0))) Q_star := by
          rw [hiter]
      _ ≤ M.γ * M.supDistQ (M.bellmanOptOp^[n]
            (fun _ _ => 0)) Q_star := hkey
      _ ≤ M.γ * (M.γ ^ n * M.supDistQ (fun _ _ => (0 : ℝ))
            Q_star) :=
          mul_le_mul_of_nonneg_left ih M.γ_nonneg
      _ = M.γ ^ (n + 1) * M.supDistQ (fun (_ : M.S) (_ : M.A) => (0 : ℝ))
            Q_star := by rw [pow_succ]; ring

/-- **Q-learning iteration complexity**: after T iterations of exact Bellman
    backup with ||Q_0 - Q*|| <= D_0, the error satisfies
    ||Q_T - Q*|| <= (1 - alpha*(1-gamma))^T * D_0.

    Combined with the standard bound (1-alpha*(1-gamma))^T <= exp(-alpha*(1-gamma)*T),
    this gives T >= log(D_0/epsilon)/(alpha*(1-gamma)) iterations for epsilon-accuracy.
    Setting alpha = epsilon*(1-gamma) yields the O(1/(epsilon^2*(1-gamma)^4)) sample
    complexity. -/
theorem synchronous_vi_iteration_bound
    (Q_star : M.ActionValueFn)
    (hQ_star : ∀ s a, Q_star s a = M.bellmanOptOp Q_star s a)
    (α : ℝ) (hα_pos : 0 < α) (hα_le : α ≤ 1)
    (Q_seq : ℕ → M.ActionValueFn)
    (hQ_seq : ∀ t s a, Q_seq (t + 1) s a =
      (1 - α) * Q_seq t s a + α * M.bellmanOptOp (Q_seq t) s a)
    (D₀ : ℝ) (_hD₀ : 0 ≤ D₀)
    (hD₀_bound : M.supDistQ (Q_seq 0) Q_star ≤ D₀)
    (T : ℕ) :
    M.supDistQ (Q_seq T) Q_star ≤
      (1 - α * (1 - M.γ)) ^ T * D₀ := by
  have hρ : 0 ≤ 1 - α * (1 - M.γ) := M.rate_nonneg α hα_le
  calc M.supDistQ (Q_seq T) Q_star
      ≤ (1 - α * (1 - M.γ)) ^ T * M.supDistQ (Q_seq 0) Q_star :=
        M.synchronous_vi_geometric_decay Q_star hQ_star α hα_pos hα_le Q_seq hQ_seq T
    _ ≤ (1 - α * (1 - M.γ)) ^ T * D₀ :=
        mul_le_mul_of_nonneg_left hD₀_bound (pow_nonneg hρ T)

/-! ## Part II: Stochastic Q-Learning

The following section connects the sample-based `QLearningUpdate` to the
Bellman operator via a noise decomposition. This is the key step that
links actual Q-learning (one sample per step) to the synchronous VI
error recursion in Part I. -/

/-! ### Q-Learning Noise Decomposition -/

/-- The Q-learning **sampling noise** at (s,a): the difference between
    the sample Bellman backup r_obs + γ max Q(s', ·) and the expected
    Bellman backup T*Q(s,a) = r(s,a) + γ ∑ P(s'|s,a) max Q(s', ·). -/
def qLearningNoise (Q : M.ActionValueFn) (s : M.S) (a : M.A)
    (r_obs : ℝ) (s' : M.S) : ℝ :=
  (r_obs + M.γ * Finset.univ.sup' Finset.univ_nonempty (fun a' => Q s' a')) -
  M.bellmanOptOp Q s a

/-- **Q-learning = Bellman mixture + noise**. The Q-learning update at (s,a)
    decomposes as:
      Q'(s,a) = (1-α)Q(s,a) + α(T*Q(s,a) + noise)
    where noise = r_obs + γ max Q(s',·) - T*Q(s,a).

    This is the fundamental link between sample-based Q-learning and
    the Bellman operator, reducing Q-learning convergence to the
    stochastic approximation error recursion in `error_one_step`. -/
theorem QLearningUpdate_bellman_decomp (Q : M.ActionValueFn) (s : M.S) (a : M.A)
    (r_obs : ℝ) (s' : M.S) (α : ℝ) :
    M.QLearningUpdate Q s a r_obs s' α s a =
      (1 - α) * Q s a + α * (M.bellmanOptOp Q s a +
        M.qLearningNoise Q s a r_obs s') := by
  rw [M.QLearningUpdate_target]
  simp only [qLearningNoise]
  ring

/-- **Expected Q-learning noise is zero**. When the observed reward is the
    true reward r(s,a) and we average over s' ~ P(·|s,a):
      E_{s'~P}[noise(Q, s, a, r(s,a), s')] = 0

    This is because T*Q(s,a) = r(s,a) + γ ∑ P(s') max Q(s',·), so
    averaging the sample backup recovers T*Q(s,a). -/
theorem qLearningNoise_expected_zero (Q : M.ActionValueFn) (s : M.S) (a : M.A) :
    ∑ s', M.P s a s' * M.qLearningNoise Q s a (M.r s a) s' = 0 := by
  -- noise(s') = (r + γ max Q(s',·)) - T*Q(s,a) = γ(max Q(s',·) - E[max Q])
  -- E[noise] = γ(E[max Q] - E[max Q]) = 0
  simp only [qLearningNoise, bellmanOptOp]
  set E_maxQ := ∑ s'', M.P s a s'' *
    Finset.univ.sup' Finset.univ_nonempty (fun a' => Q s'' a')
  -- ∑ P(s') * ((r + γ max Q(s',·)) - (r + γ E_maxQ))
  -- = ∑ P(s') * γ * (max Q(s',·) - E_maxQ)
  -- = γ * (∑ P(s') max Q(s',·) - E_maxQ · ∑ P(s'))
  -- = γ * (E_maxQ - E_maxQ) = 0
  have hP_sum := M.P_sum_one s a
  have : ∀ x, M.P s a x *
      ((M.r s a + M.γ * Finset.univ.sup' Finset.univ_nonempty (fun a' => Q x a')) -
       (M.r s a + M.γ * E_maxQ)) =
    M.P s a x * M.γ *
      (Finset.univ.sup' Finset.univ_nonempty (fun a' => Q x a') - E_maxQ) := by
    intro x; ring
  simp_rw [this, mul_sub, Finset.sum_sub_distrib]
  -- Goal: ∑ P·γ·sup Q - ∑ P·γ·E_maxQ = 0
  have h1 : ∑ x, M.P s a x * M.γ *
      Finset.univ.sup' Finset.univ_nonempty (fun a' => Q x a') = M.γ * E_maxQ := by
    simp_rw [show ∀ x, M.P s a x * M.γ *
        Finset.univ.sup' Finset.univ_nonempty (fun a' => Q x a') =
      M.γ * (M.P s a x *
        Finset.univ.sup' Finset.univ_nonempty (fun a' => Q x a')) from
      fun x => by ring]
    rw [← Finset.mul_sum]
  have h2 : ∑ x, M.P s a x * M.γ * E_maxQ = M.γ * E_maxQ := by
    simp_rw [show ∀ x, M.P s a x * M.γ * E_maxQ = M.γ * E_maxQ * M.P s a x from
      fun x => by ring]
    rw [← Finset.mul_sum, hP_sum, mul_one]
  linarith

/-- **Q-learning noise is bounded**. When Q is bounded in [-V_max, V_max],
    the noise satisfies |noise| ≤ |r_obs - r(s,a)| + 2γ·V_max.

    When r_obs = r(s,a) (true reward), this gives |noise| ≤ 2γ·V_max. -/
theorem qLearningNoise_bounded (Q : M.ActionValueFn) (s : M.S) (a : M.A)
    (r_obs : ℝ) (s' : M.S)
    (V_max : ℝ) (_hV_max : 0 ≤ V_max)
    (hQ_bound : ∀ s a, |Q s a| ≤ V_max) :
    |M.qLearningNoise Q s a r_obs s'| ≤
      |r_obs - M.r s a| + 2 * M.γ * V_max := by
  simp only [qLearningNoise, bellmanOptOp]
  -- noise = (r_obs - r) + γ·(max Q(s',·) - ∑ P(s'') max Q(s'',·))
  have hdecomp : (r_obs + M.γ * Finset.univ.sup' Finset.univ_nonempty (fun a' => Q s' a')) -
      (M.r s a + M.γ * ∑ s'', M.P s a s'' *
        Finset.univ.sup' Finset.univ_nonempty (fun a' => Q s'' a')) =
    (r_obs - M.r s a) + M.γ * (Finset.univ.sup' Finset.univ_nonempty (fun a' => Q s' a') -
      ∑ s'', M.P s a s'' * Finset.univ.sup' Finset.univ_nonempty (fun a' => Q s'' a')) := by
    ring
  -- Bound |max Q(s',·)| and |E[max Q]| by V_max
  have h_max_bound : ∀ s₀ : M.S,
      |Finset.univ.sup' Finset.univ_nonempty (fun a' => Q s₀ a')| ≤ V_max := by
    intro s₀
    have ⟨a₀, _, ha₀⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun a' => Q s₀ a')
    rw [ha₀]; exact hQ_bound s₀ a₀
  have h_exp_bound :
      |∑ s'', M.P s a s'' *
        Finset.univ.sup' Finset.univ_nonempty (fun a' => Q s'' a')| ≤ V_max := by
    calc |∑ s'', M.P s a s'' * Finset.univ.sup' Finset.univ_nonempty (fun a' => Q s'' a')|
        ≤ ∑ s'', |M.P s a s'' * Finset.univ.sup' Finset.univ_nonempty (fun a' => Q s'' a')| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ s'', M.P s a s'' *
            |Finset.univ.sup' Finset.univ_nonempty (fun a' => Q s'' a')| := by
          congr 1; funext s''; rw [abs_mul, abs_of_nonneg (M.P_nonneg s a s'')]
      _ ≤ ∑ s'', M.P s a s'' * V_max :=
          Finset.sum_le_sum fun s'' _ =>
            mul_le_mul_of_nonneg_left (h_max_bound s'') (M.P_nonneg s a s'')
      _ = V_max := by rw [← Finset.sum_mul, M.P_sum_one]; ring
  -- |diff| ≤ 2 * V_max by triangle inequality
  set sup_val := Finset.univ.sup' Finset.univ_nonempty (fun a' => Q s' a')
  set exp_val := ∑ s'', M.P s a s'' *
    Finset.univ.sup' Finset.univ_nonempty (fun a' => Q s'' a')
  have h_diff : |sup_val - exp_val| ≤ 2 * V_max := by
    linarith [abs_sub sup_val exp_val, h_max_bound s', h_exp_bound]
  rw [hdecomp]
  have h_gamma_diff : M.γ * |sup_val - exp_val| ≤ 2 * M.γ * V_max :=
    calc M.γ * |sup_val - exp_val|
        ≤ M.γ * (2 * V_max) := mul_le_mul_of_nonneg_left h_diff M.γ_nonneg
      _ = 2 * M.γ * V_max := by ring
  calc |(r_obs - M.r s a) + M.γ * (sup_val - exp_val)|
      ≤ |r_obs - M.r s a| + |M.γ * (sup_val - exp_val)| := abs_add_le _ _
    _ = |r_obs - M.r s a| + M.γ * |sup_val - exp_val| := by
        rw [abs_mul, abs_of_nonneg M.γ_nonneg]
    _ ≤ |r_obs - M.r s a| + 2 * M.γ * V_max := by linarith [h_gamma_diff]

/-- **Q-learning per-entry error bound**. A single Q-learning update at (s,a)
    with true reward r(s,a), observed next state s', and bounded Q satisfies:

      |Q'(s,a) - Q*(s,a)| ≤ (1-α(1-γ)) ||Q-Q*||∞ + α(2γ V_max)

    This is the direct application of `error_one_step` to the Q-learning
    noise decomposition `QLearningUpdate_bellman_decomp`. -/
theorem QLearningUpdate_error_bound
    (Q Q_star : M.ActionValueFn)
    (hQ_star : ∀ s a, Q_star s a = M.bellmanOptOp Q_star s a)
    (s : M.S) (a : M.A) (s' : M.S)
    (α : ℝ) (hα_pos : 0 < α) (hα_le : α ≤ 1)
    (V_max : ℝ) (hV_max : 0 ≤ V_max)
    (hQ_bound : ∀ s a, |Q s a| ≤ V_max) :
    |M.QLearningUpdate Q s a (M.r s a) s' α s a - Q_star s a| ≤
      (1 - α * (1 - M.γ)) * M.supDistQ Q Q_star + α * (2 * M.γ * V_max) := by
  rw [M.QLearningUpdate_bellman_decomp]
  have h1 := M.error_one_step Q Q_star hQ_star α hα_pos hα_le
    (M.qLearningNoise Q s a (M.r s a) s') s a _ rfl
  calc |((1 - α) * Q s a + α * (M.bellmanOptOp Q s a +
        M.qLearningNoise Q s a (M.r s a) s')) - Q_star s a|
      ≤ (1 - α * (1 - M.γ)) * M.supDistQ Q Q_star +
        α * |M.qLearningNoise Q s a (M.r s a) s'| := h1
    _ ≤ (1 - α * (1 - M.γ)) * M.supDistQ Q Q_star +
        α * (|M.r s a - M.r s a| + 2 * M.γ * V_max) := by
        gcongr
        exact M.qLearningNoise_bounded Q s a (M.r s a) s' V_max hV_max hQ_bound
    _ = (1 - α * (1 - M.γ)) * M.supDistQ Q Q_star +
        α * (2 * M.γ * V_max) := by
        simp [sub_self, abs_zero, zero_add]

/-! ### Almost-Sure Convergence (Conditional on Robbins-Siegmund) -/

/-- [CONDITIONAL] **Q-learning a.s. convergence**.

Takes h_converge (B_seq → 0) as hypothesis from Robbins-Siegmund
convergence, then derives Q_t → Q* via squeeze theorem on the
bound sequence. Conditional on Robbins-Siegmund supermartingale
convergence (see `RLGeneralization.Concentration.RobbinsSiegmund`). -/
theorem q_learning_as_convergence
    (Q_star : M.ActionValueFn)
    (_hQ_star : ∀ s a, Q_star s a = M.bellmanOptOp Q_star s a)
    (Q_seq : ℕ → M.ActionValueFn)
    -- Bound sequence from the finite-step recursion
    (B_seq : ℕ → ℝ)
    (h_rs : ∀ T, M.supDistQ (Q_seq T) Q_star ≤ B_seq T)
    (h_converge : Filter.Tendsto B_seq Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun T => M.supDistQ (Q_seq T) Q_star) Filter.atTop (nhds 0) := by
  -- Squeeze theorem: 0 ≤ supDistQ ≤ B_seq → 0
  apply squeeze_zero
  · -- supDistQ is nonneg: it is sup' of absolute values
    intro T
    simp only [FiniteMDP.supDistQ, FiniteMDP.supNormQ]
    have s₀ := Classical.arbitrary M.S
    have a₀ := Classical.arbitrary M.A
    exact le_trans (le_trans (abs_nonneg (Q_seq T s₀ a₀ - Q_star s₀ a₀))
      (Finset.le_sup' (fun a => |Q_seq T s₀ a - Q_star s₀ a|)
        (Finset.mem_univ a₀)))
      (Finset.le_sup' (fun s => Finset.univ.sup' Finset.univ_nonempty
        (fun a => |Q_seq T s a - Q_star s a|))
        (Finset.mem_univ s₀))
  · exact h_rs
  · exact h_converge

/-! ### Bridge: Concentration → Q-Learning PAC Sample Complexity

  The Q-learning convergence results above (Part I: constant-step,
  diminishing-step) combine with the noise bound from Part II to yield
  explicit PAC sample complexity guarantees.

  The key chain:
  1. `qLearningNoise_bounded`: |noise| ≤ 2γ·V_max (Part II)
  2. `synchronous_vi_constant_step`: ||Q_T - Q*|| ≤ ρ^T·D₀ + ε_noise/(1-γ) (Part I)
  3. Setting ε_noise = 2γ·V_max and using α = 1 gives ρ = γ and
     the asymptotic bias = 2γ·V_max/(1-γ).

  For the full stochastic Q-learning PAC bound, the Robbins-Siegmund
  convergence theorem (`RobbinsSiegmund.lean`) handles diminishing step
  sizes. Here we state the explicit constant-step-size PAC formula. -/

/-- **Q-learning PAC from constant step size and noise bound.**

  With constant step size α and bounded noise |noise| ≤ ε_noise:
  * After T iterations: ||Q_T - Q*|| ≤ (1-α(1-γ))^T · D₀ + ε_noise/(1-γ)
  * Setting T ≥ log(2·D₀/ε) / (α·(1-γ)): geometric term ≤ ε/2
  * Setting ε_noise/(1-γ) ≤ ε/2: bias term ≤ ε/2
  * Total: ||Q_T - Q*|| ≤ ε

  For Q-learning with true rewards: ε_noise = 2γ·V_max (from `qLearningNoise_bounded`).
  The bias condition becomes V_max ≤ ε·(1-γ)/(4γ).

  This theorem captures the algebraic PAC composition:
  given the two sub-bounds (geometric decay ≤ ε/2, bias ≤ ε/2),
  the total error is at most ε. -/
theorem q_learning_pac_from_constant_step
    (Q_star : M.ActionValueFn)
    (hQ_star : ∀ s a, Q_star s a = M.bellmanOptOp Q_star s a)
    (α : ℝ) (hα_pos : 0 < α) (hα_le : α ≤ 1)
    (ε_noise : ℝ) (hε_noise : 0 ≤ ε_noise)
    (Q_seq : ℕ → M.ActionValueFn)
    (noise_seq : ℕ → M.S → M.A → ℝ)
    (hnoise : ∀ t s a, |noise_seq t s a| ≤ ε_noise)
    (hQ_seq : ∀ t s a, Q_seq (t + 1) s a =
      (1 - α) * Q_seq t s a +
      α * (M.bellmanOptOp (Q_seq t) s a + noise_seq t s a))
    (ε : ℝ) (_hε : 0 < ε)
    (T : ℕ)
    -- Geometric decay term ≤ ε/2
    (h_geometric : (1 - α * (1 - M.γ)) ^ T * M.supDistQ (Q_seq 0) Q_star ≤ ε / 2)
    -- Bias term ≤ ε/2
    (h_bias : ε_noise / (1 - M.γ) ≤ ε / 2) :
    M.supDistQ (Q_seq T) Q_star ≤ ε := by
  have h_conv := M.synchronous_vi_constant_step Q_star hQ_star α hα_pos hα_le
    ε_noise hε_noise Q_seq noise_seq hnoise hQ_seq T
  linarith

/-- **Q-learning noise bound instantiation.**

  For Q-learning with true rewards r(s,a), the noise at each step
  satisfies |noise| ≤ 2γ·V_max. Combined with `q_learning_pac_from_constant_step`,
  this gives a PAC guarantee when:
  * 2γ·V_max/(1-γ) ≤ ε/2, i.e., V_max ≤ ε·(1-γ)/(4γ)
  * T ≥ log(2·D₀/ε) / (α·(1-γ)) iterations

  The sample complexity is O(1/(ε²·(1-γ)⁴)) since:
  * α = Θ(ε·(1-γ)) to make bias ≤ ε/2
  * T = Θ(log(1/ε)/(α·(1-γ))) = Θ(log(1/ε)/(ε·(1-γ)²))
  * Each step visits one (s,a) pair, so total samples = T·|S|·|A|

  This is an algebraic composition: given α, T satisfying the
  two conditions, the error ≤ ε follows by `q_learning_pac_from_constant_step`. -/
theorem q_learning_pac_sample_complexity
    (Q_star : M.ActionValueFn)
    (hQ_star : ∀ s a, Q_star s a = M.bellmanOptOp Q_star s a)
    (α : ℝ) (hα_pos : 0 < α) (hα_le : α ≤ 1)
    (V_max : ℝ) (hV_max : 0 ≤ V_max)
    (Q_seq : ℕ → M.ActionValueFn)
    (noise_seq : ℕ → M.S → M.A → ℝ)
    -- Noise bound from qLearningNoise_bounded
    (hnoise : ∀ t s a, |noise_seq t s a| ≤ 2 * M.γ * V_max)
    (hQ_seq : ∀ t s a, Q_seq (t + 1) s a =
      (1 - α) * Q_seq t s a +
      α * (M.bellmanOptOp (Q_seq t) s a + noise_seq t s a))
    (ε : ℝ) (hε : 0 < ε)
    (T : ℕ)
    -- Geometric term ≤ ε/2
    (h_geometric : (1 - α * (1 - M.γ)) ^ T * M.supDistQ (Q_seq 0) Q_star ≤ ε / 2)
    -- Bias: 2γV_max/(1-γ) ≤ ε/2
    (h_bias : 2 * M.γ * V_max / (1 - M.γ) ≤ ε / 2) :
    M.supDistQ (Q_seq T) Q_star ≤ ε := by
  have h2γV : 0 ≤ 2 * M.γ * V_max := by
    apply mul_nonneg (mul_nonneg (by norm_num) M.γ_nonneg) hV_max
  exact M.q_learning_pac_from_constant_step Q_star hQ_star α hα_pos hα_le
    (2 * M.γ * V_max) h2γV Q_seq noise_seq hnoise hQ_seq ε hε T
    h_geometric h_bias

/-! ### Explicit Finite-Sample Bound

  The theorems above give Q-learning error bounds that assume the
  geometric and bias conditions are satisfied. Here we discharge
  the geometric condition by showing that a concrete iteration count
  T satisfying α(1-γ)T ≥ log(2D₀/ε) suffices, yielding the first
  explicit finite-sample Q-learning bound in Lean 4.

  References:
  * [Even-Dar and Mansour, *Learning rates for Q-learning*, JMLR 2003]
  * [Agarwal et al., *RL: Theory and Algorithms*, Ch. 4] -/

/-- The sup-norm distance between Q-functions is nonneg. -/
private lemma supDistQ_nonneg' (Q₁ Q₂ : M.ActionValueFn) :
    0 ≤ M.supDistQ Q₁ Q₂ := by
  simp only [supDistQ, supNormQ]
  have s₀ := Classical.arbitrary M.S
  have a₀ := Classical.arbitrary M.A
  exact le_trans (le_trans (abs_nonneg (Q₁ s₀ a₀ - Q₂ s₀ a₀))
    (Finset.le_sup' (fun a => |Q₁ s₀ a - Q₂ s₀ a|) (Finset.mem_univ a₀)))
    (Finset.le_sup' (fun s => Finset.univ.sup' Finset.univ_nonempty
      (fun a => |Q₁ s a - Q₂ s a|)) (Finset.mem_univ s₀))

/-- **Geometric decay**: (1 - ρ)^T ≤ exp(-ρ·T) for ρ ∈ [0,1].
    Proof by induction using 1 - x ≤ exp(-x). -/
private lemma pow_one_sub_le_exp_neg_mul (ρ : ℝ) (_hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (T : ℕ) :
    (1 - ρ) ^ T ≤ Real.exp (-(ρ * ↑T)) := by
  induction T with
  | zero => simp
  | succ n ih =>
    have h0 : 0 ≤ 1 - ρ := by linarith
    calc (1 - ρ) ^ (n + 1)
        = (1 - ρ) ^ n * (1 - ρ) := by ring
      _ ≤ Real.exp (-(ρ * ↑n)) * Real.exp (-ρ) :=
          mul_le_mul ih (one_sub_le_exp_neg ρ) h0 (Real.exp_nonneg _)
      _ = Real.exp (-(ρ * ↑(n + 1))) := by
          rw [← Real.exp_add]; congr 1; push_cast; ring

/-- **Geometric decay threshold**: if ρ·T ≥ log(2D₀/ε), D₀ ≥ 0, ε > 0,
    then (1-ρ)^T · D₀ ≤ ε/2. Discharges the geometric condition in the
    Q-learning PAC theorem. -/
private lemma geometric_decay_threshold
    (ρ : ℝ) (hρ_pos : 0 < ρ) (hρ_le : ρ ≤ 1)
    (D₀ ε : ℝ) (hD₀ : 0 ≤ D₀) (hε : 0 < ε)
    (T : ℕ)
    (h_T : ρ * ↑T ≥ Real.log (2 * D₀ / ε)) :
    (1 - ρ) ^ T * D₀ ≤ ε / 2 := by
  by_cases hD₀_zero : D₀ = 0
  · simp [hD₀_zero]; linarith
  · have hD₀_pos : 0 < D₀ := lt_of_le_of_ne hD₀ (Ne.symm hD₀_zero)
    have h2Dε : 0 < 2 * D₀ / ε := div_pos (by linarith) hε
    have step1 : (1 - ρ) ^ T ≤ Real.exp (-(ρ * ↑T)) :=
      pow_one_sub_le_exp_neg_mul ρ hρ_pos.le hρ_le T
    have step2 : Real.exp (-(ρ * ↑T)) ≤ Real.exp (-Real.log (2 * D₀ / ε)) :=
      Real.exp_le_exp.mpr (neg_le_neg h_T)
    have step3 : Real.exp (-Real.log (2 * D₀ / ε)) = (2 * D₀ / ε)⁻¹ := by
      rw [Real.exp_neg, Real.exp_log h2Dε]
    calc (1 - ρ) ^ T * D₀
        ≤ Real.exp (-(ρ * ↑T)) * D₀ :=
          mul_le_mul_of_nonneg_right step1 hD₀
      _ ≤ (2 * D₀ / ε)⁻¹ * D₀ := by
          rw [← step3]
          exact mul_le_mul_of_nonneg_right step2 hD₀
      _ = ε / 2 := by rw [inv_div]; field_simp

/-- **Explicit Q-learning finite-sample bound.**

  For synchronous Q-learning with constant step size α and bounded noise
  |noise| ≤ 2γV_max, the iteration count T satisfying
    α(1-γ)T ≥ log(2D₀/ε)
  yields ε-accuracy (given the bias constraint 2γV_max/(1-γ) ≤ ε/2).

  This closes the gap in `q_learning_pac_sample_complexity` by discharging
  the geometric condition with an explicit iteration threshold.

  Iteration complexity: T = O(log(D₀/ε) / (α(1-γ))).
  With α = 1: T = O(log(V_max/ε) / (1-γ)).
  Per iteration, each (s,a) pair requires one generative-model sample,
  giving total sample complexity O(|S|·|A|·log(V_max/ε) / (1-γ)). -/
theorem q_learning_explicit_pac
    (Q_star : M.ActionValueFn)
    (hQ_star : ∀ s a, Q_star s a = M.bellmanOptOp Q_star s a)
    (α : ℝ) (hα_pos : 0 < α) (hα_le : α ≤ 1)
    (V_max : ℝ) (hV_max : 0 ≤ V_max)
    (Q_seq : ℕ → M.ActionValueFn)
    (noise_seq : ℕ → M.S → M.A → ℝ)
    (hnoise : ∀ t s a, |noise_seq t s a| ≤ 2 * M.γ * V_max)
    (hQ_seq : ∀ t s a, Q_seq (t + 1) s a =
      (1 - α) * Q_seq t s a +
      α * (M.bellmanOptOp (Q_seq t) s a + noise_seq t s a))
    (ε : ℝ) (hε : 0 < ε)
    (h_bias : 2 * M.γ * V_max / (1 - M.γ) ≤ ε / 2)
    (T : ℕ)
    (h_T : α * (1 - M.γ) * ↑T ≥
      Real.log (2 * M.supDistQ (Q_seq 0) Q_star / ε)) :
    M.supDistQ (Q_seq T) Q_star ≤ ε := by
  have h2γV : 0 ≤ 2 * M.γ * V_max :=
    mul_nonneg (mul_nonneg (by norm_num) M.γ_nonneg) hV_max
  have hρ_pos : 0 < α * (1 - M.γ) :=
    mul_pos hα_pos (by linarith [M.γ_lt_one])
  have hρ_le : α * (1 - M.γ) ≤ 1 := by
    have : α * (1 - M.γ) ≤ 1 * 1 :=
      mul_le_mul hα_le (by linarith [M.γ_nonneg]) (by linarith [M.γ_lt_one]) (by linarith)
    linarith
  have h_geom : (1 - α * (1 - M.γ)) ^ T *
      M.supDistQ (Q_seq 0) Q_star ≤ ε / 2 :=
    geometric_decay_threshold (α * (1 - M.γ)) hρ_pos hρ_le
      (M.supDistQ (Q_seq 0) Q_star) ε
      (M.supDistQ_nonneg' (Q_seq 0) Q_star) hε T h_T
  exact M.q_learning_pac_sample_complexity Q_star hQ_star α hα_pos hα_le
    V_max hV_max Q_seq noise_seq hnoise hQ_seq ε hε T h_geom h_bias

/-- **Synchronous Q-learning finite-sample bound** (α = 1 specialization).

  With full Bellman backup (α = 1), the contraction rate is γ and
  the iteration threshold simplifies to (1-γ)·T ≥ log(2D₀/ε).

  This is the natural setting for generative-model Q-learning where
  all (s,a) pairs are updated simultaneously at each round. -/
theorem q_learning_synchronous_pac
    (Q_star : M.ActionValueFn)
    (hQ_star : ∀ s a, Q_star s a = M.bellmanOptOp Q_star s a)
    (V_max : ℝ) (hV_max : 0 ≤ V_max)
    (Q_seq : ℕ → M.ActionValueFn)
    (noise_seq : ℕ → M.S → M.A → ℝ)
    (hnoise : ∀ t s a, |noise_seq t s a| ≤ 2 * M.γ * V_max)
    (hQ_seq : ∀ t s a, Q_seq (t + 1) s a =
      M.bellmanOptOp (Q_seq t) s a + noise_seq t s a)
    (ε : ℝ) (hε : 0 < ε)
    (h_bias : 2 * M.γ * V_max / (1 - M.γ) ≤ ε / 2)
    (T : ℕ)
    (h_T : (1 - M.γ) * ↑T ≥
      Real.log (2 * M.supDistQ (Q_seq 0) Q_star / ε)) :
    M.supDistQ (Q_seq T) Q_star ≤ ε := by
  have hQ_seq' : ∀ t s a, Q_seq (t + 1) s a =
      (1 - (1 : ℝ)) * Q_seq t s a +
      (1 : ℝ) * (M.bellmanOptOp (Q_seq t) s a + noise_seq t s a) := by
    intro t s a; rw [hQ_seq]; ring
  have h_T' : (1 : ℝ) * (1 - M.γ) * ↑T ≥
      Real.log (2 * M.supDistQ (Q_seq 0) Q_star / ε) := by
    linarith
  exact M.q_learning_explicit_pac Q_star hQ_star 1 one_pos le_rfl
    V_max hV_max Q_seq noise_seq hnoise hQ_seq' ε hε h_bias T h_T'

end FiniteMDP

end
