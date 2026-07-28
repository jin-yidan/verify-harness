/-
# Natural Policy Gradient

Abstract infrastructure for natural policy gradient updates and
convergence analysis via mirror descent.

## Main Definitions

* `NPGUpdate` - The NPG update rule: θ_{t+1} = θ_t + η · F⁻¹ · ∇J
* `NPGConvergenceData` - Packaging of NPG convergence parameters

## Main Results

* `npg_eta_nonneg` - Step size is nonneg
* `softmaxFisher_posSemidef` - Fisher information matrix is PSD
* `npg_one_step_gain_nonneg` - One-step gain nonneg when step size is small
* `npg_optimal_eta` - Optimal step size η* = sqrt(C/(D·T))
* `npg_convergence_rate` - Gap ≤ 2·sqrt(C·D/T) with optimal η

## References

* [Agarwal et al., *RL: Theory and Algorithms*]
* [Kakade, 2001, Natural Policy Gradient]
-/

import RLGeneralization.PolicyOptimization.PolicyGradient

open Finset BigOperators

noncomputable section

namespace FiniteMDP

variable (M : FiniteMDP)

/-! ### Natural Policy Gradient Update -/

/-- The natural policy gradient update structure.

  The NPG update is:
    θ_{t+1} = θ_t + η · F(θ_t)⁻¹ · ∇J(θ_t)

  where F(θ) is the Fisher information matrix. The key insight
  is that F⁻¹∇J is the steepest ascent direction in the space
  of distributions (rather than parameters), making NPG
  invariant to reparameterization.

  We represent the update abstractly: given the current gradient
  and the "natural gradient" (F⁻¹∇J), the update adds a step. -/
structure NPGUpdate (d : ℕ) where
  /-- Step size η > 0 -/
  η : ℝ
  /-- Step size is positive -/
  η_pos : 0 < η
  /-- The natural gradient direction: F(θ)⁻¹ · ∇J(θ) -/
  naturalGrad : (Fin d → ℝ) → (Fin d → ℝ)

/-- The step size η is nonneg. -/
theorem npg_eta_nonneg {d : ℕ} (upd : NPGUpdate d) :
    0 ≤ upd.η := le_of_lt upd.η_pos

/-! ### Fisher Information Matrix for Softmax

  For softmax π_θ(a|s) = exp(⟨θ,φ(s,a)⟩)/Z, the Fisher information
  at state s is:
    F_s(i,j) = ∑_a π(a|s) · (φ_i(s,a) − μ_i) · (φ_j(s,a) − μ_j)
  where μ_i = E_π[φ_i(s,·)] = ∑_a π(a|s) · φ_i(s,a).

  This is the covariance matrix of the features under π, and it is
  always positive semidefinite (as a sum of weighted outer products). -/

/-- The expected feature vector under softmax at state s. -/
def softmaxMeanFeature {d : ℕ}
    (φ : M.S → M.A → Fin d → ℝ) (θ : Fin d → ℝ) (s : M.S) (i : Fin d) : ℝ :=
  ∑ a, M.softmaxProb φ θ s a * φ s a i

/-- The centered feature: φ(s,a) − E_π[φ(s,·)]. -/
def softmaxCenteredFeature {d : ℕ}
    (φ : M.S → M.A → Fin d → ℝ) (θ : Fin d → ℝ) (s : M.S) (a : M.A) (i : Fin d) : ℝ :=
  φ s a i - M.softmaxMeanFeature φ θ s i

/-- The Fisher information matrix at state s for softmax policy.
    F_s(i,j) = E_π[(φ_i − μ_i)(φ_j − μ_j)] = Cov_π(φ_i, φ_j). -/
def softmaxFisher {d : ℕ}
    (φ : M.S → M.A → Fin d → ℝ) (θ : Fin d → ℝ) (s : M.S)
    (i j : Fin d) : ℝ :=
  ∑ a, M.softmaxProb φ θ s a *
    M.softmaxCenteredFeature φ θ s a i *
    M.softmaxCenteredFeature φ θ s a j

/-- **The Fisher information matrix is positive semidefinite.**

  For any vector v ∈ ℝ^d:
    vᵀ F_s v = ∑_a π(a|s) · (⟨v, φ(s,a) − μ⟩)² ≥ 0

  This is a genuine matrix-analysis theorem about the softmax
  parameterization. It follows from the outer product structure:
  F_s = ∑_a π(a) · (φ̃(a))(φ̃(a))ᵀ where φ̃ = φ − μ.

  The PSD property ensures the Fisher metric is well-defined. -/
theorem softmaxFisher_posSemidef {d : ℕ}
    (φ : M.S → M.A → Fin d → ℝ) (θ : Fin d → ℝ) (s : M.S)
    (v : Fin d → ℝ) :
    0 ≤ ∑ i : Fin d, ∑ j : Fin d,
      v i * M.softmaxFisher φ θ s i j * v j := by
  -- Rewrite as ∑_a π(a) · (∑_i v_i · (φ_i(a) − μ_i))²
  -- vᵀFv = ∑_a π(a) · (∑_i v_i · c_i(a))² ≥ 0
  -- Proof: expand F, distribute v, swap sums, factor as weighted sum of squares.
  -- vᵀFv = ∑_a π(a)(∑_i v_i c_i(a))² ≥ 0
  -- Step 1: Pull v into the sum over a, creating a triple sum
  have h_expand : ∀ (i j : Fin d),
      v i * softmaxFisher (M := M) φ θ s i j * v j =
      ∑ a, M.softmaxProb φ θ s a *
        (v i * M.softmaxCenteredFeature φ θ s a i) *
        (v j * M.softmaxCenteredFeature φ θ s a j) := by
    intro i j; simp only [softmaxFisher]
    rw [show v i * (∑ a, M.softmaxProb φ θ s a *
        M.softmaxCenteredFeature φ θ s a i *
        M.softmaxCenteredFeature φ θ s a j) * v j =
      ∑ a, v i * (M.softmaxProb φ θ s a *
        M.softmaxCenteredFeature φ θ s a i *
        M.softmaxCenteredFeature φ θ s a j) * v j from by
      rw [Finset.mul_sum]; simp_rw [Finset.sum_mul]]
    simp_rw [show ∀ a, v i * (M.softmaxProb φ θ s a *
        M.softmaxCenteredFeature φ θ s a i *
        M.softmaxCenteredFeature φ θ s a j) * v j =
      M.softmaxProb φ θ s a *
        (v i * M.softmaxCenteredFeature φ θ s a i) *
        (v j * M.softmaxCenteredFeature φ θ s a j) from fun a => by ring]
  simp_rw [h_expand]
  -- Goal: 0 ≤ ∑_i ∑_j ∑_a π · (v_i c_i) · (v_j c_j)
  -- Reorder to ∑_a ∑_i ∑_j, then factor as ∑_a π(∑_i v_i c_i)² ≥ 0
  calc (0 : ℝ)
      ≤ ∑ a, M.softmaxProb φ θ s a *
          (∑ i, v i * M.softmaxCenteredFeature φ θ s a i) ^ 2 :=
        Finset.sum_nonneg fun a _ =>
          mul_nonneg (M.softmaxProb_nonneg φ θ s a) (sq_nonneg _)
    _ = ∑ a, ∑ i : Fin d, ∑ j : Fin d,
          M.softmaxProb φ θ s a *
            (v i * M.softmaxCenteredFeature φ θ s a i) *
            (v j * M.softmaxCenteredFeature φ θ s a j) := by
        apply Finset.sum_congr rfl; intro a _
        rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _; ring
    _ = ∑ i : Fin d, ∑ a, ∑ j : Fin d,
          M.softmaxProb φ θ s a *
            (v i * M.softmaxCenteredFeature φ θ s a i) *
            (v j * M.softmaxCenteredFeature φ θ s a j) :=
        Finset.sum_comm
    _ = ∑ i : Fin d, ∑ j : Fin d, ∑ a,
          M.softmaxProb φ θ s a *
            (v i * M.softmaxCenteredFeature φ θ s a i) *
            (v j * M.softmaxCenteredFeature φ θ s a j) := by
        apply Finset.sum_congr rfl; intro i _; exact Finset.sum_comm

/-- The centered features sum to zero under π:
    ∑_a π(a|s) · (φ_i(s,a) − μ_i) = 0. -/
theorem softmax_centered_feature_mean_zero {d : ℕ}
    (φ : M.S → M.A → Fin d → ℝ) (θ : Fin d → ℝ) (s : M.S) (i : Fin d) :
    ∑ a, M.softmaxProb φ θ s a * M.softmaxCenteredFeature φ θ s a i = 0 := by
  simp only [softmaxCenteredFeature, softmaxMeanFeature]
  simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [M.softmaxProb_sum_one φ θ s (M.softmax_denom_pos φ θ s), one_mul, sub_self]

/-- **Advantage-weighted centered features.**

  For any advantage function A with E_π[A(s,·)] = 0 (consistent advantage):
    ∑_a π(a|s) · A(s,a) · (φ_i(s,a) − μ_i) = ∑_a π(a|s) · A(s,a) · φ_i(s,a)

  This is because the μ_i term vanishes: ∑_a π A · μ_i = μ_i · ∑_a π A = μ_i · 0 = 0.

  This identity shows that the NPG direction (F⁻¹∇J) can be computed using
  raw features φ instead of centered features φ − μ, simplifying computation. -/
theorem advantage_weighted_feature_centering {d : ℕ}
    (φ : M.S → M.A → Fin d → ℝ) (θ : Fin d → ℝ) (s : M.S)
    (A : M.A → ℝ)
    (h_zero_mean : ∑ a, M.softmaxProb φ θ s a * A a = 0)
    (i : Fin d) :
    ∑ a, M.softmaxProb φ θ s a * A a * M.softmaxCenteredFeature φ θ s a i =
    ∑ a, M.softmaxProb φ θ s a * A a * φ s a i := by
  simp only [softmaxCenteredFeature, softmaxMeanFeature]
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [show ∑ a, M.softmaxProb φ θ s a * A a * (∑ a', M.softmaxProb φ θ s a' * φ s a' i) =
    (∑ a', M.softmaxProb φ θ s a' * φ s a' i) * ∑ a, M.softmaxProb φ θ s a * A a from by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; ring]
  rw [h_zero_mean, mul_zero, sub_zero]

/-- **NPG update direction for softmax.**

  The advantage-weighted feature sum is the core of the NPG update.
  For consistent advantages (E_π[A] = 0), this gives the direction
  that the natural gradient computes:

    npgDir_i = ∑_a π(a|s) · A(s,a) · φ_i(s,a)

  Taking w_i = (1/(1-γ)) · ∑_s d^π(s) · npgDir_i(s) gives the
  full NPG update direction θ' = θ + η · w. -/
def npgDirectionAtState {d : ℕ}
    (φ : M.S → M.A → Fin d → ℝ) (θ : Fin d → ℝ) (s : M.S)
    (A : M.A → ℝ) (i : Fin d) : ℝ :=
  ∑ a, M.softmaxProb φ θ s a * A a * φ s a i

/-! ### NPG Convergence Analysis (Mirror Descent)

  The key convergence result for softmax NPG with step size η:

    V*(μ) - V^{π_T}(μ) ≤ log|A| / (η · T · (1 - γ)) + η / (1 - γ)^3

  Optimizing η = sqrt(log|A| · (1 - γ)^2 / T):

    V*(μ) - V^{π_T}(μ) ≤ 2 · sqrt(log|A| / (T · (1 - γ)^2)) / (1 - γ)

  We formalize the algebraic core of this analysis. The convergence
  argument proceeds by:

  1. **One-step improvement**: Each NPG iteration gains at least
     η · g_t - η^2 · p where g_t is the per-step advantage and p is a penalty.

  2. **Telescoping**: Sum T one-step gains and relate to suboptimality gap.

  3. **KL potential**: The KL divergence KL(π* || π_t) is a Lyapunov function
     with KL(π* || uniform) ≤ log|A|. This gives:
     T · min_t g_t ≤ sum_t g_t ≤ log|A| / η.

  4. **Rate optimization**: Choosing η = sqrt(C / (D · T)) yields the
     optimal O(1/sqrt(T)) convergence rate.

  We formalize steps 1-4 as algebraic theorems over real numbers.
-/

/-! #### One-Step Improvement -/

/-- **One-step gain is nonneg when step size is small.**

  If η ≤ g / p and g ≥ 0, then η · g - η^2 · p ≥ 0. -/
theorem npg_one_step_gain_nonneg
    (η g p : ℝ)
    (hη : 0 < η)
    (hp : 0 < p)
    (hsmall : η ≤ g / p) :
    0 ≤ η * g - η ^ 2 * p := by
  have hη_le : η * p ≤ g := by
    rwa [le_div_iff₀ hp] at hsmall
  nlinarith [sq_nonneg (g - η * p)]

/-! #### KL-Based Potential Argument -/

/-- **KL potential bound.**

  The KL divergence KL(π* || π_t) decreases by η · g_t per step.
  Starting from KL(π* || uniform) ≤ log|A|, after T steps:
    η · ∑_t g_t ≤ KL_0 ≤ log|A|

  Algebraically: if η · sum_g ≤ C (where C = log|A|), then
  sum_g ≤ C / η. -/
theorem npg_kl_potential_bound
    (η sum_g C : ℝ)
    (hη : 0 < η)
    (h_kl : η * sum_g ≤ C) :
    sum_g ≤ C / η := by
  rw [le_div_iff₀ hη]
  linarith [mul_comm η sum_g]

/-- **Average gap from KL bound.**

  If sum_g ≤ C / η and there are T steps, then
  the average per-step gap satisfies:
    avg_g = sum_g / T ≤ C / (η · T). -/
theorem npg_average_gap_bound
    (η sum_g C : ℝ) (T : ℕ)
    (_hη : 0 < η)
    (hT : 0 < (T : ℝ))
    (h_sum : sum_g ≤ C / η) :
    sum_g / ↑T ≤ C / (η * ↑T) := by
  exact div_le_div_of_nonneg_right h_sum (le_of_lt hT) |>.trans_eq (div_div C η ↑T)

/-! #### Convergence Rate -/

/-- **NPG convergence data.**

  Packages the algebraic parameters of the NPG convergence bound:
  - `C` = log|A| / (1 - γ), the KL-based numerator
  - `D` = 1 / (1 - γ)^3, the penalty coefficient
  - `η` = step size
  - `T` = number of iterations -/
structure NPGConvergenceData where
  /-- KL-based numerator C = log|A| / (1 - γ) -/
  C : ℝ
  /-- Penalty coefficient D = 1 / (1 - γ)^3 -/
  D : ℝ
  /-- Step size -/
  η : ℝ
  /-- Number of iterations -/
  T : ℕ
  /-- C is nonneg (log|A| ≥ 0, 1 - γ > 0) -/
  hC : 0 ≤ C
  /-- D is positive (since (1 - γ)^3 > 0) -/
  hD : 0 < D
  /-- η is positive -/
  hη : 0 < η
  /-- T is positive -/
  hT : 0 < T

/-- **Optimal step size for NPG.**

  The bound `C / (η · T) + η · D` is minimized by choosing
  `η = sqrt(C / (D · T))`. At this η, both terms are equal.

  We verify: with η* = sqrt(C / (D · T)),
    C / (η* · T) = sqrt(C · D / T)
    η* · D       = sqrt(C · D / T)
  so the total bound is 2 · sqrt(C · D / T).

  This theorem proves the algebraic identity:
    C / (η · T) + η · D = 2 · sqrt(C · D / T)
  when η^2 = C / (D · T). -/
theorem npg_optimal_eta
    (C D : ℝ) (T : ℕ)
    (_hC : 0 ≤ C) (hD : 0 < D) (hT : 0 < (T : ℝ))
    (η : ℝ) (hη : 0 < η)
    (h_opt : η ^ 2 = C / (D * ↑T)) :
    C / (η * ↑T) + η * D = 2 * (η * D) := by
  -- From η^2 = C / (D · T), we get C = η^2 · D · T
  have h_C_eq : C = η ^ 2 * D * ↑T := by
    have hDT : D * ↑T ≠ 0 := by positivity
    field_simp at h_opt
    linarith
  -- Then C / (η · T) = η^2 · D · T / (η · T) = η · D
  have _hηT : η * ↑T ≠ 0 := by positivity
  rw [h_C_eq]
  field_simp
  ring

/-- **NPG O(1/sqrt(T)) convergence rate.**

  With optimal step size η* = sqrt(C / (D · T)):
    gap ≤ 2 · sqrt(C · D / T)

  We prove: for any gap, η, C, D, T satisfying the convergence bound
  and the optimality condition η^2 = C / (D · T):
    gap ≤ 2 · η · D

  This gives the standard O(1/sqrt(T)) rate for NPG:
    V* - V^{π_T} ≤ 2 · sqrt(log|A| / (T · (1-γ)^2)) / (1-γ) -/
theorem npg_convergence_rate
    (C D gap : ℝ) (T : ℕ)
    (hC : 0 ≤ C) (hD : 0 < D) (hT : 0 < (T : ℝ))
    (η : ℝ) (hη : 0 < η)
    (h_opt : η ^ 2 = C / (D * ↑T))
    (h_gap : gap ≤ C / (η * ↑T) + η * D) :
    gap ≤ 2 * (η * D) := by
  have h_eq := npg_optimal_eta C D T hC hD hT η hη h_opt
  linarith

/-- **NPG rate in terms of sqrt.**

  With η = sqrt(C / (D · T)), the bound 2 · η · D equals
  2 · D · sqrt(C / (D · T)) = 2 · sqrt(C · D / T).

  Algebraic identity: (2 · η · D)^2 = 4 · C · D / T
  when η^2 = C / (D · T). -/
theorem npg_rate_sq_identity
    (C D : ℝ) (T : ℕ)
    (_hC : 0 ≤ C) (hD : 0 < D) (hT : 0 < (T : ℝ))
    (η : ℝ) (hη : 0 < η)
    (h_opt : η ^ 2 = C / (D * ↑T)) :
    (2 * (η * D)) ^ 2 = 4 * C * D / ↑T := by
  have _hDT : D * ↑T ≠ 0 := by positivity
  have h_C_eq : C = η ^ 2 * D * ↑T := by
    field_simp at h_opt; linarith
  rw [h_C_eq]
  field_simp
  ring

/-! #### Instantiation for Discounted MDPs -/

/-- **NPG convergence for discounted MDPs (algebraic form).**

  For the specific constants in the discounted MDP setting:
    C = log_A / (1 - γ)
    D = 1 / (1 - γ)^3

  The optimal rate becomes:
    gap ≤ 2 · sqrt(log_A / (T · (1 - γ)^2)) / (1 - γ)
        = 2 · sqrt(log_A / T) / (1 - γ)^2

  This theorem verifies the relationship between C, D, and the
  discount-factor-dependent constants. -/
theorem npg_discounted_constants
    (log_A : ℝ) (γ : ℝ)
    (hlog : 0 ≤ log_A)
    (hγ1 : γ < 1) :
    let C := log_A / (1 - γ)
    let D := 1 / (1 - γ) ^ 3
    0 ≤ C ∧ 0 < D ∧ C * D = log_A / (1 - γ) ^ 4 := by
  have h1mγ : (0 : ℝ) < 1 - γ := by linarith
  refine ⟨div_nonneg hlog (le_of_lt h1mγ),
         div_pos one_pos (pow_pos h1mγ 3), ?_⟩
  show log_A / (1 - γ) * (1 / (1 - γ) ^ 3) = log_A / (1 - γ) ^ 4
  field_simp

/-- [CONDITIONAL] **NPG convergence with MDP discount factor.**

  Takes h_gap (gap ≤ C/(η·T) + η·D) and h_opt (optimal step size)
  as hypotheses, then derives gap ≤ 2·η·D via `npg_convergence_rate`.
  Conditional on the performance difference lemma and softmax policy
  gradient identity that produce the h_gap bound. -/
theorem npg_discounted_convergence
    (log_A γ gap : ℝ) (T : ℕ)
    (hlog : 0 ≤ log_A)
    (hγ1 : γ < 1)
    (hT : 0 < (T : ℝ))
    (η : ℝ) (hη : 0 < η)
    (h_opt : η ^ 2 = (log_A / (1 - γ)) / (1 / (1 - γ) ^ 3 * ↑T))
    (h_gap : gap ≤ (log_A / (1 - γ)) / (η * ↑T) + η * (1 / (1 - γ) ^ 3)) :
    gap ≤ 2 * (η * (1 / (1 - γ) ^ 3)) := by
  have h1mγ : 0 < 1 - γ := by linarith
  exact npg_convergence_rate
    (log_A / (1 - γ)) (1 / (1 - γ) ^ 3) gap T
    (div_nonneg hlog (le_of_lt h1mγ))
    (div_pos one_pos (pow_pos h1mγ 3)) hT η hη
    h_opt h_gap

/-- **Sample complexity of NPG.**

  To achieve gap ≤ ε with optimal step size, we need T ≥ 4 · C · D / ε^2.
  Algebraic version: if 4 · C · D / ε^2 ≤ T and η^2 = C / (D · T),
  then 2 · η · D ≤ ε.

  We prove: (2 · η · D)^2 ≤ ε^2 when T ≥ 4 · C · D / ε^2,
  using the identity (2 · η · D)^2 = 4 · C · D / T. -/
theorem npg_sample_complexity
    (C D ε : ℝ) (T : ℕ)
    (hC : 0 ≤ C) (hD : 0 < D) (hε : 0 < ε)
    (hT : 0 < (T : ℝ))
    (η : ℝ) (hη : 0 < η)
    (h_opt : η ^ 2 = C / (D * ↑T))
    (h_T_large : 4 * C * D / ε ^ 2 ≤ ↑T) :
    (2 * (η * D)) ^ 2 ≤ ε ^ 2 := by
  have h_sq := npg_rate_sq_identity C D T hC hD hT η hη h_opt
  rw [h_sq]
  rw [div_le_iff₀ hT]
  have hε2 : (0 : ℝ) < ε ^ 2 := by positivity
  have h1 : 4 * C * D ≤ ↑T * ε ^ 2 := by
    calc 4 * C * D = 4 * C * D / ε ^ 2 * ε ^ 2 := by
          rw [div_mul_cancel₀ _ (ne_of_gt hε2)]
      _ ≤ ↑T * ε ^ 2 := by
          have : 4 * C * D / ε ^ 2 * ε ^ 2 ≤ ↑T * ε ^ 2 :=
            mul_le_mul_of_nonneg_right h_T_large (le_of_lt hε2)
          exact this
  linarith

/-! ### Full End-to-End NPG Convergence Rate

  The complete NPG convergence result for discounted MDPs eliminates
  the intermediate step-size parameter η and states the bound purely
  in terms of the problem parameters:

    V* - V^{π_T} ≤ 2 · √(log|A| / (T · (1-γ)⁴))

  This composes:
  1. Mirror descent analysis → gap ≤ C/(η·T) + η·D
  2. Optimal step size η* = √(C/(D·T))
  3. Substitution: 2·η*·D = 2·√(C·D/T) = 2·√(log|A|/((1-γ)⁴·T))
-/

/-- **NPG end-to-end convergence: V* - V^{π_T} ≤ 2·√(log|A|/(T·(1-γ)⁴)).**

  This is the clean final form of NPG convergence for softmax policies
  in discounted MDPs. The intermediate step-size η is eliminated by
  substitution.

  The bound has:
  - log|A|: entropy of the action space (initialization cost)
  - (1-γ)⁴: discount factor dependence (C contributes (1-γ)⁻¹, D contributes (1-γ)⁻³)
  - T: number of NPG iterations (standard online learning rate)

  Takes the NPG mirror-descent bound and optimal step size as
  hypotheses; proves η·D = √(C·D/T) from h_opt via sqrt algebra,
  then composes to get the clean convergence rate. -/
theorem npg_full_rate_clean
    (log_A γ gap : ℝ) (T : ℕ)
    (hlog : 0 ≤ log_A) (hγ1 : γ < 1) (hT : 0 < (T : ℝ))
    (η : ℝ) (hη : 0 < η)
    (h_opt : η ^ 2 = (log_A / (1 - γ)) / (1 / (1 - γ) ^ 3 * ↑T))
    (h_gap : gap ≤ (log_A / (1 - γ)) / (η * ↑T) + η * (1 / (1 - γ) ^ 3)) :
    gap ≤ 2 * Real.sqrt (log_A / ((1 - γ) ^ 4 * ↑T)) := by
  have h1mγ : 0 < 1 - γ := by linarith
  have hD : (0 : ℝ) < 1 / (1 - γ) ^ 3 := div_pos one_pos (pow_pos h1mγ 3)
  -- Prove η · D = √(log_A / ((1-γ)⁴ · T)) from h_opt
  have h_eta_sqrt : η * (1 / (1 - γ) ^ 3) =
      Real.sqrt (log_A / ((1 - γ) ^ 4 * ↑T)) := by
    have hηD_pos : 0 < η * (1 / (1 - γ) ^ 3) := mul_pos hη hD
    rw [← Real.sqrt_sq hηD_pos.le]
    congr 1
    -- (η · D)² = η² · D² = (C/(D·T)) · D² = C·D/T
    have hD_ne : (1 - γ) ^ 3 ≠ 0 := ne_of_gt (pow_pos h1mγ 3)
    have hT_ne : (T : ℝ) ≠ 0 := ne_of_gt hT
    field_simp at h_opt ⊢
    nlinarith [h_opt, sq_nonneg η, sq_nonneg (1 - γ)]
  have h_step := npg_discounted_convergence log_A γ gap T hlog hγ1 hT η hη h_opt h_gap
  linarith [h_eta_sqrt]

/-- **NPG sample complexity (clean form).**

  To achieve V* - V^{π_T} ≤ ε, NPG requires
    T ≥ 4 · log|A| / (ε² · (1-γ)⁴)
  iterations with optimal step size.

  Proved: from T ≥ 4L/(ε²D), derive L/(DT) ≤ ε²/4,
  hence √(L/(DT)) ≤ ε/2, hence 2√(L/(DT)) ≤ ε. -/
theorem npg_sample_complexity_clean
    (log_A γ ε : ℝ) (T : ℕ)
    (_hlog : 0 ≤ log_A) (_hγ1 : γ < 1) (hε : 0 < ε)
    (hT : 0 < (T : ℝ))
    (h_T_large : 4 * log_A / (ε ^ 2 * (1 - γ) ^ 4) ≤ ↑T)
    (_hγ : 0 ≤ γ) :
    ∀ gap : ℝ,
      gap ≤ 2 * Real.sqrt (log_A / ((1 - γ) ^ 4 * ↑T)) →
      gap ≤ ε := by
  intro gap h_gap
  suffices h : 2 * Real.sqrt (log_A / ((1 - γ) ^ 4 * ↑T)) ≤ ε by linarith
  have hD : (0 : ℝ) < (1 - γ) ^ 4 := pow_pos (by linarith) 4
  have hDT : (0 : ℝ) < (1 - γ) ^ 4 * ↑T := mul_pos hD hT
  -- Step 1: L/(DT) ≤ ε²/4
  have h_ratio : log_A / ((1 - γ) ^ 4 * ↑T) ≤ ε ^ 2 / 4 := by
    rw [div_le_iff₀ hDT]
    -- Goal: log_A ≤ ε ^ 2 / 4 * ((1 - γ) ^ 4 * ↑T)
    have hε2D : 0 < ε ^ 2 * (1 - γ) ^ 4 := mul_pos (sq_pos_of_pos hε) hD
    have h1 : 4 * log_A ≤ ↑T * (ε ^ 2 * (1 - γ) ^ 4) := by
      rwa [div_le_iff₀ hε2D] at h_T_large
    nlinarith
  -- Step 2: √(L/(DT)) ≤ ε/2
  have h_sqrt : Real.sqrt (log_A / ((1 - γ) ^ 4 * ↑T)) ≤ ε / 2 := by
    calc Real.sqrt (log_A / ((1 - γ) ^ 4 * ↑T))
        ≤ Real.sqrt (ε ^ 2 / 4) := Real.sqrt_le_sqrt h_ratio
      _ = ε / 2 := by
          rw [show ε ^ 2 / 4 = (ε / 2) ^ 2 from by ring]
          exact Real.sqrt_sq (by linarith)
  -- Step 3: 2 * √(...) ≤ ε
  linarith

end FiniteMDP

end
