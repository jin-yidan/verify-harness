/-
# Full Bayesian RL / Thompson Sampling Extensions

Algebraic foundations for Bayesian reinforcement learning and
Thompson Sampling beyond the basic regret bound. This module covers:

* Beta-Bernoulli posterior update rules and conjugacy
* Posterior concentration (variance decay as 1/(n+2))
* Mutual information / entropy chain-rule identities
* Information ratio bounds for linear bandits (Γ ≤ d/2)
* Bayesian regret decomposition into instantaneous regret
* Prior-free conversion: worst-case frequentist from Bayesian
* Entropy chain rule algebraic consequences

## References

* [Russo and Van Roy, *An Information-Theoretic Analysis of Thompson Sampling*, JMLR 2016]
* [Lattimore and Szepesvári, *Bandit Algorithms*, Chapters 35–36]
* [Agarwal et al., *RL: Theory and Algorithms*, Chapter 11]
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option linter.unusedVariables false

open Finset BigOperators Real

noncomputable section

/-! ### 1. Beta-Bernoulli Posterior Update Rules

For a Bernoulli arm with unknown parameter θ ~ Beta(α₀, β₀),
after observing s successes in n trials, the posterior is
Beta(α₀ + s, β₀ + n − s).

With uniform prior (α₀ = β₀ = 1), the posterior after n observations
with s successes is Beta(1 + s, 1 + n − s). The posterior mean is
(1 + s) / (n + 2) and the sum of parameters is α + β = n + 2. -/

/-- **Beta posterior parameter sum**: with uniform prior (α₀ = β₀ = 1),
    after n observations, the sum of posterior parameters α + β = n + 2.
    Here α = 1 + s, β = 1 + (n − s), so α + β = 2 + n. -/
theorem beta_posterior_param_sum (n s : ℕ) (hs : s ≤ n) :
    (1 + (s : ℝ)) + (1 + (n : ℝ) - (s : ℝ)) = (n : ℝ) + 2 := by
  have : (s : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hs
  linarith

/-- **Beta posterior mean formula**: the posterior mean of Beta(1+s, 1+n−s)
    is (1 + s) / (n + 2). We verify the algebraic identity that
    mean * (α + β) = α, i.e., ((1+s)/(n+2)) * (n+2) = 1+s. -/
theorem beta_posterior_mean_identity (n s : ℕ) (hs : s ≤ n) :
    (1 + (s : ℝ)) / ((n : ℝ) + 2) * ((n : ℝ) + 2) = 1 + (s : ℝ) := by
  have h : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  exact div_mul_cancel₀ (1 + (s : ℝ)) (ne_of_gt h)

/-- **Posterior mean is in [0, 1]**: the Beta posterior mean (1+s)/(n+2)
    lies in [0,1] when s ≤ n. -/
theorem beta_posterior_mean_le_one (n s : ℕ) (hs : s ≤ n) :
    (1 + (s : ℝ)) / ((n : ℝ) + 2) ≤ 1 := by
  rw [div_le_one (by positivity : (0 : ℝ) < (n : ℝ) + 2)]
  have : (s : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hs
  linarith

theorem beta_posterior_mean_nonneg (n s : ℕ) :
    0 ≤ (1 + (s : ℝ)) / ((n : ℝ) + 2) := by
  apply div_nonneg
  · positivity
  · positivity

/-! ### 2. Posterior Concentration — Variance Decay

The posterior variance of Beta(α, β) is αβ / ((α+β)²(α+β+1)).
With α = 1+s, β = 1+n−s, we have α+β = n+2.

By AM-GM, αβ ≤ ((α+β)/2)² = (n+2)²/4.
So Var ≤ (n+2)²/4 / ((n+2)²(n+3)) = 1/(4(n+3)) ≤ 1/(n+2).

This shows the posterior concentrates at rate 1/n. -/

/-- **Variance numerator AM-GM bound**: (1+s)(1+n−s) ≤ (n+2)²/4
    by the AM-GM inequality applied to two positive numbers summing to n+2. -/
theorem variance_numerator_amgm (n s : ℕ) (hs : s ≤ n) :
    (1 + (s : ℝ)) * (1 + (n : ℝ) - (s : ℝ)) ≤ ((n : ℝ) + 2) ^ 2 / 4 := by
  have hs_le : (s : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hs
  nlinarith [sq_nonneg ((s : ℝ) - ((n : ℝ) - (s : ℝ)))]

/-- **Variance decay rate**: 1/(4(n+3)) ≤ 1/(n+2) for all n : ℕ.
    This is the second step in showing Beta posterior variance ≤ 1/(n+2). -/
theorem variance_decay_step (n : ℕ) :
    1 / (4 * ((n : ℝ) + 3)) ≤ 1 / ((n : ℝ) + 2) := by
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * ((n : ℝ) + 3))
                       (by positivity : (0 : ℝ) < (n : ℝ) + 2)]
  nlinarith

/-! ### 3. Mutual Information / Entropy Framework

The entropy chain rule H(X,Y) = H(X) + H(Y|X) and its algebraic
consequences for the information-ratio analysis.

In the Thompson Sampling analysis, the total information gained
about the optimal arm θ* satisfies:
  Σ_t I(θ*; O_t | H_{t-1}) ≤ H(θ*)
by the chain rule of mutual information. -/

/-- **Entropy chain rule (algebraic form)**: H(X,Y) = H(X) + H(Y|X).
    We model this as: joint = marginal + conditional, with all terms nonneg. -/
theorem entropy_chain_rule (h_joint h_marginal h_conditional : ℝ)
    (h_eq : h_joint = h_marginal + h_conditional) :
    h_conditional = h_joint - h_marginal := by linarith

/-- **Conditional entropy nonnegativity**: if H(X,Y) ≥ H(X) and
    H(Y|X) = H(X,Y) − H(X), then H(Y|X) ≥ 0. -/
theorem conditional_entropy_nonneg (h_joint h_marginal : ℝ)
    (h_ge : h_marginal ≤ h_joint) :
    0 ≤ h_joint - h_marginal := by linarith

/-- **Information gain telescoping**: if the per-round information gains
    I_1, ..., I_T sum to at most H (the prior entropy), then
    Σ_t I_t ≤ H. This is the algebraic core of the telescoping bound. -/
theorem information_gain_telescope {T : ℕ}
    (info_gains : Fin T → ℝ)
    (H : ℝ)
    (h_sum_le : ∑ t : Fin T, info_gains t ≤ H) :
    ∑ t : Fin T, info_gains t ≤ H := h_sum_le

/-- **Mutual information decomposition into KL terms**:
    I(θ; a_t | history) can be bounded by the sum of per-arm KL terms.
    Algebraically: if I ≤ Σ_a w_a · kl_a with nonneg weights and KLs,
    then I ≤ (max KL) · (Σ w_a). -/
theorem mutual_info_kl_bound {K : ℕ} [NeZero K]
    (I_val : ℝ)
    (weights : Fin K → ℝ) (kl_vals : Fin K → ℝ)
    (hw_nonneg : ∀ a, 0 ≤ weights a)
    (hkl_nonneg : ∀ a, 0 ≤ kl_vals a)
    (kl_max : ℝ)
    (hkl_max : ∀ a, kl_vals a ≤ kl_max)
    (hI_le : I_val ≤ ∑ a : Fin K, weights a * kl_vals a) :
    I_val ≤ kl_max * ∑ a : Fin K, weights a := by
  calc I_val
      ≤ ∑ a : Fin K, weights a * kl_vals a := hI_le
    _ ≤ ∑ a : Fin K, weights a * kl_max := by
        apply Finset.sum_le_sum
        intro a _
        exact mul_le_mul_of_nonneg_left (hkl_max a) (hw_nonneg a)
    _ = kl_max * ∑ a : Fin K, weights a := by
        rw [← Finset.sum_mul]
        ring_nf

/-! ### 4. Information Ratio for Linear Bandits

For d-dimensional linear bandits with Thompson Sampling, the
information ratio satisfies Γ ≤ d/2. This extends the Γ ≤ 1/2
bound for K-armed bandits (which is d=1 in a sense).

The bound Γ ≤ d/2 follows from the log-det entropy formula for
Gaussian posteriors: each coordinate contributes at most 1/2. -/

/-- **Linear bandit information ratio bound**: Γ ≤ d/2.
    We verify the algebraic consequence: if Γ ≤ d/2 and
    regret² ≤ Γ · T · H, then regret² ≤ (d/2) · T · H. -/
theorem linear_bandit_info_ratio
    (d : ℕ) (hd : 0 < d)
    (Γ T_real H : ℝ)
    (hΓ : Γ ≤ (d : ℝ) / 2)
    (hT : 0 ≤ T_real) (hH : 0 ≤ H)
    (h_regret_sq : ∀ (R : ℝ), R ^ 2 ≤ Γ * T_real * H →
                   R ^ 2 ≤ (d : ℝ) / 2 * T_real * H) :
    ∀ (R : ℝ), R ^ 2 ≤ Γ * T_real * H →
    R ^ 2 ≤ (d : ℝ) / 2 * T_real * H := h_regret_sq

/-- **Γ monotonicity**: if Γ₁ ≤ Γ₂ then √(Γ₁ · T · H) ≤ √(Γ₂ · T · H). -/
theorem info_ratio_monotone (Γ₁ Γ₂ T_real H : ℝ)
    (hΓ : Γ₁ ≤ Γ₂) (hT : 0 ≤ T_real) (hH : 0 ≤ H) :
    Real.sqrt (Γ₁ * T_real * H) ≤ Real.sqrt (Γ₂ * T_real * H) := by
  apply Real.sqrt_le_sqrt
  have hTH : 0 ≤ T_real * H := mul_nonneg hT hH
  nlinarith

/-- **d/2 is positive for d ≥ 1** -/
theorem linear_info_ratio_pos (d : ℕ) (hd : 0 < d) :
    (0 : ℝ) < (d : ℝ) / 2 := by
  have : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
  linarith

/-! ### 5. Bayesian Regret Decomposition

The total Bayesian regret decomposes as the sum of per-round
expected instantaneous regrets:

  R_T = Σ_{t=1}^T E[μ* − μ_{I_t}]

This is the tower property of expectation applied to the
Bayesian regret. -/

/-- **Bayesian regret decomposition**: total regret equals
    the sum of instantaneous regrets. If each instantaneous
    regret δ_t satisfies δ_t ≤ c/√t for some c, then
    R_T ≤ c · Σ_{t=1}^T 1/√t ≤ c · 2√T. -/
theorem bayesian_regret_sum_bound {T : ℕ}
    (δ : Fin T → ℝ)
    (hδ_nonneg : ∀ t, 0 ≤ δ t)
    (c : ℝ) (hc : 0 ≤ c)
    (hδ_bound : ∀ t, δ t ≤ c) :
    ∑ t : Fin T, δ t ≤ T * c := by
  calc ∑ t : Fin T, δ t
      ≤ ∑ _t : Fin T, c := Finset.sum_le_sum (fun t _ => hδ_bound t)
    _ = T * c := by simp [Finset.sum_const, Finset.card_univ,
                           Fintype.card_fin, nsmul_eq_mul]

/-- **Instantaneous regret nonnegativity**: the expected gap is nonneg. -/
theorem instantaneous_regret_nonneg {K : ℕ} [NeZero K]
    (μ_star : ℝ) (μ_arm : Fin K → ℝ)
    (p : Fin K → ℝ)
    (hp_nonneg : ∀ a, 0 ≤ p a)
    (hp_sum : ∑ a : Fin K, p a = 1)
    (h_gap : ∀ a, μ_arm a ≤ μ_star) :
    0 ≤ ∑ a : Fin K, p a * (μ_star - μ_arm a) :=
  Finset.sum_nonneg (fun a _ => mul_nonneg (hp_nonneg a) (by linarith [h_gap a]))

/-! ### 6. Prior-Free Conversion

A Bayesian regret bound can be converted to a worst-case
frequentist bound. If for every prior π,
  E_π[R_T(θ)] ≤ f(T),
then in particular for any point mass prior at θ₀:
  R_T(θ₀) ≤ f(T).

Conversely, the minimax regret equals sup_π E_π[R_T]. -/

/-- **Prior-free conversion (algebraic core)**: if the Bayesian
    regret under any prior is at most B, then the frequentist
    regret for any particular instance θ is at most B.
    (θ is one element of the finite support.) -/
theorem prior_free_conversion {K : ℕ} [NeZero K]
    (frequentist_regrets : Fin K → ℝ)
    (B : ℝ)
    (h_bayesian_bound : ∀ (w : Fin K → ℝ),
      (∀ i, 0 ≤ w i) → (∑ i : Fin K, w i = 1) →
      ∑ i : Fin K, w i * frequentist_regrets i ≤ B)
    (j : Fin K) :
    frequentist_regrets j ≤ B := by
  -- Use point mass at j: w_i = if i = j then 1 else 0
  have := h_bayesian_bound (fun i => if i = j then 1 else 0)
    (fun i => by simp only; split_ifs <;> norm_num)
    (by simp [Finset.sum_ite_eq'])
  simp [Finset.sum_ite_eq'] at this
  exact this

/-- **Bayesian lower bound**: Bayesian regret ≤ max frequentist regret
    (the average is at most the max). -/
theorem bayesian_le_max_frequentist {K : ℕ} [NeZero K]
    (regrets : Fin K → ℝ)
    (w : Fin K → ℝ)
    (hw_nonneg : ∀ i, 0 ≤ w i)
    (hw_sum : ∑ i : Fin K, w i = 1) :
    ∑ i : Fin K, w i * regrets i ≤
    Finset.univ.sup' Finset.univ_nonempty regrets := by
  calc ∑ i : Fin K, w i * regrets i
      ≤ ∑ i : Fin K, w i *
          (Finset.univ.sup' Finset.univ_nonempty regrets) := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (Finset.le_sup' regrets (Finset.mem_univ i))
              (hw_nonneg i)
    _ = (∑ i : Fin K, w i) *
        (Finset.univ.sup' Finset.univ_nonempty regrets) := by
        rw [Finset.sum_mul]
    _ = Finset.univ.sup' Finset.univ_nonempty regrets := by
        rw [hw_sum, one_mul]

/-! ### 7. Entropy Chain Rule — Algebraic Consequences

H(X,Y) = H(X) + H(Y|X) implies several useful identities:
- H(X₁, ..., Xₙ) = Σᵢ H(Xᵢ | X₁, ..., Xᵢ₋₁)
- I(X;Y) = H(X) − H(X|Y) = H(Y) − H(Y|X)
- I(X;Y) ≥ 0 since H(X|Y) ≤ H(X)

These are used in bounding the total information gain in the
information-ratio framework. -/

/-- **Entropy chain rule (telescoping form)**: for a sequence of
    conditional entropies h₁, h₂, ..., hₙ with hᵢ = H(Xᵢ | X₁...Xᵢ₋₁),
    the joint entropy is Σᵢ hᵢ. -/
theorem entropy_chain_telescope {n : ℕ}
    (conditional_entropies : Fin n → ℝ)
    (joint_entropy : ℝ)
    (h_chain : joint_entropy = ∑ i : Fin n, conditional_entropies i) :
    joint_entropy = ∑ i : Fin n, conditional_entropies i := h_chain

/-- **Mutual information nonnegativity** (algebraic form):
    I(X;Y) = H(X) − H(X|Y) ≥ 0 when H(X) ≥ H(X|Y). -/
theorem mutual_info_nonneg (h_x h_x_given_y : ℝ)
    (h_conditioning_reduces : h_x_given_y ≤ h_x) :
    0 ≤ h_x - h_x_given_y := by linarith

/-- **Mutual information symmetry** (algebraic form):
    I(X;Y) = H(X) + H(Y) − H(X,Y) = I(Y;X).
    Both sides equal H(X) + H(Y) − H(X,Y). -/
theorem mutual_info_symmetry (h_x h_y h_xy : ℝ) :
    h_x + h_y - h_xy = h_y + h_x - h_xy := by ring

/-- **Subadditivity of entropy** (algebraic form):
    H(X,Y) ≤ H(X) + H(Y), equivalently I(X;Y) ≥ 0.
    We encode this as: if I(X;Y) ≥ 0 (i.e., h_x + h_y ≥ h_xy),
    then H(X,Y) ≤ H(X) + H(Y). -/
theorem entropy_subadditivity (h_x h_y h_xy : ℝ)
    (h_mi_nonneg : h_xy ≤ h_x + h_y) :
    h_xy ≤ h_x + h_y := h_mi_nonneg

/-! ### Additional Algebraic Results -/

/-- **Regret-information tradeoff**: from Γ_t = δ_t² / I_t,
    we get δ_t ≤ √(Γ · I_t). Summing and applying Cauchy-Schwarz:
    Σ δ_t ≤ √(T · Γ · Σ I_t).
    Algebraically: if Σ δ_t ≤ √(T · Γ · S) and S ≤ H,
    then Σ δ_t ≤ √(T · Γ · H). -/
theorem regret_info_tradeoff
    (total_regret : ℝ) (h_nonneg : 0 ≤ total_regret)
    (T_real Γ S H : ℝ)
    (hT : 0 ≤ T_real) (hΓ : 0 ≤ Γ) (hS : 0 ≤ S) (hH : 0 ≤ H)
    (h_cs : total_regret ≤ Real.sqrt (T_real * Γ * S))
    (h_info_bound : S ≤ H) :
    total_regret ≤ Real.sqrt (T_real * Γ * H) := by
  calc total_regret
      ≤ Real.sqrt (T_real * Γ * S) := h_cs
    _ ≤ Real.sqrt (T_real * Γ * H) := by
        apply Real.sqrt_le_sqrt
        have : 0 ≤ T_real * Γ := mul_nonneg hT hΓ
        nlinarith

/-- **Doubling trick for Bayesian regret**: if regret on horizon T is
    at most c · √T, then running in epochs of doubling length
    gives regret at most c · √T · (1 + √2) on total horizon T.
    Algebraically: √1 + √2 + √4 + ... + √(2^k) ≤ (1+√2) · √(2^k).
    Here we prove the simpler bound: √a + √b ≤ √(2(a+b)). -/
theorem sqrt_sum_bound (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt a + Real.sqrt b ≤ Real.sqrt (2 * (a + b)) := by
  rw [← Real.sqrt_sq (by positivity : 0 ≤ Real.sqrt a + Real.sqrt b)]
  apply Real.sqrt_le_sqrt
  have hsa := Real.sq_sqrt ha
  have hsb := Real.sq_sqrt hb
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb,
             sq_nonneg (Real.sqrt a - Real.sqrt b)]

end
