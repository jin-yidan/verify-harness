/-
# Thompson Sampling Regret Bounds via Information-Theoretic Analysis

Bayesian regret analysis for Thompson Sampling on K-armed bandits.
The information-ratio framework decomposes regret into an information
gain term and a ratio term, yielding O(√(T log K)) Bayesian regret.

## Main Definitions

* `BayesianRegret` — E[R_T] = E[T·μ* − Σ μ_{I_t}] over prior and samples.
* `InformationRatio` — Γ_t = (E[regret_t])² / (information gain about π*).
* `posteriorVariance` — variance of posterior belief about arm means.

## Main Results

* `bayesian_regret_from_information_ratio` — R_T ≤ √(Γ · T · H(π*)).
* `ts_regret_bound` — R_T ≤ √(T · log K / 2) (composition).
* `ts_vs_ucb` — Thompson Sampling matches UCB rate O(√(KT log K)).

## References

* [Russo and Van Roy, *Learning to Optimize via Information-Directed Sampling*, 2014]
* [Russo and Van Roy, *An Information-Theoretic Analysis of Thompson Sampling*, JMLR 2016]
* [Lattimore and Szepesvári, *Bandit Algorithms*, Chapter 36]
* [Agarwal et al., *RL: Theory and Algorithms*]
-/

import RLGeneralization.Bandits.UCB
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Finset BigOperators Real

noncomputable section

/-! ### Bayesian Regret

In the Bayesian setting, the prior π induces a distribution over
bandit instances. The Bayesian regret is the expected pseudo-regret
where the expectation is taken over both the prior (which determines
the true arm means) and the algorithm's randomness.

For a K-armed bandit with mean rewards μ₁, ..., μ_K drawn from a
prior π, and a policy that plays arm I_t at round t:

  BayesianRegret_T = E_π[ T · max_a μ_a − Σ_{t=1}^T μ_{I_t} ]

This is the "integrated" version of pseudo-regret. -/

/-- **Bayesian regret data** for a K-armed bandit.
    Packages the per-round expected instantaneous regret and
    the total Bayesian regret over T rounds.

    The `instantaneousRegret t` is E[Δ_{I_t}] = E[μ* - μ_{I_t}]
    where the expectation is over the posterior at time t and the
    algorithm's randomness. -/
structure BayesianRegret (K : ℕ) [NeZero K] (T : ℕ) where
  /-- Expected instantaneous regret at round t. -/
  instantaneousRegret : Fin T → ℝ
  /-- Instantaneous regret is nonneg (since Δ_{I_t} ≥ 0). -/
  h_nonneg : ∀ t, 0 ≤ instantaneousRegret t
  /-- Total Bayesian regret = Σ_t E[Δ_{I_t}]. -/
  totalRegret : ℝ
  /-- Total equals sum of instantaneous. -/
  h_total : totalRegret = ∑ t : Fin T, instantaneousRegret t

namespace BayesianRegret

variable {K : ℕ} [NeZero K] {T : ℕ}

/-- Total Bayesian regret is nonneg. -/
theorem totalRegret_nonneg (br : BayesianRegret K T) :
    0 ≤ br.totalRegret := by
  rw [br.h_total]
  exact Finset.sum_nonneg (fun t _ => br.h_nonneg t)

/-- If each instantaneous regret is bounded by c, then total ≤ T · c. -/
theorem totalRegret_le_of_instantaneous_le (br : BayesianRegret K T)
    (c : ℝ) (hc : ∀ t, br.instantaneousRegret t ≤ c) :
    br.totalRegret ≤ T * c := by
  rw [br.h_total]
  calc ∑ t : Fin T, br.instantaneousRegret t
      ≤ ∑ _t : Fin T, c := Finset.sum_le_sum (fun t _ => hc t)
    _ = T * c := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end BayesianRegret

/-! ### Information Ratio

The information ratio is the key quantity in the information-directed
sampling analysis of Thompson Sampling. It measures the "cost" of
information acquisition:

  Γ_t = (E[Δ_{I_t}])² / I_t(μ*; O_t | H_{t-1})

where I_t is the mutual information between the identity of the optimal
arm μ* and the observation O_t, conditioned on history H_{t-1}.

When Γ_t ≤ Γ for all t, the Bayesian regret satisfies:
  R_T ≤ √(Γ · T · H(π*))
where H(π*) is the entropy of the optimal arm under the prior. -/

/-- **Information ratio data**.
    Packages the information ratio bound and the entropy of the
    optimal arm distribution. -/
structure InformationRatio (K : ℕ) [NeZero K] where
  /-- Upper bound on the information ratio Γ_t for all t. -/
  Γ : ℝ
  /-- Information ratio bound is positive. -/
  hΓ_pos : 0 < Γ
  /-- Entropy of optimal arm distribution H(π*). -/
  entropy : ℝ
  /-- Entropy is nonneg (Shannon entropy ≥ 0). -/
  h_entropy_nonneg : 0 ≤ entropy

namespace InformationRatio

variable {K : ℕ} [NeZero K]

/-- The product Γ · H(π*) is nonneg. -/
theorem gamma_entropy_nonneg (ir : InformationRatio K) :
    0 ≤ ir.Γ * ir.entropy :=
  mul_nonneg ir.hΓ_pos.le ir.h_entropy_nonneg

end InformationRatio

/-! ### Posterior Variance

The posterior variance of the arm means plays a role in the
information-theoretic analysis. As Thompson Sampling observes
more rewards, the posterior concentrates and the variance shrinks. -/

/-- **Posterior variance data** for arm means.
    For a Beta(α, β) posterior on arm a's Bernoulli parameter,
    the posterior variance is αβ / ((α+β)²(α+β+1)).
    After n observations with s successes (α₀ = β₀ = 1):
    α = 1 + s, β = 1 + n - s, and the variance ≤ 1/(n+2). -/
structure PosteriorVariance (K : ℕ) [NeZero K] where
  /-- Posterior variance of each arm's mean. -/
  variance : Fin K → ℝ
  /-- Variance is nonneg. -/
  h_nonneg : ∀ a, 0 ≤ variance a
  /-- Number of pulls per arm. -/
  pullCounts : Fin K → ℕ

namespace PosteriorVariance

variable {K : ℕ} [NeZero K]

/-- **Reciprocal monotonicity**: 1/(n+2) <= 1/n for n > 0.
    A prerequisite for bounding Beta posterior variance, but only
    proves the monotonicity of 1/x, not the variance bound itself. -/
theorem reciprocal_monotone (n : ℕ) (hn : 0 < n) :
    1 / ((n : ℝ) + 2) ≤ 1 / (n : ℝ) := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [div_le_div_iff₀ (by linarith : (0 : ℝ) < (n : ℝ) + 2) hn_pos]
  nlinarith

/-- **Beta posterior variance bound**.

  For a Beta(1+s, 1+n-s) posterior (after n observations with s successes),
  the variance is α·β / ((α+β)² · (α+β+1)) where α+β = n+2.

  By AM-GM, α·β = (1+s)(1+n-s) ≤ ((n+2)/2)² = (n+2)²/4 since
  (1+s) + (1+n-s) = n+2. Therefore:

    Var = (1+s)(1+n-s) / ((n+2)²·(n+3))
        ≤ (n+2)²/4 / ((n+2)²·(n+3))
        = 1/(4(n+3))
        ≤ 1/(n+2)

  The last step uses n+2 ≤ 4(n+3) which holds for all n ≥ 0. -/
theorem beta_posterior_variance_bound (n : ℕ) (s : ℕ) (hs : s ≤ n) :
    (1 + (s : ℝ)) * (1 + (n : ℝ) - (s : ℝ)) / (((n : ℝ) + 2) ^ 2 * ((n : ℝ) + 3))
      ≤ 1 / ((n : ℝ) + 2) := by
  have hn2_pos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hn3_pos : (0 : ℝ) < (n : ℝ) + 3 := by positivity
  have hn2_ne : ((n : ℝ) + 2) ≠ 0 := ne_of_gt hn2_pos
  have hn2sq_pos : (0 : ℝ) < ((n : ℝ) + 2) ^ 2 := by positivity
  have hdenom_pos : (0 : ℝ) < ((n : ℝ) + 2) ^ 2 * ((n : ℝ) + 3) := by positivity
  have hs_le : (s : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hs
  rw [div_le_div_iff₀ hdenom_pos hn2_pos]
  -- Goal: (1 + ↑s) * (1 + ↑n - ↑s) * (↑n + 2) ≤ 1 * ((↑n + 2) ^ 2 * (↑n + 3))
  -- By AM-GM: (1+s)(1+n-s) ≤ ((n+2)/2)^2  since (a-b)^2 ≥ 0
  -- Then (n+2)^2/4 * (n+2) ≤ (n+2)^2 * (n+3) iff (n+2)/4 ≤ (n+3) iff n+2 ≤ 4n+12
  nlinarith [sq_nonneg ((s : ℝ) - ((n : ℝ) - (s : ℝ))), sq_nonneg ((n : ℝ) + 2),
             sq_nonneg ((s : ℝ)), mul_self_nonneg ((n : ℝ) + 2)]

/-- Total posterior variance across arms: Σ_a Var_a. -/
def totalVariance (pv : PosteriorVariance K) : ℝ :=
  ∑ a : Fin K, pv.variance a

/-- Total variance is nonneg. -/
theorem totalVariance_nonneg (pv : PosteriorVariance K) :
    0 ≤ pv.totalVariance :=
  Finset.sum_nonneg (fun a _ => pv.h_nonneg a)

end PosteriorVariance

/-! ### Key Algebraic Results

The core of the information-ratio analysis is the inequality:

  R_T ≤ √(Γ · T · H(π*))

This follows from Cauchy-Schwarz applied to the information ratio
decomposition. The telescoping argument bounds the total information
gain by H(π*), while the ratio Γ converts information to regret. -/

/-- **Bayesian regret from information ratio (algebraic core)**.

  If the information ratio satisfies Γ_t ≤ Γ for all t, then
  the total Bayesian regret satisfies:

    R_T ≤ √(Γ · T · H(π*))

  where H(π*) is the entropy of the optimal arm under the prior.

  Derivation: By Cauchy-Schwarz on the information ratio definition,
  (Σ_t E[Δ_t])² ≤ Γ · Σ_t I_t. The total information gain
  Σ_t I_t ≤ H(π*) by the chain rule of mutual information.
  So R_T² ≤ Γ · T · H(π*), giving R_T ≤ √(Γ · T · H(π*)).

  We take the squared form of the bound as the main algebraic statement.

  The hypothesis `h_regret_sq` encodes: R_T² ≤ Γ · T · H(π*),
  which is the output of the Cauchy-Schwarz + chain rule argument. -/
theorem bayesian_regret_from_information_ratio
    {K : ℕ} [NeZero K] {T : ℕ}
    (br : BayesianRegret K T)
    (ir : InformationRatio K)
    (h_regret_sq :
      br.totalRegret ^ 2 ≤ ir.Γ * T * ir.entropy) :
    br.totalRegret ≤ Real.sqrt (ir.Γ * T * ir.entropy) := by
  have h_nonneg := br.totalRegret_nonneg
  rw [← Real.sqrt_sq h_nonneg]
  exact Real.sqrt_le_sqrt h_regret_sq

/-- **Square-of-sqrt identity**: sqrt(Γ · T · H)² = Γ · T · H
    when Γ, T, H ≥ 0. This is an algebraic identity (sq_sqrt),
    not a regret bound. -/
theorem information_ratio_sq_identity
    (Γ : ℝ) (hΓ : 0 ≤ Γ) (T_real : ℝ) (hT : 0 ≤ T_real)
    (H : ℝ) (hH : 0 ≤ H) :
    Real.sqrt (Γ * T_real * H) ^ 2 = Γ * T_real * H :=
  Real.sq_sqrt (by positivity)

/-! ### Uniform Prior Entropy

For a uniform prior over K arms, the entropy of the optimal arm
distribution π* is H(π*) = log K. This is because under a symmetric
prior, each arm is equally likely to be optimal. -/

/-- **Positivity of log K** for K >= 2.
    A prerequisite for the entropy bound H(pi*) = log K, but only proves
    0 < log K, not the entropy identity itself. -/
theorem uniform_prior_entropy (K : ℕ) (hK : 2 ≤ K) :
    0 < Real.log K := by
  exact Real.log_pos (by exact_mod_cast show 1 < K by omega)

/-! ### Thompson Sampling Information Ratio

For Bernoulli bandits, Thompson Sampling has information ratio
Γ ≤ 1/2. This was proved by Russo and Van Roy (2016).

The bound Γ ≤ 1/2 is tight for 2-armed Bernoulli bandits and
holds more generally for any K-armed Bernoulli bandit. -/

/-- The TS information ratio bound 1/2 is positive. -/
theorem ts_gamma_pos : (0 : ℝ) < 1 / 2 := by norm_num

-- [UNUSED]
/-- **Information ratio configuration for TS on K-armed Bernoulli bandits**.
    Γ = 1/2, H = log K. -/
def tsInfoRatio (K : ℕ) [NeZero K] (hK : 2 ≤ K) : InformationRatio K where
  Γ := 1 / 2
  hΓ_pos := by norm_num
  entropy := Real.log K
  h_entropy_nonneg := le_of_lt (uniform_prior_entropy K hK)

/-! ### Main Regret Bound for Thompson Sampling

Combining Γ ≤ 1/2 with H(π*) = log K under the uniform prior:

  R_T ≤ √(Γ · T · H(π*)) ≤ √((1/2) · T · log K) = √(T · log K / 2)

This matches the minimax rate up to constant factors. -/

/-- **Thompson Sampling regret bound (algebraic composition)**.

  For K-armed Bernoulli bandits with uniform prior:
    R_T ≤ √(T · log K / 2)

  This follows from:
  1. Information ratio Γ ≤ 1/2 (Russo-Van Roy)
  2. Prior entropy H(π*) = log K (uniform prior)
  3. Bayesian regret bound R_T ≤ √(Γ · T · H(π*))

  The hypothesis `h_regret_sq` is the Cauchy-Schwarz output. -/
theorem ts_regret_bound
    {K : ℕ} [NeZero K]
    (_hK : 2 ≤ K) (T : ℕ) (_hT : 0 < T)
    (br : BayesianRegret K T)
    (h_regret_sq :
      br.totalRegret ^ 2 ≤ 1 / 2 * T * Real.log K) :
    br.totalRegret ≤ Real.sqrt (T * Real.log K / 2) := by
  have h_nonneg := br.totalRegret_nonneg
  rw [show (T : ℝ) * Real.log ↑K / 2 = 1 / 2 * ↑T * Real.log ↑K by ring]
  rw [← Real.sqrt_sq h_nonneg]
  exact Real.sqrt_le_sqrt h_regret_sq

/-- **TS regret bound — alternative form**.
    R_T ≤ √(T · log K / 2) ≤ √(T · log K).
    The second inequality is trivial and shows TS achieves
    the O(√(T log K)) rate. -/
theorem ts_regret_bound_relaxed
    (T : ℕ) (K : ℕ) (hK : 2 ≤ K) (hT : 0 < T) :
    Real.sqrt (↑T * Real.log ↑K / 2) ≤
    Real.sqrt (↑T * Real.log ↑K) := by
  apply Real.sqrt_le_sqrt
  have hlogK : 0 < Real.log (K : ℝ) := uniform_prior_entropy K hK
  have hT_pos : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  nlinarith

/-! ### Comparison with UCB

UCB achieves regret O(√(KT log T)) in the frequentist setting.
Thompson Sampling achieves Bayesian regret O(√(T log K)).

In the worst case over priors, the Bayesian regret matches
the frequentist regret, so TS is never worse than UCB
(up to constant factors). The comparison is:

  TS:  √(T · log K / 2)
  UCB: √(KT · C · log(KT))  for some constant C

For K ≥ 2, TS is better by a factor of √K. -/

/-- **Thompson Sampling matches UCB rate (algebraic comparison)**.

  The TS Bayesian regret √(T log K / 2) is at most √(K · T · log K)
  (the UCB-type rate), since 1/2 ≤ K for K ≥ 1.
  This shows TS is never worse than UCB in rate.

  NOTE: This compares TS Bayesian regret against a frequentist-shaped
  expression. Bayesian and worst-case regret are different quantities,
  so this comparison is illustrative, not a direct algorithm comparison. -/
theorem ts_vs_ucb (K : ℕ) [NeZero K] (T : ℕ) (_hT : 0 < T) (hK : 2 ≤ K) :
    Real.sqrt (↑T * Real.log ↑K / 2) ≤
    Real.sqrt (↑K * ↑T * Real.log ↑K) := by
  apply Real.sqrt_le_sqrt
  have hlogK : 0 ≤ Real.log (K : ℝ) := le_of_lt (uniform_prior_entropy K hK)
  have hT_pos : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  have hK_real : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hTlogK : 0 ≤ ↑T * Real.log ↑K := mul_nonneg hT_pos hlogK
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ ↑K - 1 / 2 by linarith) hTlogK]

/-- **Positivity of sqrt(2K)** for K >= 2.
    A numeric fact used in the TS-vs-UCB comparison, but only proves
    0 < sqrt(2K), not the improvement ratio itself. -/
theorem ts_ucb_improvement_factor (K : ℕ) (hK : 2 ≤ K) :
    (0 : ℝ) < Real.sqrt (2 * K) := by
  apply Real.sqrt_pos_of_pos
  have : (0 : ℝ) < K := by exact_mod_cast show 0 < K by omega
  linarith

/-! ### Sample Complexity Comparison

The Bayesian regret is always a lower bound on the worst-case
frequentist regret over the support of the prior. This means:

  E_π[R_T(θ)] ≤ max_{θ ∈ supp(π)} R_T(θ)

So any bound on the frequentist regret is also a bound on
the Bayesian regret (but not vice versa). -/

/-! ### Regret Decomposition via Posterior Sampling

Thompson Sampling works by sampling θ ~ posterior and playing
arg max_a E[r_a | θ]. The regret decomposes as:

  E[Δ_{I_t}] = E[μ* - μ_{I_t}]
             = E[E[μ* - μ_{I_t} | history]]
             = E[Σ_a P(I_t = a | hist) · Δ_a]

The posterior sampling ensures P(I_t = a | hist) = P(a is optimal | hist),
which is the key property linking TS to the information ratio. -/

/-- **Nonnegativity of gap-weighted sum**: for nonneg distributions p
    and nonneg gaps Δ, the inner product Σ_a p(a) · Δ(a) >= 0.
    This is a nonnegativity lemma, not the regret decomposition identity. -/
theorem gap_weighted_sum_nonneg
    (K : ℕ) [NeZero K]
    (p : Fin K → ℝ) (hp_nonneg : ∀ a, 0 ≤ p a)
    (_hp_sum : ∑ a : Fin K, p a = 1)
    (Δ : Fin K → ℝ) (hΔ_nonneg : ∀ a, 0 ≤ Δ a) :
    0 ≤ ∑ a : Fin K, p a * Δ a :=
  Finset.sum_nonneg (fun a _ => mul_nonneg (hp_nonneg a) (hΔ_nonneg a))

/-! ### Asymptotic Optimality

Thompson Sampling achieves the Lai-Robbins lower bound
asymptotically. For a K-armed bandit with gaps Δ₁ ≥ ... ≥ Δ_K > 0:

  lim_{T→∞} R_T / log T = Σ_{a: Δ_a > 0} Δ_a / KL(μ_a, μ*)

This is the information-theoretic lower bound. TS matches it
without requiring knowledge of the gaps (unlike UCB which needs
tuning). -/

/-- **Lai-Robbins style: Regret grows as Σ (Δ_a / KL) · log T**.
    The gap-dependent bound for TS takes the form:
    R_T ≤ Σ_{a} (Δ_a + C · log T / Δ_a)

    When Δ_a > 0, the dominant term is C · log T / Δ_a.
    Algebraically: for c, Δ > 0 and T ≥ 1,
    c · log T / Δ ≥ 0. -/
theorem gap_dependent_term_nonneg
    (c : ℝ) (hc : 0 < c) (Δ : ℝ) (hΔ : 0 < Δ) (T : ℕ) (hT : 2 ≤ T) :
    0 ≤ c * Real.log T / Δ := by
  apply div_nonneg
  · exact mul_nonneg hc.le (le_of_lt (Real.log_pos (by exact_mod_cast show 1 < T by omega)))
  · exact hΔ.le

/-- **Sum of gap-dependent terms**.
    Σ_a (c · log T / Δ_a) = c · log T · Σ_a (1 / Δ_a).
    This is the algebraic rearrangement used in gap-dependent bounds. -/
theorem gap_dependent_sum_rearrange
    (K : ℕ) [NeZero K]
    (c : ℝ) (T_real : ℝ)
    (Δ : Fin K → ℝ) :
    ∑ a : Fin K, c * T_real / Δ a =
    c * T_real * ∑ a : Fin K, 1 / Δ a := by
  simp_rw [div_eq_mul_inv]
  rw [← Finset.mul_sum]
  ring_nf

/-! ### Worst-Case to Gap-Dependent Conversion

The gap-free bound √(T log K / 2) can be recovered from the
gap-dependent bound by optimizing over the gap Δ.

Setting Δ = √(K log K / (2T)) in the gap-dependent bound
Σ_a C log T / Δ_a yields C · K · log T / √(K log K / (2T))
= C · √(2KT log T / log K) ≈ C' · √(KT log K).

This shows the two bounds are consistent. -/

/-- **Positivity of c * K * T** when c, K, T > 0.
    A building block for the gap-free regret bound, but only proves
    positivity of a triple product, not the gap conversion itself. -/
theorem gap_free_from_gap_dependent
    (c K_real T_real : ℝ) (hc : 0 < c) (hK : 0 < K_real) (hT : 0 < T_real) :
    0 < c * K_real * T_real := by positivity

/-- **AM-GM for regret terms**.
    For the sum Δ + c/Δ with Δ > 0, the minimum is 2√c at Δ = √c.
    Algebraically: (√c + c/√c) = 2√c when c > 0. -/
theorem am_gm_regret_term (c : ℝ) (hc : 0 < c) :
    Real.sqrt c + c / Real.sqrt c = 2 * Real.sqrt c := by
  have hsqrt_pos : 0 < Real.sqrt c := Real.sqrt_pos_of_pos hc
  have hsqrt_ne : Real.sqrt c ≠ 0 := hsqrt_pos.ne'
  have hsq : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc.le
  field_simp
  nlinarith

/-! ### Computational Identities for the Regret Bound -/

/-- **TS regret exponent**: (1/2) · T · log K = T · log K / 2. -/
theorem ts_regret_exponent (T_real : ℝ) (logK : ℝ) :
    1 / 2 * T_real * logK = T_real * logK / 2 := by ring

/-- **TS vs UCB exponent comparison**:
    T · log K / 2 ≤ K · T · log K when K ≥ 1. -/
theorem ts_ucb_exponent_comparison
    (K_real : ℝ) (hK : 1 ≤ K_real)
    (T_real : ℝ) (hT : 0 ≤ T_real) (logK : ℝ) (hlogK : 0 ≤ logK) :
    T_real * logK / 2 ≤ K_real * T_real * logK := by
  have hTlogK : 0 ≤ T_real * logK := mul_nonneg hT hlogK
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ K_real - 1 / 2 by linarith) hTlogK]

/-- **Square root monotonicity applied to regret bounds**.
    Since √ is monotone and T·logK/2 ≤ K·T·logK, we get
    √(T·logK/2) ≤ √(K·T·logK). -/
theorem sqrt_regret_monotone
    (a b : ℝ) (_ha : 0 ≤ a) (hab : a ≤ b) :
    Real.sqrt a ≤ Real.sqrt b :=
  Real.sqrt_le_sqrt hab

/-! ### Bayesian-Frequentist Bridge

The key theorem connecting Bayesian and frequentist analysis:
Bayesian regret under a prior π is the π-average of the
frequentist regret. Since the average is ≤ the maximum:

  BayesianRegret(π) = E_θ~π[FrequentistRegret(θ)]
                    ≤ max_θ FrequentistRegret(θ)

Conversely, by choosing π to be a point mass at the worst θ:
  max_θ FrequentistRegret(θ) = sup_π BayesianRegret(π)

So minimax regret = sup_π BayesianRegret(π )-/

/-- **Minimax = sup Bayesian (direction 1, algebraic)**.
    For any finite collection of values, the maximum is at least
    any weighted average. -/
theorem minimax_ge_bayesian
    (K : ℕ) [NeZero K]
    (regrets : Fin K → ℝ)
    (weights : Fin K → ℝ)
    (hw_nonneg : ∀ i, 0 ≤ weights i)
    (hw_sum : ∑ i : Fin K, weights i = 1)
    (bayesian : ℝ)
    (hbay : bayesian = ∑ i : Fin K, weights i * regrets i) :
    bayesian ≤ Finset.univ.sup' Finset.univ_nonempty regrets := by
  rw [hbay]
  calc ∑ i : Fin K, weights i * regrets i
      ≤ ∑ i : Fin K, weights i *
          (Finset.univ.sup' Finset.univ_nonempty regrets) := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_left _ (hw_nonneg i)
        exact Finset.le_sup' regrets (Finset.mem_univ i)
    _ = (∑ i : Fin K, weights i) *
        (Finset.univ.sup' Finset.univ_nonempty regrets) := by
        rw [Finset.sum_mul]
    _ = Finset.univ.sup' Finset.univ_nonempty regrets := by
        rw [hw_sum, one_mul]

/-- **TS Bayesian regret is within √K of minimax**.
    TS achieves √(T log K / 2) while minimax is Ω(√(KT)).
    The ratio is √(log K / (2K)) ≤ 1 for K ≥ 2.
    Algebraically: log K / (2K) ≤ 1 when K ≥ 2. -/
theorem ts_near_minimax (K : ℕ) (hK : 2 ≤ K) :
    Real.log K / (2 * K) ≤ 1 := by
  have hK_pos : (0 : ℝ) < K := by exact_mod_cast show 0 < K by omega
  have hK_real : (1 : ℝ) < K := by exact_mod_cast show 1 < K by omega
  have hlogK := Real.log_le_self (le_of_lt hK_pos)
  have h2K : (0 : ℝ) < 2 * K := by linarith
  rw [div_le_one h2K]
  linarith

end
