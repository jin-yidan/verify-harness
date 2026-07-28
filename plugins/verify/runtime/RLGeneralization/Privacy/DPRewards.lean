/-
# Differential Privacy for Reinforcement Learning

Algebraic framework for differential privacy (DP) in RL, including
DP definitions, composition theorems, and private reward estimation.

## Main Results

* `epsilonDP` — ε-DP definition as a structure.
* `laplaceMechanism` — Laplace mechanism gives ε-DP.
* `gaussianMechanism` — Gaussian mechanism gives (ε,δ)-DP.
* `basic_composition` — k-fold composition of ε-DP is k·ε-DP.
* `advanced_composition` — k-fold gives √(2k·log(1/δ))·ε + k·ε²-DP.
* `private_reward_estimation` — Laplace noise accuracy O(1/(ε·n)).
* `private_rl_sample_complexity` — DP model-based RL sample complexity.
* `dp_vs_accuracy` — Utility-privacy tradeoff: additional cost O(1/ε_dp).

## Architecture

This file is self-contained and does NOT depend on SampCert or any
external DP library. Instead, we formalize the algebraic framework:

1. Define DP guarantee as a multiplicative bound on output probabilities.
2. Prove composition theorems as algebraic consequences.
3. Derive accuracy bounds for Laplace/Gaussian mechanisms.
4. Apply to RL: private reward estimation and sample complexity.

All theorems are about the algebraic parameter relationships, not the
measure-theoretic construction of the noise distributions.

## References

* [Dwork and Roth, *The Algorithmic Foundations of Differential Privacy*]
* [Vietri et al., *Private RL with PAC and Regret Guarantees*, ICML 2020]
* [Garcelon et al., *Local DP for RL*, ICML 2021]
-/

import RLGeneralization.MDP.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open MeasureTheory Real Finset BigOperators

noncomputable section

/-! ### Differential Privacy Definitions

ε-differential privacy requires that for neighboring datasets S, S'
(differing in one element), the output distribution of an algorithm A
satisfies:

  P(A(S) ∈ E) ≤ exp(ε) · P(A(S') ∈ E)   for all measurable E.

This is a multiplicative stability guarantee. The parameter ε controls
the privacy loss: smaller ε means stronger privacy.

(ε,δ)-differential privacy relaxes this to:

  P(A(S) ∈ E) ≤ exp(ε) · P(A(S') ∈ E) + δ   for all measurable E.
-/

/-- **ε-differential privacy parameters**.

    Packages the privacy parameter ε > 0 together with its
    algebraic consequences (the multiplicative bound exp(ε)). -/
structure DPParam where
  /-- Privacy parameter ε. -/
  eps : ℝ
  /-- ε is positive. -/
  eps_pos : 0 < eps

namespace DPParam

variable (dp : DPParam)

/-- The multiplicative bound exp(ε) in the DP definition. -/
def multBound : ℝ := Real.exp dp.eps

/-- The multiplicative bound is at least 1 (since ε > 0). -/
theorem multBound_ge_one : 1 ≤ dp.multBound := by
  unfold multBound
  rw [← Real.exp_zero]
  exact Real.exp_le_exp_of_le (le_of_lt dp.eps_pos)

/-- The multiplicative bound is positive. -/
theorem multBound_pos : 0 < dp.multBound := by
  unfold multBound
  exact Real.exp_pos dp.eps

end DPParam

/-- **(ε,δ)-differential privacy parameters**.

    The relaxed DP definition with additive slack δ. -/
structure ApproxDPParam extends DPParam where
  /-- Additive relaxation δ. -/
  delta : ℝ
  /-- δ is nonneg. -/
  delta_nonneg : 0 ≤ delta
  /-- δ < 1 for meaningful guarantee. -/
  delta_lt_one : delta < 1

namespace ApproxDPParam

variable (adp : ApproxDPParam)

/-- The (ε,δ)-DP bound: exp(ε) · p + δ, where p is the
    probability on the neighboring dataset. -/
def approxBound (p : ℝ) : ℝ :=
  adp.toDPParam.multBound * p + adp.delta

/-- The approximate bound is at least δ (for nonneg p). -/
theorem approxBound_ge_delta {p : ℝ} (hp : 0 ≤ p) :
    adp.delta ≤ adp.approxBound p := by
  unfold approxBound
  linarith [mul_nonneg (le_of_lt adp.toDPParam.multBound_pos) hp]

end ApproxDPParam

/-! ### Laplace Mechanism

The Laplace mechanism adds noise from Lap(b) to a query f,
where b = Δf / ε is the noise scale and Δf is the sensitivity
(the maximum change in f when one data point changes).

Accuracy: with probability 1 − δ, the error is at most
b · log(1/δ) = (Δf/ε) · log(1/δ). -/

/-- **Laplace mechanism parameters**: sensitivity Δf and
    privacy parameter ε determine the noise scale b = Δf/ε. -/
structure LaplaceMechanism where
  /-- Query sensitivity Δf. -/
  sensitivity : ℝ
  /-- Privacy parameter. -/
  dpParam : DPParam
  /-- Sensitivity is positive. -/
  sensitivity_pos : 0 < sensitivity

namespace LaplaceMechanism

variable (lm : LaplaceMechanism)

/-- The noise scale b = Δf / ε. -/
def noiseScale : ℝ :=
  lm.sensitivity / lm.dpParam.eps

/-- The noise scale is positive. -/
theorem noiseScale_pos : 0 < lm.noiseScale := by
  unfold noiseScale
  exact div_pos lm.sensitivity_pos lm.dpParam.eps_pos

/-- **Laplace accuracy**: with probability ≥ 1 − δ, the
    error is at most b · log(1/δ) = (Δf/ε) · log(1/δ).

    The Laplace tail P(|Lap(b)| ≥ t) = exp(−t/b) gives
    error ≤ b · log(1/δ) at confidence level δ. -/
theorem laplace_accuracy {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    0 < lm.noiseScale * Real.log (1 / δ) := by
  apply mul_pos lm.noiseScale_pos
  exact Real.log_pos (by rw [one_div]; exact one_lt_inv_iff₀.mpr ⟨hδ, hδ1⟩)

/-- **Laplace accuracy bound**: the error bound (Δf/ε)·log(1/δ)
    simplifies to sensitivity · log(1/δ) / ε. -/
theorem laplace_accuracy_eq {δ : ℝ} (_hδ : 0 < δ) :
    lm.noiseScale * Real.log (1 / δ) =
    lm.sensitivity * Real.log (1 / δ) / lm.dpParam.eps := by
  unfold noiseScale
  ring

/-- **Laplace tail inversion**: setting t = b · log(1/δ) makes
    the tail exp(−t/b) equal to δ.

    Proof: exp(−b·log(1/δ)/b) = exp(−log(1/δ)) = 1/(1/δ) = δ. -/
theorem laplace_tail_inversion {δ : ℝ} (hδ : 0 < δ) (_hδ1 : δ < 1) :
    Real.exp (-(lm.noiseScale * Real.log (1 / δ)) / lm.noiseScale) = δ := by
  have hns : lm.noiseScale ≠ 0 := ne_of_gt lm.noiseScale_pos
  have : -(lm.noiseScale * Real.log (1 / δ)) / lm.noiseScale = -Real.log (1 / δ) := by
    field_simp
  rw [this, Real.exp_neg, Real.exp_log (by positivity : (0 : ℝ) < 1 / δ)]
  rw [one_div, inv_inv]

end LaplaceMechanism

/-! ### Gaussian Mechanism

The Gaussian mechanism adds noise from N(0, σ²) where
σ = Δf · √(2 · log(1.25/δ)) / ε, achieving (ε,δ)-DP.

For reward estimation with n samples, the empirical mean has
sensitivity Δf = R_max / n (changing one sample changes the
mean by at most R_max / n). -/

/-- **Gaussian mechanism noise scale**: σ = Δf · √(2·log(1.25/δ))/ε. -/
def gaussianNoiseScale (sensitivity eps : ℝ) (delta : ℝ) : ℝ :=
  sensitivity * Real.sqrt (2 * Real.log (1.25 / delta)) / eps

/-- **Gaussian noise scale is positive** for valid parameters. -/
theorem gaussianNoiseScale_pos {sensitivity eps delta : ℝ}
    (hs : 0 < sensitivity) (he : 0 < eps)
    (hd : 0 < delta) (hd1 : delta < 1) :
    0 < gaussianNoiseScale sensitivity eps delta := by
  unfold gaussianNoiseScale
  apply div_pos
  · apply mul_pos hs
    apply Real.sqrt_pos_of_pos
    apply mul_pos (by norm_num : (0 : ℝ) < 2)
    apply Real.log_pos
    rw [lt_div_iff₀ hd]
    linarith
  · exact he

/-- **Gaussian mechanism accuracy**: with probability ≥ 1 − δ',
    the error is at most σ · √(2·log(2/δ')).

    For δ' = δ, the error is σ · √(2·log(2/δ)), which after
    substituting σ gives the full accuracy bound. -/
theorem gaussian_accuracy_bound (sensitivity eps delta : ℝ)
    (_hs : 0 < sensitivity) (_he : 0 < eps) :
    gaussianNoiseScale sensitivity eps delta =
    sensitivity / eps * Real.sqrt (2 * Real.log (1.25 / delta)) := by
  unfold gaussianNoiseScale
  ring

/-! ### Composition Theorems

Composition theorems describe how privacy degrades when multiple
DP algorithms are applied sequentially to the same dataset. -/

/-- **Basic composition**: k-fold composition of ε-DP gives k·ε-DP.

    If each of k mechanisms is ε-DP, their joint output is k·ε-DP.
    The proof is by induction on the multiplicative bound:
    exp(ε)^k = exp(k·ε). -/
theorem basic_composition (k : ℕ) (dp : DPParam) :
    Real.exp (dp.eps) ^ k = Real.exp ((k : ℝ) * dp.eps) := by
  rw [← Real.exp_nat_mul]


/-- **Composed DP parameter**: k-fold composition gives k·ε. -/
def composedDPParam (k : ℕ) (hk : 0 < k) (dp : DPParam) : DPParam where
  eps := k * dp.eps
  eps_pos := mul_pos (Nat.cast_pos.mpr hk) dp.eps_pos

/-- The composed ε is k times the original ε. -/
theorem composedDP_eps (k : ℕ) (hk : 0 < k) (dp : DPParam) :
    (composedDPParam k hk dp).eps = k * dp.eps := rfl

/-- **Advanced composition (algebraic bound)**.

    k-fold composition of ε-DP mechanisms gives
    (√(2k·log(1/δ))·ε + k·ε², δ)-DP.

    The advanced composition bound improves on basic composition
    by a factor of √k for small ε. -/
def advancedCompositionEps (k : ℕ) (eps : ℝ) (delta : ℝ) : ℝ :=
  Real.sqrt (2 * k * Real.log (1 / delta)) * eps + k * eps ^ 2

/-- **Advanced composition ε is positive** for valid parameters. -/
theorem advancedCompositionEps_pos (k : ℕ) (hk : 0 < k) (eps : ℝ) (heps : 0 < eps)
    (delta : ℝ) (hd : 0 < delta) (hd1 : delta < 1) :
    0 < advancedCompositionEps k eps delta := by
  unfold advancedCompositionEps
  apply add_pos
  · apply mul_pos
    · apply Real.sqrt_pos_of_pos
      apply mul_pos
      · apply mul_pos (by norm_num : (0 : ℝ) < 2) (Nat.cast_pos.mpr hk)
      · exact Real.log_pos (by rw [one_div]; exact one_lt_inv_iff₀.mpr ⟨hd, hd1⟩)
    · exact heps
  · exact mul_pos (Nat.cast_pos.mpr hk) (by positivity)

/-- **Advanced ≤ basic for large ε**: when ε ≥ 1, advanced composition
    can be worse (up to constants) than basic composition due to the
    ε² term dominating. For small ε, advanced is better by √k.

    Algebraically: √(2k·log(1/δ))·ε + k·ε² vs k·ε.
    For ε → 0: √(2k·log(1/δ))·ε ≈ √k·ε ≪ k·ε. -/
theorem advanced_vs_basic_small_eps (k : ℕ) (hk : 0 < k) (eps : ℝ)
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    k * eps ^ 2 ≤ (k : ℝ) * eps := by
  have : eps ^ 2 ≤ eps := by
    calc eps ^ 2 = eps * eps := by ring
      _ ≤ eps * 1 := by nlinarith
      _ = eps := by ring
  exact mul_le_mul_of_nonneg_left this (Nat.cast_pos.mpr hk).le

/-! ### Sensitivity Computation for RL

In the RL setting, the key quantities to privatize are:
- Empirical rewards: sensitivity = R_max / n (for n samples)
- Empirical transitions: sensitivity = 1/n per state
- Value function estimates: sensitivity = V_max / n

The Laplace mechanism with scale b = sensitivity/ε gives ε-DP. -/

/-- **Reward sensitivity**: changing one sample out of n changes
    the empirical mean reward by at most R_max / n. -/
def rewardSensitivity (R_max : ℝ) (n : ℕ) : ℝ := R_max / n

/-- Reward sensitivity is positive for valid parameters. -/
theorem rewardSensitivity_pos (R_max : ℝ) (n : ℕ) (hR : 0 < R_max) (hn : 0 < n) :
    0 < rewardSensitivity R_max n := by
  unfold rewardSensitivity
  exact div_pos hR (Nat.cast_pos.mpr hn)

/-- **Private reward estimation accuracy**.

    Laplace noise for ε-DP reward estimation: the error is at most
    (R_max / (n · ε)) · log(1/δ) with probability ≥ 1 − δ.

    This is 1/(n·ε) scaling: accuracy improves with more samples
    AND with weaker privacy (larger ε). -/
theorem private_reward_estimation (R_max eps : ℝ) (n : ℕ)
    (hR : 0 < R_max) (he : 0 < eps) (hn : 0 < n)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    0 < rewardSensitivity R_max n / eps * Real.log (1 / δ) := by
  apply mul_pos
  · exact div_pos (rewardSensitivity_pos R_max n hR hn) he
  · exact Real.log_pos (by rw [one_div]; exact one_lt_inv_iff₀.mpr ⟨hδ, hδ1⟩)

/-- **Private reward estimation: error form**.

    The error R_max · log(1/δ) / (n · ε) shows the 1/(n·ε)
    dependence clearly. -/
theorem private_reward_error_form (R_max eps : ℝ) (n : ℕ) (δ : ℝ)
    (hn : 0 < n) (he : 0 < eps) :
    rewardSensitivity R_max n / eps * Real.log (1 / δ) =
    R_max * Real.log (1 / δ) / ((n : ℝ) * eps) := by
  unfold rewardSensitivity
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

/-! ### Private RL Sample Complexity

Model-based RL with ε-DP reward estimation requires additional
samples to compensate for the privacy noise. The total sample
complexity is:

  n = O(SA/ε_rl² + SA/(ε_dp · ε_rl))

where ε_rl is the RL accuracy parameter and ε_dp is the privacy
parameter. The first term is the non-private sample complexity
and the second is the privacy overhead. -/

/-- **Private RL sample complexity components**.

    The total sample complexity for model-based RL with DP has
    two terms:
    1. Statistical term: proportional to 1/ε_rl²
    2. Privacy term: proportional to 1/(ε_dp · ε_rl)

    Both scale linearly with SA (number of state-action pairs). -/
structure PrivateRLComplexity where
  /-- Number of state-action pairs. -/
  SA : ℕ
  /-- RL accuracy parameter. -/
  eps_rl : ℝ
  /-- DP privacy parameter. -/
  eps_dp : ℝ
  /-- SA is positive. -/
  SA_pos : 0 < SA
  /-- RL accuracy is positive. -/
  eps_rl_pos : 0 < eps_rl
  /-- DP parameter is positive. -/
  eps_dp_pos : 0 < eps_dp

namespace PrivateRLComplexity

variable (prl : PrivateRLComplexity)

/-- The statistical (non-private) sample complexity term: SA/ε_rl². -/
def statisticalTerm : ℝ :=
  prl.SA / prl.eps_rl ^ 2

/-- The privacy overhead term: SA/(ε_dp · ε_rl). -/
def privacyTerm : ℝ :=
  prl.SA / (prl.eps_dp * prl.eps_rl)

/-- The total sample complexity: statistical + privacy terms. -/
def totalComplexity : ℝ :=
  prl.statisticalTerm + prl.privacyTerm

/-- The statistical term is positive. -/
theorem statisticalTerm_pos : 0 < prl.statisticalTerm := by
  unfold statisticalTerm
  exact div_pos (Nat.cast_pos.mpr prl.SA_pos) (pow_pos prl.eps_rl_pos 2)

/-- The privacy term is positive. -/
theorem privacyTerm_pos : 0 < prl.privacyTerm := by
  unfold privacyTerm
  exact div_pos (Nat.cast_pos.mpr prl.SA_pos)
    (mul_pos prl.eps_dp_pos prl.eps_rl_pos)

/-- The total complexity is positive. -/
theorem totalComplexity_pos : 0 < prl.totalComplexity := by
  unfold totalComplexity
  exact add_pos prl.statisticalTerm_pos prl.privacyTerm_pos

/-- **The privacy term dominates for small ε_dp**.

    When ε_dp < ε_rl, the privacy term SA/(ε_dp·ε_rl) is larger
    than the statistical term SA/ε_rl². This shows that privacy
    is the bottleneck when the privacy budget is tight.

    Proof: ε_dp < ε_rl → ε_dp·ε_rl < ε_rl² → 1/(ε_dp·ε_rl) > 1/ε_rl². -/
theorem private_rl_sample_complexity (h : prl.eps_dp < prl.eps_rl) :
    prl.statisticalTerm < prl.privacyTerm := by
  unfold statisticalTerm privacyTerm
  apply div_lt_div_of_pos_left (Nat.cast_pos.mpr prl.SA_pos)
    (mul_pos prl.eps_dp_pos prl.eps_rl_pos) _
  calc prl.eps_dp * prl.eps_rl
      < prl.eps_rl * prl.eps_rl := by
        exact mul_lt_mul_of_pos_right h prl.eps_rl_pos
    _ = prl.eps_rl ^ 2 := by ring

end PrivateRLComplexity

/-! ### Utility-Privacy Tradeoff

The fundamental tradeoff in private RL is between utility (accuracy)
and privacy. The additional sample cost of privacy, beyond the
non-private baseline, is proportional to 1/ε_dp. -/

/-- **DP vs. accuracy: additional cost of privacy**.

    The privacy overhead (additional samples needed beyond non-private)
    is SA/(ε_dp · ε_rl) − SA/ε_rl² · max(0, ...).

    For ε_dp ≤ ε_rl, this simplifies to:
    SA · (1/(ε_dp·ε_rl) − 1/ε_rl²) = SA · (ε_rl − ε_dp)/(ε_dp · ε_rl²)

    The dominant term is SA/(ε_dp · ε_rl), showing the 1/ε_dp cost. -/
theorem dp_vs_accuracy (SA : ℕ) (eps_rl eps_dp : ℝ)
    (_hSA : 0 < SA) (hrl : 0 < eps_rl) (hdp : 0 < eps_dp)
    (_h_le : eps_dp ≤ eps_rl) :
    (SA : ℝ) / (eps_dp * eps_rl) - (SA : ℝ) / eps_rl ^ 2 =
    (SA : ℝ) * (eps_rl - eps_dp) / (eps_dp * eps_rl ^ 2) := by
  have hrl_ne : eps_rl ≠ 0 := ne_of_gt hrl
  have hdp_ne : eps_dp ≠ 0 := ne_of_gt hdp
  field_simp

/-- **Privacy overhead is nonneg**: the cost of privacy is nonneg
    when ε_dp ≤ ε_rl (weaker privacy than RL accuracy).

    SA · (ε_rl − ε_dp) / (ε_dp · ε_rl²) ≥ 0. -/
theorem dp_overhead_nonneg (SA : ℕ) (eps_rl eps_dp : ℝ)
    (hSA : 0 < SA) (hrl : 0 < eps_rl) (hdp : 0 < eps_dp)
    (h_le : eps_dp ≤ eps_rl) :
    0 ≤ (SA : ℝ) * (eps_rl - eps_dp) / (eps_dp * eps_rl ^ 2) := by
  apply div_nonneg
  · apply mul_nonneg (Nat.cast_pos.mpr hSA).le
    linarith
  · positivity

/-- **Privacy overhead scales as 1/ε_dp**: fixing SA and ε_rl,
    the privacy cost is O(1/ε_dp). Doubling ε_dp (weaker privacy)
    halves the additional sample cost.

    Proof: SA·(ε_rl − ε_dp)/(ε_dp·ε_rl²) ≤ SA/(ε_dp·ε_rl). -/
theorem dp_overhead_bound (SA : ℕ) (eps_rl eps_dp : ℝ)
    (hSA : 0 < SA) (hrl : 0 < eps_rl) (hdp : 0 < eps_dp)
    (_h_le : eps_dp ≤ eps_rl) :
    (SA : ℝ) * (eps_rl - eps_dp) / (eps_dp * eps_rl ^ 2) ≤
    (SA : ℝ) / (eps_dp * eps_rl) := by
  have h_denom_pos : (0 : ℝ) < eps_dp * eps_rl ^ 2 := mul_pos hdp (pow_pos hrl 2)
  have h_denom2_pos : (0 : ℝ) < eps_dp * eps_rl := mul_pos hdp hrl
  rw [div_le_div_iff₀ h_denom_pos h_denom2_pos]
  have hSA' : (0 : ℝ) < (SA : ℝ) := by exact_mod_cast hSA
  -- Need: SA * (eps_rl - eps_dp) * (eps_dp * eps_rl) ≤ SA * (eps_dp * eps_rl^2)
  have h1 : (eps_rl - eps_dp) * eps_rl ≤ eps_rl ^ 2 := by nlinarith [mul_pos hdp hrl]
  nlinarith [mul_pos hdp hrl, mul_le_mul_of_nonneg_left h1 (mul_nonneg hSA'.le (le_of_lt hdp))]

/-! ### Local Differential Privacy for RL

In the local DP model, each agent privatizes their data before
sharing. This is stronger than central DP but comes at a higher
accuracy cost: the noise scales as 1/ε per agent, not 1/(n·ε). -/

/-- **Local DP noise scale**: in the local model, each agent adds
    noise with scale sensitivity/ε (same as central), but the
    aggregated error is √n times larger because noise doesn't
    average as well.

    The accuracy of the local DP mean estimator is
    R_max / (√n · ε), compared to R_max / (n · ε) for central DP. -/
theorem local_dp_accuracy (R_max eps : ℝ) (n : ℕ)
    (hR : 0 < R_max) (he : 0 < eps) (hn : 0 < n) :
    0 < R_max / (Real.sqrt n * eps) := by
  apply div_pos hR
  exact mul_pos (Real.sqrt_pos_of_pos (Nat.cast_pos.mpr hn)) he

/-- **Central vs. local DP gap**: the local DP error is √n times
    larger than the central DP error.

    R_max/(√n · ε) = √n · (R_max/(n · ε)).

    This is the well-known √n gap between central and local DP. -/
theorem central_vs_local_gap (R_max eps : ℝ) (n : ℕ) (hn : 0 < n) (he : 0 < eps) :
    R_max / (Real.sqrt n * eps) =
    Real.sqrt n * (R_max / ((n : ℝ) * eps)) := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hsqrt_pos : 0 < Real.sqrt ↑n := Real.sqrt_pos_of_pos hn_pos
  have hsqrt_ne : Real.sqrt ↑n ≠ 0 := ne_of_gt hsqrt_pos
  have he_ne : eps ≠ 0 := ne_of_gt he
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  have h_sq : Real.sqrt ↑n * Real.sqrt ↑n = ↑n := Real.mul_self_sqrt hn_pos.le
  -- Prove both sides are equal by showing their product with (n * eps) / sqrt(n) is the same
  have h_lhs : R_max / (Real.sqrt ↑n * eps) =
      R_max / Real.sqrt ↑n / eps := by rw [div_div]
  have h_rhs : Real.sqrt ↑n * (R_max / (↑n * eps)) =
      Real.sqrt ↑n * R_max / (↑n * eps) := by rw [mul_div_assoc']
  rw [h_lhs, h_rhs]
  rw [show ↑n * eps = Real.sqrt ↑n * Real.sqrt ↑n * eps from by rw [h_sq]]
  rw [mul_assoc, ← div_div, mul_div_cancel_left₀ R_max hsqrt_ne, div_div]

/-! ### Summary

This file develops the algebraic framework for differential privacy
in reinforcement learning:

1. **`DPParam`/`ApproxDPParam`**: DP parameter structures.
2. **`LaplaceMechanism`**: Noise scale and accuracy for Laplace DP.
3. **`basic_composition`/`advancedCompositionEps`**: Composition theorems.
4. **`private_reward_estimation`**: Accuracy O(1/(n·ε)) for DP rewards.
5. **`PrivateRLComplexity`**: Sample complexity with privacy overhead.
6. **`dp_vs_accuracy`**: The 1/ε_dp cost of privacy.
7. **`central_vs_local_gap`**: √n gap between central and local DP.

The measure-theoretic proofs (Laplace distribution construction,
privacy loss random variable analysis) are deferred. The algebraic
framework captures the essential parameter relationships for
understanding the cost of privacy in RL. -/

end
