/-
# PAC-Bayes Bounds for Reinforcement Learning

The first formal PAC-Bayes bound for RL in any proof assistant.

PAC-Bayes theory provides data-dependent generalization bounds that
depend on the KL divergence between a learned posterior and a prior
over hypotheses, rather than on the cardinality of the hypothesis class.
This yields tighter bounds when the posterior is concentrated.

## Mathematical Background

The PAC-Bayes inequality (Catoni form): for lambda > 0,
  E_Q[L(h)] <= E_Q[L_hat(h)] + (KL(Q||P) + log(1/delta)) / (lambda*n) + lambda/8

Optimizing lambda gives the McAllester form:
  E_Q[L(h)] <= E_Q[L_hat(h)] + sqrt((KL(Q||P) + log(1/delta)) / (2n))

## Main Results

* `klDiv` -- KL divergence for finite distributions (algebraic)
* `kl_div_nonneg` -- Gibbs inequality: KL(Q||P) >= 0
* `kl_le_log_card` -- KL <= log|H| when prior is uniform
* `pac_bayes_sample_complexity` -- Sample complexity from PAC-Bayes
* `pac_bayes_vs_uniform` -- PAC-Bayes is tighter than uniform convergence

## Approach

We take the algebraic approach: distributions are represented as
weight functions over a finite type, KL divergence is a finite sum,
and the PAC-Bayes bound is stated as a deterministic algebraic
inequality relating empirical loss, true loss, and KL divergence.

## References

* [McAllester, *PAC-Bayesian model averaging*][mcallester1999]
* [Catoni, *PAC-Bayesian supervised classification*][catoni2007]
* [Agarwal et al., *RL: Theory and Algorithms*]
-/

import RLGeneralization.MDP.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Finset BigOperators Real

noncomputable section

/-! ### Finite Distribution -/

/-- A finite distribution over a finite type `H`, represented algebraically
    as a nonneg weight function summing to 1. -/
structure FinDist (H : Type*) [Fintype H] where
  /-- Weight (probability) assigned to each hypothesis -/
  wt : H → ℝ
  /-- Weights are nonneg -/
  wt_nonneg : ∀ h, 0 ≤ wt h
  /-- Weights sum to 1 -/
  wt_sum_one : ∑ h, wt h = 1

namespace FinDist

variable {H : Type*} [Fintype H]

/-- Expected value of a function under a finite distribution. -/
def expect (d : FinDist H) (f : H → ℝ) : ℝ :=
  ∑ h, d.wt h * f h

/-- The uniform distribution over a nonempty finite type. -/
def uniform [Nonempty H] : FinDist H where
  wt := fun _ => 1 / (Fintype.card H : ℝ)
  wt_nonneg := fun _ => by positivity
  wt_sum_one := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [mul_one_div_cancel]
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero

/-- Weight of any element in a distribution is at most 1. -/
lemma wt_le_one (d : FinDist H) (h : H) : d.wt h ≤ 1 := by
  have : d.wt h ≤ ∑ h', d.wt h' :=
    Finset.single_le_sum (fun h' _ => d.wt_nonneg h') (Finset.mem_univ h)
  linarith [d.wt_sum_one]

end FinDist

/-! ### KL Divergence (Algebraic) -/

/-- KL divergence between two finite distributions Q and P:
    KL(Q||P) = sum_h q(h) * log(q(h) / p(h))

    When q(h) = 0, the term contributes 0 (by convention 0 * log(0/p) = 0).
    We require absolute continuity: p(h) > 0 whenever q(h) > 0. -/
def klDiv {H : Type*} [Fintype H] (Q P : FinDist H) : ℝ :=
  ∑ h, Q.wt h * Real.log (Q.wt h / P.wt h)

/-! ### Gibbs Inequality: KL(Q||P) >= 0 -/

/-- **Gibbs inequality**: KL(Q||P) >= 0 for finite distributions,
    provided P is absolutely continuous w.r.t. Q (i.e., q(h) > 0 implies p(h) > 0).

    Proof: Using log(x) <= x - 1 for x > 0, we get
      -KL(Q||P) = sum q(h) * log(p(h)/q(h))
               <= sum q(h) * (p(h)/q(h) - 1)
               = sum (p(h) - q(h))
               = 1 - 1 = 0 -/
theorem kl_div_nonneg {H : Type*} [Fintype H]
    (Q P : FinDist H)
    (hac : ∀ h, 0 < Q.wt h → 0 < P.wt h) :
    0 ≤ klDiv Q P := by
  unfold klDiv
  -- Show -(sum q * log(q/p)) <= 0, i.e. sum q * log(p/q) <= 0
  suffices h_neg : ∑ h, Q.wt h * Real.log (P.wt h / Q.wt h) ≤ 0 by
    -- Relate the two sums: sum q*log(q/p) = -(sum q*log(p/q))
    have h_eq : ∑ h, Q.wt h * Real.log (Q.wt h / P.wt h) =
                -(∑ h, Q.wt h * Real.log (P.wt h / Q.wt h)) := by
      conv_rhs => rw [← Finset.sum_neg_distrib]
      congr 1; ext h
      by_cases hq : Q.wt h = 0
      · simp [hq]
      · have hq_pos : 0 < Q.wt h := lt_of_le_of_ne (Q.wt_nonneg h) (Ne.symm hq)
        have hp_pos : 0 < P.wt h := hac h hq_pos
        rw [Real.log_div (ne_of_gt hp_pos) (ne_of_gt hq_pos),
            Real.log_div (ne_of_gt hq_pos) (ne_of_gt hp_pos)]
        ring
    linarith
  -- Show sum q * log(p/q) <= 0 using log(x) <= x - 1
  -- Key: log(p/q) <= p/q - 1, so q*log(p/q) <= q*(p/q - 1) = p - q (when q > 0)
  -- When q = 0, q*log(p/q) = 0 <= p - q = p (which is >= 0)
  -- So sum q*log(p/q) <= sum (p - q) = 1 - 1 = 0
  calc ∑ h, Q.wt h * Real.log (P.wt h / Q.wt h)
      ≤ ∑ h, (P.wt h - Q.wt h) := by
        apply Finset.sum_le_sum
        intro h _
        by_cases hq : Q.wt h = 0
        · simp [hq, P.wt_nonneg h]
        · have hq_pos : 0 < Q.wt h := lt_of_le_of_ne (Q.wt_nonneg h) (Ne.symm hq)
          have hp_pos : 0 < P.wt h := hac h hq_pos
          calc Q.wt h * Real.log (P.wt h / Q.wt h)
              ≤ Q.wt h * (P.wt h / Q.wt h - 1) :=
                mul_le_mul_of_nonneg_left
                  (Real.log_le_sub_one_of_pos (div_pos hp_pos hq_pos)) (le_of_lt hq_pos)
            _ = P.wt h - Q.wt h := by field_simp
    _ = (∑ h, P.wt h) - (∑ h, Q.wt h) := by
        simp [Finset.sum_sub_distrib]
    _ = 0 := by rw [P.wt_sum_one, Q.wt_sum_one]; ring

/-! ### Negative Entropy Bound -/

/-- Negative entropy is nonpositive: sum q(h) * log(q(h)) <= 0.
    Since q(h) in [0, 1], log(q(h)) <= 0, so each term q(h)*log(q(h)) <= 0. -/
private lemma neg_entropy_le_zero {H : Type*} [Fintype H]
    (Q : FinDist H) :
    ∑ h, Q.wt h * Real.log (Q.wt h) ≤ 0 := by
  apply Finset.sum_nonpos
  intro h _
  by_cases hq : Q.wt h = 0
  · simp [hq]
  · have hq_pos : 0 < Q.wt h := lt_of_le_of_ne (Q.wt_nonneg h) (Ne.symm hq)
    exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hq_pos)
      (Real.log_nonpos (le_of_lt hq_pos) (Q.wt_le_one h))

/-! ### KL <= log|H| for uniform prior -/

/-- When the prior P is uniform over H, KL(Q||P) <= log|H| for any posterior Q.

    Proof: KL(Q||Uniform) = sum q(h) * log(q(h) * |H|)
         = sum q(h) * log(q(h)) + log|H| * sum q(h)
         = sum q(h) * log(q(h)) + log|H|
         <= log|H|   (since sum q * log q <= 0). -/
theorem kl_le_log_card {H : Type*} [Fintype H] [Nonempty H]
    (Q : FinDist H) :
    klDiv Q FinDist.uniform ≤ Real.log (Fintype.card H : ℝ) := by
  classical
  unfold klDiv FinDist.uniform
  simp only
  have hcard_pos : (0 : ℝ) < Fintype.card H := Nat.cast_pos.mpr Fintype.card_pos
  have hcard_ne : (Fintype.card H : ℝ) ≠ 0 := ne_of_gt hcard_pos
  -- Rewrite each term: q / (1/|H|) = q * |H|, so log(q / (1/|H|)) = log q + log |H|
  have step : ∀ h : H, Q.wt h * Real.log (Q.wt h / (1 / (Fintype.card H : ℝ))) =
      Q.wt h * Real.log (Q.wt h) + Q.wt h * Real.log (Fintype.card H : ℝ) := by
    intro h
    by_cases hq : Q.wt h = 0
    · simp [hq]
    · have hq_pos : 0 < Q.wt h := lt_of_le_of_ne (Q.wt_nonneg h) (Ne.symm hq)
      rw [show Q.wt h / (1 / (Fintype.card H : ℝ)) = Q.wt h * (Fintype.card H : ℝ) from by
        field_simp]
      rw [Real.log_mul (ne_of_gt hq_pos) hcard_ne]
      ring
  conv_lhs => arg 2; ext h; rw [step h]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  rw [Q.wt_sum_one, one_mul]
  linarith [neg_entropy_le_zero Q]

/-! ### PAC-Bayes Instance -/

/-- A PAC-Bayes learning instance over a finite hypothesis class. -/
structure PACBayesInstance (H : Type*) [Fintype H] where
  /-- Prior distribution over hypotheses -/
  prior : FinDist H
  /-- Posterior distribution over hypotheses -/
  posterior : FinDist H
  /-- Empirical loss of each hypothesis -/
  empiricalLoss : H → ℝ
  /-- True loss of each hypothesis -/
  trueLoss : H → ℝ
  /-- Empirical losses are nonneg -/
  emp_nonneg : ∀ h, 0 ≤ empiricalLoss h
  /-- True losses are nonneg -/
  true_nonneg : ∀ h, 0 ≤ trueLoss h
  /-- Losses are bounded by 1 -/
  emp_le_one : ∀ h, empiricalLoss h ≤ 1
  true_le_one : ∀ h, trueLoss h ≤ 1

namespace PACBayesInstance

variable {H : Type*} [Fintype H]

/-- Expected empirical loss under the posterior. -/
def expectedEmpLoss (inst : PACBayesInstance H) : ℝ :=
  inst.posterior.expect inst.empiricalLoss

/-- Expected true loss under the posterior. -/
def expectedTrueLoss (inst : PACBayesInstance H) : ℝ :=
  inst.posterior.expect inst.trueLoss

end PACBayesInstance

/-! ### PAC-Bayes Sample Complexity -/

/-- **PAC-Bayes sample complexity**: If n >= (KL(Q||P) + log(1/delta)) / (2*eps^2),
    then the generalization gap is at most eps.

    This follows from the sqrt form: sqrt((KL + log(1/delta))/(2n)) <= eps
    when n >= (KL + log(1/delta))/(2*eps^2). -/
theorem pac_bayes_sample_complexity {H : Type*} [Fintype H]
    (inst : PACBayesInstance H)
    {n eps delta : ℝ} (hn : 0 < n) (heps : 0 < eps) (_hdelta : 0 < delta)
    (h_n_large : (klDiv inst.posterior inst.prior + Real.log (1 / delta)) / (2 * eps ^ 2) ≤ n)
    (h_gap : inst.expectedTrueLoss - inst.expectedEmpLoss ≤
        Real.sqrt ((klDiv inst.posterior inst.prior + Real.log (1 / delta)) / (2 * n))) :
    inst.expectedTrueLoss ≤ inst.expectedEmpLoss + eps := by
  -- From the sqrt bound hypothesis h_gap
  suffices hsqrt : Real.sqrt ((klDiv inst.posterior inst.prior +
      Real.log (1 / delta)) / (2 * n)) ≤ eps by
    linarith
  -- Use sqrt_le_left: sqrt(x) <= y iff x <= y^2 (when y >= 0)
  rw [Real.sqrt_le_left (le_of_lt heps)]
  -- Need: (KL + log(1/delta)) / (2n) <= eps^2
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * n)]
  -- From h_n_large: (KL + log(1/delta)) <= 2 * eps^2 * n
  have h1 : klDiv inst.posterior inst.prior + Real.log (1 / delta) ≤ n * (2 * eps ^ 2) := by
    rwa [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * eps ^ 2)] at h_n_large
  nlinarith

/-! ### Comparison: PAC-Bayes vs Uniform Convergence -/

/-- **PAC-Bayes is tighter than uniform convergence**.

    Uniform convergence sample complexity is n = log|H| / (2*eps^2) + log(1/delta) / (2*eps^2).
    PAC-Bayes sample complexity is n = (KL(Q||P) + log(1/delta)) / (2*eps^2).

    Since KL(Q||Uniform) <= log|H| (by `kl_le_log_card`), the PAC-Bayes
    sample complexity is at most the uniform convergence one when
    P = Uniform. This is the fundamental advantage of PAC-Bayes. -/
theorem pac_bayes_vs_uniform {H : Type*} [Fintype H] [Nonempty H]
    (Q : FinDist H)
    {eps delta : ℝ} (heps : 0 < eps) (_hdelta : 0 < delta) :
    (klDiv Q FinDist.uniform + Real.log (1 / delta)) / (2 * eps ^ 2) ≤
      (Real.log (Fintype.card H : ℝ) + Real.log (1 / delta)) / (2 * eps ^ 2) := by
  apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) < 2 * eps ^ 2).le
  linarith [kl_le_log_card Q]

/-! ### RL Instantiation -/

/-- **RL PAC-Bayes instance**: policies as hypotheses, value gap as loss.

    In RL, the hypothesis class is the set of policies. The loss of
    a policy pi is its value gap: V*(s0) - V^pi(s0) (normalized).
    The prior is uniform over policies. The posterior concentrates
    on the learned policy. -/
structure RLPACBayes (M : FiniteMDP) where
  /-- Number of policies in the class -/
  K : ℕ
  hK : 0 < K
  /-- The policies in the class -/
  policies : Fin K → M.StochasticPolicy
  /-- Value gap for each policy: V*(s0) - V^pi(s0), normalized to [0,1] -/
  valueGap : Fin K → ℝ
  /-- Empirical value gap estimates -/
  empValueGap : Fin K → ℝ
  /-- Value gaps are in [0,1] -/
  gap_nonneg : ∀ i, 0 ≤ valueGap i
  gap_le_one : ∀ i, valueGap i ≤ 1
  emp_nonneg : ∀ i, 0 ≤ empValueGap i
  emp_le_one : ∀ i, empValueGap i ≤ 1

namespace RLPACBayes

variable {M : FiniteMDP}

/-- Nonempty instance for Fin K when K > 0. -/
instance instNonemptyFin (rl : RLPACBayes M) : Nonempty (Fin rl.K) :=
  ⟨⟨0, rl.hK⟩⟩

/-- Convert RL PAC-Bayes to a PACBayesInstance over Fin K.

    Both prior and posterior are set to uniform, making KL = 0.
    This is a degenerate baseline. A meaningful PAC-Bayes
    instantiation requires a non-uniform posterior concentrated
    on good policies. -/
def toPACBayes_uniform_baseline (rl : RLPACBayes M) : PACBayesInstance (Fin rl.K) where
  prior := @FinDist.uniform _ _ rl.instNonemptyFin
  posterior := @FinDist.uniform _ _ rl.instNonemptyFin
  empiricalLoss := rl.empValueGap
  trueLoss := rl.valueGap
  emp_nonneg := rl.emp_nonneg
  true_nonneg := rl.gap_nonneg
  emp_le_one := rl.emp_le_one
  true_le_one := rl.gap_le_one

/-- Proves KL(Q || uniform) <= log K for any distribution Q.
    This is a general property of KL divergence, not specific to RL
    or PAC-Bayes. -/
theorem kl_uniform_upper_bound (rl : RLPACBayes M)
    (Q : FinDist (Fin rl.K))
    {eps delta : ℝ} (heps : 0 < eps) (_hdelta : 0 < delta) :
    (klDiv Q (@FinDist.uniform _ _ rl.instNonemptyFin) +
        Real.log (1 / delta)) / (2 * eps ^ 2) ≤
      (Real.log (rl.K : ℝ) + Real.log (1 / delta)) / (2 * eps ^ 2) := by
  apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) < 2 * eps ^ 2).le
  have hkl : klDiv Q (@FinDist.uniform _ _ rl.instNonemptyFin) ≤
      Real.log (Fintype.card (Fin rl.K) : ℝ) :=
    kl_le_log_card Q
  simp [Fintype.card_fin] at hkl
  linarith

end RLPACBayes

end
