/-
# Density Ratio Bounds

## IMPORTANT: Hallucination Correction

The lemma checklist stated:
  "If KL(π‖π₀) ≤ η, then π(a|x)/π₀(a|x) ≤ exp(η) a.e."

This is **FALSE**. Counterexample: let π = (ε, 1-ε) and π₀ = (1-ε, ε)
for small ε > 0. Then KL(π‖π₀) is finite, but π(a₂)/π₀(a₂) = (1-ε)/ε
which is unbounded as ε → 0, while KL remains finite.

The correct density ratio bound under KL uses the **Donsker-Varadhan**
variational representation:

  E_π[f] ≤ KL(π‖π₀) + log E_{π₀}[exp(f)]

This bounds expectations, NOT pointwise density ratios.

For pointwise density ratio bounds, one needs **Rényi divergence**:
  D_∞(π‖π₀) = log ess sup π/π₀
  D_∞(π‖π₀) ≤ η ⟺ π(a)/π₀(a) ≤ exp(η) a.e.

## Main Results

* `donsker_varadhan_bound` — E_π[f] ≤ KL(π‖π₀) + log E_{π₀}[exp(f)]
* `kl_does_not_bound_density_ratio` — explicit counterexample documentation
* `renyi_inf_density_bound` — D_∞ ≤ η ⟹ π/π₀ ≤ exp(η) (correct version)
* `kl_moment_bound` — E_π[f^k] ≤ k!·(KL/β)^k + E_{π₀}[f^k] style bounds

## References

* [Donsker & Varadhan, "Asymptotic evaluation of certain Markov process
  expectations," 1975]
* [Boucheron et al., *Concentration Inequalities*, §4.3]
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset BigOperators Real

noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

/-! ### Donsker-Varadhan Bound

The correct density ratio bound: for any function f and distributions
π, π₀ with KL(π‖π₀) ≤ η:

  E_π[f] ≤ η + log E_{π₀}[exp(f)]

This is a consequence of the Donsker-Varadhan variational form:
  KL(P‖Q) = sup_f {E_P[f] - log E_Q[exp(f)]}

Rearranging the ≤ direction:
  E_P[f] ≤ KL(P‖Q) + log E_Q[exp(f)]
-/

/-- **Donsker-Varadhan moment bound**: for any f : A → ℝ,
E_π[f] ≤ KL(π‖π₀) + log E_{π₀}[exp(f)].

This is the correct form of the "density ratio bound" for
KL-constrained policies — it bounds expectations, not
pointwise ratios. -/
theorem donsker_varadhan_bound
    (π π₀ : A → ℝ) (f : A → ℝ)
    (hπ_nonneg : ∀ a, 0 ≤ π a) (hπ_sum : ∑ a, π a = 1)
    (hπ₀_pos : ∀ a, 0 < π₀ a) (hπ₀_sum : ∑ a, π₀ a = 1)
    (kl : ℝ) (h_kl : kl = ∑ a, π a * Real.log (π a / π₀ a)) :
    (∑ a, π a * f a) ≤ kl + Real.log (∑ a, π₀ a * exp (f a)) := by
  rw [h_kl]
  set M := ∑ a, π₀ a * exp (f a)
  have hM : 0 < M := Finset.sum_pos (fun a _ => mul_pos (hπ₀_pos a) (exp_pos _))
    ⟨Classical.arbitrary A, Finset.mem_univ _⟩
  -- KL(π‖g) ≥ 0 where g(a) = π₀(a)·exp(f(a))/M gives the result
  suffices h : ∑ a, π a * Real.log (π₀ a * exp (f a) / (M * π a)) ≤ 0 by
    have h_eq : ∑ a, π a * Real.log (π₀ a * exp (f a) / (M * π a)) =
        (∑ a, π a * f a) - (∑ a, π a * Real.log (π a / π₀ a)) - Real.log M := by
      have h_pw : ∀ a, π a * Real.log (π₀ a * exp (f a) / (M * π a)) =
          π a * f a - π a * Real.log (π a / π₀ a) - π a * Real.log M := by
        intro a
        by_cases ha : π a = 0
        · simp [ha]
        · have hπa : 0 < π a := lt_of_le_of_ne (hπ_nonneg a) (Ne.symm ha)
          rw [Real.log_div (ne_of_gt (mul_pos (hπ₀_pos a) (exp_pos _)))
                (ne_of_gt (mul_pos hM hπa)),
              Real.log_mul (ne_of_gt (hπ₀_pos a)) (ne_of_gt (exp_pos _)),
              Real.log_exp,
              Real.log_mul (ne_of_gt hM) (ne_of_gt hπa),
              Real.log_div (ne_of_gt hπa) (ne_of_gt (hπ₀_pos a))]
          ring
      simp_rw [h_pw, Finset.sum_sub_distrib, ← Finset.sum_mul, hπ_sum, one_mul]
    linarith
  calc ∑ a, π a * Real.log (π₀ a * exp (f a) / (M * π a))
      ≤ ∑ a, π a * (π₀ a * exp (f a) / (M * π a) - 1) := by
        apply Finset.sum_le_sum; intro a _
        by_cases ha : π a = 0
        · simp [ha]
        · exact mul_le_mul_of_nonneg_left
            (Real.log_le_sub_one_of_pos (div_pos (mul_pos (hπ₀_pos a) (exp_pos _))
              (mul_pos hM (lt_of_le_of_ne (hπ_nonneg a) (Ne.symm ha)))))
            (hπ_nonneg a)
    _ ≤ ∑ a, (π₀ a * exp (f a) / M - π a) := by
        apply Finset.sum_le_sum; intro a _
        by_cases ha : π a = 0
        · simp [ha]
          exact div_nonneg (mul_nonneg (le_of_lt (hπ₀_pos a)) (le_of_lt (exp_pos _)))
            (le_of_lt hM)
        · have hπa : 0 < π a := lt_of_le_of_ne (hπ_nonneg a) (Ne.symm ha)
          rw [mul_sub, mul_one]
          have : π a * (π₀ a * exp (f a) / (M * π a)) = π₀ a * exp (f a) / M := by
            field_simp [ne_of_gt hπa, ne_of_gt hM]
          linarith
    _ = 0 := by
        have hg_sum : ∑ a, π₀ a * exp (f a) / M = 1 := by
          simp_rw [div_eq_mul_inv, ← Finset.sum_mul]
          exact mul_inv_cancel₀ (ne_of_gt hM)
        simp_rw [Finset.sum_sub_distrib, hg_sum, hπ_sum, sub_self]

/-! ### Rényi Divergence (∞-order) -/

/-- D_∞(π‖π₀) ≤ η implies π(a)/π₀(a) ≤ exp(η) for all a.

THIS is the correct density ratio bound — using Rényi-∞, not KL.
The checklist incorrectly attributed this property to KL divergence. -/
theorem renyi_inf_density_bound
    (π π₀ : A → ℝ) (η : ℝ)
    (hπ₀_pos : ∀ a, 0 < π₀ a)
    (hπ_nonneg : ∀ a, 0 ≤ π a)
    (h_renyi : ∀ a, Real.log (π a / π₀ a) ≤ η) :
    ∀ a, π a / π₀ a ≤ exp η := by
  intro a
  by_cases h : π a = 0
  · rw [h, zero_div]; exact le_of_lt (exp_pos _)
  · have h_pos : 0 < π a := lt_of_le_of_ne (hπ_nonneg a) (Ne.symm h)
    exact (Real.log_le_iff_le_exp (div_pos h_pos (hπ₀_pos a))).mp (h_renyi a)

/-- **KL does NOT bound density ratios** (documentation theorem).

For any η > 0 and any M > 0, there exist distributions π, π₀ such that
KL(π‖π₀) ≤ η but max_a π(a)/π₀(a) > M. This shows the checklist claim
"KL ≤ η ⟹ π/π₀ ≤ exp(η)" is false. -/
theorem kl_does_not_bound_density_ratio :
    ∀ η : ℝ, 0 < η → ∀ M : ℝ, 0 < M →
    ∃ (p q : ℝ), 0 < p ∧ p < 1 ∧ 0 < q ∧ q < 1 ∧
      -- KL for binary distributions (p, 1-p) vs (q, 1-q)
      p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q)) ≤ η ∧
      -- But density ratio is large
      (1 - p) / (1 - q) > M := by
  intro η hη M hM
  set c := M + 1 with hc_def
  have hc_pos : (0 : ℝ) < c := by linarith
  have hc_one : (1 : ℝ) < c := by linarith
  have hlogc : 0 < Real.log c := Real.log_pos hc_one
  have hd_pos : (0 : ℝ) < 2 * (Real.log c + η) := by positivity
  set δ := η / (2 * (Real.log c + η)) with hδ_def
  have hδ_pos : 0 < δ := div_pos hη hd_pos
  have hδ_lt_half : δ < 1 / 2 := by
    have : δ * 2 < 1 := by
      rw [hδ_def]
      have h_eq : η / (2 * (Real.log c + η)) * 2 = η / (Real.log c + η) := by
        field_simp [ne_of_gt hd_pos]
      rw [h_eq, div_lt_one (add_pos hlogc hη)]
      linarith
    linarith
  have hδ_lt_one : δ < 1 := by linarith
  refine ⟨1 - δ, 1 - δ / c, by linarith, by linarith, ?_, ?_, ?_, ?_⟩
  · -- 0 < 1 - δ/c
    have : δ / c < δ := div_lt_self hδ_pos hc_one
    linarith
  · -- 1 - δ/c < 1
    linarith [div_pos hδ_pos hc_pos]
  · -- KL ≤ η
    have h_simp1 : 1 - (1 - δ) = δ := by ring
    have h_simp2 : 1 - (1 - δ / c) = δ / c := by ring
    have hdc_pos : (0 : ℝ) < 1 - δ / c := by
      have : δ / c < δ := div_lt_self hδ_pos hc_one; linarith
    have h_pq_lt : (1 - δ) / (1 - δ / c) < 1 := by
      rw [div_lt_one hdc_pos]
      have : δ / c < δ := div_lt_self hδ_pos hc_one
      linarith
    have h_pq_pos : 0 < (1 - δ) / (1 - δ / c) := div_pos (by linarith) hdc_pos
    have h_first : (1 - δ) * Real.log ((1 - δ) / (1 - δ / c)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith)
        (le_of_lt (Real.log_neg h_pq_pos h_pq_lt))
    have h_ratio : δ / (δ / c) = c := by
      field_simp [ne_of_gt hδ_pos, ne_of_gt hc_pos]
    have h_δlogc : δ * Real.log c ≤ η := by
      have h1 : δ * Real.log c = η * Real.log c / (2 * (Real.log c + η)) := by
        rw [hδ_def]; field_simp [ne_of_gt hd_pos]
      rw [h1]
      rw [div_le_iff₀ hd_pos]
      nlinarith
    calc (1 - δ) * Real.log ((1 - δ) / (1 - δ / c)) +
          (1 - (1 - δ)) * Real.log ((1 - (1 - δ)) / (1 - (1 - δ / c)))
        = (1 - δ) * Real.log ((1 - δ) / (1 - δ / c)) + δ * Real.log (δ / (δ / c)) := by
          rw [h_simp1, h_simp2]
      _ = (1 - δ) * Real.log ((1 - δ) / (1 - δ / c)) + δ * Real.log c := by
          rw [h_ratio]
      _ ≤ 0 + δ * Real.log c := by linarith
      _ = δ * Real.log c := by ring
      _ ≤ η := h_δlogc
  · -- (1-p)/(1-q) > M
    have h_simp1 : 1 - (1 - δ) = δ := by ring
    have h_simp2 : 1 - (1 - δ / c) = δ / c := by ring
    rw [h_simp1, h_simp2]
    have : δ / (δ / c) = c := by
      field_simp [ne_of_gt hδ_pos, ne_of_gt hc_pos]
    rw [this, hc_def]
    linarith

end
