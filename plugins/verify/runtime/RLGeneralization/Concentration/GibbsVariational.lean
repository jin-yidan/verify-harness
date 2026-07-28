import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Gibbs Variational Inequality

The log-partition function `log(∑ exp(xᵢ))` upper-bounds the
entropy-regularized linear objective `∑ pᵢ xᵢ + H(p)` for any
probability distribution p, where H(p) = -∑ pᵢ log(pᵢ) is the
Shannon entropy. Equality holds iff p is the softmax of x.

This is the core identity connecting log-sum-exp to entropy-regularized
optimization, used in MaxEnt RL, soft Q-learning / SAC, follow the
regularized leader (FTRL), and natural policy gradient (NPG).

## Main Results

* `gibbs_variational` — ∑ pᵢ xᵢ - ∑ pᵢ log(pᵢ) ≤ log(∑ exp(xᵢ))

## Relation to existing results

Mathematically this is the `Q = uniform` special case of
`klDiv_donsker_varadhan_le` (Generalization/KLProperties.lean): with
KL(P‖U) = ∑ pᵢ log pᵢ + log n and log E_U[exp x] = log ∑ exp xᵢ − log n the
log n terms cancel. It is kept as a standalone because the raw finite-sum
statement has no `FinDist` dependency and the derivation is not a 1–2-line
instantiation (gate audit 2026-06-10, rlverify/results/gate_ab_test.md).
-/

open Real Finset BigOperators

noncomputable section

/-- **Gibbs variational inequality** (log-partition variational bound).

    For any probability distribution `p` on a finite type and any
    payoff vector `x`:

      ∑ pᵢ xᵢ + H(p) ≤ log(∑ exp(xᵢ))

    where H(p) = -∑ pᵢ log(pᵢ) is the Shannon entropy.

    Equivalently, the log-partition function is the convex conjugate
    of the negative entropy over the probability simplex.

    Proof: construct the softmax distribution qᵢ = exp(xᵢ)/Z,
    show KL(p ‖ q) ≥ 0 via `log(t) ≤ t - 1`, and rearrange. -/
theorem gibbs_variational {ι : Type*} [Fintype ι] [Nonempty ι]
    (p : ι → ℝ) (x : ι → ℝ)
    (hp_nonneg : ∀ i, 0 ≤ p i)
    (hp_sum : ∑ i, p i = 1) :
    ∑ i, p i * x i - ∑ i, p i * Real.log (p i) ≤
    Real.log (∑ i, Real.exp (x i)) := by
  set Z := ∑ i, Real.exp (x i)
  have hZ : 0 < Z := Finset.sum_pos (fun i _ => Real.exp_pos (x i))
    ⟨Classical.arbitrary ι, Finset.mem_univ _⟩
  set q : ι → ℝ := fun i => Real.exp (x i) / Z
  have hq_pos : ∀ i, 0 < q i := fun i => div_pos (Real.exp_pos _) hZ
  have hq_sum : ∑ i, q i = 1 := by
    simp_rw [q, div_eq_mul_inv, ← Finset.sum_mul]
    exact mul_inv_cancel₀ (ne_of_gt hZ)
  have hlog_q : ∀ i, Real.log (q i) = x i - Real.log Z := by
    intro i
    simp_rw [q]
    rw [Real.log_div (ne_of_gt (Real.exp_pos _)) (ne_of_gt hZ), Real.log_exp]
  suffices h_kl : 0 ≤ ∑ i, p i * Real.log (p i) - ∑ i, p i * Real.log (q i) by
    have h_log_q_sum : ∑ i, p i * Real.log (q i) =
        ∑ i, p i * x i - Real.log Z := by
      have : ∀ i, p i * Real.log (q i) = p i * x i - p i * Real.log Z := by
        intro i; rw [hlog_q i, mul_sub]
      simp_rw [this, Finset.sum_sub_distrib, ← Finset.sum_mul, hp_sum, one_mul]
    linarith
  have h_neg : ∑ i, p i * Real.log (q i / p i) ≤ 0 := by
    calc ∑ i, p i * Real.log (q i / p i)
        ≤ ∑ i, (q i - p i) := by
          apply Finset.sum_le_sum
          intro i _
          by_cases hi : p i = 0
          · simp [hi, (hq_pos i).le]
          · have hpi : 0 < p i := lt_of_le_of_ne (hp_nonneg i) (Ne.symm hi)
            calc p i * Real.log (q i / p i)
                ≤ p i * (q i / p i - 1) :=
                  mul_le_mul_of_nonneg_left
                    (Real.log_le_sub_one_of_pos (div_pos (hq_pos i) hpi)) hpi.le
              _ = q i - p i := by field_simp
      _ = 0 := by
          simp only [Finset.sum_sub_distrib, hq_sum, hp_sum, sub_self]
  have h_convert : ∑ i, p i * Real.log (p i) - ∑ i, p i * Real.log (q i) =
      -(∑ i, p i * Real.log (q i / p i)) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    congr 1; funext i
    by_cases hi : p i = 0
    · simp [hi]
    · have hpi : 0 < p i := lt_of_le_of_ne (hp_nonneg i) (Ne.symm hi)
      rw [Real.log_div (ne_of_gt (hq_pos i)) (ne_of_gt hpi)]
      ring
  rw [h_convert]
  linarith

end
