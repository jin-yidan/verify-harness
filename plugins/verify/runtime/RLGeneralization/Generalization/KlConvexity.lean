/-
# Joint Convexity of KL Divergence

KL(tP₁+(1−t)P₂ ‖ tQ₁+(1−t)Q₂) ≤ t·KL(P₁‖Q₁) + (1−t)·KL(P₂‖Q₂).

## Main Results

* `kl_convexity` — joint convexity of the KL divergence, finite case,
  for nonnegative (not necessarily normalized) numerator vectors.

## References

* Cover & Thomas, Elements of Information Theory, Theorem 2.7.2
* Proved from `log_sum_le_sum_log` (Thm 2.7.1, KLProperties.lean);
  kernel-verified in run kl_convexity_cover_thomas_2_7_2 (2026-06-10)
* Consumers: mixture-policy analyses, mirror descent / TRPO regularizer
  convexity, information-theoretic lower bounds
-/
import RLGeneralization.Generalization.KLProperties

open Finset BigOperators

/-- Pointwise mixture bound for 0 < t < 1: the two-element log-sum
    inequality with the scales t, (1−t) cancelled inside the logs. -/
private lemma kl_pointwise_convex {a₁ a₂ b₁ b₂ t : ℝ}
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    (ht0 : 0 < t) (ht1 : t < 1) :
    (t * a₁ + (1 - t) * a₂) *
      Real.log ((t * a₁ + (1 - t) * a₂) / (t * b₁ + (1 - t) * b₂)) ≤
    t * (a₁ * Real.log (a₁ / b₁)) + (1 - t) * (a₂ * Real.log (a₂ / b₂)) := by
  have ht1' : (0 : ℝ) < 1 - t := by linarith
  have key := log_sum_le_sum_log (Finset.univ : Finset (Fin 2))
      ![t * a₁, (1 - t) * a₂] ![t * b₁, (1 - t) * b₂]
      (by
        intro i _
        fin_cases i
        · simpa using mul_nonneg ht0.le ha₁
        · simpa using mul_nonneg ht1'.le ha₂)
      (by
        intro i _
        fin_cases i
        · simpa using mul_pos ht0 hb₁
        · simpa using mul_pos ht1' hb₂)
      (by
        simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons]
        exact add_pos (mul_pos ht0 hb₁) (mul_pos ht1' hb₂))
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] at key
  rw [mul_div_mul_left _ _ (ne_of_gt ht0), mul_div_mul_left _ _ (ne_of_gt ht1')] at key
  have e1 : t * a₁ * Real.log (a₁ / b₁) = t * (a₁ * Real.log (a₁ / b₁)) := by ring
  have e2 : (1 - t) * a₂ * Real.log (a₂ / b₂) = (1 - t) * (a₂ * Real.log (a₂ / b₂)) := by
    ring
  linarith [key]

/-- **Joint convexity of KL divergence** (Cover & Thomas, Thm 2.7.2):
    KL(tP₁+(1−t)P₂ ‖ tQ₁+(1−t)Q₂) ≤ t·KL(P₁‖Q₁) + (1−t)·KL(P₂‖Q₂),
    finite case, nonnegative numerators, positive denominators. -/
theorem kl_convexity {ι : Type*} [Fintype ι]
    (p₁ p₂ q₁ q₂ : ι → ℝ) (t : ℝ)
    (hp₁ : ∀ i, 0 ≤ p₁ i) (hp₂ : ∀ i, 0 ≤ p₂ i)
    (hq₁ : ∀ i, 0 < q₁ i) (hq₂ : ∀ i, 0 < q₂ i)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∑ i, (t * p₁ i + (1 - t) * p₂ i) *
      Real.log ((t * p₁ i + (1 - t) * p₂ i) / (t * q₁ i + (1 - t) * q₂ i)) ≤
    t * ∑ i, p₁ i * Real.log (p₁ i / q₁ i) +
      (1 - t) * ∑ i, p₂ i * Real.log (p₂ i / q₂ i) := by
  rcases eq_or_lt_of_le ht0 with h0 | h0
  · simp [← h0]
  rcases eq_or_lt_of_le ht1 with h1 | h1
  · simp [h1]
  calc ∑ i, (t * p₁ i + (1 - t) * p₂ i) *
        Real.log ((t * p₁ i + (1 - t) * p₂ i) / (t * q₁ i + (1 - t) * q₂ i))
      ≤ ∑ i, (t * (p₁ i * Real.log (p₁ i / q₁ i)) +
              (1 - t) * (p₂ i * Real.log (p₂ i / q₂ i))) := by
        apply Finset.sum_le_sum
        intro i _
        exact kl_pointwise_convex (hp₁ i) (hp₂ i) (hq₁ i) (hq₂ i) h0 h1
    _ = t * ∑ i, p₁ i * Real.log (p₁ i / q₁ i) +
        (1 - t) * ∑ i, p₂ i * Real.log (p₂ i / q₂ i) := by
        rw [Finset.sum_add_distrib]
        congr 1 <;> rw [← Finset.mul_sum]

