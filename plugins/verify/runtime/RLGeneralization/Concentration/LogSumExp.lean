import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Log-Sum-Exp Bounds

The log-sum-exp function `log(∑ exp(xᵢ))` is the smooth approximation to
the maximum. These bounds are used throughout online learning (EXP3, Hedge),
policy optimization (NPG, softmax PG), MaxEnt IRL, and KL-regularized MDPs.

## Main Results

* `max_le_logSumExp` — max xᵢ ≤ log(∑ exp(xᵢ))
* `logSumExp_le_max_add_log_card` — log(∑ exp(xᵢ)) ≤ max xᵢ + log K
* `logSumExp_shift` — log(∑ exp(xᵢ + c)) = c + log(∑ exp(xᵢ))
-/

open Real Finset BigOperators

noncomputable section

/-- **Lower bound**: the maximum is at most log-sum-exp.

    max_i x_i ≤ log(∑_i exp(x_i))

    Proof: exp(max x_i) ≤ ∑ exp(x_i) since the sum includes the max term,
    then take log of both sides. -/
theorem max_le_logSumExp {ι : Type*} [Fintype ι] [Nonempty ι]
    (x : ι → ℝ) :
    Finset.univ.sup' Finset.univ_nonempty x ≤
    Real.log (∑ i, Real.exp (x i)) := by
  have hsum_pos : 0 < ∑ i, Real.exp (x i) :=
    Finset.sum_pos (fun i _ => Real.exp_pos (x i)) ⟨Classical.arbitrary ι, Finset.mem_univ _⟩
  rw [← Real.exp_le_exp, Real.exp_log hsum_pos]
  calc Real.exp (Finset.univ.sup' Finset.univ_nonempty x)
      ≤ ∑ i, Real.exp (x i) := by
        have hmem : ∃ j ∈ Finset.univ, Finset.univ.sup' Finset.univ_nonempty x = x j :=
          Finset.exists_mem_eq_sup' Finset.univ_nonempty x
        obtain ⟨j, _, hj⟩ := hmem
        rw [hj]
        exact Finset.single_le_sum (fun i _ => (Real.exp_pos (x i)).le)
          (Finset.mem_univ j)

/-- **Upper bound**: log-sum-exp is at most the maximum plus log(K).

    log(∑_i exp(x_i)) ≤ max_i x_i + log K

    where K = |ι| is the number of terms.

    Proof: ∑ exp(x_i) ≤ K · exp(max x_i), so
    log(∑ exp(x_i)) ≤ log(K · exp(max)) = log K + max. -/
theorem logSumExp_le_max_add_log_card {ι : Type*} [Fintype ι] [Nonempty ι]
    (x : ι → ℝ) :
    Real.log (∑ i, Real.exp (x i)) ≤
    Finset.univ.sup' Finset.univ_nonempty x + Real.log (Fintype.card ι : ℝ) := by
  have hK_pos : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hsum_le : ∑ i, Real.exp (x i) ≤
      (Fintype.card ι : ℝ) * Real.exp (Finset.univ.sup' Finset.univ_nonempty x) := by
    calc ∑ i, Real.exp (x i)
        ≤ ∑ _i : ι, Real.exp (Finset.univ.sup' Finset.univ_nonempty x) := by
          apply Finset.sum_le_sum; intro i _
          exact Real.exp_le_exp_of_le (Finset.le_sup' x (Finset.mem_univ i))
      _ = (Fintype.card ι : ℝ) * Real.exp (Finset.univ.sup' Finset.univ_nonempty x) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hsum_pos : 0 < ∑ i, Real.exp (x i) :=
    Finset.sum_pos (fun i _ => Real.exp_pos (x i)) ⟨Classical.arbitrary ι, Finset.mem_univ _⟩
  calc Real.log (∑ i, Real.exp (x i))
      ≤ Real.log ((Fintype.card ι : ℝ) * Real.exp (Finset.univ.sup' Finset.univ_nonempty x)) :=
        Real.log_le_log hsum_pos hsum_le
    _ = Real.log (Fintype.card ι : ℝ) +
        Real.log (Real.exp (Finset.univ.sup' Finset.univ_nonempty x)) :=
        Real.log_mul (ne_of_gt hK_pos) (ne_of_gt (Real.exp_pos _))
    _ = Real.log (Fintype.card ι : ℝ) + Finset.univ.sup' Finset.univ_nonempty x := by
        rw [Real.log_exp]
    _ = Finset.univ.sup' Finset.univ_nonempty x + Real.log (Fintype.card ι : ℝ) := by
        ring

/-- **Log-sum-exp shift invariance**: adding a constant to every argument
    shifts the result by that constant.

    log(∑ exp(xᵢ + c)) = c + log(∑ exp(xᵢ))

    Proof: factor out exp(c) from the sum, then use log-of-product.
    Used for numerical stability of softmax and in entropy-regularized
    optimization (temperature scaling). -/
theorem logSumExp_shift {ι : Type*} [Fintype ι] [Nonempty ι]
    (x : ι → ℝ) (c : ℝ) :
    Real.log (∑ i, Real.exp (x i + c)) =
    c + Real.log (∑ i, Real.exp (x i)) := by
  have hZ_pos : 0 < ∑ i, Real.exp (x i) :=
    Finset.sum_pos (fun i _ => Real.exp_pos (x i))
      ⟨Classical.arbitrary ι, Finset.mem_univ _⟩
  have h_factor : ∑ i, Real.exp (x i + c) =
      (∑ i, Real.exp (x i)) * Real.exp c := by
    simp_rw [Real.exp_add]
    rw [← Finset.sum_mul]
  rw [h_factor,
      Real.log_mul (ne_of_gt hZ_pos) (ne_of_gt (Real.exp_pos c)),
      Real.log_exp, add_comm]

end
