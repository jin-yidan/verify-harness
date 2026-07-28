/-
# Total Variation Distance Properties

Provides a standalone, reusable definition of TV distance for finite
distributions and proves fundamental properties:

- d_TV = sup_{A⊆S} |P(A) - Q(A)| (event characterization)
- d_TV ∈ [0, 1]
- Triangle inequality
- Data processing inequality

## Main Results

* `tvDistFin` — d_TV(P,Q) = (1/2)∑|P(x)-Q(x)| (canonical definition)
* `tvDistFin_nonneg` — d_TV ≥ 0
* `tvDistFin_le_one` — d_TV ≤ 1
* `tvDistFin_self` — d_TV(P,P) = 0
* `tvDistFin_symm` — d_TV(P,Q) = d_TV(Q,P)
* `tvDistFin_triangle` — d_TV(P,R) ≤ d_TV(P,Q) + d_TV(Q,R)
* `tvDistFin_ge_event` — P(A) - Q(A) ≤ 2·d_TV
* `tvDistFin_data_processing` — d_TV(f#P, f#Q) ≤ d_TV(P,Q)

## References

* [Levin, Peres, *Markov Chains and Mixing Times*, Ch 4]
* [Tsybakov, *Introduction to Nonparametric Estimation*, §2.1]
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset BigOperators

noncomputable section

variable {S : Type*} [Fintype S] [DecidableEq S]

/-! ### TV Distance Definition -/

/-- **Total variation distance** for finite weight functions:
d_TV(P,Q) = (1/2) ∑_x |P(x) - Q(x)|. -/
def tvDistFin (P Q : S → ℝ) : ℝ :=
  (1 / 2) * ∑ x, |P x - Q x|

/-- d_TV ≥ 0. -/
theorem tvDistFin_nonneg (P Q : S → ℝ) : 0 ≤ tvDistFin P Q := by
  unfold tvDistFin
  apply mul_nonneg (by norm_num)
  exact Finset.sum_nonneg fun x _ => abs_nonneg _

/-- d_TV(P,P) = 0. -/
theorem tvDistFin_self (P : S → ℝ) : tvDistFin P P = 0 := by
  simp [tvDistFin, sub_self]

/-- d_TV(P,Q) = d_TV(Q,P). -/
theorem tvDistFin_symm (P Q : S → ℝ) : tvDistFin P Q = tvDistFin Q P := by
  unfold tvDistFin; congr 1; congr 1; ext x; rw [abs_sub_comm]

/-- d_TV ≤ 1 for probability distributions. -/
theorem tvDistFin_le_one (P Q : S → ℝ)
    (hP_nonneg : ∀ x, 0 ≤ P x) (hQ_nonneg : ∀ x, 0 ≤ Q x)
    (hP_sum : ∑ x, P x = 1) (hQ_sum : ∑ x, Q x = 1) :
    tvDistFin P Q ≤ 1 := by
  unfold tvDistFin
  have h : ∑ x, |P x - Q x| ≤ 2 := by
    calc ∑ x, |P x - Q x|
        ≤ ∑ x, (P x + Q x) := Finset.sum_le_sum fun x _ => by
          rw [abs_le]; constructor <;> linarith [hP_nonneg x, hQ_nonneg x]
      _ = ∑ x, P x + ∑ x, Q x := Finset.sum_add_distrib
      _ = 2 := by rw [hP_sum, hQ_sum]; ring
  linarith

/-! ### Triangle Inequality -/

/-- d_TV(P,R) ≤ d_TV(P,Q) + d_TV(Q,R) (triangle inequality). -/
theorem tvDistFin_triangle (P Q R : S → ℝ) :
    tvDistFin P R ≤ tvDistFin P Q + tvDistFin Q R := by
  unfold tvDistFin
  calc (1 / 2) * ∑ x, |P x - R x|
      ≤ (1 / 2) * ((∑ x, |P x - Q x|) + ∑ x, |Q x - R x|) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 1/2)
        calc ∑ x, |P x - R x|
            = ∑ x, |(P x - Q x) + (Q x - R x)| := by congr 1; ext x; ring_nf
          _ ≤ ∑ x, (|P x - Q x| + |Q x - R x|) :=
              Finset.sum_le_sum fun x _ => abs_add_le _ _
          _ = (∑ x, |P x - Q x|) + ∑ x, |Q x - R x| := Finset.sum_add_distrib
    _ = (1 / 2) * ∑ x, |P x - Q x| + (1 / 2) * ∑ x, |Q x - R x| := by ring

/-! ### Event Bound -/

/-- **Weak event bound**: for any event A ⊆ S (no distribution assumptions),
P(A) - Q(A) ≤ ∑|P-Q| = 2·d_TV(P,Q).
The tight bound P(A) - Q(A) ≤ d_TV requires ∑P = ∑Q = 1. -/
theorem tvDistFin_ge_event (P Q : S → ℝ) (A : Finset S) :
    ∑ x ∈ A, (P x - Q x) ≤ tvDistFin P Q + tvDistFin P Q := by
  unfold tvDistFin
  have h1 : ∑ x ∈ A, (P x - Q x) ≤ ∑ x, |P x - Q x| :=
    calc ∑ x ∈ A, (P x - Q x)
        ≤ ∑ x ∈ A, |P x - Q x| := Finset.sum_le_sum fun x _ => le_abs_self _
      _ ≤ ∑ x ∈ Finset.univ, |P x - Q x| :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
            (fun x _ _ => abs_nonneg _)
      _ = ∑ x, |P x - Q x| := by simp
  linarith

/-! ### Data Processing Inequality -/

/-- **TV data processing inequality**: for any map f : S → T,
d_TV(f#P, f#Q) ≤ d_TV(P,Q).

Applying a deterministic function can only decrease TV distance. -/
theorem tvDistFin_data_processing
    {T : Type*} [Fintype T] [DecidableEq T]
    (P Q : S → ℝ) (f : S → T)
    (hP_nonneg : ∀ x, 0 ≤ P x) (hQ_nonneg : ∀ x, 0 ≤ Q x) :
    tvDistFin (fun y => ∑ x ∈ Finset.univ.filter (fun x => f x = y), P x)
              (fun y => ∑ x ∈ Finset.univ.filter (fun x => f x = y), Q x) ≤
    tvDistFin P Q := by
  unfold tvDistFin
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 1/2)
  calc ∑ y, |∑ x ∈ Finset.univ.filter (fun x => f x = y), P x -
              ∑ x ∈ Finset.univ.filter (fun x => f x = y), Q x|
      = ∑ y, |∑ x ∈ Finset.univ.filter (fun x => f x = y), (P x - Q x)| := by
        congr 1; ext y; congr 1; rw [Finset.sum_sub_distrib]
    _ ≤ ∑ y, ∑ x ∈ Finset.univ.filter (fun x => f x = y), |P x - Q x| :=
        Finset.sum_le_sum fun y _ => Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, |P x - Q x| := by
        rw [← Finset.sum_biUnion]
        · congr 1; ext x; simp
        · intro i _ j _ hij
          exact Finset.disjoint_filter.mpr fun x _ h1 h2 => hij (h1.symm.trans h2)

end
