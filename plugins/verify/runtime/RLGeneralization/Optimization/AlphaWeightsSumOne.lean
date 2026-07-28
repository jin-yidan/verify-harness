import Mathlib
import RLGeneralization.Optimization.WeightedSurvivalSum

open Finset BigOperators

/-- Foundational fact of Jin et al. (2018) Lemma 4.1 (generalized to constant
`C` with `C ≠ -1`): the Q-learning learning-rate weights
`α_n^i = (C+1)/(C+i) · ∏_{j=i+1}^n (1 - (C+1)/(C+j))` sum to one over
`i = 1,…,n` for every `n ≥ 1`. -/
theorem alpha_weights_sum_one (C : ℝ) (hC : C + 1 ≠ 0) {n : ℕ} (hn : 1 ≤ n) :
    ∑ i ∈ Finset.Icc 1 n, ((C + 1) / (C + (i : ℝ))) *
        ∏ j ∈ Finset.Ioc i n, (1 - (C + 1) / (C + (j : ℝ))) = 1 := by
  have h := weighted_survival_sum (fun t : ℕ => (C + 1) / (C + (t : ℝ))) n
  have hzero : ∏ j ∈ Finset.Icc 1 n, (1 - (C + 1) / (C + (j : ℝ))) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_Icc.mpr ⟨le_refl 1, hn⟩)
    have hcast : (C : ℝ) + ((1 : ℕ) : ℝ) = C + 1 := by norm_num
    rw [hcast, div_self hC, sub_self]
  rw [h, hzero, sub_zero]

