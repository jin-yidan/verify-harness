/-
# Bellman Backup Noise Process

Defines noise terms from Bellman backups in linear MDPs and proves they
are zero-mean (conditional on history) and bounded.

## Main Results

* `bellmanNoise` — noise ε = V(s') - E[V(s') | s,a]
* `bellmanNoise_expectation_zero` — E[ε | s,a] = 0
* `bellmanNoise_bounded_by_V` — |ε| ≤ 2B when |V| ≤ B
* `bellmanNoise_sq_bounded` — ε² ≤ (2B)²
-/

import RLGeneralization.MDP.FiniteHorizon
import RLGeneralization.LinearMDP.Basic
import Mathlib.Tactic

set_option linter.unusedVariables false

open Finset BigOperators

noncomputable section

namespace FiniteHorizonMDP

variable (M : FiniteHorizonMDP)

def bellmanNoise (V_next : M.S → ℝ) (h : Fin M.H) (s : M.S) (a : M.A) (s' : M.S) : ℝ :=
  V_next s' - ∑ s'', M.P h s a s'' * V_next s''

theorem bellmanNoise_expectation_zero
    (V_next : M.S → ℝ) (h : Fin M.H) (s : M.S) (a : M.A) :
    ∑ s', M.P h s a s' * bellmanNoise M V_next h s a s' = 0 := by
  simp only [bellmanNoise, mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul]
  rw [M.P_sum_one h s a]
  linarith

theorem bellmanNoise_bounded_by_V
    (V_next : M.S → ℝ) (h : Fin M.H) (s : M.S) (a : M.A) (s' : M.S)
    (B : ℝ) (hB : 0 ≤ B)
    (hV : ∀ s, |V_next s| ≤ B) :
    |bellmanNoise M V_next h s a s'| ≤ 2 * B := by
  unfold bellmanNoise
  have h1 : |V_next s'| ≤ B := hV s'
  have h2 : |∑ s'', M.P h s a s'' * V_next s''| ≤ B := by
    calc |∑ s'', M.P h s a s'' * V_next s''|
        ≤ ∑ s'', |M.P h s a s'' * V_next s''| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ s'', M.P h s a s'' * |V_next s''| := by
          congr 1; ext s''
          rw [abs_mul, abs_of_nonneg (M.P_nonneg h s a s'')]
      _ ≤ ∑ s'', M.P h s a s'' * B := by
          apply Finset.sum_le_sum; intro s'' _
          exact mul_le_mul_of_nonneg_left (hV s'') (M.P_nonneg h s a s'')
      _ = B := by rw [← Finset.sum_mul, M.P_sum_one h s a, one_mul]
  have ha := abs_le.mp h1
  have hb := abs_le.mp h2
  rw [abs_le]
  constructor <;> linarith

theorem bellmanNoise_sq_bounded
    (V_next : M.S → ℝ) (h : Fin M.H) (s : M.S) (a : M.A)
    (B : ℝ) (hB : 0 ≤ B)
    (hV : ∀ s, |V_next s| ≤ B)
    (s' : M.S) :
    (bellmanNoise M V_next h s a s') ^ 2 ≤ (2 * B) ^ 2 := by
  have hbd := bellmanNoise_bounded_by_V M V_next h s a s' B hB hV
  have h2B : 0 ≤ 2 * B := by linarith
  exact sq_le_sq' (by linarith [abs_le.mp hbd]) (by linarith [abs_le.mp hbd])

end FiniteHorizonMDP

end
