import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# epoch_count_bound

Proves the epoch count bound used in UCBVI and similar RL algorithms:
If 2^E ≤ (2K)^(d*H) (counting doublings across d*H groups), then
E ≤ (3/2) * d * H * log(2K).

Key technical lemma: log(2) ≥ 2/3, proved via Taylor expansion bounds
on exp(2/3) using Mathlib's `Real.exp_bound`.
-/

open Real Finset BigOperators

noncomputable section

/-- **log(2) ≥ 2/3**, proved by showing exp(2/3) ≤ 2 via Taylor expansion bounds.

Uses `Real.exp_bound` with n=4 terms: the partial sum is 157/81 ≈ 1.938
and the error bound is 5/486 ≈ 0.010, giving exp(2/3) ≤ 947/486 < 2. -/
lemma two_thirds_le_log_two : (2 : ℝ) / 3 ≤ Real.log 2 := by
  rw [Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 2)]
  have habs : |((2:ℝ)/3)| ≤ 1 := by norm_num
  have hbound := @Real.exp_bound (2/3) habs (n := 4) (by norm_num : 0 < 4)
  have hsum : ∑ m ∈ range 4, ((2:ℝ)/3) ^ m / ↑(Nat.factorial m) = 157/81 := by
    norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  rw [hsum] at hbound
  have herr : |((2:ℝ)/3)| ^ 4 * (↑(Nat.succ 4) / (↑(Nat.factorial 4) * ↑(4:ℕ))) = 5/486 := by
    norm_num [Nat.succ, Nat.factorial]
  rw [herr] at hbound
  have h_le : rexp (2/3) - 157/81 ≤ 5/486 := le_trans (le_abs_self _) hbound
  linarith

/-- **Epoch count bound** for doubling-based RL algorithms.

If the number of epochs E satisfies 2^E ≤ (2K)^(d*H) (from counting
doublings across d*H state-action groups with K arms), then
E ≤ (3/2) * d * H * log(2K).

The proof takes logarithms of both sides, yielding E * log(2) ≤ (d*H) * log(2K),
then divides by log(2) using the bound log(2) ≥ 2/3 to obtain the factor 3/2. -/
theorem epoch_count_bound_proved
    (d H K : ℕ) (hd : 0 < d) (hH : 0 < H) (hK : 0 < K) (E : ℕ)
    (h_doubling : (2 : ℝ) ^ E ≤ (2 * ↑K) ^ (d * H)) :
    (E : ℝ) ≤ (3 / 2) * ↑d * ↑H * Real.log (2 * ↑K) := by
  have h2E_pos : (0 : ℝ) < 2 ^ E := pow_pos (by norm_num) E
  have h2K_pos : (0 : ℝ) < 2 * ↑K := by positivity
  have h2K_pow_pos : (0 : ℝ) < (2 * ↑K) ^ (d * H) := pow_pos h2K_pos (d * H)
  have hlog := Real.log_le_log h2E_pos h_doubling
  rw [Real.log_pow, Real.log_pow] at hlog
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
  have hlog2_bound := two_thirds_le_log_two
  have h_E_bound : (↑E : ℝ) * (2/3) ≤ ↑(d * H) * Real.log (2 * ↑K) := by
    calc (↑E : ℝ) * (2/3) ≤ ↑E * Real.log 2 := by
          apply mul_le_mul_of_nonneg_left hlog2_bound (Nat.cast_nonneg E)
      _ ≤ ↑(d * H) * Real.log (2 * ↑K) := hlog
  have h_cast : (↑(d * H) : ℝ) = ↑d * ↑H := by push_cast; ring
  rw [h_cast] at h_E_bound
  linarith
