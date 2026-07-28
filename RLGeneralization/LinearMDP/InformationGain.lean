/-
# Maximum Information Gain

Defines the maximum information gain γ_T for kernel-based RL and
proves algebraic bounds.

The maximum information gain measures information from T observations
about an unknown function in an RKHS:
  γ_T = max_{z_1,...,z_T} ½ log det(I + lam⁻¹ K_T)

Key bounds by kernel type:
- Linear (d-dim):  γ_T ≤ (d/2)·log(1 + T/(dlam))     = O(d log T)
- Squared exp:     γ_T = O((log T)^{d+1})
- Matérn-ν:        γ_T = O(T^{d(d+1)/(2ν+d(d+1))} (log T))

These control regret of GP-UCB and Kernel-UCBVI.

## Main Results

* `infoGainBound` — d/2 · log(1 + T/(dlam))
* `infoGainBound_nonneg` — nonnegativity
* `infoGainBound_monotone` — monotone in T
* `infoGainBound_le_linear` — bounded by T/(2lam) via log(1+x) ≤ x
* `info_gain_from_eigenvalues` — [CONDITIONAL] from AM-GM on eigenvalues

## References

* [Srinivas et al., "Gaussian Process Optimization," ICML 2010]
* [Chowdhury and Gopalan, "On Kernelized Multi-armed Bandits," ICML 2017]
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Real

noncomputable section

/-! ### Information Gain Bound Expression -/

/-- **Linear kernel information gain bound expression**:
    (d/2) · log(1 + T/(dlam)). -/
def infoGainBound (d T : ℕ) (lam : ℝ) : ℝ :=
  ↑d / 2 * Real.log (1 + ↑T / (↑d * lam))

/-- The info gain bound is nonneg when d ≥ 1, lam > 0. -/
theorem infoGainBound_nonneg (d T : ℕ) (lam : ℝ)
    (hd : 0 < d) (hlam : 0 < lam) :
    0 ≤ infoGainBound d T lam := by
  unfold infoGainBound
  apply mul_nonneg
  · positivity
  · apply Real.log_nonneg
    have : 0 ≤ ↑T / (↑d * lam) := by positivity
    linarith

/-- The info gain bound is monotone in T. -/
theorem infoGainBound_monotone (d : ℕ) (lam : ℝ)
    (hd : 0 < d) (hlam : 0 < lam)
    {T₁ T₂ : ℕ} (hT : T₁ ≤ T₂) :
    infoGainBound d T₁ lam ≤ infoGainBound d T₂ lam := by
  unfold infoGainBound
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.log_le_log
  · have : 0 ≤ ↑T₁ / (↑d * lam) := by positivity
    linarith
  · have h1 : (↑T₁ : ℝ) ≤ ↑T₂ := Nat.cast_le.mpr hT
    have h2 : 0 < ↑d * lam := by positivity
    have : ↑T₁ / (↑d * lam) ≤ ↑T₂ / (↑d * lam) :=
      div_le_div_of_nonneg_right h1 h2.le
    linarith

/-- **Info gain is bounded by T/(2lam)** via log(1+x) ≤ x.

    Simple upper bound: γ_T ≤ T/(2lam).
    The logarithmic bound `infoGainBound` is much tighter. -/
theorem infoGainBound_le_linear (d T : ℕ) (lam : ℝ)
    (hd : 0 < d) (hlam : 0 < lam) :
    infoGainBound d T lam ≤ ↑T / (2 * lam) := by
  unfold infoGainBound
  set x := ↑T / (↑d * lam) with hx_def
  have hx : 0 ≤ x := by positivity
  have h_log_le_x : Real.log (1 + x) ≤ x := by
    have h1 : 0 < 1 + x := by linarith
    have h2 : 1 + x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
    calc Real.log (1 + x) ≤ Real.log (Real.exp x) :=
          Real.log_le_log h1 h2
      _ = x := Real.log_exp x
  have hd_pos : (0 : ℝ) < ↑d := Nat.cast_pos.mpr hd
  have hd_ne : (↑d : ℝ) ≠ 0 := ne_of_gt hd_pos
  calc ↑d / 2 * Real.log (1 + x)
      ≤ ↑d / 2 * x := by
        exact mul_le_mul_of_nonneg_left h_log_le_x (by positivity)
    _ = ↑T / (2 * lam) := by
        rw [hx_def]
        field_simp

/-! ### Conditional: From Eigenvalue AM-GM to Info Gain -/

/-- [CONDITIONAL] **Information gain from eigenvalue bound**.

    The AM-GM inequality on eigenvalues gives:
      ∏(1 + lamᵢ/lam) ≤ (1 + T/(dlam))^d
    Taking logs: ½ log det(I + lam⁻¹K_T) ≤ (d/2)·log(1 + T/(dlam)).

    The eigendecomposition and AM-GM are taken as hypotheses.
    Ref: Srinivas et al. (2010), Lemma 5.4. -/
theorem info_gain_from_eigenvalues (d T : ℕ) (lam : ℝ)
    (logdet : ℝ)
    (h_logdet_le : logdet ≤ ↑d * Real.log (1 + ↑T / (↑d * lam))) :
    logdet / 2 ≤ infoGainBound d T lam := by
  unfold infoGainBound
  linarith

end
