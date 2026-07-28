/-
# Log-Determinant Ratio Bound

Bounds log(det(Λ_T)/λ^d) ≤ d·log(1 + T/(λd)) from the determinant
upper bound. Used to compute confidence ellipsoid radii for self-normalized
martingale bounds.

## Main Results

* `log_det_ratio_from_det_bound` — log of det ratio bounded by d·log(1+T/λd)
* `confidence_radius_sq` — confidence radius from log-det bound
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

set_option linter.unusedVariables false

open Real BigOperators

noncomputable section

theorem log_det_ratio_from_det_bound
    (d : ℕ) (hd : 0 < d) (T : ℕ) (lam : ℝ) (hlam : 0 < lam)
    (det_ratio : ℝ) (hdr : 0 < det_ratio)
    (h_bound : det_ratio ≤ ((lam * ↑d + ↑T) / (lam * ↑d)) ^ d) :
    Real.log det_ratio ≤ ↑d * Real.log (1 + ↑T / (lam * ↑d)) := by
  have hld : 0 < lam * ↑d := by positivity
  have h1 : (1 : ℝ) + ↑T / (lam * ↑d) = (lam * ↑d + ↑T) / (lam * ↑d) := by
    field_simp
  rw [h1]
  calc Real.log det_ratio
      ≤ Real.log (((lam * ↑d + ↑T) / (lam * ↑d)) ^ d) :=
        Real.log_le_log hdr h_bound
    _ = ↑d * Real.log ((lam * ↑d + ↑T) / (lam * ↑d)) := by
        rw [Real.log_pow]

theorem confidence_radius_sq
    (d : ℕ) (hd : 0 < d) (T : ℕ) (lam sigma delta : ℝ)
    (hlam : 0 < lam) (hsigma : 0 < sigma) (hdelta : 0 < delta)
    (det_ratio : ℝ) (hdr : 0 < det_ratio)
    (h_bound : det_ratio ≤ ((lam * ↑d + ↑T) / (lam * ↑d)) ^ d) :
    sigma ^ 2 * (Real.log det_ratio - 2 * Real.log delta) + lam ≤
    sigma ^ 2 * (↑d * Real.log (1 + ↑T / (lam * ↑d)) - 2 * Real.log delta) + lam := by
  have h_log := log_det_ratio_from_det_bound d hd T lam hlam det_ratio hdr h_bound
  nlinarith [sq_nonneg sigma]

end
