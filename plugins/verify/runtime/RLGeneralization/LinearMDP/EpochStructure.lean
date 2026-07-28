/-
# Epoch Framework

Epoch partition structure from Gram matrix doubling, and composition of
per-epoch OMD regrets into total regret.

## Main Results

* `EpochPartition` — structure: epoch lengths partition K episodes
* `total_epoch_omd_regret` — ∑ per-epoch OMD regret ≤ E·(D₀/η) + η·K·G²/2
* `epoch_count_to_omd` — compose epoch count bound with total OMD regret
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

set_option linter.unusedVariables false

open Finset BigOperators

noncomputable section

structure EpochPartition (K : ℕ) where
  E : ℕ
  epoch_len : Fin E → ℕ
  h_pos : ∀ e, 0 < epoch_len e
  h_sum_len : ∑ e : Fin E, epoch_len e = K

theorem total_epoch_omd_regret
    (K E : ℕ) (η D₀ G_sq : ℝ) (hη : 0 < η) (hD : 0 ≤ D₀) (hG : 0 ≤ G_sq)
    (epoch_len : Fin E → ℕ) (h_sum : ∑ e : Fin E, (epoch_len e : ℝ) = (K : ℝ))
    (per_epoch_regret : Fin E → ℝ)
    (h_per_epoch : ∀ e, per_epoch_regret e ≤
      D₀ / η + η * ↑(epoch_len e) * G_sq / 2) :
    ∑ e : Fin E, per_epoch_regret e ≤
      ↑E * (D₀ / η) + η * ↑K * G_sq / 2 := by
  have h1 : ∑ e : Fin E, per_epoch_regret e
      ≤ ∑ e : Fin E, (D₀ / η + η * ↑(epoch_len e) * G_sq / 2) :=
    Finset.sum_le_sum fun e _ => h_per_epoch e
  have h2 : ∑ e : Fin E, (D₀ / η + η * ↑(epoch_len e) * G_sq / 2)
      = ∑ e : Fin E, (D₀ / η) + ∑ e : Fin E, (η * ↑(epoch_len e) * G_sq / 2) :=
    Finset.sum_add_distrib
  have h3 : ∑ e : Fin E, (D₀ / η) = ↑E * (D₀ / η) := by
    rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  have h4 : ∑ e : Fin E, (η * ↑(epoch_len e) * G_sq / 2)
      = η * ↑K * G_sq / 2 := by
    have : ∑ e : Fin E, (η * ↑(epoch_len e) * G_sq / 2)
        = η * G_sq / 2 * ∑ e : Fin E, (epoch_len e : ℝ) := by
      rw [Finset.mul_sum]; congr 1; ext e; ring
    rw [this, h_sum]; ring
  linarith

theorem epoch_count_to_omd (K : ℕ) (E_bound : ℕ)
    (η D₀ G_sq : ℝ) (hη : 0 < η) (hD : 0 ≤ D₀) (hG : 0 ≤ G_sq)
    (ep : EpochPartition K)
    (hE : ep.E ≤ E_bound)
    (per_epoch_regret : Fin ep.E → ℝ)
    (h_per_epoch : ∀ e, per_epoch_regret e ≤
      D₀ / η + η * ↑(ep.epoch_len e) * G_sq / 2) :
    ∑ e : Fin ep.E, per_epoch_regret e ≤
      ↑E_bound * (D₀ / η) + η * ↑K * G_sq / 2 := by
  have h_sum : ∑ e : Fin ep.E, (ep.epoch_len e : ℝ) = (K : ℝ) := by
    have := ep.h_sum_len
    rw [← Nat.cast_sum]
    exact_mod_cast this
  have h1 := total_epoch_omd_regret K ep.E η D₀ G_sq hη hD hG ep.epoch_len h_sum
    per_epoch_regret h_per_epoch
  have h2 : (ep.E : ℝ) ≤ (E_bound : ℝ) := Nat.cast_le.mpr hE
  have h3 : 0 ≤ D₀ / η := div_nonneg hD (le_of_lt hη)
  nlinarith

end
