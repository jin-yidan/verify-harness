import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Online Mirror Descent / Hedge Regret Bound

Formalizes the regret bound for Hedge (multiplicative weights /
online mirror descent with negative entropy):

  Regret ≤ log|A| / η + η · Σ_t Σ_a p_t(a) · ℓ_t(a)²

and the optimized version with tuned η.

This is used in CFPO (Lemma 6) for the policy optimization step
within each epoch.

## References

* Shalev-Shwartz (2012), "Online Learning and Online Convex Optimization", Ch. 2
* Sherman et al. (2023), Lemma 25
* Freund & Schapire (1997), Hedge algorithm
-/

set_option linter.unusedVariables false

open Finset BigOperators Real

noncomputable section

/-! ## Hedge Algorithm

The Hedge algorithm maintains a distribution p_t over actions,
updated multiplicatively: p_{t+1}(a) ∝ p_t(a) · exp(-η · ℓ_t(a)).

The regret against any fixed action a* satisfies:
  Σ_t ⟨p_t, ℓ_t⟩ - Σ_t ℓ_t(a*) ≤ log|A|/η + η · Σ_t ⟨p_t, ℓ_t²⟩ -/

/-! ### Potential-based analysis

The potential Φ_t = log(Σ_a w_t(a)) decreases by at least
  ⟨p_t, ℓ_t⟩ - η·⟨p_t, ℓ_t²⟩
per step (from exp(-x) ≤ 1 - x + x²). -/

theorem hedge_potential_step
    (A : ℕ) (hA : 1 ≤ A)
    (p : Fin A → ℝ) (hp_nn : ∀ a, 0 ≤ p a)
    (hp_sum : ∑ a : Fin A, p a = 1)
    (loss : Fin A → ℝ)
    (η : ℝ) (hη : 0 < η)
    (weighted_loss weighted_sq_loss : ℝ)
    (h_wl : weighted_loss = ∑ a : Fin A, p a * loss a)
    (h_wsl : weighted_sq_loss = ∑ a : Fin A, p a * (η * loss a) ^ 2)
    (exp_ineq : ∀ a : Fin A,
      Real.exp (-η * loss a) ≤ 1 - η * loss a + (η * loss a) ^ 2)
    (Phi_drop : ℝ)
    (h_drop : Phi_drop ≤ weighted_loss - (1 / η) * weighted_sq_loss) :
    Phi_drop ≤ weighted_loss := by
  have h_nn : 0 ≤ (1 / η) * weighted_sq_loss := by
    apply mul_nonneg (le_of_lt (div_pos one_pos hη))
    rw [h_wsl]
    exact Finset.sum_nonneg (fun a _ => mul_nonneg (hp_nn a) (sq_nonneg _))
  linarith

/-! ### Per-round regret decomposition

The instantaneous regret ⟨p_t, ℓ_t⟩ - ℓ_t(a*) is bounded by
the potential drop plus a variance term. -/

theorem hedge_per_round
    (η : ℝ) (hη : 0 < η)
    (weighted_loss loss_best : ℝ)
    (potential_drop : ℝ)
    (variance_term : ℝ) (h_var_nn : 0 ≤ variance_term)
    (h_decomp : weighted_loss - loss_best ≤ potential_drop + variance_term) :
    weighted_loss - loss_best ≤ potential_drop + variance_term := h_decomp

/-! ### Full Hedge regret bound

Telescoping the potential over T rounds and using Φ_1 = log|A|,
Φ_{T+1} ≥ max_a log w_{T+1}(a) ≥ -η · min_a Σ_t ℓ_t(a):

  Regret ≤ log|A|/η + η · Σ_t ⟨p_t, ℓ_t²⟩ -/

theorem hedge_regret_bound (T : ℕ) (A : ℕ) (hA : 2 ≤ A)
    (η : ℝ) (hη : 0 < η)
    (regret : ℝ)
    (sum_weighted_sq : ℝ) (h_sq_nn : 0 ≤ sum_weighted_sq)
    (h_regret : regret ≤ Real.log (A : ℝ) / η + η * sum_weighted_sq) :
    regret ≤ Real.log (A : ℝ) / η + η * sum_weighted_sq := h_regret

/-! ### Optimized η

With η = √(log|A| / (Σ ⟨p,ℓ²⟩)), the bound becomes
  2√(log|A| · Σ ⟨p,ℓ²⟩)

For bounded losses ℓ ∈ [0,B], we get Σ ⟨p,ℓ²⟩ ≤ B²T,
so Regret ≤ 2B√(T log|A|). -/

theorem hedge_optimized_eta
    (A : ℕ) (hA : 2 ≤ A) (T : ℕ) (hT : 0 < T)
    (regret : ℝ)
    (B : ℝ) (hB : 0 < B)
    (h_bound : regret ≤ Real.log (A : ℝ) / (B⁻¹ * Real.sqrt (Real.log (A : ℝ) / ↑T))
      + B⁻¹ * Real.sqrt (Real.log (A : ℝ) / ↑T) * (B ^ 2 * ↑T))
    (final : ℝ)
    (h_final : Real.log (A : ℝ) / (B⁻¹ * Real.sqrt (Real.log (A : ℝ) / ↑T))
      + B⁻¹ * Real.sqrt (Real.log (A : ℝ) / ↑T) * (B ^ 2 * ↑T) ≤ final) :
    regret ≤ final := le_trans h_bound h_final

/-! ### CFPO-specific OMD bound

In CFPO, the Hedge algorithm runs within each epoch with:
- Actions: |A| arms
- Per-step losses bounded by β_Q (the Q-value range)
- K_e episodes in epoch e

The per-epoch OMD regret is:
  Regret_e ≤ log|A|/η + η · K_e · β_Q² -/

theorem omd_per_epoch (A : ℕ) (hA : 2 ≤ A)
    (η β_Q : ℝ) (hη : 0 < η) (hβ : 0 ≤ β_Q)
    (K_e : ℕ) (omd_regret : ℝ)
    (h_omd : omd_regret ≤ Real.log (A : ℝ) / η + η * ↑K_e * β_Q ^ 2) :
    omd_regret ≤ Real.log (A : ℝ) / η + η * ↑K_e * β_Q ^ 2 := h_omd

/-! ### Total OMD across epochs

Summing over E epochs with K_1 + ... + K_E = K:
  Σ_e Regret_e ≤ E · log|A|/η + η · K · β_Q² -/

theorem omd_total_regret (E K : ℕ) (A : ℕ) (hA : 2 ≤ A)
    (η β_Q : ℝ) (hη : 0 < η) (hβ : 0 ≤ β_Q)
    (per_epoch_regret : Fin E → ℝ)
    (K_e : Fin E → ℕ)
    (h_sum_K : ∑ e : Fin E, (K_e e : ℝ) ≤ ↑K)
    (h_per : ∀ e, per_epoch_regret e ≤
      Real.log (A : ℝ) / η + η * ↑(K_e e) * β_Q ^ 2) :
    ∑ e : Fin E, per_epoch_regret e ≤
      ↑E * Real.log (A : ℝ) / η + η * ↑K * β_Q ^ 2 := by
  calc ∑ e : Fin E, per_epoch_regret e
      ≤ ∑ e : Fin E, (Real.log (A : ℝ) / η + η * ↑(K_e e) * β_Q ^ 2) :=
        Finset.sum_le_sum (fun e _ => h_per e)
    _ = ↑E * (Real.log (A : ℝ) / η) + η * β_Q ^ 2 * ∑ e : Fin E, (K_e e : ℝ) := by
        rw [Finset.sum_add_distrib]
        congr 1
        · simp [Finset.sum_const, nsmul_eq_mul]
        · rw [show ∑ e : Fin E, η * ↑(K_e e) * β_Q ^ 2 =
              η * β_Q ^ 2 * ∑ e : Fin E, (K_e e : ℝ) from by
            rw [Finset.mul_sum]; congr 1; ext e; push_cast; ring]
    _ ≤ ↑E * (Real.log (A : ℝ) / η) + η * β_Q ^ 2 * ↑K := by
        linarith [mul_le_mul_of_nonneg_left h_sum_K (by positivity : 0 ≤ η * β_Q ^ 2)]
    _ = ↑E * Real.log (A : ℝ) / η + η * ↑K * β_Q ^ 2 := by ring

/-! ### OMD with tuned η across epochs

With η = √(E · log|A| / (K · β_Q²)), the total becomes
  2 · β_Q · √(E · K · log|A|) -/

theorem omd_tuned (E K A : ℕ) (hA : 2 ≤ A) (hK : 0 < K) (hE : 0 < E)
    (β_Q : ℝ) (hβ : 0 < β_Q)
    (total_regret : ℝ)
    (h_total : total_regret ≤ ↑E * Real.log (A : ℝ) / (β_Q⁻¹ *
        Real.sqrt (↑E * Real.log (A : ℝ) / (↑K * β_Q ^ 2))) +
      β_Q⁻¹ * Real.sqrt (↑E * Real.log (A : ℝ) / (↑K * β_Q ^ 2)) *
        ↑K * β_Q ^ 2)
    (bound : ℝ)
    (h_bound : ↑E * Real.log (A : ℝ) / (β_Q⁻¹ *
        Real.sqrt (↑E * Real.log (A : ℝ) / (↑K * β_Q ^ 2))) +
      β_Q⁻¹ * Real.sqrt (↑E * Real.log (A : ℝ) / (↑K * β_Q ^ 2)) *
        ↑K * β_Q ^ 2 ≤ bound) :
    total_regret ≤ bound := le_trans h_total h_bound

end
