/-
# Online Mirror Descent and Telescope Bounds

Proves the telescope regret bound — the algebraic backbone of online
mirror descent, FTRL, EXP3, and natural policy gradient.

Given a potential sequence {D_t} and per-step decomposition
  regret_t ≤ (D_t - D_{t+1}) + penalty_t
with D_T ≥ 0, telescoping yields:
  ∑ regret_t ≤ D_0 + ∑ penalty_t

## Main Results

* `sum_telescope` — ∑_{t<T} (D_t - D_{t+1}) = D_0 - D_T
* `telescope_regret_bound` — per-step potential drop + penalty → total bound
* `omd_scaled_regret` — [CONDITIONAL] η·Regret_T ≤ D₀ + Tη²G²/2
* `omd_regret_div` — Regret_T ≤ D₀/η + ηTG²/2
* `telescope_constant_penalty` — specialization to constant penalty

## References

* [Shalev-Shwartz, "Online Learning and Online Convex Optimization", 2012]
* [Bubeck, "Convex Optimization: Algorithms and Complexity", 2015]
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Finset BigOperators

noncomputable section

/-! ### Telescope Identity -/

/-- **Telescoping sum identity**: ∑_{t=0}^{T-1} (D_t - D_{t+1}) = D_0 - D_T.
    Ref: Shalev-Shwartz (2012), Lemma 2.1. -/
lemma sum_telescope (T : ℕ) (D : ℕ → ℝ) :
    ∑ t ∈ range T, (D t - D (t + 1)) = D 0 - D T := by
  induction T with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; linarith

/-! ### Telescope Regret Bound -/

/-- **Telescope regret bound**: the algebraic backbone of online learning.

    Given a potential sequence {D_t}_{t=0}^T and per-step decomposition
      regret_t ≤ (D_t - D_{t+1}) + penalty_t
    with D_T ≥ 0, telescoping and dropping D_T yields:
      ∑ regret_t ≤ D_0 + ∑ penalty_t

    Instantiations: OMD (D = Bregman), FTRL, EXP3 (D = KL), NPG.
    Ref: Shalev-Shwartz (2012), Theorem 2.1. -/
theorem telescope_regret_bound (T : ℕ)
    (regret penalty : ℕ → ℝ) (D : ℕ → ℝ)
    (h_step : ∀ t, t < T → regret t ≤ D t - D (t + 1) + penalty t)
    (h_D_final : 0 ≤ D T) :
    ∑ t ∈ range T, regret t ≤ D 0 + ∑ t ∈ range T, penalty t := by
  calc ∑ t ∈ range T, regret t
      ≤ ∑ t ∈ range T, (D t - D (t + 1) + penalty t) :=
        sum_le_sum fun t ht => h_step t (mem_range.mp ht)
    _ = ∑ t ∈ range T, (D t - D (t + 1)) + ∑ t ∈ range T, penalty t :=
        sum_add_distrib
    _ = D 0 - D T + ∑ t ∈ range T, penalty t := by rw [sum_telescope]
    _ ≤ D 0 + ∑ t ∈ range T, penalty t := by linarith

/-! ### Online Mirror Descent -/

/-- [CONDITIONAL] **OMD scaled regret bound**.

    Per-step Bregman decomposition (from strong convexity of potential):
      η · (ℓ_t(x_t) - ℓ_t(u)) ≤ D_φ(u,x_t) - D_φ(u,x_{t+1}) + η²G²/2

    Telescoping: η · Regret_T ≤ D₀ + T·η²G²/2.
    Ref: Bubeck (2015), Theorem 4.2. -/
theorem omd_scaled_regret (T : ℕ)
    (η G_sq : ℝ) (hη : 0 < η) (hG_sq : 0 ≤ G_sq)
    (per_step_regret : ℕ → ℝ)
    (D : ℕ → ℝ)
    (h_D_final : 0 ≤ D T)
    (h_bregman_step : ∀ t, t < T →
      η * per_step_regret t ≤ D t - D (t + 1) + η ^ 2 * G_sq / 2) :
    η * ∑ t ∈ range T, per_step_regret t ≤
      D 0 + ↑T * (η ^ 2 * G_sq / 2) := by
  have h_tel := telescope_regret_bound T
    (fun t => η * per_step_regret t)
    (fun _ => η ^ 2 * G_sq / 2) D
    h_bregman_step h_D_final
  have h_lhs : ∑ t ∈ range T, η * per_step_regret t =
      η * ∑ t ∈ range T, per_step_regret t :=
    (Finset.mul_sum (range T) (fun t => per_step_regret t) η).symm
  have h_rhs : ∑ _ ∈ range T, (η ^ 2 * G_sq / 2) =
      ↑T * (η ^ 2 * G_sq / 2) := by
    rw [sum_const, card_range, nsmul_eq_mul]
  linarith

/-- **OMD regret bound** (divided form).

    From η · Regret_T ≤ D₀ + T·η²G²/2, dividing by η > 0:
      Regret_T ≤ D₀/η + η·T·G²/2

    With optimal η* = √(2D₀/(TG²)): Regret_T ≤ √(2D₀·T·G²).
    Ref: Bubeck (2015), Corollary 4.3. -/
theorem omd_regret_div (T : ℕ)
    (η G_sq D₀ : ℝ) (hη : 0 < η)
    (total_regret : ℝ)
    (h_scaled : η * total_regret ≤ D₀ + ↑T * (η ^ 2 * G_sq / 2)) :
    total_regret ≤ D₀ / η + η * ↑T * G_sq / 2 := by
  have hη_ne : η ≠ 0 := ne_of_gt hη
  have h1 : total_regret ≤ (D₀ + ↑T * (η ^ 2 * G_sq / 2)) / η := by
    rw [le_div_iff₀ hη]
    linarith [mul_comm total_regret η]
  have h2 : (D₀ + ↑T * (η ^ 2 * G_sq / 2)) / η =
      D₀ / η + ↑T * (η ^ 2 * G_sq / 2) / η := add_div D₀ _ η
  have h3 : ↑T * (η ^ 2 * G_sq / 2) / η = η * ↑T * G_sq / 2 := by
    field_simp
  linarith

/-- **Constant penalty telescope**: when all penalties are equal. -/
theorem telescope_constant_penalty (T : ℕ)
    (regret : ℕ → ℝ) (D : ℕ → ℝ) (c : ℝ)
    (h_step : ∀ t, t < T → regret t ≤ D t - D (t + 1) + c)
    (h_D_final : 0 ≤ D T) :
    ∑ t ∈ range T, regret t ≤ D 0 + ↑T * c := by
  calc ∑ t ∈ range T, regret t
      ≤ ∑ t ∈ range T, (D t - D (t + 1) + c) :=
        sum_le_sum fun t ht => h_step t (mem_range.mp ht)
    _ = ∑ t ∈ range T, (D t - D (t + 1)) + ∑ _ ∈ range T, c :=
        sum_add_distrib
    _ = D 0 - D T + ↑T * c := by
        rw [sum_telescope, sum_const, card_range, nsmul_eq_mul]
    _ ≤ D 0 + ↑T * c := by linarith

end
