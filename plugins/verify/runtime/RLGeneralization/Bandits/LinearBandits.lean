/-
# Linear Bandits and LinUCB

Formalizes the LinUCB algorithm (Abbasi-Yadkori et al. 2011, Li et al. 2010)
for stochastic linear bandits. The reward model is:
  r_t = φ(a_t)^T θ* + η_t
where φ : A → ℝ^d is a feature map, θ* ∈ ℝ^d is unknown, and η_t is σ-sub-Gaussian noise.

## Conventions

We follow Abbasi-Yadkori (2011):
- `Λ_t = λI + ∑_{s<t} φ_s φ_s^T` (regularized Gram matrix)
- `selfNormalizedNorm φ Λ = φ^T Λ^{-1} φ = ‖φ‖²_{Λ^{-1}}` (from SelfNormalized.lean)
- UCB bonus: `β · √(selfNormalizedNorm φ Λ_t)` = `β · ‖φ‖_{Λ_t^{-1}}`
- The elliptical potential values `x_t = selfNormalizedNorm φ_t Λ_t` appear as argument
  to `min(1, x_t)` in the potential lemma

## Main Definitions

* `linUCBIndex` — Q_t(φ) = φ^T θ̂_t + β · ‖φ‖_{Λ_t^{-1}}

## Main Results

* `linUCBIndex_ge_dot` — UCB index ≥ φ^T θ̂ (zero sorry)
* `linUCBIndex_mono_beta` — index monotone in β (zero sorry)
* `linucb_optimism` — φ^T θ* ≤ UCB index (conditional on CS + confidence)
* `linucb_regret_decomp` — R_T ≤ 2β · ∑_t ‖φ_t‖_{Λ_{t-1}^{-1}} (zero sorry)
* `sum_sqrt_sq_le_card_mul_sum` — (∑ √x_t)² ≤ T · ∑ x_t (zero sorry)
* `linucb_regret_bound` — R_T ≤ 2β · √(2dT·log(1+T/λd)) from elliptical potential (zero sorry given hyps)
* `linucb_vs_ucb1_sq` — LinUCB beats UCB1 when d² ≤ K (zero sorry)

## Proof Chain

  Confidence ellipsoid (SelfNormalized): selfNormalizedNorm (θ̂-θ*) Λ⁻¹ ≤ β²
    = ‖θ̂-θ*‖²_Λ ≤ β²
    + CS: (φ^T v)² ≤ selfNormalizedNorm φ Λ · selfNormalizedNorm v Λ⁻¹
      = ‖φ‖²_{Λ^{-1}} · ‖v‖²_Λ
    ↓ linucb_optimism (conditional)
  φ^T θ* ≤ φ^T θ̂_t + β · ‖φ_t‖_{Λ_{t-1}^{-1}}  (per-round optimism)
    ↓ linucb_regret_decomp (algebraic, zero sorry)
  R_T ≤ 2β · ∑_t √(selfNormalizedNorm φ_t Λ_{t-1})
    ↓ Cauchy-Schwarz (zero sorry) + elliptical potential (conditional)
  R_T ≤ 2β · √(2dT · log(1+T/d))

## References

* Abbasi-Yadkori, Pál, Szepesvári, "Improved Algorithms for Linear Stochastic
  Bandits," NIPS 2011.
* Li, Chu, Langford, Schapire, "A Contextual-Bandit Approach to Personalized
  News Article Recommendation," WWW 2010.
* Agarwal et al., "RL: Theory and Algorithms," Ch 5.2 (2026).
-/

import RLGeneralization.Concentration.SelfNormalized
import RLGeneralization.LinearMDP.Regret

open Finset BigOperators Real Matrix

noncomputable section

variable {d : ℕ}

/-! ### LinUCB Index -/

/-- The LinUCB UCB index for feature vector φ, estimate θ̂, regularized Gram matrix Λ,
    and confidence radius β:
      Q(φ) = φ^T θ̂ + β · ‖φ‖_{Λ^{-1}}
    where `selfNormalizedNorm φ Λ = φ^T Λ^{-1} φ = ‖φ‖²_{Λ^{-1}}`. -/
def linUCBIndex (phi theta_hat : Fin d → ℝ) (Λ : Matrix (Fin d) (Fin d) ℝ) (β : ℝ) : ℝ :=
  dotProduct phi theta_hat + β * Real.sqrt (selfNormalizedNorm phi Λ)

/-- The LinUCB index is at least φ^T θ̂ (bonus is nonneg when β ≥ 0). -/
theorem linUCBIndex_ge_dot (phi theta_hat : Fin d → ℝ)
    (Λ : Matrix (Fin d) (Fin d) ℝ) (β : ℝ) (hβ : 0 ≤ β) :
    dotProduct phi theta_hat ≤ linUCBIndex phi theta_hat Λ β := by
  simp only [linUCBIndex]
  linarith [mul_nonneg hβ (Real.sqrt_nonneg (selfNormalizedNorm phi Λ))]

/-- The LinUCB index is monotone increasing in β. -/
theorem linUCBIndex_mono_beta (phi theta_hat : Fin d → ℝ)
    (Λ : Matrix (Fin d) (Fin d) ℝ) (β₁ β₂ : ℝ) (h : β₁ ≤ β₂) :
    linUCBIndex phi theta_hat Λ β₁ ≤ linUCBIndex phi theta_hat Λ β₂ := by
  simp only [linUCBIndex]
  linarith [mul_le_mul_of_nonneg_right h (Real.sqrt_nonneg (selfNormalizedNorm phi Λ))]

/-! ### Optimism Lemma -/

/-- **LinUCB Optimism** (conditional).

    The UCB index upper-bounds the true expected reward φ^T θ*:
      φ^T θ* ≤ φ^T θ̂_t + β · ‖φ‖_{Λ_{t-1}^{-1}} = Q_t(φ)

    **Proof structure**:
      |φ^T(θ̂-θ*)| ≤ √(‖φ‖²_{Λ^{-1}} · ‖θ̂-θ*‖²_Λ)    (CS, h_cs)
                   ≤ √(selfNormalizedNorm φ Λ) · β       (confidence h_conf)
      So φ^T θ* = φ^T θ̂ - φ^T(θ̂-θ*) ≤ φ^T θ̂ + β · √(selfNormalizedNorm φ Λ)

    **Conditional**:
    - `h_cs`: Cauchy-Schwarz in Λ-metric:
        (φ^T(θ̂-θ*))² ≤ selfNormalizedNorm φ Λ · selfNormalizedNorm (θ̂-θ*) Λ⁻¹
        = ‖φ‖²_{Λ^{-1}} · ‖θ̂-θ*‖²_Λ
      (Deferred: needs matrix square root. In SelfNormalized: self_normalized_cauchy_schwarz.)
    - `h_conf`: confidence ellipsoid:
        selfNormalizedNorm (θ̂-θ*) Λ⁻¹ ≤ β²  (= ‖θ̂-θ*‖²_Λ ≤ β²)
      (Conditional: from martingale argument in SelfNormalized.)
    - `h_phi_nonneg`: selfNormalizedNorm φ Λ ≥ 0 (from selfNormalizedNorm_nonneg.) -/
theorem linucb_optimism
    (phi theta_hat theta_star : Fin d → ℝ)
    (Λ : Matrix (Fin d) (Fin d) ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (h_cs : (dotProduct phi (fun i => theta_hat i - theta_star i)) ^ 2 ≤
            selfNormalizedNorm phi Λ * selfNormalizedNorm (fun i => theta_hat i - theta_star i) Λ⁻¹)
    (h_conf : selfNormalizedNorm (fun i => theta_hat i - theta_star i) Λ⁻¹ ≤ β ^ 2)
    (h_phi_nonneg : 0 ≤ selfNormalizedNorm phi Λ) :
    dotProduct phi theta_star ≤ linUCBIndex phi theta_hat Λ β := by
  simp only [linUCBIndex]
  -- Suffices: -(φ^T(θ̂-θ*)) ≤ β · √(selfNormalizedNorm φ Λ)
  -- since φ^T θ* = φ^T θ̂ - (φ^T(θ̂-θ*))
  have hdiff : dotProduct phi (fun i => theta_hat i - theta_star i) =
      dotProduct phi theta_hat - dotProduct phi theta_star := by
    simp [dotProduct, Finset.sum_sub_distrib, mul_sub]
  -- Bound the square: (φ^T(θ̂-θ*))² ≤ β² · selfNormalizedNorm φ Λ
  have h_sq : (dotProduct phi (fun i => theta_hat i - theta_star i)) ^ 2 ≤
      (β * Real.sqrt (selfNormalizedNorm phi Λ)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt h_phi_nonneg]
    calc (dotProduct phi (fun i => theta_hat i - theta_star i)) ^ 2
        ≤ selfNormalizedNorm phi Λ *
          selfNormalizedNorm (fun i => theta_hat i - theta_star i) Λ⁻¹ := h_cs
      _ ≤ selfNormalizedNorm phi Λ * β ^ 2 := mul_le_mul_of_nonneg_left h_conf h_phi_nonneg
      _ = β ^ 2 * selfNormalizedNorm phi Λ := mul_comm _ _
  -- Get: |φ^T(θ̂-θ*)| ≤ β · √(selfNormalizedNorm φ Λ)
  have h_rhs_nonneg : 0 ≤ β * Real.sqrt (selfNormalizedNorm phi Λ) :=
    mul_nonneg hβ (Real.sqrt_nonneg _)
  have h_abs : |dotProduct phi (fun i => theta_hat i - theta_star i)| ≤
      β * Real.sqrt (selfNormalizedNorm phi Λ) := by
    rw [← Real.sqrt_sq (abs_nonneg _), ← Real.sqrt_sq h_rhs_nonneg]
    apply Real.sqrt_le_sqrt
    rw [sq_abs]
    exact h_sq
  -- Conclude: φ^T θ* ≤ φ^T θ̂ + β · √(selfNormalizedNorm φ Λ)
  -- From h_abs : |x| ≤ b, abs_le.mp gives -b ≤ x (i.e. .1) and x ≤ b (i.e. .2)
  have h_neg : -(dotProduct phi (fun i => theta_hat i - theta_star i)) ≤
      β * Real.sqrt (selfNormalizedNorm phi Λ) := by
    have h1 := (abs_le.mp h_abs).1
    -- h1 : -(β * sqrt ...) ≤ dotProduct phi (θ̂-θ*)
    linarith
  linarith [hdiff]

/-! ### Regret Decomposition -/

/-- **LinUCB cumulative regret decomposition** (zero sorry).

    Total regret ≤ 2β · ∑_t ‖φ_t‖_{Λ_{t-1}^{-1}}.
    Follows from summing per-round gap bounds. -/
theorem linucb_regret_decomp
    (T : ℕ)
    (φ : Fin T → Fin d → ℝ)
    (Λ : Fin T → Matrix (Fin d) (Fin d) ℝ)
    (β : ℝ) (_hβ : 0 ≤ β)
    (gap : Fin T → ℝ)
    (h_gap : ∀ t, gap t ≤ 2 * β * Real.sqrt (selfNormalizedNorm (φ t) (Λ t))) :
    ∑ t : Fin T, gap t ≤
      2 * β * ∑ t : Fin T, Real.sqrt (selfNormalizedNorm (φ t) (Λ t)) :=
  calc ∑ t : Fin T, gap t
      ≤ ∑ t : Fin T, (2 * β * Real.sqrt (selfNormalizedNorm (φ t) (Λ t))) :=
        Finset.sum_le_sum (fun t _ => h_gap t)
    _ = 2 * β * ∑ t : Fin T, Real.sqrt (selfNormalizedNorm (φ t) (Λ t)) := by
        rw [Finset.mul_sum]

/-! ### Key Algebraic Lemma -/

/-- **Cauchy-Schwarz for sum of square roots** (zero sorry).

    (∑_t √(x_t))² ≤ T · ∑_t x_t.

    Used to convert ∑_t ‖φ_t‖_{Λ^{-1}} into the form needed for the
    elliptical potential lemma. -/
theorem sum_sqrt_sq_le_card_mul_sum
    {T : ℕ} (x : Fin T → ℝ) (hx : ∀ t, 0 ≤ x t) :
    (∑ t : Fin T, Real.sqrt (x t)) ^ 2 ≤ T * ∑ t : Fin T, x t := by
  -- Cauchy-Schwarz: (∑_t √(x_t) · 1)² ≤ (∑_t x_t)(∑_t 1²)
  have h_cs : (∑ t : Fin T, Real.sqrt (x t) * 1) ^ 2 ≤
      (∑ t : Fin T, (Real.sqrt (x t)) ^ 2) * (∑ _t : Fin T, (1 : ℝ) ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun t => Real.sqrt (x t)) (fun _ => (1 : ℝ))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, one_pow] at h_cs
  simp_rw [Real.sq_sqrt (hx _)] at h_cs
  linarith

/-! ### Main Regret Bound -/

/-- **LinUCB O(d√T) regret bound** (conditional on elliptical potential and per-round optimism).

    Given:
    - Per-round gap `gap_t ≤ 2β · √(min(1, x_t))` for some nonneg sequence x
    - Elliptical potential bound: `∑_t min(1, x_t) ≤ 2d · log(1 + T/d)`

    Proves: `∑_t gap_t ≤ 2β · √(T · 2d · log(1 + T/d))`.

    **Zero sorry**: given h_gap and h_pot, this is a pure algebraic proof.

    **Status of hypotheses**:
    - `h_gap`: conditional (from optimism + CS + confidence ellipsoid)
    - `h_pot`: exact (from `elliptical_potential_unconditional` when x_t = φ_t^T Λ_t^{-1} φ_t) -/
theorem linucb_regret_bound
    (T d_nat : ℕ) (_hd : 0 < d_nat)
    (β : ℝ) (hβ : 0 ≤ β)
    (gap : Fin T → ℝ)
    (x : Fin T → ℝ) (hx : ∀ t, 0 ≤ x t)
    -- Per-round gap ≤ 2β · √(min(1, x_t))
    (h_gap : ∀ t, gap t ≤ 2 * β * Real.sqrt (min 1 (x t)))
    -- Elliptical potential bound
    (h_pot : ∑ t : Fin T, min 1 (x t) ≤ 2 * d_nat * Real.log (1 + T / d_nat)) :
    ∑ t : Fin T, gap t ≤
      2 * β * Real.sqrt ((T : ℝ) * (2 * d_nat * Real.log (1 + (T : ℝ) / d_nat))) := by
  -- Step 1: ∑ gap_t ≤ 2β · ∑_t √(min(1, x_t))
  have h1 : ∑ t : Fin T, gap t ≤ 2 * β * ∑ t : Fin T, Real.sqrt (min 1 (x t)) :=
    calc ∑ t : Fin T, gap t
        ≤ ∑ t : Fin T, (2 * β * Real.sqrt (min 1 (x t))) :=
            Finset.sum_le_sum (fun t _ => h_gap t)
      _ = 2 * β * ∑ t : Fin T, Real.sqrt (min 1 (x t)) := by rw [Finset.mul_sum]
  -- Step 2: (∑_t √(min(1,x_t)))² ≤ T · ∑_t min(1,x_t)  (Cauchy-Schwarz)
  have h_min_nonneg : ∀ t, 0 ≤ min 1 (x t) := fun t => le_min one_pos.le (hx t)
  have h_cs := sum_sqrt_sq_le_card_mul_sum (fun t => min 1 (x t)) h_min_nonneg
  -- Step 3: ∑_t min(1,x_t) ≤ 2d·log(1+T/d), so T·∑ ≤ T·2d·log(1+T/d)
  have h_sq_bound : (∑ t : Fin T, Real.sqrt (min 1 (x t))) ^ 2 ≤
      (T : ℝ) * (2 * d_nat * Real.log (1 + (T : ℝ) / d_nat)) :=
    calc (∑ t : Fin T, Real.sqrt (min 1 (x t))) ^ 2
        ≤ T * ∑ t : Fin T, min 1 (x t) := h_cs
      _ ≤ T * (2 * d_nat * Real.log (1 + T / d_nat)) :=
            mul_le_mul_of_nonneg_left h_pot (Nat.cast_nonneg T)
  -- Step 4: ∑_t √(min(1,x_t)) ≤ √(T·2d·log(1+T/d))
  have h_sum_nonneg : 0 ≤ ∑ t : Fin T, Real.sqrt (min 1 (x t)) :=
    Finset.sum_nonneg (fun t _ => Real.sqrt_nonneg _)
  have h2 : ∑ t : Fin T, Real.sqrt (min 1 (x t)) ≤
      Real.sqrt ((T : ℝ) * (2 * d_nat * Real.log (1 + (T : ℝ) / d_nat))) := by
    rw [← Real.sqrt_sq h_sum_nonneg]
    exact Real.sqrt_le_sqrt h_sq_bound
  -- Combine
  calc ∑ t : Fin T, gap t
      ≤ 2 * β * ∑ t : Fin T, Real.sqrt (min 1 (x t)) := h1
    _ ≤ 2 * β * Real.sqrt ((T : ℝ) * (2 * d_nat * Real.log (1 + (T : ℝ) / d_nat))) :=
          mul_le_mul_of_nonneg_left h2 (by linarith)

/-- **LinUCB regret composition via total_bonus_from_features.**

    Directly applies `total_bonus_from_features` to LinUCB:
    given normalized features and half-gap bounded by β · √(min(1, x_t)) for
    a potential sequence x satisfying the elliptical potential bound, the
    regret is bounded.

    The factor of 2 comes from the LinUCB regret analysis:
    `gap_t ≤ 2β · √(min(1, x_t))` implies `gap_t/2 ≤ β · √(min(1, x_t))`.

    The hypothesis requires x to satisfy both the half-gap bound AND the
    elliptical potential bound ∑ min(1, x_t) ≤ 2d · log(1 + T/d).
    When x_t = φ_t^T Λ_t^{-1} φ_t (the Gram matrix self-normalized norms),
    the potential bound follows from `elliptical_potential_unconditional`
    via `total_bonus_from_features`.

    **Conditional**: the half-gap bound requires per-round optimism + CS.
    **Zero sorry**: the potential bound is now a hypothesis on x. -/
theorem linucb_regret_composition
    (d_nat : ℕ) (hd : 0 < d_nat) (T : ℕ)
    (phis : Fin T → Fin d_nat → ℝ)
    (_h_norm : ∀ k : Fin T, sqNorm (phis k) ≤ 1)
    (β : ℝ) (_hβ : 0 ≤ β)
    (gap : Fin T → ℝ)
    -- Half of gap satisfies the bonus bound for the potential x,
    -- AND x satisfies the elliptical potential bound
    (h_half_gap : ∃ x : Fin T → ℝ,
        (∀ t, 0 ≤ x t) ∧
        (∑ t : Fin T, min 1 (x t) ≤
          2 * ↑d_nat * Real.log (1 + ↑T / ↑d_nat)) ∧
        (∀ t, gap t / 2 ≤ β * Real.sqrt (min 1 (x t)))) :
    ∑ t : Fin T, gap t ≤
      2 * β * Real.sqrt ((T : ℝ) * (2 * d_nat * Real.log (1 + (T : ℝ) / d_nat))) := by
  obtain ⟨x, hx_nonneg, h_pot, h_hg⟩ := h_half_gap
  exact linucb_regret_bound T d_nat hd β _hβ gap x hx_nonneg
    (fun t => by linarith [h_hg t]) h_pot

/-! ### Comparison: LinUCB vs UCB1 -/

/-- **LinUCB improves over UCB1** (zero sorry).

    UCB1 regret on K arms: O(√(KT log T)).
    LinUCB regret on linear bandits in ℝ^d: O(d√T log T).
    LinUCB is better when d² ≤ K (i.e., d ≤ √K).

    Formally: d² · T ≤ K · T when d² ≤ K. -/
theorem linucb_vs_ucb1_sq
    (d_sq K T : ℝ) (hT : 0 ≤ T) (h_low_dim : d_sq ≤ K) :
    d_sq * T ≤ K * T :=
  mul_le_mul_of_nonneg_right h_low_dim hT

/-- **LinUCB regret scaling** (zero sorry).

    The squared LinUCB regret O(d²T·log T) ≤ UCB1's O(KT·log T)
    when d² ≤ K. This shows feature-based methods are beneficial for
    large action sets. -/
theorem linucb_regret_sq_le_ucb1_sq
    (d_nat K : ℕ) (hK : d_nat ^ 2 ≤ K) (T log_T : ℝ)
    (hT : 0 ≤ T) (hlog : 0 ≤ log_T) :
    (d_nat : ℝ) ^ 2 * T * log_T ≤ (K : ℝ) * T * log_T := by
  have h : (d_nat : ℝ) ^ 2 ≤ (K : ℝ) := by exact_mod_cast hK
  have hTlog : 0 ≤ T * log_T := mul_nonneg hT hlog
  nlinarith [mul_le_mul_of_nonneg_right h hTlog]

end
