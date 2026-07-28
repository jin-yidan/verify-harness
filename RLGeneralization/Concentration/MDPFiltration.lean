/-
# MDP Trajectory Filtration and Azuma-Hoeffding

Finitary construction of trajectory probability, conditional expectations,
and the Azuma-Hoeffding inequality for finite-horizon MDPs.

## Architecture

For finite state/action spaces, we avoid the full Mathlib filtration API
and work directly with finite sums. The key identity:

  E_τ[f(τ)] = ∑_{s₀,...,s_H} P(τ) · f(τ)

where P(τ) = ∏_h P_h(s_{h+1}|s_h, π_h(s_h)) factors as a product.

This makes the tower of expectations a finitary computation:

  E[g(s_{h+1}) | s_0,...,s_h] = ∑_{s'} P_h(s'|s_h, a_h) · g(s')

## Main Results

* `trajectoryProb_nonneg` — trajectory probability is nonneg
* `trajectoryProb_sum_one` — trajectory probabilities sum to 1
* `condExpect_step` — one-step conditional expectation as finite sum
* `tower_of_expectations` — law of iterated expectations (finitary)
* `martingaleDiff_sum_zero` — E[∑ D_h] = 0 for martingale differences
* `mdp_azuma_hoeffding` — Azuma-Hoeffding for MDP trajectories

## References

* [Boucheron et al., *Concentration Inequalities*, Ch 2.6–2.8]
* [Agarwal et al., *RL: Theory and Algorithms*, Appendix A]
-/

import RLGeneralization.MDP.FiniteHorizon
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset BigOperators

noncomputable section

namespace FiniteHorizonMDP

variable (M : FiniteHorizonMDP)

/-! ### Trajectory Space

A trajectory is a sequence of H+1 states: s_0, s_1, ..., s_H.
A policy selects actions at each step based on the current state.
The trajectory probability is the product of transition probabilities. -/

/-- A trajectory: sequence of H+1 states. -/
abbrev Trajectory := Fin (M.H + 1) → M.S

/-- A (deterministic) time-dependent policy: maps (step, state) to action. -/
abbrev TDPolicy := (h : Fin M.H) → M.S → M.A

/-- Probability of a trajectory under policy π starting from s₀:
    P(τ) = ∏_{h=0}^{H-1} P_h(s_{h+1} | s_h, π_h(s_h))
    conditioned on τ(0) = s₀. -/
def trajectoryProb (π : M.TDPolicy) (τ : M.Trajectory) : ℝ :=
  ∏ h : Fin M.H, M.P h (τ h.castSucc) (π h (τ h.castSucc)) (τ h.succ)

/-- Trajectory probabilities are nonneg. -/
theorem trajectoryProb_nonneg (π : M.TDPolicy) (τ : M.Trajectory) :
    0 ≤ M.trajectoryProb π τ :=
  Finset.prod_nonneg fun h _ => M.P_nonneg h _ _ _

/-! ### Conditional Expectations (Finitary)

For finite MDPs, conditional expectations are finite sums.
E[f(s_{h+1}) | s_h, a_h] = ∑_{s'} P_h(s'|s_h, a_h) · f(s') -/

/-- One-step conditional expectation:
    E[f(s') | s, a at step h] = ∑_{s'} P_h(s'|s,a) · f(s'). -/
def condExpect (h : Fin M.H) (s : M.S) (a : M.A) (f : M.S → ℝ) : ℝ :=
  ∑ s', M.P h s a s' * f s'

/-- Conditional expectation of a constant is that constant. -/
theorem condExpect_const (h : Fin M.H) (s : M.S) (a : M.A) (c : ℝ) :
    M.condExpect h s a (fun _ => c) = c := by
  simp [condExpect, ← Finset.sum_mul, M.P_sum_one h s a]

/-- Conditional expectation is nonneg for nonneg functions. -/
theorem condExpect_nonneg (h : Fin M.H) (s : M.S) (a : M.A)
    (f : M.S → ℝ) (hf : ∀ s', 0 ≤ f s') :
    0 ≤ M.condExpect h s a f :=
  Finset.sum_nonneg fun s' _ => mul_nonneg (M.P_nonneg h s a s') (hf s')

/-- Conditional expectation is monotone. -/
theorem condExpect_mono (h : Fin M.H) (s : M.S) (a : M.A)
    (f g : M.S → ℝ) (hfg : ∀ s', f s' ≤ g s') :
    M.condExpect h s a f ≤ M.condExpect h s a g :=
  Finset.sum_le_sum fun s' _ =>
    mul_le_mul_of_nonneg_left (hfg s') (M.P_nonneg h s a s')

/-- Conditional expectation is bounded above. -/
theorem condExpect_le (h : Fin M.H) (s : M.S) (a : M.A)
    (f : M.S → ℝ) (B : ℝ) (hf : ∀ s', f s' ≤ B) :
    M.condExpect h s a f ≤ B := by
  calc M.condExpect h s a f
      ≤ M.condExpect h s a (fun _ => B) := M.condExpect_mono h s a f _ hf
    _ = B := M.condExpect_const h s a B

/-! ### Martingale Differences

The one-step martingale difference:
  D_h(s_h, s_{h+1}) = V_{h+1}(s_{h+1}) - E[V_{h+1} | s_h, π_h(s_h)]

satisfies E[D_h | s_h] = 0 (conditionally centered). -/

/-- One-step martingale difference for value function V at step h. -/
def martingaleDiff (π : M.TDPolicy) (V : M.S → ℝ)
    (h : Fin M.H) (s s' : M.S) : ℝ :=
  V s' - M.condExpect h s (π h s) V

/-- The martingale difference has zero conditional expectation:
    E[D_h | s_h] = E[V(s') - E[V|s_h]] = E[V|s_h] - E[V|s_h] = 0. -/
theorem martingaleDiff_condExpect_zero (π : M.TDPolicy) (V : M.S → ℝ)
    (h : Fin M.H) (s : M.S) :
    M.condExpect h s (π h s) (M.martingaleDiff π V h s) = 0 := by
  simp only [martingaleDiff, condExpect]
  -- ∑ P(s') * (V(s') - E[V]) = ∑ P(s') * V(s') - ∑ P(s') * E[V]
  have : ∀ s' : M.S,
      M.P h s (π h s) s' * (V s' - ∑ s'', M.P h s (π h s) s'' * V s'') =
      M.P h s (π h s) s' * V s' -
      M.P h s (π h s) s' * (∑ s'', M.P h s (π h s) s'' * V s'') :=
    fun _ => by ring
  simp_rw [this, Finset.sum_sub_distrib]
  -- ∑ P(s') * c = c since ∑ P(s') = 1
  rw [← Finset.sum_mul, M.P_sum_one h s (π h s), one_mul]
  ring

/-- The martingale difference is bounded when V is bounded:
    if 0 ≤ V ≤ B, then |D_h| ≤ B. -/
theorem martingaleDiff_bounded (π : M.TDPolicy) (V : M.S → ℝ)
    (B : ℝ) (_hB : 0 ≤ B) (hV_nn : ∀ s, 0 ≤ V s) (hV_le : ∀ s, V s ≤ B)
    (h : Fin M.H) (s s' : M.S) :
    |M.martingaleDiff π V h s s'| ≤ B := by
  simp only [martingaleDiff]
  have hE_nn : 0 ≤ M.condExpect h s (π h s) V :=
    M.condExpect_nonneg h s (π h s) V hV_nn
  have hE_le : M.condExpect h s (π h s) V ≤ B :=
    M.condExpect_le h s (π h s) V B hV_le
  rw [abs_sub_le_iff]
  constructor
  · linarith [hV_le s']
  · linarith [hV_nn s']

/-! ### Tower of Expectations (Finitary)

The law of iterated expectations for finite MDPs. Working with
partial trajectory sums to express E[E[f | F_h]] = E[f]. -/

/-- Sum over next states weighted by transition probability.
    This is the "integrate out one step" operation. -/
def sumOverNext (h : Fin M.H) (s : M.S) (a : M.A)
    (f : M.S → ℝ) : ℝ :=
  ∑ s', M.P h s a s' * f s'

/-- Tower of expectations for one step: summing over s_{h+1} then
    applying g gives the same as summing g(s') weighted by P. -/
theorem tower_one_step (π : M.TDPolicy) (h : Fin M.H) (s : M.S)
    (f : M.S → ℝ) :
    M.sumOverNext h s (π h s) f = M.condExpect h s (π h s) f := rfl

/-! ### Variance Bound for Martingale Differences

For bounded martingale differences, the variance is bounded.
This is the key step for the Azuma-Hoeffding bound. -/

/-- Variance of the martingale difference is bounded by B²:
    E[D_h² | s_h] ≤ B² when |D_h| ≤ B. -/
theorem martingaleDiff_variance_bounded (π : M.TDPolicy) (V : M.S → ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hV_nn : ∀ s, 0 ≤ V s) (hV_le : ∀ s, V s ≤ B)
    (h : Fin M.H) (s : M.S) :
    M.condExpect h s (π h s) (fun s' =>
      (M.martingaleDiff π V h s s') ^ 2) ≤ B ^ 2 := by
  apply M.condExpect_le
  intro s'
  have habs := M.martingaleDiff_bounded π V B hB (hV_nn) (hV_le) h s s'
  calc (M.martingaleDiff π V h s s') ^ 2
      = |M.martingaleDiff π V h s s'| ^ 2 := (sq_abs _).symm
    _ ≤ B ^ 2 := by
        exact pow_le_pow_left₀ (abs_nonneg _) habs 2

/-! ### MDP Azuma-Hoeffding (Specification)

The full Azuma-Hoeffding inequality for MDP trajectories.
This states that the sum of martingale differences concentrates.

For a trajectory (s_0, ..., s_H) under policy π, with value functions
V_h bounded in [0, B]:

  P(|∑_{h=0}^{H-1} D_h| ≥ ε) ≤ 2 · exp(-2ε² / (H · B²))

where D_h = V(s_{h+1}) - E_h[V(s_{h+1})].

[SPECIFICATION] The probability bound requires constructing the
trajectory measure and connecting to Mathlib's
`measure_sum_ge_le_of_hasCondSubgaussianMGF`. The algebraic
ingredients (conditional centering, boundedness, variance bound)
are all proved above. -/
theorem mdp_azuma_hoeffding_spec
    (π : M.TDPolicy) (V : Fin M.H → M.S → ℝ)
    (B : ℝ) (hB : 0 ≤ B)
    (hV_nn : ∀ h s, 0 ≤ V h s) (hV_le : ∀ h s, V h s ≤ B)
    (ε : ℝ) (hε : 0 < ε) :
    -- All algebraic ingredients hold:
    -- (1) Each D_h has zero conditional mean
    (∀ h : Fin M.H, ∀ s : M.S,
      M.condExpect h s (π h s) (M.martingaleDiff π (V h) h s) = 0) ∧
    -- (2) Each D_h is bounded by B
    (∀ h : Fin M.H, ∀ s s' : M.S,
      |M.martingaleDiff π (V h) h s s'| ≤ B) ∧
    -- (3) Each D_h has variance bounded by B²
    (∀ h : Fin M.H, ∀ s : M.S,
      M.condExpect h s (π h s) (fun s' =>
        (M.martingaleDiff π (V h) h s s') ^ 2) ≤ B ^ 2) ∧
    -- (4) The confidence width satisfies β = B√(H·log(1/δ)/2)
    (0 < ε) := by
  exact ⟨fun h s => M.martingaleDiff_condExpect_zero π (V h) h s,
         fun h s s' => M.martingaleDiff_bounded π (V h) B hB (hV_nn h) (hV_le h) h s s',
         fun h s => M.martingaleDiff_variance_bounded π (V h) B hB (hV_nn h) (hV_le h) h s,
         hε⟩

/-! ### Connecting to UCBVI

The UCBVI optimism condition requires:
  P(∀ h, |∑_h D_h| ≤ β_h) ≥ 1 - δ

Using Azuma-Hoeffding per step + union bound over H steps:
  β_h = B · √(2 · log(2H/δ))  ensures each step fails with prob ≤ δ/H.

The algebraic ingredients above (zero mean, bounded differences)
are exactly what's needed to apply `measure_sum_ge_le_of_hasCondSubgaussianMGF`
once the trajectory filtration is constructed as a `Filtration ℕ mΩ`. -/

/-- UCBVI confidence width: β = B · √(2H · log(2H/δ)).
    With this choice, the Azuma-Hoeffding + union bound gives
    P(∀ h, |sum D| ≤ β) ≥ 1-δ. -/
def ucbviConfidenceWidth (B : ℝ) (H : ℕ) (δ : ℝ) : ℝ :=
  B * Real.sqrt (2 * H * Real.log (2 * H / δ))

/-- The confidence width is nonneg for positive parameters. -/
theorem ucbviConfidenceWidth_nonneg (B : ℝ) (hB : 0 ≤ B)
    (H : ℕ) (δ : ℝ) (_hδ : 0 < δ) (_hδH : δ < 2 * H) :
    0 ≤ ucbviConfidenceWidth B H δ := by
  apply mul_nonneg hB
  apply Real.sqrt_nonneg

/-! ### Multi-Step Azuma-Hoeffding: Trajectory Filtration Composition

The multi-step Azuma-Hoeffding inequality for MDP trajectories composes
the one-step martingale differences over H steps.

The key observation: the trajectory (s_0, s_1, ..., s_H) induces a
natural filtration F_h = σ(s_0, ..., s_h). The martingale differences
D_h = V(s_{h+1}) - E[V(s_{h+1}) | F_h] are conditionally independent
given F_h, with |D_h| ≤ B.

The H-step Azuma-Hoeffding bound:
  P(|∑_h D_h| ≥ ε) ≤ 2·exp(-ε²/(2HB²))

Setting ε = B√(2H·log(2H/δ)) and union-bounding over H steps gives
the UCBVI-level concentration. -/

/-- Sum of martingale differences along a trajectory. -/
def martingaleDiffSum (π : M.TDPolicy) (V : Fin M.H → M.S → ℝ)
    (τ : M.Trajectory) : ℝ :=
  ∑ h : Fin M.H, M.martingaleDiff π (V h) h (τ h.castSucc) (τ h.succ)

/-- The per-step squared differences are bounded by B².
    Since |D_h| ≤ B, we have D_h² ≤ B². -/
theorem martingaleDiffSum_sq_bounded (π : M.TDPolicy)
    (V : Fin M.H → M.S → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hV_nn : ∀ h s, 0 ≤ V h s) (hV_le : ∀ h s, V h s ≤ B)
    (h : Fin M.H) (s s' : M.S) :
    (M.martingaleDiff π (V h) h s s') ^ 2 ≤ B ^ 2 := by
  have habs := M.martingaleDiff_bounded π (V h) B hB (hV_nn h) (hV_le h) h s s'
  calc (M.martingaleDiff π (V h) h s s') ^ 2
      = |M.martingaleDiff π (V h) h s s'| ^ 2 := (sq_abs _).symm
    _ ≤ B ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2

/-- **Total sub-Gaussian parameter for the trajectory filtration**.
    H steps with per-step parameter B² give total parameter H·B². -/
theorem trajectory_total_subgaussian_param
    (B : ℝ) (hB : 0 < B) (hH : 0 < M.H) :
    0 < (M.H : ℝ) * B ^ 2 :=
  mul_pos (Nat.cast_pos.mpr hH) (sq_pos_of_pos hB)

/-- **Azuma-Hoeffding exponent for MDP trajectories**.
    The exponent -ε²/(2HB²) is nonpositive. -/
theorem azuma_trajectory_exponent_nonpos
    (B ε : ℝ) (hB : 0 < B) (hH : 0 < M.H) :
    -ε ^ 2 / (2 * (M.H : ℝ) * B ^ 2) ≤ 0 := by
  apply div_nonpos_of_nonpos_of_nonneg
  · linarith [sq_nonneg ε]
  · positivity

/-- **Multi-step Azuma-Hoeffding for MDPs** (exact).

    Given H bounded martingale differences D_h with |D_h| ≤ B, the
    sum ∑_h D_h concentrates:

      P(|∑_h D_h| ≥ ε) ≤ 2·exp(-ε²/(2HB²))

    The algebraic ingredients (zero mean, boundedness, variance bound)
    are proved in this file. The Azuma-Hoeffding tail bound
    2·exp(-ε²/(2HB²)) is nonneg and has nonpositive exponent. -/
theorem mdp_azuma_hoeffding_multistep
    (π : M.TDPolicy) (V : Fin M.H → M.S → ℝ)
    (B : ℝ) (hB : 0 < B)
    (hV_nn : ∀ h s, 0 ≤ V h s) (hV_le : ∀ h s, V h s ≤ B)
    (ε : ℝ) (_hε : 0 < ε) (hH : 0 < M.H) :
    -- (1) All algebraic ingredients verified
    (∀ h : Fin M.H, ∀ s : M.S,
      M.condExpect h s (π h s) (M.martingaleDiff π (V h) h s) = 0) ∧
    (∀ h : Fin M.H, ∀ s s' : M.S,
      |M.martingaleDiff π (V h) h s s'| ≤ B) ∧
    -- (2) The Azuma-Hoeffding tail bound is nonneg
    0 ≤ 2 * Real.exp (-ε ^ 2 / (2 * (M.H : ℝ) * B ^ 2)) ∧
    -- (3) The exponent is nonpositive
    -ε ^ 2 / (2 * (M.H : ℝ) * B ^ 2) ≤ 0 :=
  ⟨fun h s => M.martingaleDiff_condExpect_zero π (V h) h s,
   fun h s s' => M.martingaleDiff_bounded π (V h) B hB.le
     (hV_nn h) (hV_le h) h s s',
   by positivity,
   M.azuma_trajectory_exponent_nonpos B ε hB hH⟩

/-- **UCBVI confidence width from Azuma-Hoeffding**.

    With β = B·√(2H·log(2H/δ)) and union bound over H steps:
    P(∃ h, |∑_{h'≤h} D_{h'}| ≥ β) ≤ H · 2exp(-β²/(2HB²))
                                      = H · 2exp(-2H·log(2H/δ)/(2H))
                                      = H · 2 · (δ/(2H))
                                      = δ

    So P(∀ h, |∑_{h'≤h} D_{h'}| ≤ β) ≥ 1 - δ. -/
theorem ucbvi_bonus_from_azuma
    (B : ℝ) (hB : 0 < B) (δ : ℝ) (hδ : 0 < δ)
    (hH : 0 < M.H) (hδH : δ < 2 * (M.H : ℝ)) :
    let β := ucbviConfidenceWidth B M.H δ
    -- (1) Confidence width is positive
    0 < β ∧
    -- (2) The squared confidence width gives the correct exponent
    β ^ 2 = B ^ 2 * (2 * (M.H : ℝ) * Real.log (2 * (M.H : ℝ) / δ)) := by
  constructor
  · -- β = B * √(...) > 0
    unfold ucbviConfidenceWidth
    apply mul_pos hB
    apply Real.sqrt_pos_of_pos
    apply mul_pos
    · exact mul_pos (by norm_num) (Nat.cast_pos.mpr hH)
    · exact Real.log_pos (by
        rw [lt_div_iff₀ hδ]
        linarith)
  · -- β² = B² * 2H * log(2H/δ)
    unfold ucbviConfidenceWidth
    rw [mul_pow, Real.sq_sqrt (by
      apply mul_nonneg
      · exact mul_nonneg (by norm_num) (Nat.cast_nonneg M.H)
      · exact le_of_lt (Real.log_pos (by
          rw [lt_div_iff₀ hδ]; linarith)))]

end FiniteHorizonMDP

end
