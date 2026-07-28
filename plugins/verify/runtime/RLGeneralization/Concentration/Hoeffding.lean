/-
# Hoeffding's Inequality for Empirical MDP Estimation

Connects Mathlib's Hoeffding inequality to our MDP sampling model.

## Architecture

This file bridges the algebraic MDP framework with
probabilistic guarantees by applying Mathlib's
`measure_sum_ge_le_of_iIndepFun` to the MDP sampling setting.

The key chain is:
  1. i.i.d. samples s'₁,...,s'_N ~ P(·|s,a) for each (s,a)
  2. Indicator X_i(s') = 𝟙{s'_i = s'} is bounded in [0,1]
  3. Bounded → sub-Gaussian (Mathlib: `hasSubgaussianMGF_of_mem_Icc`)
  4. Hoeffding for sums (Mathlib: `measure_sum_ge_le_of_iIndepFun`)
  5. Union bound over all (s,a,s') triples
  6. Connect to our `simulation_lemma` → full PAC guarantee

## Status

Steps 1-5 require measure-theory plumbing (probability space
definition, random variable setup). The connection from step 5
to step 6 is already formalized in `model_based_comparison`.

## Mathlib Lemmas Used

* `hasSubgaussianMGF_of_mem_Icc` — bounded r.v. is sub-Gaussian
* `measure_sum_ge_le_of_iIndepFun` — Hoeffding for i.i.d. sums
* `MeasureTheory.Measure.iIndepFun` — independence structure

## References

* [Agarwal et al., *RL: Theory and Algorithms*]
* Appendix A.1 (scalar concentration), A.4 (discrete bound)
-/

import RLGeneralization.Generalization.SampleComplexity
import Mathlib.Probability.Moments.SubGaussian

open Finset BigOperators MeasureTheory ProbabilityTheory

noncomputable section

namespace FiniteMDP

variable (M : FiniteMDP)

/-! ### Indicator Random Variables for Transition Estimation -/

/-- Indicator function: 𝟙{x = s'} as a real-valued function.
    This is the building block for the empirical transition. -/
def transitionIndicator (s' : M.S) (x : M.S) : ℝ :=
  if x = s' then 1 else 0

lemma transitionIndicator_nonneg (s' x : M.S) :
    0 ≤ M.transitionIndicator s' x := by
  simp [transitionIndicator]; split_ifs <;> norm_num

lemma transitionIndicator_le_one (s' x : M.S) :
    M.transitionIndicator s' x ≤ 1 := by
  simp [transitionIndicator]; split_ifs <;> norm_num

lemma transitionIndicator_mem_Icc (s' x : M.S) :
    M.transitionIndicator s' x ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨M.transitionIndicator_nonneg s' x,
   M.transitionIndicator_le_one s' x⟩

/-! ### Empirical Transition as Sum of Indicators -/

/-- The empirical transition P̂(s'|s,a) = (1/N) ∑ᵢ 𝟙{sampleᵢ = s'}.
    This restates `empiricalTransition` in terms of indicator sums,
    connecting the algebraic definition to the probabilistic one.

    When `samples` are i.i.d. from P(·|s,a), each indicator
    𝟙{sampleᵢ = s'} has expectation P(s'|s,a) and is bounded
    in [0,1], making it sub-Gaussian with parameter 1/4. -/
theorem empirical_as_indicator_sum {N : ℕ} (hN : 0 < N)
    (next_states : M.S → M.A → Fin N → M.S)
    (s : M.S) (a : M.A) (s' : M.S) :
    M.empiricalTransition hN next_states s a s' =
    (∑ i : Fin N, M.transitionIndicator s'
      (next_states s a i)) / N := by
  simp only [empiricalTransition, transitionIndicator]
  congr 1; rw [Finset.sum_boole]

/-! ### Full PAC Guarantee (Composition)

  The full PAC result for the generative model
  follows by composing:

  1. **Hoeffding** (Mathlib): For i.i.d. bounded r.v.s X₁,...,X_N:
     P(|X̄ - μ| ≥ ε) ≤ 2·exp(-2Nε²)

  2. **Union bound**: Over all |S|·|A|·|S| triples (s,a,s'):
     P(∃(s,a,s'): |P̂ - P| ≥ ε) ≤ 2|S|²|A|·exp(-2Nε²)

  3. **L1 transition error**: For each (s,a):
     ∑_{s'} |P̂ - P| ≤ |S|·max_{s'} |P̂ - P|

  4. **Simulation inequality** (our `simulation_lemma`):
     |V^π - V̂^π| ≤ (ε_R + γBε_T)/(1-γ)

  5. **Comparison lemma** (our `model_based_comparison`):
     V* - V^{π̂} ≤ 2(ε_R + γBε_T)/(1-γ)

  Steps 4-5 are already formalized. Steps 1-3 require
  constructing the probability space for the generative model
  samples and applying Mathlib's Hoeffding inequality.

  The key Mathlib ingredients are:
  - `hasSubgaussianMGF_of_mem_Icc` for step 1
  - `measure_sum_ge_le_of_iIndepFun` for step 1
  - Standard union bound (Measure.meas_biUnion_le) for step 2
-/

/-! ### L1 Error from Pointwise Error (Step 3, algebraic) -/

/-- **L1 error from pointwise error** (algebraic, no probability).
    If |P̂(s'|s,a) - P(s'|s,a)| ≤ ε₀ for all s', then
    ∑_{s'} |P̂ - P| ≤ |S| · ε₀.
    This converts pointwise (entry-wise) concentration bounds
    to L1 transition error bounds used by the simulation lemma. -/
theorem l1_from_pointwise (P_hat : M.S → M.A → M.S → ℝ)
    (s : M.S) (a : M.A) (ε₀ : ℝ) (_hε₀ : 0 ≤ ε₀)
    (h_pw : ∀ s', |M.P s a s' - P_hat s a s'| ≤ ε₀) :
    ∑ s', |M.P s a s' - P_hat s a s'| ≤
      Fintype.card M.S * ε₀ := by
  calc ∑ s', |M.P s a s' - P_hat s a s'|
      ≤ ∑ _s' : M.S, ε₀ :=
        Finset.sum_le_sum (fun s' _ => h_pw s')
    _ = Fintype.card M.S * ε₀ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-! ### Probabilistic PAC Theorem -/

/-- **Union-bound step for the generative-model PAC argument**.

  If per-entry concentration holds -- for each (s,a,s') the
  probability P(|P̂(s'|s,a) - P(s'|s,a)| >= epsilon_0) <= delta_0 --
  then with probability >= 1 - |S|^2 |A| delta_0, all entries are
  simultaneously within epsilon_0 of their true values.

  This is the union bound over |S|^2 |A| triples (s,a,s'),
  converting per-entry concentration into a simultaneous guarantee.
  Composing with `model_based_comparison` yields the full PAC
  guarantee.

  **Caveat**: This theorem does NOT apply Hoeffding to actual
  samples -- it takes the per-entry concentration bound as a
  hypothesis. The Hoeffding application requires constructing
  the probability space for the generative model, which is not
  formalized here. -/
theorem pac_from_concentration
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} [IsProbabilityMeasure μ]
    -- Random empirical transitions
    (P_hat : Ω → M.S → M.A → M.S → ℝ)
    -- Per-entry concentration hypothesis:
    -- for each (s,a,s'), P(|P̂ - P| ≥ ε₀) ≤ δ₀
    (ε₀ δ₀ : ℝ) (_hε₀ : 0 ≤ ε₀) (_hδ₀ : 0 ≤ δ₀)
    (h_conc : ∀ s a s',
      μ.real {ω | ε₀ ≤ |M.P s a s' - P_hat ω s a s'|} ≤ δ₀)
    -- Measurability of the "good event"
    (h_meas_good : MeasurableSet
      {ω | ∀ s a s', |M.P s a s' - P_hat ω s a s'| < ε₀}) :
    -- Conclusion: with high probability, all entries are close
    -- P(all entries within ε₀) ≥ 1 - |S|²|A| · δ₀
    μ.real {ω | ∀ s a s',
      |M.P s a s' - P_hat ω s a s'| < ε₀} ≥
      1 - Fintype.card M.S * Fintype.card M.S *
        Fintype.card M.A * δ₀ := by
  -- P(good) = 1 - P(goodᶜ) ≥ 1 - |S|²|A|·δ₀
  -- P(goodᶜ) = P(∃ bad entry) ≤ ∑_{s,a,s'} P(bad) ≤ |S|²|A|·δ₀
  -- Use: μ(good) + μ(goodᶜ) = 1
  -- and: μ(goodᶜ) ≤ |S|²|A|·δ₀ (by union bound)
  set good := {ω | ∀ s a s',
    |M.P s a s' - P_hat ω s a s'| < ε₀}
  have h_add : μ.real good + μ.real goodᶜ =
      μ.real Set.univ :=
    measureReal_add_measureReal_compl h_meas_good
  have h_univ : μ.real Set.univ = 1 := probReal_univ
  -- Union bound: μ(goodᶜ) ≤ |S|²|A|·δ₀
  -- goodᶜ = {ω | ∃ s a s', ε₀ ≤ |P̂-P|}
  -- ⊆ ⋃_{s,a,s'} {ω | ε₀ ≤ |P̂-P| for this triple}
  -- μ(⋃) ≤ ∑ μ(each) ≤ |S|²|A|·δ₀
  have h_ub : μ.real goodᶜ ≤
      Fintype.card M.S * Fintype.card M.S *
        Fintype.card M.A * δ₀ := by
    -- goodᶜ = {ω | ∃ s a s', ε₀ ≤ |P̂-P|} ⊆ ⋃_{s,a,s'} bad(s,a,s')
    have h_subset : goodᶜ ⊆ ⋃ (p : M.S × M.A × M.S),
        {ω | ε₀ ≤ |M.P p.1 p.2.1 p.2.2 -
          P_hat ω p.1 p.2.1 p.2.2|} := by
      intro ω hω
      simp only [good, Set.mem_compl_iff, Set.mem_setOf_eq,
        not_forall, not_lt] at hω
      obtain ⟨s, a, s', h⟩ := hω
      exact Set.mem_iUnion.mpr ⟨(s, a, s'), h⟩
    -- μ(goodᶜ) ≤ μ(⋃ bad) ≤ ∑ μ(bad) ≤ |S|²|A|·δ₀
    calc μ.real goodᶜ
        ≤ μ.real (⋃ (p : M.S × M.A × M.S),
            {ω | ε₀ ≤ |M.P p.1 p.2.1 p.2.2 -
              P_hat ω p.1 p.2.1 p.2.2|}) :=
          measureReal_mono h_subset
      _ ≤ ∑ p : M.S × M.A × M.S, μ.real
            {ω | ε₀ ≤ |M.P p.1 p.2.1 p.2.2 -
              P_hat ω p.1 p.2.1 p.2.2|} :=
          measureReal_iUnion_fintype_le _
      _ ≤ ∑ _p : M.S × M.A × M.S, δ₀ :=
          Finset.sum_le_sum (fun p _ => h_conc p.1 p.2.1 p.2.2)
      _ = Fintype.card (M.S × M.A × M.S) * δ₀ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = Fintype.card M.S * Fintype.card M.S *
            Fintype.card M.A * δ₀ := by
          rw [Fintype.card_prod, Fintype.card_prod]
          push_cast; ring
  linarith

end FiniteMDP

end
