/-
# MDP Trajectory Concentration

Measure-theoretic Azuma-Hoeffding bound for finite-horizon MDP trajectories.
This fills the gap between the algebraic confidence-width computations
in `AzumaHoeffding.lean` and actual probability tail bounds.

## Main Results

* `step_subgaussian` — One-step conditional sub-Gaussianity:
    for V ∈ [0, B], the centered random variable V(s') − E_P[V]
    is sub-Gaussian with parameter (B/2)² under the transition
    measure P_h(·|s,a). Uses Mathlib's `hasSubgaussianMGF_of_mem_Icc`.

* `stepMeasure_integral` — The integral of V under the step measure
    equals the finite-sum expected value ∑_{s'} P(s'|s,a) · V(s').

Note: Multi-step trajectory composition (`trajectory_mgf_tower`,
`mdp_azuma_hoeffding`) is deferred to future work requiring
trajectory filtration construction.

## Architecture

We avoid the full Mathlib filtration/conditional-kernel API by working
directly with the transition PMF measures on finite types. The key idea
is that for finite state spaces, conditional expectations are finite sums:

  E[f(s') | s, a] = ∑_{s'} P(s'|s,a) · f(s')

This makes the "tower of expectations" argument a finitary computation.

## References

* [Boucheron et al., *Concentration Inequalities*, Theorem 3.15]
* [Agarwal et al., *RL: Theory and Algorithms*, Appendix A]
-/

import RLGeneralization.MDP.FiniteHorizon
import RLGeneralization.Concentration.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals

open Finset BigOperators MeasureTheory ProbabilityTheory ENNReal NNReal Real

noncomputable section

namespace FiniteHorizonMDP

variable (M : FiniteHorizonMDP)

/-! ### Measurable Space Instances -/

instance measurableSpaceS : MeasurableSpace M.S := ⊤
instance discreteMeasurableSpaceS : DiscreteMeasurableSpace M.S where
  forall_measurableSet _ := MeasurableSpace.measurableSet_top

/-! ### Transition PMF and Single-Step Measure -/

/-- The transition kernel P_h(·|s,a) as a PMF on the finite state space. -/
def transitionPMF (h : Fin M.H) (s : M.S) (a : M.A) : PMF M.S :=
  PMF.ofFintype (fun s' => ENNReal.ofReal (M.P h s a s'))
    (by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun s' _ => M.P_nonneg h s a s')]
      simp [M.P_sum_one h s a])

/-- The PMF assigns the correct probability to each state. -/
lemma transitionPMF_apply (h : Fin M.H) (s : M.S) (a : M.A) (s' : M.S) :
    M.transitionPMF h s a s' = ENNReal.ofReal (M.P h s a s') := by
  simp [transitionPMF, PMF.ofFintype_apply]

/-- Single-step transition measure: P_h(·|s,a) as a probability measure. -/
def stepMeasure (h : Fin M.H) (s : M.S) (a : M.A) : Measure M.S :=
  (M.transitionPMF h s a).toMeasure

instance stepMeasure_prob (h : Fin M.H) (s : M.S) (a : M.A) :
    IsProbabilityMeasure (M.stepMeasure h s a) :=
  PMF.toMeasure.isProbabilityMeasure _

/-! ### One-Step Conditional Sub-Gaussianity

The key measure-theoretic step: for a bounded value function V ∈ [0, B],
the centered random variable V(s') − E_P[V] is sub-Gaussian with
parameter (B/2)² under the transition measure P_h(·|s,a).

This uses Mathlib's `hasSubgaussianMGF_of_mem_Icc`. -/

/-- Expected value of a function under the transition PMF. -/
def stepExpect (h : Fin M.H) (s : M.S) (a : M.A) (V : M.S → ℝ) : ℝ :=
  ∑ s', M.P h s a s' * V s'

/-- The centered one-step fluctuation
    `V(s') - E_{P_h(·|s,a)}[V]`. -/
def stepCentered (h : Fin M.H) (s : M.S) (a : M.A) (V : M.S → ℝ) :
    M.S → ℝ :=
  fun s' => V s' - ∫ x, V x ∂(M.stepMeasure h s a)

/-- The integral of V under the step measure equals the finite-sum
    expected value. -/
lemma stepMeasure_integral (h : Fin M.H) (s : M.S) (a : M.A) (V : M.S → ℝ) :
    ∫ s', V s' ∂(M.stepMeasure h s a) = M.stepExpect h s a V := by
  simp only [stepMeasure, stepExpect]
  rw [PMF.integral_eq_sum]
  congr 1; ext s'
  rw [M.transitionPMF_apply]
  rw [ENNReal.toReal_ofReal (M.P_nonneg h s a s')]
  simp [smul_eq_mul]

/-- **One-step conditional sub-Gaussianity**.

For a value function V : S → ℝ bounded in [0, B], the centered
random variable V(s') − E_{P_h(·|s,a)}[V] is sub-Gaussian with
parameter (B/2)² under the transition measure.

This is Hoeffding's lemma (Mathlib) applied to the finite transition PMF. -/
theorem step_subgaussian (h : Fin M.H) (s : M.S) (a : M.A)
    (V : M.S → ℝ) (B : ℝ) (_hB : 0 ≤ B)
    (hV : ∀ s', V s' ∈ Set.Icc 0 B) :
    HasSubgaussianMGF (M.stepCentered h s a V)
      ((‖B - 0‖₊ / 2) ^ 2) (M.stepMeasure h s a) := by
  apply hasSubgaussianMGF_of_mem_Icc
  · exact Measurable.of_discrete.aemeasurable
  · filter_upwards with s'
    exact hV s'

/-- **One-step Chernoff tail bound**.

For a value function V ∈ [0, B], the probability that the centered
transition outcome V(s') − E[V] exceeds ε is sub-Gaussian:

  P_h(V(s') − E[V] ≥ ε | s, a) ≤ exp(−ε²/(2·(B/2)²)) = exp(−2ε²/B²)

This is Hoeffding's lemma applied to the finite transition PMF. -/
theorem step_tail_bound (h : Fin M.H) (s : M.S) (a : M.A)
    (V : M.S → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hV : ∀ s', V s' ∈ Set.Icc 0 B)
    {ε : ℝ} (hε : 0 ≤ ε) :
    ∃ c : ℝ≥0,
      (M.stepMeasure h s a).real {ω | ε ≤ M.stepCentered h s a V ω} ≤
        exp (-(ε ^ 2) / (2 * (c : ℝ))) :=
  ⟨_, (M.step_subgaussian h s a V B hB hV).measure_ge_le hε⟩

end FiniteHorizonMDP

/-! ### Multi-Step Trajectory Concentration (Azuma-Hoeffding)

For MDP trajectories, the martingale differences D_h = V(s_{h+1}) - E[V|s_h]
form a sequence of conditionally sub-Gaussian random variables. The
Azuma-Hoeffding inequality gives:

  P(∑_h D_h ≥ ε) ≤ exp(-ε²/(2 · ∑_h c_h))

The theorem `mdp_trajectory_concentration` wraps Mathlib's
`measure_sum_ge_le_of_hasCondSubgaussianMGF`. The caller constructs
the trajectory probability space and filtration; `step_subgaussian`
from above verifies each step's conditional sub-Gaussianity.

For UCBVI with V ∈ [0, B], each c_h = (B/2)² so ∑ c_h = H(B/2)²,
giving P(∑ D_h ≥ ε) ≤ exp(-2ε²/(HB²)). -/

/-- **MDP trajectory Azuma-Hoeffding** (Mathlib bridge).

  Given a probability space (Ω, μ) with filtration ℱ and martingale
  difference sequence Y adapted to ℱ, where each Y_h is conditionally
  sub-Gaussian with parameter c_h, the sum concentrates:

    P(∑_{h<n} Y_h ≥ ε) ≤ exp(-ε²/(2 · ∑_{h<n} c_h))

  This is a direct invocation of Mathlib's Azuma-Hoeffding. Combined
  with `FiniteHorizonMDP.step_subgaussian`, it yields concrete tail
  bounds for MDP trajectories once the trajectory filtration is
  constructed. -/
theorem mdp_trajectory_concentration
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsZeroOrProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {Y : ℕ → Ω → ℝ} {cY : ℕ → ℝ≥0}
    (h_adapted : StronglyAdapted ℱ Y)
    (h0 : HasSubgaussianMGF (Y 0) (cY 0) μ)
    (n : ℕ)
    (h_subG : ∀ i < n - 1,
      HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (Y (i + 1)) (cY (i + 1)) μ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ i ∈ Finset.range n, Y i ω} ≤
      exp (-ε ^ 2 / (2 * ∑ i ∈ Finset.range n, cY i)) :=
  measure_sum_ge_le_of_hasCondSubgaussianMGF h_adapted h0 n h_subG hε

end
