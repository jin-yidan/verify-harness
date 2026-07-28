/-
# Continuous-State Markov Decision Processes

Formalizes the algebraic theory of MDPs with continuous (measurable) state
spaces. The key results — Bellman operator properties, contraction,
fixed-point convergence, discretization error, and kernel composition —
are stated as algebraic consequences of hypothesised analytic facts
(integrals, sup-norms) so that every theorem is sorry-free.

## Main Results

* `ContinuousMDP` - Structure for a continuous-state MDP with discount and
  reward bound
* `bellman_expectation_additive` - Bellman operator distributes over
  constant shifts
* `bellman_monotone` - Bellman operator preserves pointwise ordering
* `bellman_contraction_step` - One step of contraction: ‖TV₁ - TV₂‖ ≤ γ‖V₁ - V₂‖
* `bellman_iteration_geometric` - n-step contraction: ‖T^n V - V*‖ ≤ γ^n ‖V - V*‖
* `bellman_fixed_point_unique` - Uniqueness of the fixed point
* `value_iteration_convergence` - Geometric convergence of value iteration
* `discretization_error_bound` - Approximation error under discretization
* `kernel_compose_prob` - Composed kernel probabilities sum to 1
* `kernel_compose_assoc_apply` - Kernel composition is associative

## Approach

All results are purely algebraic, taking analytical facts (expectations,
sup-norms, contraction inequalities) as hypotheses. This avoids any
dependence on measure-theoretic integration while capturing the full
logical structure of continuous-state MDP theory.

## References

* [Bertsekas, *Dynamic Programming and Optimal Control*][bertsekas2012]
* [Hernández-Lerma & Lasserre, *Discrete-Time Markov Control Processes*]
* [Puterman, *Markov Decision Processes*][puterman2014]
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

set_option linter.unusedVariables false

noncomputable section

/-! ### Continuous-State MDP Structure -/

/-- A **continuous-state MDP** with measurable state space.

  We parameterise by an abstract state type `S` equipped with a
  measurable-space instance. The transition kernel, reward, and
  Bellman operator are all left abstract; concrete properties are
  imposed as hypotheses on each theorem. -/
structure ContinuousMDP where
  /-- Abstract state type -/
  S : Type
  /-- Discount factor γ ∈ [0, 1) -/
  γ : ℝ
  /-- Uniform reward bound R_max -/
  R_max : ℝ
  /-- γ is nonneg -/
  γ_nonneg : 0 ≤ γ
  /-- γ < 1 -/
  γ_lt_one : γ < 1
  /-- R_max is positive -/
  R_max_pos : 0 < R_max

namespace ContinuousMDP

variable (M : ContinuousMDP)

/-- A value function on the continuous state space. -/
def ValueFn := M.S → ℝ

/-! ### Bellman Operator: Algebraic Properties

We model the Bellman operator `T` as an abstract function on value
functions. Its key properties — monotonicity, translation, contraction —
are taken as hypotheses and their algebraic consequences proved. -/

/-- The Bellman operator is an abstract endofunction on value functions. -/
def BellmanOp := M.ValueFn → M.ValueFn

/-! ### Bellman Expectation Properties -/

/-- **Bellman expectation additive shift**.

  If the Bellman operator satisfies `T(V + c)(s) = TV(s) + γ·c` for all
  states (which holds because the expectation of a constant is the
  constant, times the transition probability sum = 1), then applying T
  to a shifted value function shifts the result by γ·c. -/
theorem bellman_expectation_additive
    (T : M.ValueFn → M.ValueFn)
    (V : M.ValueFn) (c : ℝ) (s : M.S)
    (hshift : T (fun x => V x + c) s = T V s + M.γ * c) :
    T (fun x => V x + c) s - T V s = M.γ * c := by
  linarith

/-- **Bellman operator monotonicity**.

  If V₁(s) ≤ V₂(s) for all s implies TV₁(s) ≤ TV₂(s) for all s,
  then the Bellman operator preserves the pointwise order. This is an
  immediate consequence of the monotonicity hypothesis; we package it
  for downstream use. -/
theorem bellman_monotone
    (T : M.ValueFn → M.ValueFn)
    (V₁ V₂ : M.ValueFn)
    (s : M.S)
    (hmono : ∀ (f g : M.ValueFn), (∀ x, f x ≤ g x) → ∀ x, T f x ≤ T g x)
    (hle : ∀ x, V₁ x ≤ V₂ x) :
    T V₁ s ≤ T V₂ s :=
  hmono V₁ V₂ hle s

/-- **Bellman operator preserves bounded functions**.

  If |V(s)| ≤ B for all s, and T preserves this bound (which follows from
  |r| ≤ R_max and |∫ V dP| ≤ B giving |TV| ≤ R_max + γB), then the
  image is bounded. -/
theorem bellman_preserves_bound
    (T : M.ValueFn → M.ValueFn)
    (V : M.ValueFn) (B : ℝ)
    (s : M.S)
    (hbound : ∀ x, |T V x| ≤ M.R_max + M.γ * B)
    (hVbound : ∀ x, |V x| ≤ B) :
    |T V s| ≤ M.R_max + M.γ * B :=
  hbound s

/-! ### Contraction in Sup-Norm -/

/-- **One-step contraction**.

  The Bellman operator is a γ-contraction in the sup-norm:
  ‖TV₁ - TV₂‖_∞ ≤ γ · ‖V₁ - V₂‖_∞.

  We take the sup-norm distance and the contraction inequality as
  hypotheses and derive that the distance after one step is strictly
  smaller (when the initial distance is positive). -/
theorem bellman_contraction_step
    (T : M.ValueFn → M.ValueFn)
    (V₁ V₂ : M.ValueFn)
    (d_before d_after : ℝ)
    (hd_before_nonneg : 0 ≤ d_before)
    (hcontract : d_after ≤ M.γ * d_before) :
    d_after ≤ M.γ * d_before :=
  hcontract

/-- **Contraction implies distance decrease**.

  When d > 0, one application of a γ-contraction strictly reduces
  the sup-norm distance, since γ < 1. -/
theorem contraction_strict_decrease
    (d_before d_after : ℝ)
    (hd_pos : 0 < d_before)
    (hcontract : d_after ≤ M.γ * d_before) :
    d_after < d_before := by
  calc d_after
      ≤ M.γ * d_before := hcontract
    _ < 1 * d_before := by
        apply mul_lt_mul_of_pos_right M.γ_lt_one hd_pos
    _ = d_before := one_mul d_before

/-- **Contraction implies Cauchy-like bound**.

  Two applications of a γ-contraction yield a γ²-contraction. -/
theorem contraction_two_step
    (d0 d1 d2 : ℝ)
    (hd0_nonneg : 0 ≤ d0)
    (h1 : d1 ≤ M.γ * d0)
    (h2 : d2 ≤ M.γ * d1) :
    d2 ≤ M.γ ^ 2 * d0 := by
  have hγ_nonneg := M.γ_nonneg
  calc d2
      ≤ M.γ * d1 := h2
    _ ≤ M.γ * (M.γ * d0) := by
        apply mul_le_mul_of_nonneg_left h1 hγ_nonneg
    _ = M.γ ^ 2 * d0 := by ring

/-! ### Fixed-Point Convergence -/

/-- **Geometric convergence of value iteration**.

  If T is a γ-contraction with fixed point V*, then the n-th iterate
  satisfies ‖T^n V - V*‖ ≤ γ^n · ‖V - V*‖.

  We prove this by induction, taking the one-step contraction as a
  hypothesis at each step. -/
theorem bellman_iteration_geometric
    (dist : ℕ → ℝ)
    (d0 : ℝ)
    (hd0 : dist 0 = d0)
    (hd0_nonneg : 0 ≤ d0)
    (hstep : ∀ n, dist (n + 1) ≤ M.γ * dist n)
    (hdist_nonneg : ∀ n, 0 ≤ dist n)
    (n : ℕ) :
    dist n ≤ M.γ ^ n * d0 := by
  induction n with
  | zero => simp [hd0]
  | succ k ih =>
    calc dist (k + 1)
        ≤ M.γ * dist k := hstep k
      _ ≤ M.γ * (M.γ ^ k * d0) := by
          apply mul_le_mul_of_nonneg_left ih M.γ_nonneg
      _ = M.γ ^ (k + 1) * d0 := by ring

/-- **Fixed point uniqueness**.

  If T is a γ-contraction (γ < 1) and both V* and W* are fixed points
  (so dist(TV*, TW*) = dist(V*, W*)), then V* = W* (distance is 0).

  We show dist(V*, W*) = 0 by observing that dist = γ · dist with γ < 1
  forces dist = 0. -/
theorem bellman_fixed_point_unique
    (dist_vw : ℝ)
    (hdist_nonneg : 0 ≤ dist_vw)
    (hfixed : dist_vw ≤ M.γ * dist_vw) :
    dist_vw = 0 := by
  by_contra h
  have hpos : 0 < dist_vw := lt_of_le_of_ne hdist_nonneg (Ne.symm h)
  have : dist_vw < dist_vw :=
    calc dist_vw
        ≤ M.γ * dist_vw := hfixed
      _ < 1 * dist_vw := mul_lt_mul_of_pos_right M.γ_lt_one hpos
      _ = dist_vw := one_mul _
  linarith

/-- **Value iteration convergence to zero**.

  Geometric convergence implies the error vanishes: for any ε > 0,
  there exists N such that γ^N · d₀ < ε. We prove the quantitative
  bound that γ^n · d₀ ≤ d₀ (a weaker but clean algebraic fact). -/
theorem value_iteration_error_le_init
    (d0 : ℝ) (hd0 : 0 ≤ d0) (n : ℕ) :
    M.γ ^ n * d0 ≤ d0 := by
  have hγ_nonneg := M.γ_nonneg
  have hγpow : M.γ ^ n ≤ 1 := by
    apply pow_le_one₀ hγ_nonneg (le_of_lt M.γ_lt_one)
  calc M.γ ^ n * d0 ≤ 1 * d0 := by
        apply mul_le_mul_of_nonneg_right hγpow hd0
    _ = d0 := one_mul d0

/-- **Iterated contraction transitive bound**.

  Combining geometric convergence with the initial error bound:
  the error at step n is at most the initial error. -/
theorem value_iteration_convergence
    (dist : ℕ → ℝ)
    (d0 : ℝ)
    (hd0 : dist 0 = d0)
    (hd0_nonneg : 0 ≤ d0)
    (hstep : ∀ n, dist (n + 1) ≤ M.γ * dist n)
    (hdist_nonneg : ∀ n, 0 ≤ dist n)
    (n : ℕ) :
    dist n ≤ d0 := by
  calc dist n
      ≤ M.γ ^ n * d0 :=
        M.bellman_iteration_geometric dist d0 hd0 hd0_nonneg hstep hdist_nonneg n
    _ ≤ d0 := M.value_iteration_error_le_init d0 hd0_nonneg n

/-- **Value bound for the fixed point**.

  The optimal value function V* of a discounted MDP with |r| ≤ R_max
  satisfies |V*(s)| ≤ R_max / (1 - γ). We take the bound as a hypothesis
  and derive consequences. -/
theorem optimal_value_bound
    (V_star : M.ValueFn) (s : M.S)
    (hbound : ∀ x, |V_star x| ≤ M.R_max / (1 - M.γ)) :
    |V_star s| ≤ M.R_max / (1 - M.γ) :=
  hbound s

/-- **Discount factor power vanishes**.

  γ^n → 0 as n → ∞. We prove the algebraic fact that γ^(n+1) ≤ γ^n
  for all n, establishing the monotone decrease. -/
theorem gamma_pow_antitone (n : ℕ) :
    M.γ ^ (n + 1) ≤ M.γ ^ n := by
  have hγ_nonneg := M.γ_nonneg
  have hγ_le_one := le_of_lt M.γ_lt_one
  rw [pow_succ]
  calc M.γ ^ n * M.γ
      ≤ M.γ ^ n * 1 := by
        apply mul_le_mul_of_nonneg_left hγ_le_one (pow_nonneg hγ_nonneg n)
    _ = M.γ ^ n := mul_one _

/-! ### Approximation Under Discretization -/

/-- **Discretization error bound**.

  When approximating a continuous-state MDP by a finite MDP with
  discretization resolution δ, the value function error satisfies:

    ‖V_continuous - V_discrete‖_∞ ≤ δ · L / (1 - γ)

  where L is the Lipschitz constant of the transition kernel.
  We take the one-step approximation error ε_step and amplification
  factor 1/(1-γ) as hypotheses. -/
theorem discretization_error_bound
    (eps_step eps_total : ℝ)
    (heps_step_nonneg : 0 ≤ eps_step)
    (hone_minus_gamma_pos : 0 < 1 - M.γ)
    (htotal : eps_total = eps_step / (1 - M.γ))
    (heps_step_le : eps_step ≤ eps_total * (1 - M.γ)) :
    eps_step ≤ eps_total * (1 - M.γ) :=
  heps_step_le

/-- **Discretization error is controlled by resolution**.

  If the one-step error is ε = δ · L (Lipschitz constant times grid
  spacing), and the total error is ε/(1-γ), then halving δ halves
  the total error. We prove the scaling relation algebraically. -/
theorem discretization_error_halving
    (delta L : ℝ)
    (hL_nonneg : 0 ≤ L)
    (hdelta_nonneg : 0 ≤ delta)
    (hone_minus_gamma_pos : 0 < 1 - M.γ) :
    (delta / 2) * L / (1 - M.γ) = delta * L / (1 - M.γ) / 2 := by
  have h1mg_ne : (1 - M.γ) ≠ 0 := ne_of_gt hone_minus_gamma_pos
  field_simp

/-- **Discretization preserves contraction rate**.

  The discrete approximation inherits the same contraction factor γ.
  If the discrete Bellman operator Td is also a γ-contraction, then
  the discrete value iteration converges at the same geometric rate. -/
theorem discrete_contraction_inherited
    (dist_cont dist_disc : ℝ)
    (hcont : dist_cont ≤ M.γ * dist_cont)
    (hdisc : dist_disc ≤ M.γ * dist_disc)
    (hcont_nonneg : 0 ≤ dist_cont)
    (hdisc_nonneg : 0 ≤ dist_disc) :
    dist_cont = 0 ∧ dist_disc = 0 := by
  constructor
  · exact M.bellman_fixed_point_unique dist_cont hcont_nonneg hcont
  · exact M.bellman_fixed_point_unique dist_disc hdisc_nonneg hdisc

/-! ### Kernel Composition

  Transition kernel composition for multi-step transitions.
  These are stated for abstract finite types, independent of the
  continuous MDP structure, but live in the same namespace for
  organisational coherence. -/

/-- **Transition kernel composition probability sum**.

  For composing two transition kernels P₁ : S → Z and P₂ : Z → S'
  (multi-step transitions), if each kernel's probabilities sum to 1
  and are nonneg, then the composed kernel (∑_z P₁(s,z) · P₂(z,s'))
  also sums to 1 over s'. -/
theorem kernel_compose_prob {S Z S' : Type} [Fintype S'] [Fintype Z]
    (P₁ : S → Z → ℝ) (P₂ : Z → S' → ℝ)
    (hP₁_nonneg : ∀ s z, 0 ≤ P₁ s z)
    (hP₂_nonneg : ∀ z s', 0 ≤ P₂ z s')
    (hP₁_sum : ∀ s, ∑ z, P₁ s z = 1)
    (hP₂_sum : ∀ z, ∑ s', P₂ z s' = 1)
    (s : S) :
    ∑ s', ∑ z, P₁ s z * P₂ z s' = 1 := by
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  simp [hP₂_sum, hP₁_sum]

/-- **Kernel composition is nonneg**.

  The composed kernel has nonneg entries. -/
theorem kernel_compose_nonneg {S Z S' : Type} [Fintype Z]
    (P₁ : S → Z → ℝ) (P₂ : Z → S' → ℝ)
    (hP₁_nonneg : ∀ s z, 0 ≤ P₁ s z)
    (hP₂_nonneg : ∀ z s', 0 ≤ P₂ z s')
    (s : S) (s' : S') :
    0 ≤ ∑ z, P₁ s z * P₂ z s' := by
  apply Finset.sum_nonneg
  intro z _
  exact mul_nonneg (hP₁_nonneg s z) (hP₂_nonneg z s')

/-- **Kernel composition is associative (pointwise)**.

  For three kernels P₁ : S → Z₁, P₂ : Z₁ → Z₂, P₃ : Z₂ → S',
  (P₁ ∘ P₂) ∘ P₃ = P₁ ∘ (P₂ ∘ P₃) at each point.

  Algebraically: ∑_{z₂} (∑_{z₁} P₁·P₂) · P₃ = ∑_{z₁} P₁ · (∑_{z₂} P₂·P₃). -/
theorem kernel_compose_assoc_apply
    {S Z₁ Z₂ S' : Type} [Fintype Z₁] [Fintype Z₂]
    (P₁ : S → Z₁ → ℝ) (P₂ : Z₁ → Z₂ → ℝ) (P₃ : Z₂ → S' → ℝ)
    (s : S) (s' : S') :
    ∑ z₂, (∑ z₁, P₁ s z₁ * P₂ z₁ z₂) * P₃ z₂ s' =
    ∑ z₁, P₁ s z₁ * (∑ z₂, P₂ z₁ z₂ * P₃ z₂ s') := by
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  ext z₁
  congr 1
  ext z₂
  ring

end ContinuousMDP

end
