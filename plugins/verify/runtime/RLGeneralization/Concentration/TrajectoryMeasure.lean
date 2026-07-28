/-
# Trajectory Probability Measure for Finite-Horizon MDPs

Constructs the measure-theoretic trajectory probability space for
finite-horizon MDPs, connecting the finitary definitions in
MDPFiltration.lean to Mathlib's measure theory API.

## Architecture

Given a finite-horizon MDP with states S, actions A, and horizon H,
we construct:

1. A PMF on the trajectory space `Fin (H+1) → S` conditioned on
   initial state s₀, using the product of transition probabilities.

2. The corresponding probability measure via `PMF.toMeasure`.

3. Trajectory expectations as Bochner integrals and their equivalence
   to finite sums weighted by trajectory probabilities.

4. Concentration bounds for martingale difference sums: zero mean,
   variance bound, Azuma-Hoeffding tail, and UCBVI high-probability.

The key technical result is `trajectoryProbFrom_sum_one`: for fixed s₀,
the trajectory probabilities sum to 1 over all trajectories starting
at s₀. This is proved by decomposing the Pi-type sum via
`Fin.consEquiv`, connecting the resulting product to a recursive
`chainSum`, and applying `chainSum_eq_one`.

## Main Results

* `trajectoryPMF` — PMF on trajectories conditioned on initial state
* `trajectoryMeasure` — probability measure from the PMF
* `trajectoryMeasure_isProbability` — it is a probability measure
* `trajectoryExpectation` — expectation as Bochner integral
* `trajectoryExpectation_eq_sum` — equals weighted finite sum
* `martingaleDiffSum_expectation_zero` — E[∑ D_h] = 0 (tower hypothesis)
* `martingaleDiffSum_variance_bounded` — E[(∑ D_h)²] ≤ H · B² (cross-term hypothesis)
* `trajectoryAzumaHoeffding` — tail bound (filtration hypothesis)
* `ucbvi_high_probability` — UCBVI confidence (filtration hypothesis)

## References

* [Boucheron et al., *Concentration Inequalities*, Ch 2.6–2.8]
* [Agarwal et al., *RL: Theory and Algorithms*, Appendix A]
-/

import RLGeneralization.Concentration.MDPFiltration
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open Finset BigOperators MeasureTheory

noncomputable section

namespace FiniteHorizonMDP

variable (M : FiniteHorizonMDP)

/-! ### Measurable Space on Trajectories

The trajectory space `Fin (H+1) → S` inherits discrete measurability
from the finite state space S. -/

instance trajectoryMeasurableSpace : MeasurableSpace M.Trajectory := ⊤

instance trajectoryDiscreteMeasurableSpace : DiscreteMeasurableSpace M.Trajectory where
  forall_measurableSet _ := MeasurableSpace.measurableSet_top

/-! ### Trajectory Probability Conditioned on Initial State

For a fixed initial state s₀, the trajectory probability assigns
mass `trajectoryProb π τ` to trajectories with `τ 0 = s₀` and
mass 0 to all others. This forms a proper probability distribution. -/

/-- Trajectory probability conditioned on initial state s₀.
    Returns `trajectoryProb π τ` when `τ 0 = s₀`, else 0. -/
def trajectoryProbFrom (π : M.TDPolicy) (s₀ : M.S) (τ : M.Trajectory) : ℝ :=
  if τ ⟨0, Nat.zero_lt_succ M.H⟩ = s₀ then M.trajectoryProb π τ else 0

/-- Conditional trajectory probability is nonneg. -/
theorem trajectoryProbFrom_nonneg (π : M.TDPolicy) (s₀ : M.S)
    (τ : M.Trajectory) :
    0 ≤ M.trajectoryProbFrom π s₀ τ := by
  simp only [trajectoryProbFrom]
  split
  · exact M.trajectoryProb_nonneg π τ
  · exact le_refl 0

/-! ### Sum-to-One: Recursive Chain Probability

We define the chain probability sum recursively and prove it equals 1,
then connect it to the trajectory probability sum.

The recursive formulation:
  chainSum 0 K s = 1
  chainSum (n+1) K s = ∑_{s'} K_0(s,s') · chainSum n (K ∘ succ) s'

Each step marginalizes out one transition using K_sum_one. -/

/-- Recursive chain probability sum: marginalizes out states one at a time.
    `chainSum n K s` computes ∑_{s₁,...,sₙ} ∏_{i<n} K_i(s_{i-1}, s_i)
    starting from state s. -/
def chainSum {S : Type} [Fintype S]
    (n : ℕ) (K : Fin n → S → S → ℝ) (s : S) : ℝ :=
  match n with
  | 0 => 1
  | n + 1 => ∑ s' : S, K ⟨0, Nat.zero_lt_succ n⟩ s s' *
      chainSum n (fun j => K j.succ) s'

/-- The chain probability sum equals 1 when each transition sums to 1.
    This is the key telescoping identity. -/
theorem chainSum_eq_one {S : Type} [Fintype S]
    (n : ℕ) (K : Fin n → S → S → ℝ)
    (_K_nonneg : ∀ i s s', 0 ≤ K i s s')
    (K_sum_one : ∀ i s, ∑ s', K i s s' = 1)
    (s : S) :
    chainSum n K s = 1 := by
  induction n generalizing s with
  | zero => simp [chainSum]
  | succ m ih =>
    simp only [chainSum]
    -- ∑ s', K_0(s,s') * chainSum m (K ∘ succ) s'
    -- = ∑ s', K_0(s,s') * 1  (by IH)
    -- = ∑ s', K_0(s,s') = 1  (by K_sum_one)
    have h_ih : ∀ s', chainSum m (fun j => K j.succ) s' = 1 :=
      fun s' => ih
        (fun j => K j.succ)
        (fun i s₁ s₂ => _K_nonneg i.succ s₁ s₂)
        (fun i s₁ => K_sum_one i.succ s₁) s'
    simp_rw [h_ih, mul_one]
    exact K_sum_one ⟨0, Nat.zero_lt_succ m⟩ s

/-! ### Pi-Type Decomposition: Bridge from Fintype Sum to Chain Sum

The chain sum `chainSum_eq_one` proves the mathematical content:
the telescoping product sums to 1. Below we construct the bridge
connecting the Fintype sum over `Fin (H+1) → S` to `chainSum`
using `Fin.consEquiv` for Pi-type decomposition. -/

/-- Decompose a sum over `Fin (n+1) → S` into a double sum via
    `Fin.consEquiv`: peel off the first coordinate. -/
private lemma sum_piFinSucc {S : Type} [Fintype S] (n : ℕ)
    (f : (Fin (n + 1) → S) → ℝ) :
    ∑ τ : Fin (n + 1) → S, f τ =
    ∑ s : S, ∑ τ' : Fin n → S, f (@Fin.cons n (fun _ => S) s τ') := by
  have : ∑ τ : Fin (n + 1) → S, f τ =
      ∑ p : S × (Fin n → S), f (@Fin.cons n (fun _ => S) p.1 p.2) := by
    apply Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => S)).symm
    intro τ; simp [Fin.consEquiv]
  rw [this, Fintype.sum_prod_type]

/-- Recursive chain product matching `chainSum`'s recursion.
    Given an initial state `s₀` and subsequent states `τ : Fin n → S`,
    computes the product `K₀(s₀,τ₀) · K₁(τ₀,τ₁) · ... · K_{n-1}(τ_{n-2},τ_{n-1})`. -/
private def chainProd {S : Type} [Fintype S]
    (n : ℕ) (K : Fin n → S → S → ℝ) (s₀ : S) (τ : Fin n → S) : ℝ :=
  match n with
  | 0 => 1
  | n + 1 => K ⟨0, Nat.zero_lt_succ n⟩ s₀ (τ ⟨0, Nat.zero_lt_succ n⟩) *
      chainProd n (fun j => K j.succ) (τ ⟨0, Nat.zero_lt_succ n⟩)
        (fun j => τ j.succ)

/-- The sum of `chainProd` over all trajectory suffixes equals `chainSum`. -/
private theorem sum_chainProd_eq_chainSum {S : Type} [Fintype S]
    (n : ℕ) (K : Fin n → S → S → ℝ) (s₀ : S) :
    ∑ τ : Fin n → S, chainProd n K s₀ τ = chainSum n K s₀ := by
  induction n generalizing s₀ with
  | zero => simp [chainProd, chainSum]
  | succ m ih =>
    rw [sum_piFinSucc m]
    simp only [chainProd, chainSum, @Fin.cons_succ m (fun _ => S)]
    congr 1; ext s₁
    simp only [show ∀ (s : S) (τ : Fin m → S),
        @Fin.cons m (fun _ => S) s τ ⟨0, Nat.zero_lt_succ m⟩ = s from
        fun s τ => @Fin.cons_zero m (fun _ => S) s τ]
    rw [← Finset.mul_sum]
    congr 1
    exact ih (fun j => K j.succ) s₁

/-- For `σ : Fin (n+2) → S` and `i : Fin n`,
    `σ i.succ.castSucc = (Fin.tail σ) i.castSucc`. -/
private lemma sigma_succ_castSucc_eq_tail {S : Type} {n : ℕ}
    (σ : Fin (n + 2) → S) (i : Fin n) :
    σ i.succ.castSucc = Fin.tail σ i.castSucc := by
  simp [Fin.tail, Fin.castSucc_succ]

/-- A `Finset.prod` over transition kernels indexed by `Fin n` equals
    the recursively defined `chainProd`, connecting the two formulations. -/
private theorem prod_eq_chainProd {S : Type} [Fintype S]
    (n : ℕ) (K : Fin n → S → S → ℝ) (σ : Fin (n + 1) → S) :
    (∏ h : Fin n, K h (σ h.castSucc) (σ h.succ)) =
    chainProd n K (σ 0) (Fin.tail σ) := by
  induction n with
  | zero => simp [chainProd]
  | succ m ih =>
    simp only [chainProd]
    rw [Fin.prod_univ_succ]
    simp only [Fin.castSucc_zero]
    have h_succ0 : σ (Fin.succ (0 : Fin (m + 1))) =
        Fin.tail σ ⟨0, Nat.zero_lt_succ m⟩ := by
      simp [Fin.tail]
    rw [h_succ0]
    congr 1
    have h_rw : ∀ i : Fin m,
        K i.succ (σ i.succ.castSucc) (σ i.succ.succ) =
        (fun j => K j.succ) i ((Fin.tail σ) i.castSucc) ((Fin.tail σ) i.succ) := by
      intro i; simp only [sigma_succ_castSucc_eq_tail, Fin.tail]
    simp_rw [h_rw]
    exact ih (fun j => K j.succ) (Fin.tail σ)

/-- `trajectoryProb` expressed as a generic kernel product. -/
private lemma trajectoryProb_eq_kernelProd (π : M.TDPolicy) (σ : M.Trajectory) :
    M.trajectoryProb π σ =
    ∏ h : Fin M.H,
      (fun i s s' => M.P i s (π i s) s') h (σ h.castSucc) (σ h.succ) := by
  simp [trajectoryProb]

/-- **Trajectory probabilities conditioned on s₀ sum to 1.**

    ∑ τ, trajectoryProbFrom π s₀ τ = 1

    This is the key fact needed to construct the trajectory PMF.
    The proof decomposes the Fintype sum via `Fin.consEquiv`,
    connects the resulting product to `chainSum` via `chainProd`,
    then applies `chainSum_eq_one`. -/
theorem trajectoryProbFrom_sum_one (π : M.TDPolicy) (s₀ : M.S) :
    ∑ τ : M.Trajectory, M.trajectoryProbFrom π s₀ τ = 1 := by
  -- Step 1: decompose the sum by the initial state coordinate
  change ∑ τ : Fin (M.H + 1) → M.S, M.trajectoryProbFrom π s₀ τ = 1
  rw [sum_piFinSucc M.H]
  simp only [trajectoryProbFrom]
  -- (cons s τ') ⟨0, _⟩ = s
  simp only [show ∀ (s : M.S) (τ' : Fin M.H → M.S),
    @Fin.cons M.H (fun _ => M.S) s τ' ⟨0, Nat.zero_lt_succ M.H⟩ = s from
    fun s τ' => @Fin.cons_zero M.H (fun _ => M.S) s τ']
  -- Step 2: extract the s = s₀ term
  rw [show (∑ s : M.S, ∑ τ' : Fin M.H → M.S,
    if s = s₀ then M.trajectoryProb π
      (@Fin.cons M.H (fun _ => M.S) s τ') else 0) =
    ∑ τ' : Fin M.H → M.S,
      M.trajectoryProb π (@Fin.cons M.H (fun _ => M.S) s₀ τ') from by
    rw [Finset.sum_comm]; congr 1; ext τ'
    simp [Finset.sum_ite_eq', Finset.mem_univ]]
  -- Step 3: rewrite trajectoryProb as kernel product, then apply bridge
  simp_rw [trajectoryProb_eq_kernelProd]
  simp_rw [prod_eq_chainProd M.H
    (fun i s s' => M.P i s (π i s) s')
    (@Fin.cons M.H (fun _ => M.S) s₀ _)]
  simp only [show ∀ (τ' : Fin M.H → M.S),
    @Fin.cons M.H (fun _ => M.S) s₀ τ' 0 = s₀ from
    fun _ => @Fin.cons_zero M.H (fun _ => M.S) s₀ _]
  simp only [show ∀ (τ' : Fin M.H → M.S),
    Fin.tail (@Fin.cons M.H (fun _ => M.S) s₀ τ') = τ' from
    fun τ' => by ext i; simp [Fin.tail, @Fin.cons_succ M.H (fun _ => M.S)]]
  -- Step 4: sum of chainProd = chainSum = 1
  rw [sum_chainProd_eq_chainSum]
  exact chainSum_eq_one M.H
    (fun i s s' => M.P i s (π i s) s')
    (fun i s s' => M.P_nonneg i s (π i s) s')
    (fun i s => M.P_sum_one i s (π i s)) s₀

/-! ### Trajectory PMF and Measure

Construct the PMF and probability measure on trajectories from
trajectoryProbFrom, conditioned on a fixed initial state s₀. -/

/-- The trajectory PMF: a probability mass function on `Fin (H+1) → S`
    conditioned on initial state s₀.

    The mass of trajectory τ is:
    - `trajectoryProb π τ` if τ(0) = s₀
    - 0 otherwise -/
def trajectoryPMF (π : M.TDPolicy) (s₀ : M.S)
    (h_sum : ∑ τ : M.Trajectory, M.trajectoryProbFrom π s₀ τ = 1) :
    PMF M.Trajectory :=
  PMF.ofFintype
    (fun τ => ENNReal.ofReal (M.trajectoryProbFrom π s₀ τ))
    (by
      rw [← ENNReal.ofReal_sum_of_nonneg
        (fun τ _ => M.trajectoryProbFrom_nonneg π s₀ τ)]
      simp [h_sum])

/-- The trajectory PMF assigns the correct probability to each trajectory. -/
lemma trajectoryPMF_apply (π : M.TDPolicy) (s₀ : M.S)
    (h_sum : ∑ τ : M.Trajectory, M.trajectoryProbFrom π s₀ τ = 1)
    (τ : M.Trajectory) :
    M.trajectoryPMF π s₀ h_sum τ =
      ENNReal.ofReal (M.trajectoryProbFrom π s₀ τ) := by
  simp [trajectoryPMF, PMF.ofFintype_apply]

/-- The trajectory probability measure: `PMF.toMeasure` applied to
    the trajectory PMF. This is a genuine probability measure on
    the trajectory space `Fin (H+1) → S`. -/
def trajectoryMeasure (π : M.TDPolicy) (s₀ : M.S)
    (h_sum : ∑ τ : M.Trajectory, M.trajectoryProbFrom π s₀ τ = 1) :
    Measure M.Trajectory :=
  (M.trajectoryPMF π s₀ h_sum).toMeasure

/-- **The trajectory measure is a probability measure.** -/
instance trajectoryMeasure_isProbability (π : M.TDPolicy) (s₀ : M.S)
    (h_sum : ∑ τ : M.Trajectory, M.trajectoryProbFrom π s₀ τ = 1) :
    IsProbabilityMeasure (M.trajectoryMeasure π s₀ h_sum) :=
  PMF.toMeasure.isProbabilityMeasure _

/-! ### Trajectory Expectation

Define the trajectory expectation as a Bochner integral and prove
it equals the finite sum weighted by trajectory probabilities. -/

/-- Trajectory expectation: the Bochner integral of f with respect
    to the trajectory measure.
    E_π[f] = ∫ f dμ_π -/
def trajectoryExpectation (π : M.TDPolicy) (s₀ : M.S)
    (h_sum : ∑ τ : M.Trajectory, M.trajectoryProbFrom π s₀ τ = 1)
    (f : M.Trajectory → ℝ) : ℝ :=
  ∫ τ, f τ ∂(M.trajectoryMeasure π s₀ h_sum)

/-- **Trajectory expectation equals the finite sum.**

    ∫ f dμ_π = ∑ τ, trajectoryProbFrom π s₀ τ · f(τ)

    This connects the Bochner integral to the finite-sum computation
    in MDPFiltration.lean. -/
theorem trajectoryExpectation_eq_sum (π : M.TDPolicy) (s₀ : M.S)
    (h_sum : ∑ τ : M.Trajectory, M.trajectoryProbFrom π s₀ τ = 1)
    (f : M.Trajectory → ℝ) :
    M.trajectoryExpectation π s₀ h_sum f =
      ∑ τ, (M.trajectoryProbFrom π s₀ τ) * f τ := by
  simp only [trajectoryExpectation, trajectoryMeasure]
  rw [PMF.integral_eq_sum]
  congr 1; ext τ
  rw [M.trajectoryPMF_apply]
  rw [ENNReal.toReal_ofReal (M.trajectoryProbFrom_nonneg π s₀ τ)]
  simp [smul_eq_mul]

/-! ### Martingale Difference Sum Properties

Using the trajectory measure, we prove that the sum of martingale
differences has zero expectation and bounded variance. -/

/-- The weighted sum of martingale differences along a trajectory,
    using the trajectory probability from a fixed initial state. -/
def weightedMartingaleDiffSum (π : M.TDPolicy) (V : Fin M.H → M.S → ℝ)
    (s₀ : M.S)
    (h_sum : ∑ τ : M.Trajectory, M.trajectoryProbFrom π s₀ τ = 1) :
    ℝ :=
  M.trajectoryExpectation π s₀ h_sum (M.martingaleDiffSum π V)

/-- **E_π[∑_h D_h] = 0**: The expected sum of martingale differences
    is zero under the trajectory measure.

    This follows from the zero conditional mean property of each
    martingale difference D_h = V(s_{h+1}) - E[V(s_{h+1})|s_h].

    The proof expands the expectation as a finite sum and uses
    the fact that each D_h has zero conditional mean (proved in
    MDPFiltration.lean). -/
theorem martingaleDiffSum_expectation_zero
    (π : M.TDPolicy) (V : Fin M.H → M.S → ℝ) (s₀ : M.S)
    (h_sum : ∑ τ : M.Trajectory, M.trajectoryProbFrom π s₀ τ = 1)
    -- Hypothesis: tower of expectations for the trajectory measure.
    -- Each D_h has zero conditional mean (proved in MDPFiltration.lean
    -- as martingaleDiff_condExpect_zero). Connecting this to the full
    -- trajectory-weighted sum requires marginalizing out all other
    -- time steps, which needs a Pi-type decomposition at each step.
    (h_tower : ∀ h : Fin M.H,
      ∑ τ : M.Trajectory, M.trajectoryProbFrom π s₀ τ *
        M.martingaleDiff π (V h) h (τ h.castSucc) (τ h.succ) = 0) :
    M.weightedMartingaleDiffSum π V s₀ h_sum = 0 := by
  simp only [weightedMartingaleDiffSum, trajectoryExpectation_eq_sum,
    martingaleDiffSum]
  -- ∑ τ, P(τ) * ∑_h D_h(τ) = ∑_h ∑_τ P(τ) * D_h(τ) = ∑_h 0 = 0
  rw [show (∑ τ, M.trajectoryProbFrom π s₀ τ *
      ∑ h : Fin M.H, M.martingaleDiff π (V h) h (τ h.castSucc) (τ h.succ)) =
    ∑ h : Fin M.H, ∑ τ, M.trajectoryProbFrom π s₀ τ *
      M.martingaleDiff π (V h) h (τ h.castSucc) (τ h.succ) from by
    rw [Finset.sum_comm]
    congr 1; ext τ
    rw [Finset.mul_sum]]
  simp_rw [h_tower, Finset.sum_const_zero]

/-- **E_π[(∑_h D_h)²] ≤ H · B²**: The variance of the martingale
    difference sum is bounded.

    For value functions V_h bounded in [0, B], the expected squared
    sum of martingale differences is at most H · B².

    This is the key step for the Azuma-Hoeffding bound. It uses:
    - Each D_h is bounded by B (from martingaleDiff_bounded)
    - The cross terms vanish by the martingale property
    - Each squared term contributes at most B² -/
theorem martingaleDiffSum_variance_bounded
    (π : M.TDPolicy) (V : Fin M.H → M.S → ℝ)
    (B : ℝ) (_hB : 0 ≤ B)
    (_hV_nn : ∀ h s, 0 ≤ V h s) (hV_le : ∀ h s, V h s ≤ B)
    (s₀ : M.S)
    (h_sum : ∑ τ : M.Trajectory, M.trajectoryProbFrom π s₀ τ = 1)
    -- Hypothesis: cross-term cancellation E[D_h * D_{h'}] = 0 for h != h'.
    -- This follows from the tower of expectations applied to the
    -- trajectory measure: E[D_h * D_{h'} | F_{max(h,h')}] = 0.
    -- Requires the same Pi-type marginalization as h_tower above.
    (h_cross_zero :
      M.trajectoryExpectation π s₀ h_sum
        (fun τ => (M.martingaleDiffSum π V τ) ^ 2) =
      ∑ h : Fin M.H, M.trajectoryExpectation π s₀ h_sum
        (fun τ => (M.martingaleDiff π (V h) h (τ h.castSucc) (τ h.succ)) ^ 2)) :
    M.trajectoryExpectation π s₀ h_sum
      (fun τ => (M.martingaleDiffSum π V τ) ^ 2) ≤
      (M.H : ℝ) * B ^ 2 := by
  rw [h_cross_zero]
  -- Each E[D_h²] ≤ B² since |D_h| ≤ B
  calc ∑ h : Fin M.H, M.trajectoryExpectation π s₀ h_sum
        (fun τ => (M.martingaleDiff π (V h) h (τ h.castSucc) (τ h.succ)) ^ 2)
      ≤ ∑ _h : Fin M.H, B ^ 2 := by
        apply Finset.sum_le_sum
        intro h _
        rw [trajectoryExpectation_eq_sum]
        -- ∑ τ, P(τ) * D_h²(τ) ≤ ∑ τ, P(τ) * B²
        calc ∑ τ, M.trajectoryProbFrom π s₀ τ *
              (M.martingaleDiff π (V h) h (τ h.castSucc) (τ h.succ)) ^ 2
            ≤ ∑ τ, M.trajectoryProbFrom π s₀ τ * B ^ 2 := by
              apply Finset.sum_le_sum
              intro τ _
              apply mul_le_mul_of_nonneg_left _ (M.trajectoryProbFrom_nonneg π s₀ τ)
              exact M.martingaleDiffSum_sq_bounded π V B _hB _hV_nn hV_le h _ _
          _ = B ^ 2 * ∑ τ, M.trajectoryProbFrom π s₀ τ := by
              rw [Finset.mul_sum]; congr 1; ext τ; ring
          _ = B ^ 2 := by rw [h_sum, mul_one]
    _ = (M.H : ℝ) * B ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ### Azuma-Hoeffding Tail Bound for Trajectories

The probability tail bound for the martingale difference sum.
This requires constructing the filtration and connecting to Mathlib's
Azuma-Hoeffding inequality, so we take it as a conditional hypothesis. -/

-- Hypothesis: Azuma-Hoeffding tail bound.
-- Discharging this requires constructing a Filtration on the trajectory
-- space, showing the martingale differences are adapted and conditionally
-- sub-Gaussian, then applying Mathlib's Azuma-Hoeffding
-- (measure_sum_ge_le_of_hasCondSubgaussianMGF). The algebraic
-- ingredients (zero conditional mean, bounded differences) are proved
-- in MDPFiltration.lean.

/-- **Azuma-Hoeffding for MDP trajectories.**

    μ_π {τ | |∑_h D_h(τ)| ≥ ε} ≤ 2 · exp(-ε²/(2·H·B²))

    This is the concentration inequality for the sum of martingale
    differences along a trajectory. The algebraic ingredients (zero
    conditional mean, bounded differences) are proved in
    MDPFiltration.lean. The connection to Mathlib's Azuma-Hoeffding
    requires constructing the trajectory filtration. -/
theorem trajectoryAzumaHoeffding
    (π : M.TDPolicy) (V : Fin M.H → M.S → ℝ)
    (B : ℝ) (hB : 0 < B)
    (hV_nn : ∀ h s, 0 ≤ V h s) (hV_le : ∀ h s, V h s ≤ B)
    (ε : ℝ) (hε : 0 < ε) (_hH : 0 < M.H)
    (s₀ : M.S)
    (h_sum : ∑ τ : M.Trajectory, M.trajectoryProbFrom π s₀ τ = 1)
    -- Hypothesis: the Azuma-Hoeffding tail bound itself.
    -- See block comment above for what is needed to discharge this.
    (h_azuma_tail :
      (M.trajectoryMeasure π s₀ h_sum).real
        {τ | ε ≤ |M.martingaleDiffSum π V τ|} ≤
      2 * Real.exp (-ε ^ 2 / (2 * (M.H : ℝ) * B ^ 2))) :
    -- Conclusion: the tail bound holds AND all algebraic ingredients verified
    (M.trajectoryMeasure π s₀ h_sum).real
      {τ | ε ≤ |M.martingaleDiffSum π V τ|} ≤
      2 * Real.exp (-ε ^ 2 / (2 * (M.H : ℝ) * B ^ 2)) ∧
    (∀ h : Fin M.H, ∀ s : M.S,
      M.condExpect h s (π h s) (M.martingaleDiff π (V h) h s) = 0) ∧
    (∀ h : Fin M.H, ∀ s s' : M.S,
      |M.martingaleDiff π (V h) h s s'| ≤ B) ∧
    0 < ε := by
  exact ⟨h_azuma_tail,
    fun h s => M.martingaleDiff_condExpect_zero π (V h) h s,
    fun h s s' => M.martingaleDiff_bounded π (V h) B hB.le (hV_nn h) (hV_le h) h s s',
    hε⟩

/-! ### UCBVI High-Probability Bound

From the Azuma-Hoeffding tail bound combined with a union bound
over H steps, we derive the UCBVI high-probability confidence bound.

Setting ε = B√(2H·log(2H/δ)):
  P(∀ h, |∑_{h'≤h} D_{h'}| ≤ β) ≥ 1 - δ

where β = ucbviConfidenceWidth B H δ. -/

-- Hypothesis: UCBVI high-probability event from Azuma-Hoeffding + union bound.
-- Requires per-step Azuma-Hoeffding tail bounds (h_azuma_tail above)
-- combined with a union bound over H steps: P(exists h, bad_h) <= sum_h P(bad_h).
-- The confidence width computation is proved in MDPFiltration.lean
-- (ucbvi_bonus_from_azuma).

/-- **UCBVI high-probability bound.**

    With β = B·√(2H·log(2H/δ)):
    μ_π {τ | ∀ h, |∑_{h'≤h} D_{h'}(τ)| ≤ β} ≥ 1 - δ

    This combines the Azuma-Hoeffding tail bound with a union bound
    over H steps. The confidence width β = ucbviConfidenceWidth B H δ
    is defined in MDPFiltration.lean. -/
theorem ucbvi_high_probability
    (π : M.TDPolicy) (V : Fin M.H → M.S → ℝ)
    (B : ℝ) (hB : 0 < B)
    (_hV_nn : ∀ h s, 0 ≤ V h s) (_hV_le : ∀ h s, V h s ≤ B)
    (δ : ℝ) (hδ : 0 < δ) (_hδ_le : δ ≤ 1)
    (hH : 0 < M.H) (hδH : δ < 2 * (M.H : ℝ))
    (s₀ : M.S)
    (h_sum : ∑ τ : M.Trajectory, M.trajectoryProbFrom π s₀ τ = 1)
    -- Hypothesis: the high-probability event itself.
    -- See block comment above for what is needed to discharge this.
    (h_high_prob :
      1 - δ ≤ (M.trajectoryMeasure π s₀ h_sum).real
        {τ | ∀ h : Fin M.H, |∑ h' ∈ Finset.univ.filter (· ≤ h),
          M.martingaleDiff π (V h') h' (τ h'.castSucc) (τ h'.succ)| ≤
          ucbviConfidenceWidth B M.H δ}) :
    -- Conclusion: the high-probability bound holds with correct width
    (1 - δ ≤ (M.trajectoryMeasure π s₀ h_sum).real
      {τ | ∀ h : Fin M.H, |∑ h' ∈ Finset.univ.filter (· ≤ h),
        M.martingaleDiff π (V h') h' (τ h'.castSucc) (τ h'.succ)| ≤
        ucbviConfidenceWidth B M.H δ}) ∧
    0 < ucbviConfidenceWidth B M.H δ ∧
    ucbviConfidenceWidth B M.H δ ^ 2 =
      B ^ 2 * (2 * (M.H : ℝ) * Real.log (2 * (M.H : ℝ) / δ)) := by
  have h_bonus := M.ucbvi_bonus_from_azuma B hB δ hδ hH hδH
  exact ⟨h_high_prob, h_bonus.1, h_bonus.2⟩

/-! ### Summary of the Measure-Theoretic Bridge

The module provides the following bridge from MDPFiltration.lean's
finitary definitions to Mathlib's measure theory:

1. **trajectoryPMF / trajectoryMeasure**: Genuine probability measure
   on trajectories, constructed from transition probabilities via
   PMF.toMeasure.

2. **trajectoryExpectation_eq_sum**: The Bochner integral equals the
   finite weighted sum, connecting Mathlib's integral API to the
   finitary computations in MDPFiltration.lean.

3. **Conditional hypotheses**: The tail bounds (Azuma-Hoeffding,
   UCBVI high-probability) are taken as conditional hypotheses
   parameterized by the filtration construction. The algebraic
   ingredients are all verified from MDPFiltration.lean.

The remaining gap is the trajectory filtration construction:
given the trajectory measure, construct a `Filtration ℕ mΩ`
where ℱ_h = σ(τ(0), ..., τ(h)), and verify that the martingale
differences are adapted and conditionally sub-Gaussian. This
would discharge the conditional hypotheses via
`measure_sum_ge_le_of_hasCondSubgaussianMGF` from Mathlib. -/

end FiniteHorizonMDP

end
