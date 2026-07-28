import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open Finset BigOperators

noncomputable section

namespace FiniteCPT

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]

/-- The probability mass of the finite event selected at level `k`. -/
def tailMass (p : ι → ℝ) (event : κ → Finset ι) (k : κ) : ℝ :=
  ∑ i ∈ event k, p i

/-- A finite weighted-tail gain functional.

`width k` is the length of a utility interval on which `event k` is the
upper-tail event.  For normalized nonnegative masses and the utility-induced
tail events, this is the exact finite-support CPT tail integral. -/
def gain (w : ℝ → ℝ) (width : κ → ℝ) (event : κ → Finset ι)
    (p : ι → ℝ) : ℝ :=
  ∑ k, width k * w (tailMass p event k)

/-- The gain-side CPT influence assigned to atom `i`. -/
def influence (wPrime : ℝ → ℝ) (width : κ → ℝ)
    (event : κ → Finset ι) (p : ι → ℝ) (i : ι) : ℝ :=
  ∑ k, if i ∈ event k then
    width k * wPrime (tailMass p event k)
  else 0

/-- The derivative of a finite weighted-tail gain is the atomwise derivative
weighted by its tail influence.  For probability masses and utility-induced
events, this is the finite chain-rule and Fubini step behind CPT gradients. -/
theorem hasDerivAt_gain
    (w wPrime : ℝ → ℝ) (width : κ → ℝ) (event : κ → Finset ι)
    (p : ι → ℝ → ℝ) (p' : ι → ℝ) (θ : ℝ)
    (hw : ∀ k, HasDerivAt w
      (wPrime (tailMass (fun i => p i θ) event k))
      (tailMass (fun i => p i θ) event k))
    (hp : ∀ i, HasDerivAt (p i) (p' i) θ) :
    HasDerivAt
      (fun t => gain w width event (fun i => p i t))
      (∑ i, p' i * influence wPrime width event (fun j => p j θ) i)
      θ := by
  have htail : ∀ k, HasDerivAt
      (fun t => tailMass (fun i => p i t) event k)
      (tailMass p' event k) θ := by
    intro k
    unfold tailMass
    exact HasDerivAt.fun_sum (fun i hi => hp i)
  have hlevel : ∀ k, HasDerivAt
      (fun t => width k * w (tailMass (fun i => p i t) event k))
      (width k * (wPrime (tailMass (fun i => p i θ) event k) *
        tailMass p' event k)) θ := by
    intro k
    have hcomp : HasDerivAt
        (fun t => w (tailMass (fun i => p i t) event k))
        (wPrime (tailMass (fun i => p i θ) event k) * tailMass p' event k)
        θ := by
      simpa only [Function.comp_apply] using
        HasDerivAt.comp θ (hw k) (htail k)
    exact HasDerivAt.const_mul (width k) hcomp
  unfold gain
  convert HasDerivAt.fun_sum (fun k hk => hlevel k) using 1
  unfold influence tailMass
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Score form of the finite weighted-tail gradient.

If each atom derivative factors as `p' i = p i * score i`, the
weighted-tail derivative is the finite sum of `mass * influence * score`. -/
theorem hasDerivAt_gain_score
    (w wPrime : ℝ → ℝ) (width : κ → ℝ) (event : κ → Finset ι)
    (p : ι → ℝ → ℝ) (p' score : ι → ℝ) (θ : ℝ)
    (hw : ∀ k, HasDerivAt w
      (wPrime (tailMass (fun i => p i θ) event k))
      (tailMass (fun i => p i θ) event k))
    (hp : ∀ i, HasDerivAt (p i) (p' i) θ)
    (hscore : ∀ i, p' i = p i θ * score i) :
    HasDerivAt
      (fun t => gain w width event (fun i => p i t))
      (∑ i, p i θ *
        (influence wPrime width event (fun j => p j θ) i * score i))
      θ := by
  convert hasDerivAt_gain w wPrime width event p p' θ hw hp using 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [hscore i]
  ring

/-- A two-sided finite weighted-tail value: gain transform minus loss transform. -/
def value (wPlus wMinus : ℝ → ℝ)
    (gainWidth : κ → ℝ) (gainEvent : κ → Finset ι)
    (lossWidth : κ → ℝ) (lossEvent : κ → Finset ι)
    (p : ι → ℝ) : ℝ :=
  gain wPlus gainWidth gainEvent p -
    gain wMinus lossWidth lossEvent p

/-- The net CPT influence is gain influence minus loss influence. -/
def netInfluence (wPrimePlus wPrimeMinus : ℝ → ℝ)
    (gainWidth : κ → ℝ) (gainEvent : κ → Finset ι)
    (lossWidth : κ → ℝ) (lossEvent : κ → Finset ι)
    (p : ι → ℝ) (i : ι) : ℝ :=
  influence wPrimePlus gainWidth gainEvent p i -
    influence wPrimeMinus lossWidth lossEvent p i

/-- Two-sided finite weighted-tail score-gradient identity, coordinatewise.

For a scalar policy parameter (or one coordinate/direction of a vector
parameter), the derivative of the gain-minus-loss transform is the finite
weighted sum of the net influence times the atom score. -/
theorem hasDerivAt_value_score
    (wPlus wPrimePlus wMinus wPrimeMinus : ℝ → ℝ)
    (gainWidth : κ → ℝ) (gainEvent : κ → Finset ι)
    (lossWidth : κ → ℝ) (lossEvent : κ → Finset ι)
    (p : ι → ℝ → ℝ) (p' score : ι → ℝ) (θ : ℝ)
    (hwPlus : ∀ k, HasDerivAt wPlus
      (wPrimePlus (tailMass (fun i => p i θ) gainEvent k))
      (tailMass (fun i => p i θ) gainEvent k))
    (hwMinus : ∀ k, HasDerivAt wMinus
      (wPrimeMinus (tailMass (fun i => p i θ) lossEvent k))
      (tailMass (fun i => p i θ) lossEvent k))
    (hp : ∀ i, HasDerivAt (p i) (p' i) θ)
    (hscore : ∀ i, p' i = p i θ * score i) :
    HasDerivAt
      (fun t => value wPlus wMinus gainWidth gainEvent
        lossWidth lossEvent (fun i => p i t))
      (∑ i, p i θ *
        (netInfluence wPrimePlus wPrimeMinus gainWidth gainEvent
          lossWidth lossEvent (fun j => p j θ) i * score i))
      θ := by
  have hGain := hasDerivAt_gain_score wPlus wPrimePlus gainWidth gainEvent
    p p' score θ hwPlus hp hscore
  have hLoss := hasDerivAt_gain_score wMinus wPrimeMinus lossWidth lossEvent
    p p' score θ hwMinus hp hscore
  unfold value
  convert hGain.sub hLoss using 1
  unfold netInfluence
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- A finite-horizon trajectory mass: a parameter-independent base mass
times the product of its per-step policy probabilities. -/
def trajectoryMass {T : Type*} [Fintype T]
    (base : ℝ) (policy : T → ℝ → ℝ) (θ : ℝ) : ℝ :=
  base * ∏ t, policy t θ

/-- The derivative of a finite product factorizes into the product times
the sum of its factor scores.  The score relation is stated without logs,
so it also applies to any chosen continuous extension at zero mass. -/
theorem hasDerivAt_trajectoryMass_score
    {T : Type*} [Fintype T]
    (base : ℝ) (policy : T → ℝ → ℝ)
    (policy' score : T → ℝ) (θ : ℝ)
    (hpolicy : ∀ t, HasDerivAt (policy t) (policy' t) θ)
    (hscore : ∀ t, policy' t = policy t θ * score t) :
    HasDerivAt
      (trajectoryMass base policy)
      (trajectoryMass base policy θ * ∑ t, score t)
      θ := by
  classical
  have hprod : HasDerivAt
      (fun x => ∏ t, policy t x)
      ((∏ t, policy t θ) * ∑ t, score t)
      θ := by
    convert HasDerivAt.fun_finset_prod
      (u := Finset.univ) (fun t ht => hpolicy t) using 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    rw [hscore t]
    simp only [smul_eq_mul]
    rw [← mul_assoc, Finset.prod_erase_mul _ _ ht]
  unfold trajectoryMass
  convert HasDerivAt.const_mul base hprod using 1
  ring

/-- Finite weighted-tail gradient for factored finite trajectories.

The parameter-independent base can contain initial-state and transition
factors.  Each per-step factor derivative is represented by a score, and the
resulting product score is their finite sum.  Probability factors specialize
the statement to the finite-support CPT policy-gradient setting. -/
theorem hasDerivAt_value_trajectory_score
    {T : Type*} [Fintype T]
    (wPlus wPrimePlus wMinus wPrimeMinus : ℝ → ℝ)
    (gainWidth : κ → ℝ) (gainEvent : κ → Finset ι)
    (lossWidth : κ → ℝ) (lossEvent : κ → Finset ι)
    (base : ι → ℝ) (policy : ι → T → ℝ → ℝ)
    (policy' score : ι → T → ℝ) (θ : ℝ)
    (hwPlus : ∀ k, HasDerivAt wPlus
      (wPrimePlus (tailMass
        (fun i => trajectoryMass (base i) (policy i) θ) gainEvent k))
      (tailMass (fun i => trajectoryMass (base i) (policy i) θ) gainEvent k))
    (hwMinus : ∀ k, HasDerivAt wMinus
      (wPrimeMinus (tailMass
        (fun i => trajectoryMass (base i) (policy i) θ) lossEvent k))
      (tailMass (fun i => trajectoryMass (base i) (policy i) θ) lossEvent k))
    (hpolicy : ∀ i t, HasDerivAt (policy i t) (policy' i t) θ)
    (hscore : ∀ i t, policy' i t = policy i t θ * score i t) :
    HasDerivAt
      (fun x => value wPlus wMinus gainWidth gainEvent lossWidth lossEvent
        (fun i => trajectoryMass (base i) (policy i) x))
      (∑ i, trajectoryMass (base i) (policy i) θ *
        (netInfluence wPrimePlus wPrimeMinus gainWidth gainEvent
          lossWidth lossEvent
          (fun j => trajectoryMass (base j) (policy j) θ) i *
          ∑ t, score i t))
      θ := by
  classical
  let trajectoryDeriv : ι → ℝ := fun i =>
    trajectoryMass (base i) (policy i) θ * ∑ t, score i t
  have hp : ∀ i, HasDerivAt
      (trajectoryMass (base i) (policy i)) (trajectoryDeriv i) θ := by
    intro i
    exact hasDerivAt_trajectoryMass_score (base i) (policy i)
      (policy' i) (score i) θ (hpolicy i) (hscore i)
  apply hasDerivAt_value_score wPlus wPrimePlus wMinus wPrimeMinus
    gainWidth gainEvent lossWidth lossEvent
    (fun i => trajectoryMass (base i) (policy i))
    trajectoryDeriv (fun i => ∑ t, score i t) θ
    hwPlus hwMinus hp
  intro i
  rfl

/-- Finite weighted-tail trajectory gradient with genuine log-factor scores.

The nonzero hypothesis is the support condition needed for every displayed
log derivative to exist.  For normalized trajectory masses and utility-tail
events, this specializes to the coordinatewise finite-trajectory form of
Lepel--Barakat (2026), Theorem 3, with the missing support condition explicit. -/
theorem finite_weighted_tail_policy_gradient
    {T : Type*} [Fintype T]
    (wPlus wPrimePlus wMinus wPrimeMinus : ℝ → ℝ)
    (gainWidth : κ → ℝ) (gainEvent : κ → Finset ι)
    (lossWidth : κ → ℝ) (lossEvent : κ → Finset ι)
    (base : ι → ℝ) (policy : ι → T → ℝ → ℝ)
    (policy' : ι → T → ℝ) (θ : ℝ)
    (hwPlus : ∀ k, HasDerivAt wPlus
      (wPrimePlus (tailMass
        (fun i => trajectoryMass (base i) (policy i) θ) gainEvent k))
      (tailMass (fun i => trajectoryMass (base i) (policy i) θ) gainEvent k))
    (hwMinus : ∀ k, HasDerivAt wMinus
      (wPrimeMinus (tailMass
        (fun i => trajectoryMass (base i) (policy i) θ) lossEvent k))
      (tailMass (fun i => trajectoryMass (base i) (policy i) θ) lossEvent k))
    (hpolicy : ∀ i t, HasDerivAt (policy i t) (policy' i t) θ)
    (hnonzero : ∀ i t, policy i t θ ≠ 0) :
    HasDerivAt
      (fun x => value wPlus wMinus gainWidth gainEvent lossWidth lossEvent
        (fun i => trajectoryMass (base i) (policy i) x))
      (∑ i, trajectoryMass (base i) (policy i) θ *
        (netInfluence wPrimePlus wPrimeMinus gainWidth gainEvent
          lossWidth lossEvent
          (fun j => trajectoryMass (base j) (policy j) θ) i *
          ∑ t, deriv (fun x => Real.log (policy i t x)) θ))
      θ := by
  classical
  apply hasDerivAt_value_trajectory_score wPlus wPrimePlus wMinus
    wPrimeMinus gainWidth gainEvent lossWidth lossEvent base policy policy'
    (fun i t => deriv (fun x => Real.log (policy i t x)) θ) θ
    hwPlus hwMinus hpolicy
  intro i t
  have hlog := (hpolicy i t).log (hnonzero i t)
  rw [hlog.deriv]
  field_simp [hnonzero i t]

end FiniteCPT

