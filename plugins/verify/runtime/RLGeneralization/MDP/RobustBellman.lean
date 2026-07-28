/-
# Robust Bellman Operators over Row-Uncertainty Sets

Infrastructure for robust (distributionally ambiguous) MDPs: the transition
row at each state–action pair is only known to lie in an uncertainty set
`U s a ⊆ Δ(S)`. The robust Bellman optimality operator backs up the
worst-case (infimum) transition row at each `(s, a)`.

## Main Results

* `abs_csInf_image_sub_csInf_image_le` - the infimum over a nonempty set is
  nonexpansive under uniform perturbation: if `|f x - g x| ≤ ε` on `s`, then
  `|inf f(s) - inf g(s)| ≤ ε`. (Generic; the inf-side analog of
  `FiniteMDP.abs_sup_sub_sup_le`.)
* `robustBellmanOp_contraction` - the robust Bellman optimality operator is a
  γ-contraction in the sup norm, for ANY family of nonempty row-uncertainty
  sets inside the simplex.
* `robustFixedPoint_isFixedPt` / `robustFixedPoint_unique` /
  `tendsto_iterate_robustOpVSpace` - existence, uniqueness, and value-iteration
  convergence of the robust fixed point, via Banach on `PiLp ∞`.
* `IsRectangular` / `rowProjection_setProd` - (s,a)-rectangularity of a joint
  uncertainty set, and the fact that a product of row sets is rectangular with
  the expected row projections.

## Caveat (why rectangularity is defined here)

The fixed point of the robust operator equals the worst case over a JOINT
kernel set `PSet` only when `PSet` is (s,a)-rectangular (Iyengar 2005; Nilim &
El Ghaoui 2005). For non-rectangular `PSet` the per-stage worst case is
strictly more adversarial than the global one and the identity fails — see
`runs/robust_vi_any_uncertainty_set_*_refute_*.lean` for a kernel-checked
counterexample. The contraction and fixed-point results in this file are
about the OPERATOR, which is well defined for any row family; identifying
its fixed point with `min_{P ∈ PSet} V^{π,P}` additionally needs
`IsRectangular PSet`.

## References

* [Iyengar, *Robust Dynamic Programming*, Math. OR 2005]
* [Nilim & El Ghaoui, *Robust Control of Markov Decision Processes with
  Uncertain Transition Matrices*, Oper. Res. 2005]
-/

import RLGeneralization.MDP.Resolvent
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Topology.MetricSpace.Contracting

open Finset BigOperators

noncomputable section

namespace RobustMDP

variable {S A : Type*} [Fintype S] [Nonempty S] [Fintype A] [Nonempty A]

/-! ### Infimum is nonexpansive under uniform perturbation -/

/-- If two functions are uniformly `ε`-close on a nonempty set, their infima
over that set are `ε`-close. Generic inf-side analog of
`FiniteMDP.abs_sup_sub_sup_le`; the algebraic heart of robust Bellman
contraction. -/
theorem abs_csInf_image_sub_csInf_image_le {α : Type*} {s : Set α}
    (hs : s.Nonempty) {f g : α → ℝ} {ε : ℝ}
    (hf : BddBelow (f '' s)) (hg : BddBelow (g '' s))
    (h : ∀ x ∈ s, |f x - g x| ≤ ε) :
    |sInf (f '' s) - sInf (g '' s)| ≤ ε := by
  have key : ∀ F G : α → ℝ, BddBelow (F '' s) →
      (∀ x ∈ s, F x ≤ G x + ε) → sInf (F '' s) ≤ sInf (G '' s) + ε := by
    intro F G hF hle
    rw [← sub_le_iff_le_add]
    apply le_csInf (hs.image G)
    rintro b ⟨x, hx, rfl⟩
    have h1 : sInf (F '' s) ≤ F x := csInf_le hF ⟨x, hx, rfl⟩
    linarith [hle x hx]
  have h1 : sInf (f '' s) ≤ sInf (g '' s) + ε :=
    key f g hf (fun x hx => by linarith [(abs_le.mp (h x hx)).2])
  have h2 : sInf (g '' s) ≤ sInf (f '' s) + ε :=
    key g f hg (fun x hx => by linarith [(abs_le.mp (h x hx)).1])
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-! ### Expected value under a transition row -/

/-- Expected value of `V` under the transition row `p`. -/
def rowVal (p V : S → ℝ) : ℝ := ∑ s', p s' * V s'

omit [Nonempty S] in
lemma rowVal_sub (p V₁ V₂ : S → ℝ) :
    rowVal p V₁ - rowVal p V₂ = rowVal p (fun s => V₁ s - V₂ s) := by
  unfold rowVal
  rw [← Finset.sum_sub_distrib]
  congr 1; ext s'; ring

/-- A simplex row keeps the expected value within the sup norm of `V`. -/
lemma abs_rowVal_le_supNorm (p V : S → ℝ) (hp : p ∈ stdSimplex ℝ S) :
    |rowVal p V| ≤ Finset.univ.sup' Finset.univ_nonempty (fun s => |V s|) :=
  FiniteMDP.abs_weighted_sum_le_bound p V _ hp.1 hp.2
    (fun s => Finset.le_sup' (fun s => |V s|) (Finset.mem_univ s))

/-- The image of a simplex-contained row set under `rowVal · V` is bounded
below (by `-‖V‖_∞`), so its infimum is well behaved. -/
lemma bddBelow_rowVal_image (V : S → ℝ) (U : Set (S → ℝ))
    (hU : U ⊆ stdSimplex ℝ S) :
    BddBelow ((fun p => rowVal p V) '' U) := by
  refine ⟨-(Finset.univ.sup' Finset.univ_nonempty (fun s => |V s|)), ?_⟩
  rintro x ⟨p, hp, rfl⟩
  have h := abs_rowVal_le_supNorm p V (hU hp)
  linarith [(abs_le.mp h).1]

/-! ### The robust Bellman optimality operator -/

variable (r : S → A → ℝ) (γ : ℝ) (U : S → A → Set (S → ℝ))

/-- Worst-case (robust) backup at `(s, a)`: the adversary picks the
transition row in `U s a` minimizing the expected continuation value. -/
def robustBackup (V : S → ℝ) (s : S) (a : A) : ℝ :=
  r s a + γ * sInf ((fun p => rowVal p V) '' U s a)

/-- The robust Bellman optimality operator:
`(T V)(s) = max_a [ r(s,a) + γ · inf_{p ∈ U s a} pᵀV ]`. -/
def robustBellmanOp (V : S → ℝ) : S → ℝ :=
  fun s => Finset.univ.sup' Finset.univ_nonempty (robustBackup r γ U V s)

/-- **The robust Bellman operator is `γ`-Lipschitz in sup norm** (hence a
contraction when `γ < 1` — see `robustOpVSpace_contracting`), for any family
of nonempty row-uncertainty sets contained in the simplex. The per-(s,a) map
is an infimum of `γ`-Lipschitz affine maps, hence `γ`-Lipschitz
(`abs_csInf_image_sub_csInf_image_le`); the finite max preserves the
constant (`FiniteMDP.abs_sup_sub_sup_le`). -/
theorem robustBellmanOp_contraction (hγ : 0 ≤ γ)
    (hU_ne : ∀ s a, (U s a).Nonempty)
    (hU_sub : ∀ s a, U s a ⊆ stdSimplex ℝ S)
    (V₁ V₂ : S → ℝ) :
    Finset.univ.sup' Finset.univ_nonempty
        (fun s => |robustBellmanOp r γ U V₁ s - robustBellmanOp r γ U V₂ s|) ≤
      γ * Finset.univ.sup' Finset.univ_nonempty (fun s => |V₁ s - V₂ s|) := by
  set D := Finset.univ.sup' Finset.univ_nonempty (fun s => |V₁ s - V₂ s|) with hD
  apply Finset.sup'_le
  intro s _
  refine le_trans (FiniteMDP.abs_sup_sub_sup_le _ _) ?_
  apply Finset.sup'_le
  intro a _
  have hdiff : robustBackup r γ U V₁ s a - robustBackup r γ U V₂ s a =
      γ * (sInf ((fun p => rowVal p V₁) '' U s a) -
           sInf ((fun p => rowVal p V₂) '' U s a)) := by
    unfold robustBackup; ring
  rw [hdiff, abs_mul, abs_of_nonneg hγ]
  apply mul_le_mul_of_nonneg_left _ hγ
  apply abs_csInf_image_sub_csInf_image_le (hU_ne s a)
    (bddBelow_rowVal_image V₁ (U s a) (hU_sub s a))
    (bddBelow_rowVal_image V₂ (U s a) (hU_sub s a))
  intro p hp
  rw [rowVal_sub]
  exact abs_rowVal_le_supNorm p _ (hU_sub s a hp)

/-! ### Banach: unique fixed point and value-iteration convergence -/

/-- The complete sup-norm model for state-value functions. -/
abbrev VSpace (S : Type*) [Fintype S] := PiLp (⊤ : ENNReal) (fun _ : S => ℝ)

/-- View a value function as a point of the complete `PiLp ∞` space. -/
def toVSpace (V : S → ℝ) : VSpace S := (WithLp.equiv (⊤ : ENNReal) _).symm V

/-- Forget a `PiLp ∞` point back to a value function. -/
def ofVSpace (x : VSpace S) : S → ℝ := fun s => x s

/-- The `PiLp ∞` metric is the finite sup distance. -/
lemma vSpace_dist_eq (x y : VSpace S) :
    dist x y = Finset.univ.sup' Finset.univ_nonempty (fun s => |x s - y s|) := by
  rw [PiLp.dist_eq_iSup,
      ← Finset.sup'_univ_eq_ciSup (f := fun s : S => dist (x s) (y s))]
  apply Finset.sup'_congr Finset.univ_nonempty rfl
  intro s _
  exact Real.dist_eq (x s) (y s)

/-- The robust Bellman operator transported to the complete `PiLp ∞` space. -/
def robustOpVSpace (x : VSpace S) : VSpace S :=
  toVSpace (robustBellmanOp r γ U (ofVSpace x))

lemma robustOpVSpace_dist_le (hγ : 0 ≤ γ)
    (hU_ne : ∀ s a, (U s a).Nonempty)
    (hU_sub : ∀ s a, U s a ⊆ stdSimplex ℝ S)
    (x y : VSpace S) :
    dist (robustOpVSpace r γ U x) (robustOpVSpace r γ U y) ≤ γ * dist x y := by
  rw [vSpace_dist_eq, vSpace_dist_eq]
  exact robustBellmanOp_contraction r γ U hγ hU_ne hU_sub
    (ofVSpace x) (ofVSpace y)

lemma robustOpVSpace_contracting (hγ : 0 ≤ γ) (hγ1 : γ < 1)
    (hU_ne : ∀ s a, (U s a).Nonempty)
    (hU_sub : ∀ s a, U s a ⊆ stdSimplex ℝ S) :
    ContractingWith ⟨γ, hγ⟩ (robustOpVSpace r γ U) := by
  refine ⟨hγ1, LipschitzWith.of_dist_le_mul ?_⟩
  intro x y
  simpa using robustOpVSpace_dist_le r γ U hγ hU_ne hU_sub x y

/-- The unique fixed point of the robust Bellman operator (robust value
iteration's limit), via Banach's fixed-point theorem. -/
def robustFixedPoint (hγ : 0 ≤ γ) (hγ1 : γ < 1)
    (hU_ne : ∀ s a, (U s a).Nonempty)
    (hU_sub : ∀ s a, U s a ⊆ stdSimplex ℝ S) : VSpace S :=
  ContractingWith.fixedPoint (robustOpVSpace r γ U)
    (robustOpVSpace_contracting r γ U hγ hγ1 hU_ne hU_sub)

theorem robustFixedPoint_isFixedPt (hγ : 0 ≤ γ) (hγ1 : γ < 1)
    (hU_ne : ∀ s a, (U s a).Nonempty)
    (hU_sub : ∀ s a, U s a ⊆ stdSimplex ℝ S) :
    Function.IsFixedPt (robustOpVSpace r γ U)
      (robustFixedPoint r γ U hγ hγ1 hU_ne hU_sub) :=
  ContractingWith.fixedPoint_isFixedPt
    (robustOpVSpace_contracting r γ U hγ hγ1 hU_ne hU_sub)

/-- Any fixed point of the robust Bellman operator is THE fixed point. -/
theorem robustFixedPoint_unique (hγ : 0 ≤ γ) (hγ1 : γ < 1)
    (hU_ne : ∀ s a, (U s a).Nonempty)
    (hU_sub : ∀ s a, U s a ⊆ stdSimplex ℝ S)
    {x : VSpace S} (hx : Function.IsFixedPt (robustOpVSpace r γ U) x) :
    x = robustFixedPoint r γ U hγ hγ1 hU_ne hU_sub :=
  (robustOpVSpace_contracting r γ U hγ hγ1 hU_ne hU_sub).fixedPoint_unique hx

/-- Robust value iteration converges to the robust fixed point from any
initial value function. -/
theorem tendsto_iterate_robustOpVSpace (hγ : 0 ≤ γ) (hγ1 : γ < 1)
    (hU_ne : ∀ s a, (U s a).Nonempty)
    (hU_sub : ∀ s a, U s a ⊆ stdSimplex ℝ S) (x : VSpace S) :
    Filter.Tendsto (fun n => (robustOpVSpace r γ U)^[n] x) Filter.atTop
      (nhds (robustFixedPoint r γ U hγ hγ1 hU_ne hU_sub)) :=
  ContractingWith.tendsto_iterate_fixedPoint
    (robustOpVSpace_contracting r γ U hγ hγ1 hU_ne hU_sub) x

/-- A priori geometric convergence rate for robust value iteration. -/
theorem apriori_dist_iterate_robustFixedPoint_le (hγ : 0 ≤ γ) (hγ1 : γ < 1)
    (hU_ne : ∀ s a, (U s a).Nonempty)
    (hU_sub : ∀ s a, U s a ⊆ stdSimplex ℝ S) (x : VSpace S) (n : ℕ) :
    dist ((robustOpVSpace r γ U)^[n] x)
        (robustFixedPoint r γ U hγ hγ1 hU_ne hU_sub) ≤
      dist x (robustOpVSpace r γ U x) * γ ^ n / (1 - γ) :=
  ContractingWith.apriori_dist_iterate_fixedPoint_le
    (robustOpVSpace_contracting r γ U hγ hγ1 hU_ne hU_sub) x n

/-! ### Linear payoffs on the simplex are maximized at a vertex -/

/-- The vertex (pure / deterministic) row concentrated at `a`. -/
def pureRow [DecidableEq S] (a : S) : S → ℝ := fun s => if s = a then 1 else 0

omit [Nonempty S] in
lemma pureRow_mem_stdSimplex [DecidableEq S] (a : S) :
    pureRow a ∈ stdSimplex ℝ S := by
  constructor
  · intro s
    unfold pureRow
    split <;> norm_num
  · simp [pureRow]

omit [Nonempty S] in
lemma rowVal_pureRow [DecidableEq S] (a : S) (V : S → ℝ) :
    rowVal (pureRow a) V = V a := by
  unfold rowVal pureRow
  simp [ite_mul]

/-- **A linear payoff on the probability simplex attains its maximum at a
vertex**: the supremum of `p ↦ pᵀV` over the simplex is `max V`, attained at
the point mass on a maximizing coordinate. (In MDP terms: a deterministic
maximizing action exists; the upper-bound half is
`FiniteMDP.weighted_sum_le_max`.) -/
theorem isGreatest_rowVal_stdSimplex (V : S → ℝ) :
    IsGreatest ((fun p => rowVal p V) '' stdSimplex ℝ S)
      (Finset.univ.sup' Finset.univ_nonempty V) := by
  classical
  constructor
  · obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty V
    exact ⟨pureRow a, pureRow_mem_stdSimplex a,
      (rowVal_pureRow a V).trans ha.symm⟩
  · rintro x ⟨p, hp, rfl⟩
    exact FiniteMDP.weighted_sum_le_max p V hp.1 hp.2

/-! ### (s,a)-rectangularity -/

/-- The `(s, a)`-row projection of a joint kernel-uncertainty set. -/
def rowProjection (PSet : Set (S → A → S → ℝ)) (s : S) (a : A) : Set (S → ℝ) :=
  (fun P => P s a) '' PSet

/-- A joint uncertainty set is **(s,a)-rectangular** when any kernel whose
rows all lie in the corresponding row projections is itself a member — i.e.
the set is the product of its row projections. This is the hypothesis under
which the robust operator's fixed point equals the worst case over the joint
set (Iyengar 2005); WITHOUT it the identity fails. -/
def IsRectangular (PSet : Set (S → A → S → ℝ)) : Prop :=
  ∀ P : S → A → S → ℝ, (∀ s a, P s a ∈ rowProjection PSet s a) → P ∈ PSet

omit [Fintype S] [Nonempty S] [Fintype A] [Nonempty A] in
/-- A product of row sets is rectangular. -/
theorem isRectangular_setProd (U : S → A → Set (S → ℝ)) :
    IsRectangular {P : S → A → S → ℝ | ∀ s a, P s a ∈ U s a} := by
  intro P hP s a
  obtain ⟨Q, hQ, hQrow⟩ := hP s a
  rw [← hQrow]
  exact hQ s a

omit [Fintype S] [Nonempty S] [Fintype A] [Nonempty A] in
/-- The row projections of a product of nonempty row sets are exactly the
row sets. -/
theorem rowProjection_setProd (U : S → A → Set (S → ℝ))
    (hU_ne : ∀ s a, (U s a).Nonempty) (s : S) (a : A) :
    rowProjection {P : S → A → S → ℝ | ∀ s a, P s a ∈ U s a} s a = U s a := by
  apply Set.Subset.antisymm
  · rintro p ⟨P, hP, rfl⟩
    exact hP s a
  · intro p hp
    classical
    refine ⟨fun s' a' => if h : s' = s ∧ a' = a then p else (hU_ne s' a').some, ?_, ?_⟩
    · intro s' a'
      by_cases h : s' = s ∧ a' = a
      · simpa [h, h.1, h.2] using hp
      · simp only [dif_neg h]
        exact (hU_ne s' a').some_mem
    · simp

end RobustMDP
