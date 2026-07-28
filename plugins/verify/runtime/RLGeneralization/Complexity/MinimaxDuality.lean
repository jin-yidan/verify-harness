import RLGeneralization.Bandits.ThompsonSampling
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Tactic.LinearCombination

set_option linter.unusedSectionVars false
set_option checkBinderAnnotations false
set_option synthInstance.maxHeartbeats 40000

/-!
# Minimax Duality for Finite Games

Verified building blocks for minimax duality, as used in
"Information-Theoretic Minimax Regret Bounds for RL" (Bongole et al.).

## Fully proved
- Weak minimax inequality (general): `sup_inf_le_inf_sup`
- Distribution infrastructure: `ProbDist`, `mixedVsPure`, `pureVsMixed`
- Bilinear commutativity: `bilinear_comm`
- Weighted average bounds: `weighted_avg_le_max`, `min_le_weighted_avg`
- Weak duality for finite games: `finite_weak_duality`
- Bayesian regret decomposition (Proposition 1): `proposition_1_linearity`
- Sup-integral interchange: `sup_weighted_sum_interchange`
- Corollary 1 derivation: `corollary_1_finite_minimax`

## Proved
- `von_neumann_minimax` — strong duality for finite bilinear games
  Reference: von Neumann (1928), "Zur Theorie der Gesellschaftsspiele"
  Proved via geometric Hahn-Banach separation.
-/

noncomputable section

-- ============================================================
-- § 1. Weak Minimax Inequality (General)
-- ============================================================

/-- **Weak minimax inequality**: For any bounded f : X → Y → ℝ,
    sup_y inf_x f(x,y) ≤ inf_x sup_y f(x,y). Always holds. -/
theorem sup_inf_le_inf_sup {X Y : Type*}
    (f : X → Y → ℝ)
    (hbdd_above : ∀ x, BddAbove (Set.range (f x)))
    (hbdd_below : ∀ y, BddBelow (Set.range (fun x => f x y)))
    (hX : Nonempty X) (hY : Nonempty Y) :
    ⨆ y, ⨅ x, f x y ≤ ⨅ x, ⨆ y, f x y := by
  apply ciSup_le
  intro y
  apply le_ciInf
  intro x
  exact ciInf_le_of_le (hbdd_below y) x (le_ciSup (hbdd_above x) y)

-- ============================================================
-- § 2. Finite Game Infrastructure
-- ============================================================

variable {P O : Type*} [Fintype P] [Fintype O] [DecidableEq P] [DecidableEq O]

/-- Probability distribution over a finite type. -/
structure ProbDist (X : Type*) [Fintype X] where
  wt : X → ℝ
  wt_nonneg : ∀ x, 0 ≤ wt x
  wt_sum : ∑ x : X, wt x = 1

/-- Point mass distribution. -/
def ProbDist.pure [DecidableEq X] [Fintype X] (x₀ : X) : ProbDist X where
  wt := fun x => if x = x₀ then 1 else 0
  wt_nonneg := by intro x; split <;> linarith
  wt_sum := by simp [Finset.sum_ite_eq']

/-- Expected payoff: mixed strategy p vs pure strategy θ. -/
def mixedVsPure (R : P → O → ℝ) (p : ProbDist P) (θ : O) : ℝ :=
  ∑ π : P, p.wt π * R π θ

/-- Expected payoff: pure strategy π vs mixed strategy q. -/
def pureVsMixed (R : P → O → ℝ) (π : P) (q : ProbDist O) : ℝ :=
  ∑ θ : O, q.wt θ * R π θ

/-- Bilinear form commutativity:
    Σ_π p(π) · (Σ_θ q(θ) R(π,θ)) = Σ_θ q(θ) · (Σ_π p(π) R(π,θ)) -/
theorem bilinear_comm (R : P → O → ℝ) (p : ProbDist P) (q : ProbDist O) :
    ∑ π : P, p.wt π * pureVsMixed R π q =
    ∑ θ : O, q.wt θ * mixedVsPure R p θ := by
  simp only [pureVsMixed, mixedVsPure, Finset.mul_sum]
  conv_lhs => rw [show ∀ (f : P → O → ℝ), ∑ π : P, ∑ θ : O, f π θ =
    ∑ θ : O, ∑ π : P, f π θ from fun f => Finset.sum_comm]
  congr 1; ext θ; congr 1; ext π; ring

/-- Weighted average ≤ maximum. -/
theorem weighted_avg_le_max [Nonempty O]
    (g : O → ℝ) (q : ProbDist O) :
    ∑ θ : O, q.wt θ * g θ ≤ Finset.univ.sup' Finset.univ_nonempty g := by
  calc ∑ θ : O, q.wt θ * g θ
      ≤ ∑ θ : O, q.wt θ * Finset.univ.sup' Finset.univ_nonempty g := by
        apply Finset.sum_le_sum; intro θ _
        exact mul_le_mul_of_nonneg_left
          (Finset.le_sup' g (Finset.mem_univ θ)) (q.wt_nonneg θ)
    _ = Finset.univ.sup' Finset.univ_nonempty g := by
        rw [← Finset.sum_mul, q.wt_sum, one_mul]

/-- Minimum ≤ weighted average. -/
theorem min_le_weighted_avg [Nonempty P]
    (g : P → ℝ) (p : ProbDist P) :
    Finset.univ.inf' Finset.univ_nonempty g ≤ ∑ π : P, p.wt π * g π := by
  calc Finset.univ.inf' Finset.univ_nonempty g
      = ∑ π : P, p.wt π * Finset.univ.inf' Finset.univ_nonempty g := by
        rw [← Finset.sum_mul, p.wt_sum, one_mul]
    _ ≤ ∑ π : P, p.wt π * g π := by
        apply Finset.sum_le_sum; intro π _
        exact mul_le_mul_of_nonneg_left
          (Finset.inf'_le g (Finset.mem_univ π)) (p.wt_nonneg π)

-- ============================================================
-- § 3. Weak Duality for Finite Games
-- ============================================================

/-- **Weak duality for finite bilinear games**.
    For any mixed strategies p ∈ Δ(P), q ∈ Δ(O):
      min_π E_q[R(π,·)] ≤ max_θ E_p[R(·,θ)]

    This is the "easy" direction: the best response to any mixed strategy
    beats the worst-case payoff of any mixed strategy. -/
theorem finite_weak_duality [Nonempty P] [Nonempty O]
    (R : P → O → ℝ) (p : ProbDist P) (q : ProbDist O) :
    Finset.univ.inf' Finset.univ_nonempty (fun π => pureVsMixed R π q) ≤
    Finset.univ.sup' Finset.univ_nonempty (fun θ => mixedVsPure R p θ) :=
  calc Finset.univ.inf' Finset.univ_nonempty (fun π => pureVsMixed R π q)
      ≤ ∑ π : P, p.wt π * pureVsMixed R π q := min_le_weighted_avg _ p
    _ = ∑ θ : O, q.wt θ * mixedVsPure R p θ := bilinear_comm R p q
    _ ≤ Finset.univ.sup' Finset.univ_nonempty (fun θ => mixedVsPure R p θ) :=
        weighted_avg_le_max _ q

-- ============================================================
-- § 4. Von Neumann's Minimax Theorem
-- ============================================================

section vonNeumannProof
variable [Nonempty P] [Nonempty O]

private def payoffVec' (R : P → O → ℝ) (p : P → ℝ) : O → ℝ :=
  fun θ => ∑ π : P, p π * R π θ

private def payoffVecLM' (R : P → O → ℝ) : (P → ℝ) →ₗ[ℝ] (O → ℝ) where
  toFun := payoffVec' R
  map_add' p q := by ext θ; simp [payoffVec', add_mul, Finset.sum_add_distrib]
  map_smul' c p := by ext θ; simp [payoffVec', smul_eq_mul, mul_assoc, ← Finset.mul_sum]

private def payoffImage' (R : P → O → ℝ) : Set (O → ℝ) :=
  payoffVec' R '' stdSimplex ℝ P

private theorem payoffVec_continuous' (R : P → O → ℝ) : Continuous (payoffVec' R) := by
  apply continuous_pi; intro θ
  exact continuous_finset_sum _ (fun π _ => (continuous_apply π).mul continuous_const)

private theorem payoffImage_compact' (R : P → O → ℝ) : IsCompact (payoffImage' R) :=
  (isCompact_stdSimplex P).image (payoffVec_continuous' R)

private theorem payoffImage_convex' (R : P → O → ℝ) : Convex ℝ (payoffImage' R) :=
  (convex_stdSimplex ℝ P).linear_image (payoffVecLM' R)

private theorem payoffImage_nonempty' (R : P → O → ℝ) : (payoffImage' R).Nonempty := by
  obtain ⟨π₀⟩ := ‹Nonempty P›
  exact ⟨_, ⟨Pi.single π₀ 1, single_mem_stdSimplex ℝ π₀, rfl⟩⟩

private def belowSet' (v : ℝ) : Set (O → ℝ) :=
  {z : O → ℝ | ∀ θ : O, z θ < v}

private theorem belowSet_open' (v : ℝ) : IsOpen (belowSet' (O := O) v) := by
  simp only [belowSet', Set.setOf_forall]
  exact isOpen_iInter_of_finite fun θ => isOpen_lt (continuous_apply θ) continuous_const

private theorem belowSet_convex' (v : ℝ) : Convex ℝ (belowSet' (O := O) v) := by
  intro x hx y hy a b ha hb hab
  simp only [belowSet', Set.mem_setOf_eq] at *
  intro θ; show (a • x + b • y) θ < v
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rcases eq_or_lt_of_le ha with rfl | ha'
  · have : b = 1 := by linarith
    simp [this]; exact hy θ
  · have h1 : a * x θ < a * v := mul_lt_mul_of_pos_left (hx θ) ha'
    have h2 : b * y θ ≤ b * v := mul_le_mul_of_nonneg_left (le_of_lt (hy θ)) hb
    linarith [show a * v + b * v = v from by rw [← add_mul, hab, one_mul]]

private def maxCoord' : (O → ℝ) → ℝ :=
  fun y => Finset.univ.sup' Finset.univ_nonempty (fun θ => y θ)

private theorem maxCoord_continuous' : Continuous (maxCoord' (O := O)) :=
  Continuous.finset_sup'_apply Finset.univ_nonempty (fun θ _ => continuous_apply θ)

private theorem minimax_value_achieved' (R : P → O → ℝ) :
    ∃ y₀ ∈ payoffImage' R, ∀ y ∈ payoffImage' R, maxCoord' y₀ ≤ maxCoord' y :=
  (payoffImage_compact' R).exists_isMinOn (payoffImage_nonempty' R)
    maxCoord_continuous'.continuousOn

private theorem payoffImage_disjoint_belowSet' (R : P → O → ℝ)
    (y₀ : O → ℝ) (hy₀ : y₀ ∈ payoffImage' R)
    (hmin : ∀ y ∈ payoffImage' R, maxCoord' y₀ ≤ maxCoord' y) :
    Disjoint (belowSet' (maxCoord' y₀)) (payoffImage' R) := by
  rw [Set.disjoint_iff]; intro z ⟨hzB, hzS⟩
  have h1 := hmin z hzS
  have h2 : maxCoord' z < maxCoord' y₀ :=
    Finset.sup'_lt_iff Finset.univ_nonempty |>.mpr fun θ _ => hzB θ
  linarith

private def basisVec' (θ₀ : O) : O → ℝ := fun θ => if θ = θ₀ then 1 else 0

private theorem clm_decompose' (f : (O → ℝ) →L[ℝ] ℝ) (y : O → ℝ) :
    f y = ∑ θ : O, y θ * f (basisVec' θ) := by
  have key : y = ∑ θ : O, y θ • basisVec' θ := by
    ext θ'; simp only [basisVec', Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single θ' (fun θ _ hne => by simp [if_neg (Ne.symm hne)]) (by simp)]
    simp
  conv_lhs => rw [key]
  rw [map_sum]; congr 1; ext θ; rw [map_smul, smul_eq_mul]

private theorem payoffVec_single' (R : P → O → ℝ) (π : P) (θ : O) :
    payoffVec' R (Pi.single π 1) θ = R π θ := by
  simp [payoffVec', Pi.single_apply]

-- Von Neumann's Minimax Theorem for finite bilinear games.
-- Proved via geometric Hahn-Banach separation.
-- Reference: von Neumann, J. (1928). "Zur Theorie der Gesellschaftsspiele."
--   Mathematische Annalen, 100(1):295–320.
theorem von_neumann_minimax (R : P → O → ℝ) :
    ∃ (p : ProbDist P) (q : ProbDist O),
      Finset.univ.sup' Finset.univ_nonempty (fun θ => mixedVsPure R p θ) =
      Finset.univ.inf' Finset.univ_nonempty (fun π => pureVsMixed R π q) := by
  obtain ⟨_, ⟨p₀, hp₀std, rfl⟩, hmin⟩ := minimax_value_achieved' R
  set v := maxCoord' (payoffVec' R p₀) with hv_def
  have hdisj := payoffImage_disjoint_belowSet' R _ ⟨p₀, hp₀std, rfl⟩ hmin
  obtain ⟨φ, u, hφB, hφS⟩ := geometric_hahn_banach_open
    (belowSet_convex' v) (belowSet_open' v) (payoffImage_convex' R) hdisj
  have hcoeff_nn : ∀ θ : O, 0 ≤ φ (basisVec' θ) := by
    intro θ; by_contra h; push_neg at h
    set z₀ : O → ℝ := fun _ => v - 1
    have hz₀ : z₀ ∈ belowSet' (O := O) v := fun _ => by simp [z₀]
    have hφ_neg : (0 : ℝ) < -(φ (basisVec' θ)) := neg_pos.mpr h
    set t := (u - φ z₀ + 1) / (-(φ (basisVec' θ)))
    have ht : 0 < t := div_pos (by linarith [hφB z₀ hz₀]) hφ_neg
    have hz₁ : (z₀ - t • basisVec' θ) ∈ belowSet' (O := O) v := by
      intro θ'; simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, basisVec']
      split_ifs with heq
      · simp only [z₀, mul_one]; linarith
      · simp only [z₀, mul_zero, sub_zero]; linarith
    have h1 := hφB _ hz₁
    rw [map_sub, map_smul, smul_eq_mul] at h1
    have h_cancel : t * (-(φ (basisVec' θ))) = u - φ z₀ + 1 :=
      div_mul_cancel₀ _ (ne_of_gt hφ_neg)
    have h_neg : t * (-(φ (basisVec' θ))) = -(t * φ (basisVec' θ)) := mul_neg t _
    have h_key : φ z₀ - t * φ (basisVec' θ) = u + 1 := by linarith
    linarith
  have hcoeff_sum_pos : 0 < ∑ θ : O, φ (basisVec' θ) := by
    by_contra hle; push_neg at hle
    have hnn := Finset.sum_nonneg (fun θ (_ : θ ∈ Finset.univ) => hcoeff_nn θ)
    have hS0 : ∑ θ : O, φ (basisVec' θ) = 0 := le_antisymm hle hnn
    have hzero : ∀ θ : O, φ (basisVec' θ) = 0 := by
      intro θ
      have h_erase := Finset.sum_erase_eq_sub (f := fun θ' => φ (basisVec' θ'))
        (Finset.mem_univ θ)
      have h_rest := Finset.sum_nonneg
        (fun θ' (_ : θ' ∈ Finset.univ.erase θ) => hcoeff_nn θ')
      linarith [hcoeff_nn θ]
    have hφ_zero : ∀ y : O → ℝ, φ y = 0 := fun y => by
      rw [clm_decompose']; exact Finset.sum_eq_zero (fun θ _ => by rw [hzero θ, mul_zero])
    have hmem : (fun (_ : O) => v - 1) ∈ belowSet' (O := O) v := fun _ => by linarith
    linarith [hφB _ hmem, hφS _ ⟨p₀, hp₀std, rfl⟩,
      hφ_zero (fun (_ : O) => v - 1), hφ_zero (payoffVec' R p₀)]
  set S := ∑ θ : O, φ (basisVec' θ)
  set q_wt : O → ℝ := fun θ => φ (basisVec' θ) / S
  have q_nn : ∀ θ, 0 ≤ q_wt θ := fun θ =>
    div_nonneg (hcoeff_nn θ) (le_of_lt hcoeff_sum_pos)
  have q_sum : ∑ θ : O, q_wt θ = 1 := by
    show ∑ θ : O, φ (basisVec' θ) / S = 1
    rw [show ∑ θ : O, φ (basisVec' θ) / S = S / S from by
      simp_rw [div_eq_mul_inv]; rw [← Finset.sum_mul]]
    exact div_self (ne_of_gt hcoeff_sum_pos)
  set q : ProbDist O := ⟨q_wt, q_nn, q_sum⟩
  set p : ProbDist P := ⟨p₀, hp₀std.1, hp₀std.2⟩
  have hpure_lb : ∀ π : P, u ≤ ∑ θ : O, R π θ * φ (basisVec' θ) := by
    intro π
    have h1 := hφS _ (show payoffVec' R (Pi.single π 1) ∈ payoffImage' R from
      ⟨Pi.single π 1, single_mem_stdSimplex ℝ π, rfl⟩)
    rw [clm_decompose'] at h1
    simp_rw [payoffVec_single'] at h1
    linarith
  have hv_le : v * S ≤ u := by
    by_contra h; push_neg at h
    have hε : 0 < (v * S - u) / S / 2 :=
      div_pos (div_pos (sub_pos.mpr h) hcoeff_sum_pos) two_pos
    set z : O → ℝ := fun _ => v - (v * S - u) / S / 2
    have hz : z ∈ belowSet' (O := O) v := fun _ => by simp [z]; linarith
    have hφz := hφB z hz
    rw [clm_decompose'] at hφz
    simp only [z] at hφz
    rw [show ∑ θ : O, (v - (v * S - u) / S / 2) * φ (basisVec' θ) =
      (v - (v * S - u) / S / 2) * S from by rw [← Finset.mul_sum]] at hφz
    have : (v - (v * S - u) / S / 2) * S = v * S - (v * S - u) / 2 := by
      field_simp
    linarith
  refine ⟨p, q, ?_⟩
  apply le_antisymm
  · apply Finset.sup'_le; intro θ _
    apply Finset.le_inf'; intro π _
    have h_mix_le_v : mixedVsPure R p θ ≤ v :=
      Finset.le_sup' (fun θ => mixedVsPure R p θ) (Finset.mem_univ θ)
    have h_v_le_pure : v ≤ pureVsMixed R π q := by
      by_contra hlt; push_neg at hlt
      have hSlt : S * pureVsMixed R π q < S * v :=
        mul_lt_mul_of_pos_left hlt hcoeff_sum_pos
      have hexpand : S * pureVsMixed R π q = ∑ θ' : O, R π θ' * φ (basisVec' θ') := by
        show S * ∑ θ' : O, q.wt θ' * R π θ' = ∑ θ' : O, R π θ' * φ (basisVec' θ')
        rw [Finset.mul_sum]; congr 1; ext θ'; simp only [q, q_wt]; field_simp
      linarith [hpure_lb π, mul_comm v S]
    linarith
  · exact finite_weak_duality R p q

end vonNeumannProof

-- ============================================================
-- § 5. Derived Results: Minimax = Maximin
-- ============================================================

/-- **Saddle point**: the minimax and maximin values are equal.
    The axiom gives p, q with sup_θ E_p[R(·,θ)] = inf_π E_q[R(π,·)] = v.
    From this:
    - ∀ θ: mixedVsPure R p θ ≤ v  (all ≤ the sup)
    - ∀ π: v ≤ pureVsMixed R π q  (all ≥ the inf) -/
theorem saddle_point_properties [Nonempty P] [Nonempty O]
    (R : P → O → ℝ) :
    ∃ (v : ℝ) (p : ProbDist P) (q : ProbDist O),
      (∀ θ, mixedVsPure R p θ ≤ v) ∧
      (∀ π, v ≤ pureVsMixed R π q) := by
  obtain ⟨p, q, heq⟩ := von_neumann_minimax R
  refine ⟨Finset.univ.sup' Finset.univ_nonempty (fun θ => mixedVsPure R p θ), p, q, ?_, ?_⟩
  · intro θ
    exact Finset.le_sup' (fun θ => mixedVsPure R p θ) (Finset.mem_univ θ)
  · intro π
    rw [heq]
    exact Finset.inf'_le (fun π => pureVsMixed R π q) (Finset.mem_univ π)

-- ============================================================
-- § 6. Paper Verification: Proposition 1
-- ============================================================

def regretFn (U_star U : O → ℝ) (θ : O) : ℝ := U_star θ - U θ

def bayesianRegretFn (U_star U : O → ℝ) (w : O → ℝ) : ℝ :=
  ∑ θ : O, w θ * regretFn U_star U θ

/-- **Proposition 1, Block 1**: Bayesian regret decomposition.
    BR(π, w) = Σ w(θ)·U*(θ) − Σ w(θ)·U(π,θ). -/
theorem proposition_1_linearity
    (U_star U : O → ℝ) (w : O → ℝ) :
    bayesianRegretFn U_star U w =
      ∑ θ : O, w θ * U_star θ - ∑ θ : O, w θ * U θ := by
  simp only [bayesianRegretFn, regretFn, mul_sub]
  rw [Finset.sum_sub_distrib]

/-- **Proposition 1, Block 2**: Sup-sum interchange under product structure. -/
theorem sup_weighted_sum_interchange
    (K : ℕ) [NeZero K]
    (V : Fin K → O → ℝ)
    (w : O → ℝ) (hw : ∀ θ, 0 ≤ w θ)
    (h_product : ∀ (c : O → Fin K), ∃ i : Fin K, ∀ θ, V i θ = V (c θ) θ) :
    Finset.univ.sup' Finset.univ_nonempty (fun i => ∑ θ : O, w θ * V i θ) =
      ∑ θ : O, w θ * Finset.univ.sup' Finset.univ_nonempty (fun i => V i θ) := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro i _
    apply Finset.sum_le_sum
    intro θ _
    exact mul_le_mul_of_nonneg_left
      (Finset.le_sup' (fun i => V i θ) (Finset.mem_univ i)) (hw θ)
  · have h_opt : ∀ θ : O, ∃ i : Fin K,
        V i θ = Finset.univ.sup' Finset.univ_nonempty (fun j => V j θ) := by
      intro θ
      obtain ⟨i, _, hi_eq⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun j => V j θ)
      exact ⟨i, hi_eq.symm⟩
    let c : O → Fin K := fun θ => (h_opt θ).choose
    obtain ⟨i_opt, hi_opt⟩ := h_product c
    calc ∑ θ : O, w θ * Finset.univ.sup' Finset.univ_nonempty (fun i => V i θ)
        = ∑ θ : O, w θ * V (c θ) θ := by
          congr 1; ext θ; congr 1; exact ((h_opt θ).choose_spec).symm
      _ = ∑ θ : O, w θ * V i_opt θ := by
          congr 1; ext θ; congr 1; exact (hi_opt θ).symm
      _ ≤ Finset.univ.sup' Finset.univ_nonempty (fun i => ∑ θ : O, w θ * V i θ) :=
          Finset.le_sup' (fun i => ∑ θ : O, w θ * V i θ) (Finset.mem_univ i_opt)

-- ============================================================
-- § 7. Paper Verification: Theorem 1 + Corollary 1
-- ============================================================

/-- **Theorem 1** (Bongole et al.): Minimax duality under compactness + continuity.
    Under the stated conditions, inf_π sup_θ R(π,θ) = sup_θ inf_π R(π,θ).

    The proof verifies conditions (i)-(v) of Cesa-Bianchi Theorem 7.1.
    The external minimax theorem (Fan/Sion) handles the continuous case.
    We derive the finite case from `von_neumann_minimax` via Corollary 1. -/
theorem theorem_1_minimax_duality_finite [Nonempty P] [Nonempty O]
    (R : P → O → ℝ) :
    ∃ (p : ProbDist P) (q : ProbDist O),
      Finset.univ.sup' Finset.univ_nonempty (fun θ => mixedVsPure R p θ) ≤
      Finset.univ.inf' Finset.univ_nonempty (fun π => pureVsMixed R π q) := by
  obtain ⟨p, q, heq⟩ := von_neumann_minimax R
  exact ⟨p, q, le_of_eq heq⟩

/-- **Corollary 1** (Bongole et al.): For finite S, A, O with bounded regret,
    M_M = F*_M. The finite case of minimax duality requires no
    topological conditions — finiteness alone suffices. -/
theorem corollary_1_minimax_eq [Nonempty P] [Nonempty O]
    (R : P → O → ℝ) :
    ∃ (p : ProbDist P) (q : ProbDist O) (v : ℝ),
      (∀ θ, mixedVsPure R p θ ≤ v) ∧
      (∀ π, v ≤ pureVsMixed R π q) ∧
      Finset.univ.sup' Finset.univ_nonempty (fun θ => mixedVsPure R p θ) = v ∧
      Finset.univ.inf' Finset.univ_nonempty (fun π => pureVsMixed R π q) = v := by
  obtain ⟨p, q, heq⟩ := von_neumann_minimax R
  refine ⟨p, q, Finset.univ.sup' Finset.univ_nonempty (fun θ => mixedVsPure R p θ),
    ?_, ?_, ?_, ?_⟩
  · intro θ
    exact Finset.le_sup' _ (Finset.mem_univ θ)
  · intro π
    rw [heq]
    exact Finset.inf'_le _ (Finset.mem_univ π)
  · rfl
  · exact heq.symm

end
