import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Tactic.LinearCombination
import RLGeneralization.Complexity.MinimaxDuality

set_option linter.unusedSectionVars false
set_option checkBinderAnnotations false
set_option synthInstance.maxHeartbeats 40000

noncomputable section

variable {P O : Type*} [Fintype P] [Fintype O] [DecidableEq P] [DecidableEq O]
  [Nonempty P] [Nonempty O]

def payoffVec (R : P → O → ℝ) (p : P → ℝ) : O → ℝ :=
  fun θ => ∑ π : P, p π * R π θ

def payoffVecLM (R : P → O → ℝ) : (P → ℝ) →ₗ[ℝ] (O → ℝ) where
  toFun := payoffVec R
  map_add' p q := by ext θ; simp [payoffVec, add_mul, Finset.sum_add_distrib]
  map_smul' c p := by ext θ; simp [payoffVec, smul_eq_mul, mul_assoc, ← Finset.mul_sum]

def payoffImage (R : P → O → ℝ) : Set (O → ℝ) :=
  payoffVec R '' stdSimplex ℝ P

theorem payoffVec_continuous (R : P → O → ℝ) : Continuous (payoffVec R) := by
  apply continuous_pi; intro θ
  exact continuous_finset_sum _ (fun π _ => (continuous_apply π).mul continuous_const)

theorem payoffImage_compact (R : P → O → ℝ) : IsCompact (payoffImage R) :=
  (isCompact_stdSimplex P).image (payoffVec_continuous R)

theorem payoffImage_convex (R : P → O → ℝ) : Convex ℝ (payoffImage R) :=
  (convex_stdSimplex ℝ P).linear_image (payoffVecLM R)

theorem payoffImage_nonempty (R : P → O → ℝ) : (payoffImage R).Nonempty := by
  obtain ⟨π₀⟩ := ‹Nonempty P›
  exact ⟨_, ⟨Pi.single π₀ 1, single_mem_stdSimplex ℝ π₀, rfl⟩⟩

def belowSet (v : ℝ) : Set (O → ℝ) :=
  {z : O → ℝ | ∀ θ : O, z θ < v}

theorem belowSet_open (v : ℝ) : IsOpen (belowSet (O := O) v) := by
  simp only [belowSet, Set.setOf_forall]
  exact isOpen_iInter_of_finite fun θ => isOpen_lt (continuous_apply θ) continuous_const

theorem belowSet_convex (v : ℝ) : Convex ℝ (belowSet (O := O) v) := by
  intro x hx y hy a b ha hb hab
  simp only [belowSet, Set.mem_setOf_eq] at *
  intro θ; show (a • x + b • y) θ < v
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rcases eq_or_lt_of_le ha with rfl | ha'
  · have : b = 1 := by linarith
    simp [this]; exact hy θ
  · have h1 : a * x θ < a * v := mul_lt_mul_of_pos_left (hx θ) ha'
    have h2 : b * y θ ≤ b * v := mul_le_mul_of_nonneg_left (le_of_lt (hy θ)) hb
    linarith [show a * v + b * v = v from by rw [← add_mul, hab, one_mul]]

def maxCoord : (O → ℝ) → ℝ := fun y => Finset.univ.sup' Finset.univ_nonempty (fun θ => y θ)

theorem maxCoord_continuous : Continuous (maxCoord (O := O)) :=
  Continuous.finset_sup'_apply Finset.univ_nonempty (fun θ _ => continuous_apply θ)

theorem minimax_value_achieved (R : P → O → ℝ) :
    ∃ y₀ ∈ payoffImage R, ∀ y ∈ payoffImage R, maxCoord y₀ ≤ maxCoord y :=
  (payoffImage_compact R).exists_isMinOn (payoffImage_nonempty R) maxCoord_continuous.continuousOn

theorem payoffImage_disjoint_belowSet (R : P → O → ℝ)
    (y₀ : O → ℝ) (hy₀ : y₀ ∈ payoffImage R)
    (hmin : ∀ y ∈ payoffImage R, maxCoord y₀ ≤ maxCoord y) :
    Disjoint (belowSet (maxCoord y₀)) (payoffImage R) := by
  rw [Set.disjoint_iff]; intro z ⟨hzB, hzS⟩
  have h1 := hmin z hzS
  have h2 : maxCoord z < maxCoord y₀ :=
    Finset.sup'_lt_iff Finset.univ_nonempty |>.mpr fun θ _ => hzB θ
  linarith

def basisVec (θ₀ : O) : O → ℝ := fun θ => if θ = θ₀ then 1 else 0

theorem clm_decompose (f : (O → ℝ) →L[ℝ] ℝ) (y : O → ℝ) :
    f y = ∑ θ : O, y θ * f (basisVec θ) := by
  have key : y = ∑ θ : O, y θ • basisVec θ := by
    ext θ'; simp only [basisVec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single θ' (fun θ _ hne => by simp [if_neg (Ne.symm hne)]) (by simp)]
    simp
  conv_lhs => rw [key]
  rw [map_sum]; congr 1; ext θ; rw [map_smul, smul_eq_mul]

theorem payoffVec_single (R : P → O → ℝ) (π : P) (θ : O) :
    payoffVec R (Pi.single π 1) θ = R π θ := by
  simp [payoffVec, Pi.single_apply]

theorem von_neumann_minimax_proved (R : P → O → ℝ) :
    ∃ (p : ProbDist P) (q : ProbDist O),
      Finset.univ.sup' Finset.univ_nonempty (fun θ => mixedVsPure R p θ) =
      Finset.univ.inf' Finset.univ_nonempty (fun π => pureVsMixed R π q) := by
  obtain ⟨_, ⟨p₀, hp₀std, rfl⟩, hmin⟩ := minimax_value_achieved R
  set v := maxCoord (payoffVec R p₀) with hv_def
  have hdisj := payoffImage_disjoint_belowSet R _ ⟨p₀, hp₀std, rfl⟩ hmin
  obtain ⟨φ, u, hφB, hφS⟩ := geometric_hahn_banach_open
    (belowSet_convex v) (belowSet_open v) (payoffImage_convex R) hdisj
  have hcoeff_nn : ∀ θ : O, 0 ≤ φ (basisVec θ) := by
    intro θ; by_contra h; push_neg at h
    set z₀ : O → ℝ := fun _ => v - 1
    have hz₀ : z₀ ∈ belowSet (O := O) v := fun _ => by simp [z₀]
    have hφ_neg : (0 : ℝ) < -(φ (basisVec θ)) := neg_pos.mpr h
    set t := (u - φ z₀ + 1) / (-(φ (basisVec θ)))
    have ht : 0 < t := div_pos (by linarith [hφB z₀ hz₀]) hφ_neg
    have hz₁ : (z₀ - t • basisVec θ) ∈ belowSet (O := O) v := by
      intro θ'; simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, basisVec]
      split_ifs with heq
      · simp only [z₀, mul_one]; linarith
      · simp only [z₀, mul_zero, sub_zero]; linarith
    have h1 := hφB _ hz₁
    rw [map_sub, map_smul, smul_eq_mul] at h1
    have h_cancel : t * (-(φ (basisVec θ))) = u - φ z₀ + 1 :=
      div_mul_cancel₀ _ (ne_of_gt hφ_neg)
    have h_neg : t * (-(φ (basisVec θ))) = -(t * φ (basisVec θ)) := mul_neg t _
    have h_key : φ z₀ - t * φ (basisVec θ) = u + 1 := by linarith
    linarith
  have hcoeff_sum_pos : 0 < ∑ θ : O, φ (basisVec θ) := by
    by_contra hle; push_neg at hle
    have hnn := Finset.sum_nonneg (fun θ (_ : θ ∈ Finset.univ) => hcoeff_nn θ)
    have hS0 : ∑ θ : O, φ (basisVec θ) = 0 := le_antisymm hle hnn
    have hzero : ∀ θ : O, φ (basisVec θ) = 0 := by
      intro θ
      have h_erase := Finset.sum_erase_eq_sub (f := fun θ' => φ (basisVec θ'))
        (Finset.mem_univ θ)
      have h_rest := Finset.sum_nonneg
        (fun θ' (_ : θ' ∈ Finset.univ.erase θ) => hcoeff_nn θ')
      linarith [hcoeff_nn θ]
    have hφ_zero : ∀ y : O → ℝ, φ y = 0 := fun y => by
      rw [clm_decompose]; exact Finset.sum_eq_zero (fun θ _ => by rw [hzero θ, mul_zero])
    have hmem : (fun (_ : O) => v - 1) ∈ belowSet (O := O) v := fun _ => by linarith
    linarith [hφB _ hmem, hφS _ ⟨p₀, hp₀std, rfl⟩,
      hφ_zero (fun (_ : O) => v - 1), hφ_zero (payoffVec R p₀)]
  set S := ∑ θ : O, φ (basisVec θ)
  set q_wt : O → ℝ := fun θ => φ (basisVec θ) / S
  have q_nn : ∀ θ, 0 ≤ q_wt θ := fun θ => div_nonneg (hcoeff_nn θ) (le_of_lt hcoeff_sum_pos)
  have q_sum : ∑ θ : O, q_wt θ = 1 := by
    show ∑ θ : O, φ (basisVec θ) / S = 1
    rw [show ∑ θ : O, φ (basisVec θ) / S = S / S from by
      simp_rw [div_eq_mul_inv]; rw [← Finset.sum_mul]]
    exact div_self (ne_of_gt hcoeff_sum_pos)
  set q : ProbDist O := ⟨q_wt, q_nn, q_sum⟩
  set p : ProbDist P := ⟨p₀, hp₀std.1, hp₀std.2⟩
  have hpure_lb : ∀ π : P, u ≤ ∑ θ : O, R π θ * φ (basisVec θ) := by
    intro π
    have h1 := hφS _ (show payoffVec R (Pi.single π 1) ∈ payoffImage R from
      ⟨Pi.single π 1, single_mem_stdSimplex ℝ π, rfl⟩)
    rw [clm_decompose] at h1
    simp_rw [payoffVec_single] at h1
    linarith
  have hv_le : v * S ≤ u := by
    by_contra h; push_neg at h
    have hε : 0 < (v * S - u) / S / 2 :=
      div_pos (div_pos (sub_pos.mpr h) hcoeff_sum_pos) two_pos
    set z : O → ℝ := fun _ => v - (v * S - u) / S / 2
    have hz : z ∈ belowSet (O := O) v := fun _ => by simp [z]; linarith
    have hφz := hφB z hz
    rw [clm_decompose] at hφz
    simp only [z] at hφz
    rw [show ∑ θ : O, (v - (v * S - u) / S / 2) * φ (basisVec θ) =
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
      have hexpand : S * pureVsMixed R π q = ∑ θ' : O, R π θ' * φ (basisVec θ') := by
        show S * ∑ θ' : O, q.wt θ' * R π θ' = ∑ θ' : O, R π θ' * φ (basisVec θ')
        rw [Finset.mul_sum]; congr 1; ext θ'; simp only [q, q_wt]; field_simp
      linarith [hpure_lb π, mul_comm v S]
    linarith
  · exact finite_weak_duality R p q

end
