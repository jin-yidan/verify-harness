/-
# Bellman Operator Contraction Properties

This file proves that the Bellman evaluation and optimality operators
are γ-contractions in the supremum norm, and derives value bounds.
Existence/uniqueness of the optimal policy is in Resolvent.lean
(`optimal_policy_exists`, `bellman_eval_unique_fixed_point`).

## Main Results

* `bellmanEvalOp_contraction` - The Bellman evaluation operator T^π is a γ-contraction
  in the sup norm: ‖T^π V₁ - T^π V₂‖_∞ ≤ γ ‖V₁ - V₂‖_∞
* `bellmanOptOp_contraction` - The Bellman optimality operator T* is a γ-contraction
  in the sup norm: ‖T* Q₁ - T* Q₂‖_∞ ≤ γ ‖Q₁ - Q₂‖_∞

## References

* [Puterman, *Markov Decision Processes*][puterman2014]
* [Bertsekas, *Dynamic Programming and Optimal Control*][bertsekas2012]
-/

import RLGeneralization.MDP.Basic

open Finset BigOperators

noncomputable section

namespace FiniteMDP

variable (M : FiniteMDP)

/-! ### Sup Norm for Value Functions -/

/-- The sup norm of a state value function on a finite state space. -/
def supNormV (V : M.StateValueFn) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun s => |V s|)

/-- The sup norm distance between two state value functions. -/
def supDistV (V₁ V₂ : M.StateValueFn) : ℝ :=
  M.supNormV (fun s => V₁ s - V₂ s)

/-- The sup norm of an action value function. -/
def supNormQ (Q : M.ActionValueFn) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun s => Finset.univ.sup' Finset.univ_nonempty (fun a => |Q s a|))

/-- The sup norm distance between two action value functions. -/
def supDistQ (Q₁ Q₂ : M.ActionValueFn) : ℝ :=
  M.supNormQ (fun s a => Q₁ s a - Q₂ s a)

/-! ### Key Lemma: Weighted Sum Contraction -/

/-- If ∑ wᵢ = 1, wᵢ ≥ 0, and |dᵢ| ≤ D for all i, then |∑ wᵢ dᵢ| ≤ D.
    This is the core algebraic fact behind Bellman contraction. -/
lemma abs_weighted_sum_le_bound {ι : Type*} [Fintype ι]
    (w d : ι → ℝ) (D : ℝ)
    (hw_nonneg : ∀ i, 0 ≤ w i) (hw_sum : ∑ i, w i = 1)
    (hd : ∀ i, |d i| ≤ D) :
    |∑ i, w i * d i| ≤ D := by
  apply abs_le.mpr
  constructor
  · -- Lower bound: -D ≤ ∑ wᵢ dᵢ
    have hterm : ∀ i, w i * (-D) ≤ w i * d i := fun i =>
      mul_le_mul_of_nonneg_left (abs_le.mp (hd i)).1 (hw_nonneg i)
    calc -D = (∑ i, w i) * (-D) := by rw [hw_sum, one_mul]
      _ = ∑ i, w i * (-D) := Finset.sum_mul Finset.univ _ _
      _ ≤ ∑ i, w i * d i := Finset.sum_le_sum (fun i _ => hterm i)
  · -- Upper bound: ∑ wᵢ dᵢ ≤ D
    have hterm : ∀ i, w i * d i ≤ w i * D := fun i =>
      mul_le_mul_of_nonneg_left (abs_le.mp (hd i)).2 (hw_nonneg i)
    calc ∑ i, w i * d i
        ≤ ∑ i, w i * D := Finset.sum_le_sum (fun i _ => hterm i)
      _ = (∑ i, w i) * D := (Finset.sum_mul Finset.univ _ _).symm
      _ = D := by rw [hw_sum, one_mul]

/-- If ∑ wᵢ = 1 and wᵢ ≥ 0, then |∑ wᵢ (fᵢ - gᵢ)| ≤ max |fᵢ - gᵢ|.
    Corollary of `abs_weighted_sum_le_bound`. -/
lemma weighted_sum_le_sup (w f g : M.S → ℝ) (hw_nonneg : ∀ s, 0 ≤ w s)
    (hw_sum : ∑ s, w s = 1) :
    |∑ s, w s * (f s - g s)| ≤
      Finset.univ.sup' Finset.univ_nonempty (fun s => |f s - g s|) := by
  apply abs_weighted_sum_le_bound w (fun s => f s - g s) _ hw_nonneg hw_sum
  intro s
  exact Finset.le_sup' (fun s => |f s - g s|) (Finset.mem_univ s)

/-! ### Bellman Evaluation Operator Contraction -/

/-- The Bellman evaluation operator T^π is a γ-contraction in the sup norm:
    For all V₁, V₂ : S → ℝ,
      ‖T^π V₁ - T^π V₂‖_∞ ≤ γ · ‖V₁ - V₂‖_∞

    Proof sketch: The reward terms cancel, leaving
      |(T^π V₁)(s) - (T^π V₂)(s)| = γ |∑_a π(a|s) ∑_{s'} P(s'|s,a) (V₁(s') - V₂(s'))|
                                    ≤ γ · ‖V₁ - V₂‖_∞
    since ∑_a π(a|s) ∑_{s'} P(s'|s,a) = 1 (stochastic weights). -/
theorem bellmanEvalOp_contraction (π : M.StochasticPolicy)
    (V₁ V₂ : M.StateValueFn) :
    M.supDistV (M.bellmanEvalOp π V₁) (M.bellmanEvalOp π V₂) ≤
      M.γ * M.supDistV V₁ V₂ := by
  -- Reduce to pointwise bound
  suffices h : ∀ s, |M.bellmanEvalOp π V₁ s - M.bellmanEvalOp π V₂ s| ≤
      M.γ * M.supDistV V₁ V₂ by
    simp only [supDistV, supNormV]
    exact Finset.sup'_le _ _ (fun s _ => h s)
  intro s
  set D := M.supDistV V₁ V₂
  -- Step 1: Reward terms cancel, leaving γ * (expectedNextValue difference)
  have hdiff : M.bellmanEvalOp π V₁ s - M.bellmanEvalOp π V₂ s =
      M.γ * (M.expectedNextValue π V₁ s - M.expectedNextValue π V₂ s) := by
    simp only [bellmanEvalOp]; ring
  rw [hdiff, abs_mul, abs_of_nonneg M.γ_nonneg]
  apply mul_le_mul_of_nonneg_left _ M.γ_nonneg
  -- Step 2: Rewrite expectedNextValue difference as a double weighted sum
  have hexpand : M.expectedNextValue π V₁ s - M.expectedNextValue π V₂ s =
      ∑ a, π.prob s a * (∑ s', M.P s a s' * (V₁ s' - V₂ s')) := by
    simp only [expectedNextValue]
    rw [← Finset.sum_sub_distrib]
    congr 1; ext a; rw [← mul_sub]; congr 1
    rw [← Finset.sum_sub_distrib]
    congr 1; ext s'; ring
  -- Step 3: Each inner sum (over s') is bounded by D
  have hinner : ∀ a, |∑ s', M.P s a s' * (V₁ s' - V₂ s')| ≤ D := by
    intro a
    apply abs_weighted_sum_le_bound _ _ D (M.P_nonneg s a) (M.P_sum_one s a)
    intro s'
    exact Finset.le_sup' (fun s => |V₁ s - V₂ s|) (Finset.mem_univ s')
  -- Step 4: Outer sum (over a) is also bounded by D
  rw [hexpand]
  exact abs_weighted_sum_le_bound _ _ D (π.prob_nonneg s) (π.prob_sum_one s) hinner

/-! ### Bellman Optimality Operator Contraction -/

/-- |sup f - sup g| ≤ sup |f - g| for any Fintype.
    Generic version used across MDP frameworks. -/
theorem abs_sup_sub_sup_le {ι : Type*} [Fintype ι] [Nonempty ι]
    (f g : ι → ℝ) :
    |Finset.univ.sup' Finset.univ_nonempty f -
      Finset.univ.sup' Finset.univ_nonempty g| ≤
      Finset.univ.sup' Finset.univ_nonempty
        (fun i => |f i - g i|) := by
  set D := Finset.univ.sup' Finset.univ_nonempty
    (fun i => |f i - g i|)
  set sf := Finset.univ.sup' Finset.univ_nonempty f
  set sg := Finset.univ.sup' Finset.univ_nonempty g
  apply abs_le.mpr
  constructor
  · have hsup_g : sg ≤ sf + D := by
      apply Finset.sup'_le; intro a _
      have h1 : g a ≤ f a + |f a - g a| := by
        linarith [neg_abs_le (f a - g a)]
      linarith [Finset.le_sup' f (Finset.mem_univ a),
        Finset.le_sup' (fun i => |f i - g i|)
          (Finset.mem_univ a)]
    linarith
  · have hsup_f : sf ≤ sg + D := by
      apply Finset.sup'_le; intro a _
      have h1 : f a ≤ g a + |f a - g a| := by
        linarith [le_abs_self (f a - g a)]
      linarith [Finset.le_sup' g (Finset.mem_univ a),
        Finset.le_sup' (fun i => |f i - g i|)
          (Finset.mem_univ a)]
    linarith

/-- Key inequality: |max_a f(a) - max_a g(a)| ≤ max_a |f(a) - g(a)| -/
lemma sup_sub_sup_le (f g : M.A → ℝ) :
    |Finset.univ.sup' Finset.univ_nonempty f - Finset.univ.sup' Finset.univ_nonempty g| ≤
      Finset.univ.sup' Finset.univ_nonempty (fun a => |f a - g a|) :=
  abs_sup_sub_sup_le f g

/-- The Bellman optimality operator is a γ-contraction in the sup norm:
    ‖T* Q₁ - T* Q₂‖_∞ ≤ γ · ‖Q₁ - Q₂‖_∞

    This is the fundamental result that guarantees:
    1. Existence and uniqueness of Q*
    2. Convergence of value iteration
    3. The basis for sample complexity bounds -/
theorem bellmanOptOp_contraction (Q₁ Q₂ : M.ActionValueFn) :
    M.supDistQ (M.bellmanOptOp Q₁) (M.bellmanOptOp Q₂) ≤
      M.γ * M.supDistQ Q₁ Q₂ := by
  -- Reduce to pointwise bound for each (s, a)
  suffices h : ∀ s a, |M.bellmanOptOp Q₁ s a - M.bellmanOptOp Q₂ s a| ≤
      M.γ * M.supDistQ Q₁ Q₂ by
    simp only [supDistQ, supNormQ]
    apply Finset.sup'_le; intro s _
    apply Finset.sup'_le; intro a _
    exact h s a
  intro s a
  -- Abbreviations for readability
  let maxQ₁ (s' : M.S) := Finset.univ.sup' Finset.univ_nonempty (fun a' => Q₁ s' a')
  let maxQ₂ (s' : M.S) := Finset.univ.sup' Finset.univ_nonempty (fun a' => Q₂ s' a')
  -- The reward terms cancel, leaving γ * weighted sum of max differences
  have hdiff : M.bellmanOptOp Q₁ s a - M.bellmanOptOp Q₂ s a =
      M.γ * ∑ s', M.P s a s' * (maxQ₁ s' - maxQ₂ s') := by
    unfold bellmanOptOp
    have hsplit : ∀ s' : M.S, M.P s a s' * (maxQ₁ s' - maxQ₂ s') =
        M.P s a s' * maxQ₁ s' - M.P s a s' * maxQ₂ s' := fun s' => mul_sub _ _ _
    simp_rw [hsplit, Finset.sum_sub_distrib]
    ring
  rw [hdiff, abs_mul, abs_of_nonneg M.γ_nonneg]
  apply mul_le_mul_of_nonneg_left _ M.γ_nonneg
  -- Bound the weighted sum: |∑ P * (maxQ₁ - maxQ₂)| ≤ supDistQ Q₁ Q₂
  apply abs_weighted_sum_le_bound _ _ (M.supDistQ Q₁ Q₂) (M.P_nonneg s a) (M.P_sum_one s a)
  intro s'
  -- |maxQ₁ s' - maxQ₂ s'| ≤ sup |Q₁ s' - Q₂ s'| ≤ supDistQ Q₁ Q₂
  have h1 : |maxQ₁ s' - maxQ₂ s'| ≤
      Finset.univ.sup' Finset.univ_nonempty (fun a' => |Q₁ s' a' - Q₂ s' a'|) :=
    M.sup_sub_sup_le (fun a' => Q₁ s' a') (fun a' => Q₂ s' a')
  have h2 : Finset.univ.sup' Finset.univ_nonempty (fun a' => |Q₁ s' a' - Q₂ s' a'|) ≤
      M.supDistQ Q₁ Q₂ := by
    apply Finset.sup'_le; intro a' _
    -- Goal: |Q₁ s' a' - Q₂ s' a'| ≤ supDistQ Q₁ Q₂
    simp only [supDistQ, supNormQ]
    exact le_trans
      (Finset.le_sup' (fun a => |Q₁ s' a - Q₂ s' a|) (Finset.mem_univ a'))
      (Finset.le_sup' (fun s => Finset.univ.sup' Finset.univ_nonempty
        (fun a => |Q₁ s a - Q₂ s a|)) (Finset.mem_univ s'))
  linarith

/-! ### Value Function Bounds -/

/-- Any value function satisfying the Bellman equation is bounded by V_max.
    Proof: From the Bellman equation, |V(s)| ≤ R_max + γ·max|V|.
    Taking max over s: max|V| ≤ R_max + γ·max|V|, so max|V| ≤ R_max/(1-γ). -/
theorem value_bounded_by_Vmax (V : M.StateValueFn) (π : M.StochasticPolicy)
    (hV : M.isValueOf V π) : ∀ s, |V s| ≤ M.V_max := by
  -- Step 1: For each s, |V s| ≤ R_max + γ * supNormV V
  have hstep : ∀ s, |V s| ≤ M.R_max + M.γ * M.supNormV V := by
    intro s
    rw [hV s]
    calc |M.expectedReward π s + M.γ * M.expectedNextValue π V s|
        ≤ |M.expectedReward π s| + |M.γ * M.expectedNextValue π V s| := abs_add_le _ _
      _ ≤ M.R_max + M.γ * M.supNormV V := by
          apply add_le_add
          · -- |expectedReward π s| ≤ R_max
            apply abs_weighted_sum_le_bound _ _ M.R_max (π.prob_nonneg s) (π.prob_sum_one s)
            intro a
            exact M.r_le_R_max s a
          · -- |γ * expectedNextValue π V s| ≤ γ * supNormV V
            rw [abs_mul, abs_of_nonneg M.γ_nonneg]
            apply mul_le_mul_of_nonneg_left _ M.γ_nonneg
            -- |expectedNextValue π V s| ≤ supNormV V
            unfold expectedNextValue
            apply abs_weighted_sum_le_bound _ _ (M.supNormV V)
              (π.prob_nonneg s) (π.prob_sum_one s)
            intro a
            apply abs_weighted_sum_le_bound _ _ (M.supNormV V)
              (M.P_nonneg s a) (M.P_sum_one s a)
            intro s'
            exact Finset.le_sup' (fun s => |V s|) (Finset.mem_univ s')
  -- Step 2: supNormV V ≤ R_max + γ * supNormV V
  have hsup : M.supNormV V ≤ M.R_max + M.γ * M.supNormV V :=
    Finset.sup'_le _ _ (fun s _ => hstep s)
  -- Step 3: (1-γ) * supNormV V ≤ R_max, so supNormV V ≤ V_max
  have hbound : M.supNormV V ≤ M.V_max := by
    have h1g : (0 : ℝ) < 1 - M.γ := by linarith [M.γ_lt_one]
    rw [V_max, le_div_iff₀ h1g]
    nlinarith [hsup]
  -- Step 4: For each s, |V s| ≤ supNormV V ≤ V_max
  intro s
  have hle : |V s| ≤ M.supNormV V := by
    simp only [supNormV]
    exact Finset.le_sup' (fun s => |V s|) (Finset.mem_univ s)
  linarith

end FiniteMDP

end
