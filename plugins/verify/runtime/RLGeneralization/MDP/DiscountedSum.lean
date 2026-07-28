import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Discounted Sum Bounds

Standalone bounds for finite discounted sums, independent of MDP structure.
These are the foundational analytic lemmas that underpin value function
bounds across discounted RL theory.

## Main Results

* `geom_sum_le_inv_one_sub` — ∑ γ^i ≤ 1/(1-γ) for 0 ≤ γ < 1
* `discounted_sum_abs_le` — |∑ γ^i rᵢ| ≤ R_max/(1-γ) for bounded rewards
* `weighted_geom_sum_le` — ∑ k·γ^k ≤ γ/(1-γ)² for 0 ≤ γ < 1

## References

* Puterman, *Markov Decision Processes*, Ch. 5
* Sutton & Barto, *Reinforcement Learning: An Introduction*, Ch. 3
-/

open Finset BigOperators

/-- **Finite geometric sum bound**: for 0 ≤ γ < 1,
    ∑_{i=0}^{n-1} γ^i ≤ 1/(1-γ).

    The finite partial sum of a geometric series with ratio in [0,1)
    is bounded by the infinite series limit. This is the fundamental
    building block for discounted MDP value function bounds.
    Ref: Puterman, MDP Ch. 5. -/
theorem geom_sum_le_inv_one_sub {γ : ℝ} (hγ_nonneg : 0 ≤ γ) (hγ_lt : γ < 1)
    (n : ℕ) : ∑ i ∈ Finset.range n, γ ^ i ≤ 1 / (1 - γ) := by
  have h1 : γ ≠ 1 := ne_of_lt hγ_lt
  have hsub_pos : (0 : ℝ) < 1 - γ := by linarith
  have hγn_le : γ ^ n ≤ 1 := pow_le_one₀ hγ_nonneg hγ_lt.le
  have hγn_nonneg : 0 ≤ γ ^ n := pow_nonneg hγ_nonneg n
  rw [geom_sum_eq h1 n, le_div_iff₀ hsub_pos]
  have h_simp : (γ ^ n - 1) / (γ - 1) * (1 - γ) = 1 - γ ^ n := by
    have h_ne : γ - 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [h_simp]
  linarith

/-- **Discounted weighted sum bound**: for 0 ≤ γ < 1 and |rᵢ| ≤ R_max,
    |∑_{i=0}^{n-1} γ^i · rᵢ| ≤ R_max/(1-γ).

    Bounds the magnitude of any finite discounted reward sum. This is
    the sequence-level lemma underlying |V^π(s)| ≤ R_max/(1-γ) for
    discounted MDPs. Ref: Puterman, MDP Prop. 5.3.1. -/
theorem discounted_sum_abs_le {γ R_max : ℝ} (hγ_nonneg : 0 ≤ γ) (hγ_lt : γ < 1)
    (hR : 0 ≤ R_max) {r : ℕ → ℝ} (hr : ∀ i, |r i| ≤ R_max)
    (n : ℕ) : |∑ i ∈ Finset.range n, γ ^ i * r i| ≤ R_max / (1 - γ) := by
  have hsub_pos : (0 : ℝ) < 1 - γ := by linarith
  calc |∑ i ∈ Finset.range n, γ ^ i * r i|
      ≤ ∑ i ∈ Finset.range n, |γ ^ i * r i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ Finset.range n, γ ^ i * |r i| := by
        congr 1; ext i
        rw [abs_mul, abs_of_nonneg (pow_nonneg hγ_nonneg i)]
    _ ≤ ∑ i ∈ Finset.range n, γ ^ i * R_max := by
        apply Finset.sum_le_sum; intro i _
        exact mul_le_mul_of_nonneg_left (hr i) (pow_nonneg hγ_nonneg i)
    _ = R_max * ∑ i ∈ Finset.range n, γ ^ i := by
        rw [Finset.mul_sum]; congr 1; ext i; ring
    _ ≤ R_max * (1 / (1 - γ)) :=
        mul_le_mul_of_nonneg_left (geom_sum_le_inv_one_sub hγ_nonneg hγ_lt n) hR
    _ = R_max / (1 - γ) := by ring

/-! ### Weighted Geometric Sum -/

private lemma weighted_geom_identity (γ : ℝ) (n : ℕ) :
    (1 - γ) * ∑ k ∈ Finset.range (n + 1), (↑k : ℝ) * γ ^ k =
    ∑ k ∈ Finset.range n, γ ^ (k + 1) - ↑n * γ ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ (fun k => (↑k : ℝ) * γ ^ k), mul_add, ih,
        Finset.sum_range_succ (fun k => γ ^ (k + 1))]
    push_cast; ring

private lemma geom_sum_factor (γ : ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range n, γ ^ (k + 1) = γ * ∑ k ∈ Finset.range n, γ ^ k := by
  simp_rw [pow_succ']
  rw [← Finset.mul_sum]

/-- **Weighted geometric sum bound**: ∑_{k<n} k·γ^k ≤ γ/(1-γ)².

    The partial sum of the "derivative of the geometric series" is
    bounded by its infinite series value. Proof: multiply by (1-γ),
    use the algebraic identity to reduce to the ordinary geometric
    sum, then bound by 1/(1-γ).

    Used in discounted MDP sensitivity, policy gradient variance,
    and eligibility trace analysis. -/
theorem weighted_geom_sum_le (n : ℕ) {γ : ℝ}
    (hγ_nn : 0 ≤ γ) (hγ_lt : γ < 1) :
    ∑ k ∈ Finset.range n, (↑k : ℝ) * γ ^ k ≤ γ / (1 - γ) ^ 2 := by
  rcases n with _ | n
  · simp; positivity
  have h1γ : (0 : ℝ) < 1 - γ := by linarith
  rw [le_div_iff₀ (sq_pos_of_pos h1γ), sq]
  calc (∑ k ∈ Finset.range (n + 1), (↑k : ℝ) * γ ^ k) * ((1 - γ) * (1 - γ))
      = (1 - γ) * ((1 - γ) * ∑ k ∈ Finset.range (n + 1), (↑k : ℝ) * γ ^ k) := by
        ring
    _ = (1 - γ) * (∑ k ∈ Finset.range n, γ ^ (k + 1) - ↑n * γ ^ (n + 1)) := by
        rw [weighted_geom_identity]
    _ ≤ (1 - γ) * ∑ k ∈ Finset.range n, γ ^ (k + 1) := by
        apply mul_le_mul_of_nonneg_left _ h1γ.le
        linarith [mul_nonneg (Nat.cast_nonneg n) (pow_nonneg hγ_nn (n + 1))]
    _ = (1 - γ) * (γ * ∑ k ∈ Finset.range n, γ ^ k) := by
        rw [geom_sum_factor]
    _ ≤ (1 - γ) * (γ * (1 / (1 - γ))) := by
        apply mul_le_mul_of_nonneg_left _ h1γ.le
        exact mul_le_mul_of_nonneg_left
          (geom_sum_le_inv_one_sub hγ_nn hγ_lt n) hγ_nn
    _ = γ := by field_simp
