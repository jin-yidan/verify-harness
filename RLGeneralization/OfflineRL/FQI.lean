/-
# Fitted Q-Iteration (FQI) for Offline RL

Definitions for fitted Q-iteration. FQI is the offline analogue of
value iteration, where the Bellman backup is approximated via
regression on a fixed dataset.

## Main Definitions

* `OfflineDataset` - Fixed dataset of transitions
* `fittedBellmanBackup` - One step of FQI
* `concentrability` - Single-policy concentrability coefficient
* `inherent_bellman_error` - Approximation error of function class

## Main Results

* `fqi_error_propagation` - FQI error propagation:
  If Q_{k+1} = T(Q_k) + ε_k with ‖ε_k‖ ≤ ε for all k, then
  ‖Q_K - Q*‖ ≤ γ^K · ‖Q_0 - Q*‖ + ε / (1 - γ)

## References

* [Agarwal et al., *RL: Theory and Algorithms*]
-/

import RLGeneralization.MDP.BellmanContraction

open Finset BigOperators

noncomputable section

namespace FiniteMDP

variable (M : FiniteMDP)

/-! ### Offline Dataset -/

/-- An offline dataset of `(s, a, r, s')` transitions.
    In offline RL this dataset is fixed and not collected adaptively. -/
structure OfflineDataset (n : ℕ) where
  states : Fin n → M.S
  actions : Fin n → M.A
  rewards : Fin n → ℝ
  next_states : Fin n → M.S

/-! ### Concentrability -/

/-- **Single-policy concentrability coefficient**.

  C^π := max_{s,a} d^π(s,a) / ν(s,a)

  where ν is the data distribution and d^π is the occupancy
  measure of policy π. This measures how well the offline
  data covers the states visited by policy π.

  Stated as a bound: the ratio d^π/ν is at most C. -/
structure Concentrability where
  /-- The concentrability coefficient -/
  C : ℝ
  hC : 0 < C

-- Inherent Bellman error: ε_F := max_h sup_{f∈F} inf_{g∈F} ‖Tf-g‖
-- Requires infimum over F, stated as parameter in theorems.

/-! ### Auxiliary: supDistQ with perturbation -/

/-- The sup norm ‖Q₁ - Q₂‖ bounds each pointwise difference. -/
lemma pointwise_le_supDistQ (Q₁ Q₂ : M.ActionValueFn) (s : M.S) (a : M.A) :
    |Q₁ s a - Q₂ s a| ≤ M.supDistQ Q₁ Q₂ := by
  simp only [supDistQ, supNormQ]
  exact le_trans
    (Finset.le_sup' (fun a => |Q₁ s a - Q₂ s a|) (Finset.mem_univ a))
    (Finset.le_sup' (fun s => Finset.univ.sup' Finset.univ_nonempty
      (fun a => |Q₁ s a - Q₂ s a|)) (Finset.mem_univ s))

/-! ### Geometric sum bound -/

/-- The partial geometric sum ∑_{i=0}^{n-1} γ^i ≤ 1/(1-γ). -/
lemma geom_sum_le_inv (n : ℕ) :
    ∑ i ∈ Finset.range n, M.γ ^ i ≤ 1 / (1 - M.γ) := by
  have h1g : (0 : ℝ) < 1 - M.γ := by linarith [M.γ_lt_one]
  have hγ_ne_one : M.γ ≠ 1 := ne_of_lt M.γ_lt_one
  rw [geom_sum_eq hγ_ne_one]
  -- (γ^n - 1) / (γ - 1) = (1 - γ^n) / (1 - γ) ≤ 1 / (1 - γ)
  rw [show M.γ ^ n - 1 = -(1 - M.γ ^ n) from by ring,
      show M.γ - 1 = -(1 - M.γ) from by ring, neg_div_neg_eq]
  apply div_le_div_of_nonneg_right _ h1g.le
  linarith [pow_nonneg M.γ_nonneg n]

/-! ### FQI Error Propagation -/

/-- **One-step approximate contraction**: If Q* is a fixed point
    of the Bellman optimality operator T, then for any Q-function
    and perturbation ε_fn:
      ‖(T(Q) + ε_fn) - Q*‖ ≤ γ · ‖Q - Q*‖ + ‖ε_fn‖_∞

    This captures one step of FQI where regression introduces
    per-step error ε_fn. -/
lemma fqi_one_step
    (Q Q_star ε_fn : M.ActionValueFn)
    (hQ_star : Q_star = M.bellmanOptOp Q_star) :
    M.supDistQ (fun s a => M.bellmanOptOp Q s a + ε_fn s a) Q_star ≤
      M.γ * M.supDistQ Q Q_star + M.supNormQ ε_fn := by
  -- Strategy: pointwise bound, then take sup.
  -- |(TQ + ε)(s,a) - Q*(s,a)| = |(TQ(s,a) - TQ*(s,a)) + ε(s,a)|
  --                             ≤ |TQ(s,a) - TQ*(s,a)| + |ε(s,a)|
  -- The first term, after taking sup, gives ‖TQ - TQ*‖ ≤ γ‖Q - Q*‖.
  -- The second term gives ‖ε‖.
  simp only [supDistQ, supNormQ]
  apply Finset.sup'_le; intro s _
  apply Finset.sup'_le; intro a _
  -- Rewrite Q* as TQ* in the subtraction
  have hQsa : Q_star s a = M.bellmanOptOp Q_star s a :=
    congr_fun (congr_fun hQ_star s) a
  have hsplit : M.bellmanOptOp Q s a + ε_fn s a - Q_star s a =
      (M.bellmanOptOp Q s a - M.bellmanOptOp Q_star s a) + ε_fn s a := by
    rw [hQsa]; ring
  calc |M.bellmanOptOp Q s a + ε_fn s a - Q_star s a|
      = |(M.bellmanOptOp Q s a - M.bellmanOptOp Q_star s a) + ε_fn s a| := by
        rw [hsplit]
    _ ≤ |M.bellmanOptOp Q s a - M.bellmanOptOp Q_star s a| + |ε_fn s a| :=
        abs_add_le _ _
    _ ≤ M.γ * (Finset.univ.sup' Finset.univ_nonempty fun s =>
          Finset.univ.sup' Finset.univ_nonempty fun a =>
            |Q s a - Q_star s a|) +
        (Finset.univ.sup' Finset.univ_nonempty fun s =>
          Finset.univ.sup' Finset.univ_nonempty fun a =>
            |ε_fn s a|) := by
      apply add_le_add
      · -- |TQ(s,a) - TQ*(s,a)| ≤ γ · supDistQ Q Q*
        -- Use the contraction: supDistQ (TQ) (TQ*) ≤ γ · supDistQ Q Q*
        -- and pointwise ≤ sup
        have hpw : |M.bellmanOptOp Q s a - M.bellmanOptOp Q_star s a| ≤
            M.supDistQ (M.bellmanOptOp Q) (M.bellmanOptOp Q_star) :=
          M.pointwise_le_supDistQ (M.bellmanOptOp Q) (M.bellmanOptOp Q_star) s a
        exact le_trans hpw (M.bellmanOptOp_contraction Q Q_star)
      · -- |ε_fn s a| ≤ supNormQ ε_fn
        exact le_trans
          (Finset.le_sup' (fun a => |ε_fn s a|) (Finset.mem_univ a))
          (Finset.le_sup' (fun s => Finset.univ.sup' Finset.univ_nonempty
            (fun a => |ε_fn s a|)) (Finset.mem_univ s))

/-- **Contraction core for fitted Q-iteration**.

  After K iterations of Fitted Q-Iteration with per-step error
  ||epsilon_k||_inf <= epsilon (from regression on offline data),
  the Q-function error satisfies:

    ||Q_K - Q*||_inf <= gamma^K * ||Q_0 - Q*||_inf + epsilon/(1-gamma)

  The gamma^K term decays the initialization error exponentially,
  while epsilon/(1-gamma) is the steady-state error from per-step
  regression noise. Proved by induction using the one-step bound
  ||Q_{k+1} - Q*|| <= gamma ||Q_k - Q*|| + epsilon and summing
  the geometric series.

  **Caveat**: This is the contraction core only. The full
  The full offline-RL bound additionally involves the concentrability coefficient
  C^pi and inherent Bellman error, relating epsilon to the
  function class and data distribution. Those statistical
  components are not formalized here. -/
theorem fqi_error_propagation
    (Q_star : M.ActionValueFn)
    (hQ_star : Q_star = M.bellmanOptOp Q_star)
    -- The FQI iterates Q_0, Q_1, ..., Q_K
    (Q : ℕ → M.ActionValueFn)
    -- Per-step regression errors
    (ε_fn : ℕ → M.ActionValueFn)
    -- FQI update: Q_{k+1} = T(Q_k) + ε_k
    (hUpdate : ∀ k s a,
      Q (k + 1) s a = M.bellmanOptOp (Q k) s a + ε_fn k s a)
    -- Per-step error bound
    (ε : ℝ) (hε : 0 ≤ ε)
    (hε_bound : ∀ k, M.supNormQ (ε_fn k) ≤ ε)
    -- Conclusion
    (K : ℕ) :
    M.supDistQ (Q K) Q_star ≤
      M.γ ^ K * M.supDistQ (Q 0) Q_star + ε / (1 - M.γ) := by
  -- We first prove the tighter bound with partial geometric sum,
  -- then relax to ε/(1-γ).
  suffices h : M.supDistQ (Q K) Q_star ≤
      M.γ ^ K * M.supDistQ (Q 0) Q_star +
        ε * ∑ i ∈ Finset.range K, M.γ ^ i by
    calc M.supDistQ (Q K) Q_star
        ≤ M.γ ^ K * M.supDistQ (Q 0) Q_star +
            ε * ∑ i ∈ Finset.range K, M.γ ^ i := h
      _ ≤ M.γ ^ K * M.supDistQ (Q 0) Q_star +
            ε * (1 / (1 - M.γ)) := by
          gcongr
          exact M.geom_sum_le_inv K
      _ = M.γ ^ K * M.supDistQ (Q 0) Q_star +
            ε / (1 - M.γ) := by ring
  -- Main induction on K
  induction K with
  | zero => simp
  | succ n ih =>
    -- One-step bound: ‖Q_{n+1} - Q*‖ ≤ γ · ‖Q_n - Q*‖ + ε
    have hstep : M.supDistQ (Q (n + 1)) Q_star ≤
        M.γ * M.supDistQ (Q n) Q_star + ε := by
      -- Q(n+1) = TQ(n) + ε_fn(n) pointwise
      have hdist_eq : M.supDistQ (Q (n + 1)) Q_star =
          M.supDistQ (fun s a => M.bellmanOptOp (Q n) s a + ε_fn n s a) Q_star := by
        simp only [supDistQ, supNormQ]
        congr 1; funext s; congr 1; funext a
        congr 1; congr 1
        exact hUpdate n s a
      rw [hdist_eq]
      calc M.supDistQ (fun s a => M.bellmanOptOp (Q n) s a + ε_fn n s a) Q_star
          ≤ M.γ * M.supDistQ (Q n) Q_star + M.supNormQ (ε_fn n) :=
            M.fqi_one_step (Q n) Q_star (ε_fn n) hQ_star
        _ ≤ M.γ * M.supDistQ (Q n) Q_star + ε := by
            gcongr; exact hε_bound n
    -- Combine with inductive hypothesis
    have hγ_nn : 0 ≤ M.γ := M.γ_nonneg
    -- Key sum identity: γ · ∑_{i<n} γ^i + 1 = ∑_{i<n+1} γ^i
    have hsum_key : M.γ * (∑ i ∈ Finset.range n, M.γ ^ i) + 1 =
        ∑ i ∈ Finset.range (n + 1), M.γ ^ i := by
      rw [Finset.mul_sum, Finset.sum_range_succ', pow_zero]
      congr 1
      apply Finset.sum_congr rfl; intro i _
      rw [pow_succ, mul_comm]
    -- Set local names for the sums to help nlinarith
    set S := ∑ i ∈ Finset.range n, M.γ ^ i with hS_def
    set S' := ∑ i ∈ Finset.range (n + 1), M.γ ^ i with hS'_def
    calc M.supDistQ (Q (n + 1)) Q_star
        ≤ M.γ * M.supDistQ (Q n) Q_star + ε := hstep
      _ ≤ M.γ * (M.γ ^ n * M.supDistQ (Q 0) Q_star + ε * S) + ε := by
          linarith [mul_le_mul_of_nonneg_left ih hγ_nn]
      _ = M.γ ^ (n + 1) * M.supDistQ (Q 0) Q_star + ε * S' := by
          have hpow : M.γ ^ (n + 1) = M.γ ^ n * M.γ := pow_succ M.γ n
          rw [hpow]; nlinarith [hsum_key]

end FiniteMDP

end
