/-
# Value Iteration

Formalizes the convergence of Q-value iteration for discounted MDPs.

## Main Results

* `value_iteration_geometric_error` - Q-function convergence:
    ‖Q^(k) - Q*‖_∞ ≤ γ^k · ‖Q^(0) - Q*‖_∞
* `value_iteration_threshold` - Iteration threshold:
    K ≥ log(C/ε)/(1-γ) ⟹ ‖Q_K - Q*‖_∞ ≤ ε
* `q_error_amplification` - Greedy-policy
  suboptimality ≤ 2‖Q-Q*‖/(1-γ)
* `value_iteration_policy_bound` - Raw policy bound:
  combines the above with `q_error_amplification`, but does not package
  the threshold-to-ε-optimal-policy corollary

## References

* [Agarwal et al., *RL: Theory and Algorithms*][agarwal2026]
-/

import RLGeneralization.MDP.BellmanContraction
import RLGeneralization.MDP.BanachFixedPoint
import RLGeneralization.MDP.PolicyIteration
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Finset BigOperators

noncomputable section

namespace FiniteMDP

variable (M : FiniteMDP)

/-! ### Value Iteration -/

/-- Q-value iteration: repeatedly apply the Bellman optimality
    operator starting from `Q^0 = 0`.
    `Q^{k+1}(s,a) = r(s,a) + γ ∑_{s'} P(s'|s,a) max_{a'} Q^k(s',a')`. -/
def valueIterationQ (k : ℕ) : M.ActionValueFn :=
  M.bellmanOptOp^[k] (fun _ _ => 0)

/-- Value iteration step unfolds correctly. -/
lemma valueIterationQ_succ (n : ℕ) :
    M.valueIterationQ (n + 1) =
    M.bellmanOptOp (M.valueIterationQ n) := by
  unfold valueIterationQ
  rw [Function.iterate_succ']
  rfl

/-- **Value iteration geometric error**.

  If Q* is a fixed point of T (i.e., Q* = TQ*), then:
    ‖Q^(k) - Q*‖_∞ ≤ γ^k · ‖Q^(0) - Q*‖_∞

  This is the Q-function convergence half of the standard value-iteration argument.
  The full policy guarantee additionally requires applying `q_error_amplification`
  (q_error_amplification) to conclude that the greedy policy
  w.r.t. Q^(k) is ε-optimal after sufficiently many iterations.

  See `value_iteration_policy_bound` below for the combined
  statement. -/
theorem value_iteration_geometric_error
    (Q_star : M.ActionValueFn)
    (hQ_star : Q_star = M.bellmanOptOp Q_star)
    (k : ℕ) :
    M.supDistQ (M.valueIterationQ k) Q_star ≤
      M.γ ^ k * M.supDistQ (M.valueIterationQ 0) Q_star := by
  induction k with
  | zero => simp
  | succ n ih =>
    -- Key step: use Q* = T(Q*) to apply contraction
    have hkey : M.supDistQ
        (M.bellmanOptOp (M.valueIterationQ n)) Q_star ≤
        M.γ * M.supDistQ (M.valueIterationQ n) Q_star := by
      have heq : M.supDistQ
          (M.bellmanOptOp (M.valueIterationQ n)) Q_star =
          M.supDistQ (M.bellmanOptOp (M.valueIterationQ n))
            (M.bellmanOptOp Q_star) := by
        -- Q_star s a = bellmanOptOp Q_star s a everywhere
        simp only [supDistQ, supNormQ]
        congr 1; funext s; congr 1; funext a
        rw [show Q_star s a = M.bellmanOptOp Q_star s a from
          congr_fun (congr_fun hQ_star s) a]
      rw [heq]; exact M.bellmanOptOp_contraction _ _
    calc M.supDistQ (M.valueIterationQ (n + 1)) Q_star
        = M.supDistQ
            (M.bellmanOptOp (M.valueIterationQ n)) Q_star := by
          rw [M.valueIterationQ_succ n]
      _ ≤ M.γ * M.supDistQ (M.valueIterationQ n) Q_star :=
          hkey
      _ ≤ M.γ * (M.γ ^ n *
            M.supDistQ (M.valueIterationQ 0) Q_star) :=
          mul_le_mul_of_nonneg_left ih M.γ_nonneg
      _ = M.γ ^ (n + 1) *
            M.supDistQ (M.valueIterationQ 0) Q_star := by
          rw [pow_succ]; ring

/-- **γ^k exponential decay** used for the iteration threshold.
  γ^k ≤ exp(-(1-γ)·k) for γ ∈ [0,1).
  Uses Mathlib's `one_sub_div_pow_le_exp_neg`. -/
theorem gamma_pow_le_exp_neg (k : ℕ) (hk : 0 < k) :
    M.γ ^ k ≤ Real.exp (-((1 - M.γ) * k)) := by
  have hle : (1 - M.γ) * k ≤ k := by
    have : 1 - M.γ ≤ 1 := by linarith [M.γ_nonneg]
    exact mul_le_of_le_one_left (Nat.cast_nonneg k) this
  calc M.γ ^ k = (1 - (1 - M.γ)) ^ k := by ring_nf
    _ = (1 - ((1 - M.γ) * k) / k) ^ k := by
        congr 1; rw [mul_div_cancel_right₀]
        exact Nat.cast_ne_zero.mpr (by omega)
    _ ≤ Real.exp (-((1 - M.γ) * k)) :=
        Real.one_sub_div_pow_le_exp_neg hle

/-- **Value-iteration convergence threshold**.

  After K ≥ log(C / ε) / (1 − γ) iterations of Q-value iteration,
  ‖Q_K − Q*‖_∞ ≤ ε, where C = ‖Q_0 − Q*‖_∞.

  Proof outline:
  1. `value_iteration_geometric_error` gives ‖Q_K − Q*‖ ≤ γ^K · C.
  2. `gamma_pow_le_exp_neg` gives γ^K ≤ exp(−(1−γ)K).
  3. The hypothesis K ≥ log(C/ε)/(1−γ) implies (1−γ)K ≥ log(C/ε),
     so exp(−(1−γ)K) ≤ ε/C. Hence γ^K · C ≤ ε. -/
theorem value_iteration_threshold
    (Q_star : M.ActionValueFn)
    (hQ_star : Q_star = M.bellmanOptOp Q_star)
    (ε : ℝ) (hε : 0 < ε)
    (C : ℝ) (hC : 0 < C)
    (hC_bound : M.supDistQ (M.valueIterationQ 0) Q_star ≤ C)
    (K : ℕ) (hK_pos : 0 < K)
    (hK : Real.log (C / ε) / (1 - M.γ) ≤ K) :
    M.supDistQ (M.valueIterationQ K) Q_star ≤ ε := by
  have h1g : (0 : ℝ) < 1 - M.γ := by linarith [M.γ_lt_one]
  -- Step 1: ‖Q_K - Q*‖ ≤ γ^K * ‖Q_0 - Q*‖ ≤ γ^K * C
  have hge := M.value_iteration_geometric_error Q_star hQ_star K
  have hge_C : M.supDistQ (M.valueIterationQ K) Q_star ≤ M.γ ^ K * C := by
    calc M.supDistQ (M.valueIterationQ K) Q_star
        ≤ M.γ ^ K * M.supDistQ (M.valueIterationQ 0) Q_star := hge
      _ ≤ M.γ ^ K * C := by
          apply mul_le_mul_of_nonneg_left hC_bound
          exact pow_nonneg M.γ_nonneg K
  -- Step 2: γ^K ≤ exp(-(1-γ)K)
  have hexp := M.gamma_pow_le_exp_neg K hK_pos
  -- Step 3: (1-γ)K ≥ log(C/ε), so exp(-(1-γ)K) ≤ ε/C
  have hεC : 0 < ε / C := div_pos hε hC
  have h_ineq : Real.log (C / ε) ≤ (1 - M.γ) * ↑K := by
    rwa [div_le_iff₀ h1g, mul_comm] at hK
  have hexp_le : Real.exp (-((1 - M.γ) * ↑K)) ≤ ε / C := by
    -- exp(-(1-γ)K) ≤ exp(-log(C/ε)) = exp(log(ε/C)) = ε/C
    calc Real.exp (-((1 - M.γ) * ↑K))
        ≤ Real.exp (-(Real.log (C / ε))) := by
          exact Real.exp_le_exp.mpr (neg_le_neg h_ineq)
      _ = Real.exp (Real.log (ε / C)) := by
          congr 1; rw [Real.log_div (ne_of_gt hC) (ne_of_gt hε)]
          rw [Real.log_div (ne_of_gt hε) (ne_of_gt hC)]; ring
      _ = ε / C := Real.exp_log hεC
  -- Step 4: γ^K * C ≤ exp(-(1-γ)K) * C ≤ (ε/C) * C = ε
  calc M.supDistQ (M.valueIterationQ K) Q_star
      ≤ M.γ ^ K * C := hge_C
    _ ≤ Real.exp (-((1 - M.γ) * K)) * C := by
        exact mul_le_mul_of_nonneg_right hexp hC.le
    _ ≤ (ε / C) * C := by
        exact mul_le_mul_of_nonneg_right hexp_le hC.le
    _ = ε := div_mul_cancel₀ ε hC.ne'

/-! ### Q-Error Amplification -/

/-- **Q-error amplification**.

  If ‖Q - Q*‖_∞ ≤ ε, then for any greedy action selector
  â(s) = argmax_a Q(s,a), the suboptimality satisfies:
    ∀ s, Q*(s, a*(s)) - Q*(s, â(s)) ≤ 2ε
  and consequently V*(s) - V^{π_Q}(s) ≤ 2ε / (1-γ).

  Informal proof sketch:
  Let a = π_Q(s). Then V*(s) - V^π(s) decomposes as:
    [V*(s) - Q*(s,a)]  ≤ 2‖Q-Q*‖ (greediness + triangle ineq)
    [Q*(s,a) - V^π(s)] = γ·P·(V*-V^π)(s,a) ≤ γΔ (Bellman)
  Solving Δ ≤ 2D + γΔ gives Δ ≤ 2D/(1-γ).

  **Caveat**: The Lean version assumes the greedy action selector
  `a_gr` and its maximality property `h_gr` as inputs, rather than
  constructing argmax internally. This avoids the need to define
  argmax for real-valued functions on finite types. The standard presentation
  implicitly constructs the greedy policy. -/
theorem q_error_amplification
    -- The Q-function we're approximating with
    (Q : M.ActionValueFn)
    -- Optimal Q* and V*
    (Q_star : M.ActionValueFn)
    (V_star : M.StateValueFn)
    (hV_star : ∀ s, V_star s =
      Finset.univ.sup' Finset.univ_nonempty (Q_star s))
    (hQ_star : ∀ s a, Q_star s a =
      M.r s a + M.γ * ∑ s', M.P s a s' * V_star s')
    -- Value of the greedy policy π_Q
    (V_pi : M.StateValueFn)
    -- Greedy action selection and its properties
    (a_gr : M.S → M.A)
    -- (i) a_gr maximizes Q at each state
    (h_gr : ∀ s a, Q s a ≤ Q s (a_gr s))
    -- (ii) V^π satisfies Bellman for the greedy policy
    (hV_pi : ∀ s, V_pi s = M.r s (a_gr s) +
      M.γ * ∑ s', M.P s (a_gr s) s' * V_pi s') :
    ∀ s, V_star s - V_pi s ≤
      2 * M.supDistQ Q Q_star / (1 - M.γ) := by
  set D := M.supDistQ Q Q_star
  -- Use one-sided sup (not absolute value) since V* ≥ V^π
  set Δ := Finset.univ.sup' Finset.univ_nonempty
    (fun s => V_star s - V_pi s)
  have h1g : (0 : ℝ) < 1 - M.γ := by linarith [M.γ_lt_one]
  -- Helper: ‖Q - Q*‖ bound for specific (s,a)
  have hD : ∀ s a, |Q s a - Q_star s a| ≤ D := fun s a => by
    simp only [D, supDistQ, supNormQ]
    exact le_trans
      (Finset.le_sup' (fun a => |Q s a - Q_star s a|)
        (Finset.mem_univ a))
      (Finset.le_sup' (fun s => Finset.univ.sup'
        Finset.univ_nonempty (fun a => |Q s a - Q_star s a|))
        (Finset.mem_univ s))
  -- Helper: V*(s') - V^π(s') ≤ Δ
  have hΔ_le : ∀ s', V_star s' - V_pi s' ≤ Δ :=
    fun s' => Finset.le_sup'
      (fun s => V_star s - V_pi s) (Finset.mem_univ s')
  -- Step 1: For each s: V*(s) - V^π(s) ≤ 2D + γΔ
  have hstep : ∀ s, V_star s - V_pi s ≤ 2 * D + M.γ * Δ := by
    intro s
    -- Term 1: V*(s) - Q*(s, a_gr s) ≤ 2D
    have h_t1 : V_star s - Q_star s (a_gr s) ≤ 2 * D := by
      rw [hV_star s]
      -- sup Q*(s,·) ≤ Q*(s,a_gr s) + 2D
      suffices hsup : Finset.univ.sup' Finset.univ_nonempty
          (Q_star s) ≤ Q_star s (a_gr s) + 2 * D by linarith
      apply Finset.sup'_le; intro a' _
      have h1 : Q_star s a' ≤ Q s a' + D := by
        linarith [neg_abs_le (Q s a' - Q_star s a'), hD s a']
      have h2 : Q s a' ≤ Q s (a_gr s) := h_gr s a'
      have h3 : Q s (a_gr s) ≤ Q_star s (a_gr s) + D := by
        linarith [le_abs_self (Q s (a_gr s) -
          Q_star s (a_gr s)), hD s (a_gr s)]
      linarith
    -- Term 2: Q*(s,a_gr s) - V^π(s) ≤ γΔ
    have h_t2 : Q_star s (a_gr s) - V_pi s ≤ M.γ * Δ := by
      rw [hQ_star s (a_gr s), hV_pi s]
      -- r + γPV* - (r + γPV^π) = γ·∑P·(V*-V^π) ≤ γΔ
      -- Direct one-sided bound (no absolute values needed)
      have hsum_le : ∑ s', M.P s (a_gr s) s' * V_star s' -
          ∑ s', M.P s (a_gr s) s' * V_pi s' ≤ Δ := by
        rw [← Finset.sum_sub_distrib]
        have hsub : ∀ s' : M.S,
            M.P s (a_gr s) s' * V_star s' -
            M.P s (a_gr s) s' * V_pi s' =
            M.P s (a_gr s) s' * (V_star s' - V_pi s') :=
          fun _ => by ring
        simp_rw [hsub]
        calc ∑ s', M.P s (a_gr s) s' *
              (V_star s' - V_pi s')
            ≤ ∑ s', M.P s (a_gr s) s' * Δ := by
              apply Finset.sum_le_sum; intro s' _
              exact mul_le_mul_of_nonneg_left (hΔ_le s')
                (M.P_nonneg s (a_gr s) s')
          _ = (∑ s', M.P s (a_gr s) s') * Δ :=
              (Finset.sum_mul _ _ _).symm
          _ = Δ := by rw [M.P_sum_one s (a_gr s), one_mul]
      linarith [mul_le_mul_of_nonneg_left hsum_le M.γ_nonneg]
    linarith
  -- Step 2: Δ ≤ 2D + γΔ (take sup of hstep)
  have hsup : Δ ≤ 2 * D + M.γ * Δ :=
    Finset.sup'_le _ _ (fun s _ => hstep s)
  -- Step 3: Solve Δ ≤ 2D/(1-γ)
  have hΔ : Δ ≤ 2 * D / (1 - M.γ) := by
    rw [le_div_iff₀ h1g]; nlinarith
  -- Step 4: Pointwise conclusion
  intro s
  linarith [hΔ_le s]

/-! ### Value-Iteration Policy Guarantee -/

/-- **Value-iteration policy bound**.

  Combines `value_iteration_geometric_error` with
  `q_error_amplification` for the raw inequality:

    V*(s) - V^{π}(s) ≤ 2·γ^k·‖Q^(0)-Q*‖_∞ / (1-γ)

  This is weaker than the standard ε-optimality corollary, which states
  the iteration threshold k ≥ ... ⟹ ε-optimal. We prove
  only the raw bound, and we assume an externally-supplied
  greedy selector `a_gr` and its Bellman equation `hV_pi`
  rather than constructing the greedy policy. -/
theorem value_iteration_policy_bound
    (Q_star : M.ActionValueFn)
    (hQ_star_fp : Q_star = M.bellmanOptOp Q_star)
    (V_star : M.StateValueFn)
    (hV_star : ∀ s, V_star s =
      Finset.univ.sup' Finset.univ_nonempty (Q_star s))
    (hQ_star_bellman : ∀ s a, Q_star s a =
      M.r s a + M.γ * ∑ s', M.P s a s' * V_star s')
    (k : ℕ)
    (V_pi : M.StateValueFn)
    (a_gr : M.S → M.A)
    (h_gr : ∀ s a,
      M.valueIterationQ k s a ≤
      M.valueIterationQ k s (a_gr s))
    (hV_pi : ∀ s, V_pi s = M.r s (a_gr s) +
      M.γ * ∑ s', M.P s (a_gr s) s' * V_pi s') :
    ∀ s, V_star s - V_pi s ≤
      2 * (M.γ ^ k *
        M.supDistQ (M.valueIterationQ 0) Q_star) /
        (1 - M.γ) := by
  have h_ge := M.value_iteration_geometric_error
    Q_star hQ_star_fp k
  have h_amp := M.q_error_amplification
    (M.valueIterationQ k) Q_star V_star
    hV_star hQ_star_bellman V_pi a_gr h_gr hV_pi
  intro s
  calc V_star s - V_pi s
      ≤ 2 * M.supDistQ (M.valueIterationQ k) Q_star /
          (1 - M.γ) := h_amp s
    _ ≤ 2 * (M.γ ^ k *
          M.supDistQ (M.valueIterationQ 0) Q_star) /
          (1 - M.γ) := by
        have h1g : (0 : ℝ) < 1 - M.γ := by
          linarith [M.γ_lt_one]
        apply div_le_div_of_nonneg_right _ h1g.le
        exact mul_le_mul_of_nonneg_left h_ge
          (by positivity)

/-- **Value-iteration bound with a constructed greedy policy**.
  Uses `greedyAction` to eliminate the external selector
  assumption from `value_iteration_policy_bound`. -/
theorem value_iteration_with_greedy
    (Q_star : M.ActionValueFn)
    (hQ_star_fp : Q_star = M.bellmanOptOp Q_star)
    (V_star : M.StateValueFn)
    (hV_star : ∀ s, V_star s =
      Finset.univ.sup' Finset.univ_nonempty (Q_star s))
    (hQ_star_bellman : ∀ s a, Q_star s a =
      M.r s a + M.γ * ∑ s', M.P s a s' * V_star s')
    (k : ℕ) (V_greedy : M.StateValueFn)
    (hV_greedy : ∀ s, V_greedy s =
      M.r s (M.greedyAction (M.valueIterationQ k) s) +
      M.γ * ∑ s', M.P s
        (M.greedyAction (M.valueIterationQ k) s) s' *
        V_greedy s') :
    ∀ s, V_star s - V_greedy s ≤
      2 * (M.γ ^ k *
        M.supDistQ (M.valueIterationQ 0) Q_star) /
        (1 - M.γ) :=
  M.value_iteration_policy_bound Q_star hQ_star_fp
    V_star hV_star hQ_star_bellman k V_greedy
    (M.greedyAction (M.valueIterationQ k))
    (fun s a => M.greedyAction_spec
      (M.valueIterationQ k) s a) hV_greedy

/-! ### ε-Optimal Policy Corollary -/

/-- **Value-iteration ε-optimality (with externally supplied V_greedy)**.
    After K ≥ log(C/ε)/(1-γ) iterations, a greedy-policy value function
    satisfying the Bellman equation for `greedyAction Q_K` is
    2ε/(1-γ)-close to V*.

    This is the core composition of `value_iteration_threshold`
    (Q-convergence) with `q_error_amplification` (Q-to-policy conversion).
    The V_greedy witness is supplied externally; see
    `value_iteration_epsilon_optimal_constructed` for the version that
    builds V_greedy internally via Banach fixed point.

    This packages the usual convergence-threshold and greedy-policy
    conversion steps into one theorem. -/
theorem value_iteration_epsilon_optimal
    (Q_star : M.ActionValueFn)
    (hQ_star_fp : Q_star = M.bellmanOptOp Q_star)
    (V_star : M.StateValueFn)
    (hV_star : ∀ s, V_star s =
      Finset.univ.sup' Finset.univ_nonempty (Q_star s))
    (hQ_star_bellman : ∀ s a, Q_star s a =
      M.r s a + M.γ * ∑ s', M.P s a s' * V_star s')
    (ε : ℝ) (hε : 0 < ε)
    (C : ℝ) (hC : 0 < C)
    (hC_bound : M.supDistQ (M.valueIterationQ 0) Q_star ≤ C)
    (K : ℕ) (hK_pos : 0 < K)
    (hK : Real.log (C / ε) / (1 - M.γ) ≤ K)
    (V_greedy : M.StateValueFn)
    (hV_greedy : ∀ s, V_greedy s =
      M.r s (M.greedyAction (M.valueIterationQ K) s) +
      M.γ * ∑ s', M.P s
        (M.greedyAction (M.valueIterationQ K) s) s' *
        V_greedy s') :
    ∀ s, V_star s - V_greedy s ≤ 2 * ε / (1 - M.γ) := by
  -- Step 1: ‖Q_K - Q*‖ ≤ ε (from the iteration threshold)
  have h_Qconv := M.value_iteration_threshold Q_star hQ_star_fp
    ε hε C hC hC_bound K hK_pos hK
  -- Step 2: V*(s) - V_greedy(s) ≤ 2‖Q_K - Q*‖/(1-γ) (Q-error amplification)
  have h_amp := M.q_error_amplification
    (M.valueIterationQ K) Q_star V_star
    hV_star hQ_star_bellman V_greedy
    (M.greedyAction (M.valueIterationQ K))
    (fun s a => M.greedyAction_spec (M.valueIterationQ K) s a)
    hV_greedy
  -- Step 3: 2‖Q_K - Q*‖/(1-γ) ≤ 2ε/(1-γ)
  have h1g : (0 : ℝ) < 1 - M.γ := by linarith [M.γ_lt_one]
  intro s
  calc V_star s - V_greedy s
      ≤ 2 * M.supDistQ (M.valueIterationQ K) Q_star /
          (1 - M.γ) := h_amp s
    _ ≤ 2 * ε / (1 - M.γ) := by
        apply div_le_div_of_nonneg_right _ h1g.le
        exact mul_le_mul_of_nonneg_left h_Qconv (by norm_num)

/-- **Value-iteration ε-optimality (self-contained)**.
    After K ≥ log(C/ε)/(1-γ) iterations of Q-value iteration,
    the greedy policy w.r.t. Q_K has value within 2ε/(1-γ) of V*.

    Unlike `value_iteration_epsilon_optimal`, this version constructs
    the greedy-policy value function internally via Banach fixed point,
    rather than requiring it as an external witness.

    This follows the standard value-iteration-to-greedy-policy route.
    Our formalization separates
    Q-convergence (value_iteration_threshold) from policy conversion
    (q_error_amplification) and constructs the greedy-policy value
    via the contraction-mapping fixed point. -/
theorem value_iteration_epsilon_optimal_constructed
    (Q_star : M.ActionValueFn)
    (hQ_star_fp : Q_star = M.bellmanOptOp Q_star)
    (V_star : M.StateValueFn)
    (hV_star : ∀ s, V_star s =
      Finset.univ.sup' Finset.univ_nonempty (Q_star s))
    (hQ_star_bellman : ∀ s a, Q_star s a =
      M.r s a + M.γ * ∑ s', M.P s a s' * V_star s')
    (ε : ℝ) (hε : 0 < ε)
    (C : ℝ) (hC : 0 < C)
    (hC_bound : M.supDistQ (M.valueIterationQ 0) Q_star ≤ C)
    (K : ℕ) (hK_pos : 0 < K)
    (hK : Real.log (C / ε) / (1 - M.γ) ≤ K) :
    ∀ s₀, V_star s₀ -
      M.valueFromQ
        (M.greedyStochasticPolicy (M.valueIterationQ K))
        (M.actionValueFixedPoint
          (M.greedyStochasticPolicy (M.valueIterationQ K))) s₀ ≤
      2 * ε / (1 - M.γ) := by
  intro s₀
  -- Construct the greedy policy and its value via Banach fixed point
  set π_K := M.greedyStochasticPolicy (M.valueIterationQ K) with hπ_K
  set Q_πK := M.actionValueFixedPoint π_K
  set V_greedy := M.valueFromQ π_K Q_πK
  -- V_greedy satisfies the Bellman equation for π_K
  have hV_isVal : M.isValueOf V_greedy π_K :=
    M.valueFromQ_isValueOf π_K Q_πK
      (M.actionValueFixedPoint_isActionValueOf π_K)
  -- For the greedy policy, the stochastic Bellman reduces to deterministic
  have hV_det : ∀ s, V_greedy s =
      M.r s (M.greedyAction (M.valueIterationQ K) s) +
      M.γ * ∑ s', M.P s
        (M.greedyAction (M.valueIterationQ K) s) s' *
        V_greedy s' := by
    intro s
    have hbellman := hV_isVal s
    rw [M.greedyPolicy_expectedReward (M.valueIterationQ K) s,
        M.greedyPolicy_expectedNextValue (M.valueIterationQ K)
          V_greedy s] at hbellman
    exact hbellman
  -- Apply the existing epsilon-optimal theorem
  exact M.value_iteration_epsilon_optimal Q_star hQ_star_fp V_star
    hV_star hQ_star_bellman ε hε C hC hC_bound K hK_pos hK
    V_greedy hV_det s₀

end FiniteMDP

end
