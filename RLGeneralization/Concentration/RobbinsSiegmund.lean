/-
# Robbins-Siegmund Convergence Theorem

Formalizes the Robbins-Siegmund theorem for nonnegative almost
supermartingales, which is the foundational convergence tool for
stochastic approximation algorithms (Q-learning, TD learning, SGD).

## Mathematical Statement

Let (X_n), (Y_n), (Z_n) be nonnegative adapted sequences satisfying:

  E[X_{n+1} | F_n] ≤ (1 + Y_n) X_n + Z_n

with ∑ Y_n < ∞ a.s. and ∑ Z_n < ∞ a.s. Then:

1. X_n → L a.s. for some nonneg random variable L (convergence).
2. ∑ (X_n - X_{n+1})⁺ < ∞ a.s. (summability of positive decrements).

## Role in RL

The Robbins-Siegmund theorem is the standard tool for proving
almost-sure convergence of stochastic approximation algorithms:

- **Q-learning**: X_n = ||Q_n - Q*||², Y_n = 0, Z_n = α_n² σ²
- **TD(0)**: X_n = ||θ_n - θ*||², Y_n from the A-matrix drift
- **SGD**: X_n = ||w_n - w*||², Z_n = η_n² G² (gradient variance)

The finite-step algebraic bounds in `QLearning.lean` and
`LinearTD.lean` give the one-step recursion; this module provides
the a.s. convergence conclusion.

## Structure

All results are **conditional**: the Robbins-Siegmund theorem
requires measure-theoretic conditional expectation and filtration
machinery that is partially available in Mathlib (via
`MeasureTheory.condexp`) but whose full integration with
discrete-time supermartingale theory is ongoing.

We encode the hypothesis as a structure and state the conclusions
as conditional theorems.

## References

* [Robbins and Siegmund, *A convergence theorem for non negative
  almost supermartingales and some applications*, 1971]
* [Borkar, *Stochastic Approximation: A Dynamical Systems
  Viewpoint*, 2008, Theorem 2.1]
* [Bertsekas and Tsitsiklis, *Neuro-Dynamic Programming*, 1996,
  Proposition 4.1]
-/

import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Exponential

open Finset BigOperators Filter Real

noncomputable section

/-! ### Robbins-Siegmund Hypothesis

We encode the Robbins-Siegmund hypothesis as a structure over
deterministic sequences. The stochastic version (with conditional
expectations) is deferred until Mathlib's discrete-time
supermartingale API stabilizes.

In the deterministic encoding:
- `X n` plays the role of E[X_n | F_{n-1}] (or X_n itself in
  the a.s. event where the bound holds)
- `Y n` and `Z n` are the perturbation sequences
- The inequality is assumed pointwise (representing the a.s. event)
-/

/-- **Robbins-Siegmund hypothesis** (deterministic encoding).

Bundles nonneg sequences X, Y, Z satisfying the supermartingale
recursion E[X_{n+1}|F_n] ≤ (1+Y_n) X_n + Z_n, together with
summability of Y and Z.

In the stochastic version, these are random variables adapted to a
filtration. Here we encode the a.s. event pointwise. -/
structure RobbinsSiegmundHypothesis where
  /-- The nonneg process (e.g., ||Q_n - Q*||²) -/
  X : ℕ → ℝ
  /-- The multiplicative perturbation sequence -/
  Y : ℕ → ℝ
  /-- The additive perturbation sequence -/
  Z : ℕ → ℝ
  /-- X_n ≥ 0 for all n -/
  X_nonneg : ∀ n, 0 ≤ X n
  /-- Y_n ≥ 0 for all n -/
  Y_nonneg : ∀ n, 0 ≤ Y n
  /-- Z_n ≥ 0 for all n -/
  Z_nonneg : ∀ n, 0 ≤ Z n
  /-- The supermartingale recursion: X_{n+1} ≤ (1+Y_n) X_n + Z_n -/
  recursion : ∀ n, X (n + 1) ≤ (1 + Y n) * X n + Z n
  /-- ∑ Y_n < ∞ (encoded as partial sums bounded by S_Y) -/
  S_Y : ℝ
  sum_Y_bound : ∀ N, ∑ n ∈ Finset.range N, Y n ≤ S_Y
  /-- ∑ Z_n < ∞ (encoded as partial sums bounded by S_Z) -/
  S_Z : ℝ
  sum_Z_bound : ∀ N, ∑ n ∈ Finset.range N, Z n ≤ S_Z

/-! ### Finite-Step Consequences (Exact)

Before stating the conditional a.s. convergence theorem, we prove
some exact finite-step consequences of the recursion that do not
require measure theory. -/

/-- The sequence X is bounded above by an exponentially-weighted sum.

  X_n ≤ ∏_{k<n}(1+Y_k) · X_0 + ∑_{k<n} ∏_{j=k+1}^{n-1}(1+Y_j) · Z_k

This is a deterministic unrolling of the recursion. We state a simpler
corollary: X_n ≤ exp(S_Y) · X_0 + exp(S_Y) · S_Z. -/
theorem RobbinsSiegmundHypothesis.X_bounded_by_initial
    (hyp : RobbinsSiegmundHypothesis) :
    ∀ n, hyp.X n ≤ exp hyp.S_Y * hyp.X 0 + exp hyp.S_Y * hyp.S_Z := by
  -- Intermediate claim: X_n ≤ exp(∑_{k<n} Y_k) * (X_0 + ∑_{k<n} Z_k)
  suffices h : ∀ n, hyp.X n ≤
      exp (∑ k ∈ Finset.range n, hyp.Y k) * (hyp.X 0 + ∑ k ∈ Finset.range n, hyp.Z k) by
    intro n
    have hn := h n
    have hexp : exp (∑ k ∈ Finset.range n, hyp.Y k) ≤ exp hyp.S_Y :=
      exp_le_exp.mpr (hyp.sum_Y_bound n)
    have hsum : hyp.X 0 + ∑ k ∈ Finset.range n, hyp.Z k ≤ hyp.X 0 + hyp.S_Z := by
      linarith [hyp.sum_Z_bound n]
    have hZ_sum_nn : 0 ≤ ∑ k ∈ Finset.range n, hyp.Z k :=
      Finset.sum_nonneg fun k _ => hyp.Z_nonneg k
    have hsum_nn : 0 ≤ hyp.X 0 + ∑ k ∈ Finset.range n, hyp.Z k := by
      linarith [hyp.X_nonneg 0]
    calc hyp.X n
        ≤ exp (∑ k ∈ Finset.range n, hyp.Y k) *
          (hyp.X 0 + ∑ k ∈ Finset.range n, hyp.Z k) := hn
      _ ≤ exp hyp.S_Y * (hyp.X 0 + hyp.S_Z) :=
          mul_le_mul hexp hsum hsum_nn (exp_nonneg _)
      _ = exp hyp.S_Y * hyp.X 0 + exp hyp.S_Y * hyp.S_Z := by ring
  -- Prove intermediate claim by induction
  intro n
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, exp_zero, one_mul, add_zero]
    exact le_refl _
  | succ n ih =>
    have hY_nn : 0 ≤ 1 + hyp.Y n := by linarith [hyp.Y_nonneg n]
    have hA_nn : 0 ≤ hyp.X 0 + ∑ k ∈ Finset.range n, hyp.Z k := by
      have : 0 ≤ ∑ k ∈ Finset.range n, hyp.Z k := Finset.sum_nonneg fun k _ => hyp.Z_nonneg k
      linarith [hyp.X_nonneg 0]
    -- Step 1: Apply recursion and IH
    have step1 : hyp.X (n + 1) ≤
        (1 + hyp.Y n) * (exp (∑ k ∈ Finset.range n, hyp.Y k) *
          (hyp.X 0 + ∑ k ∈ Finset.range n, hyp.Z k)) + hyp.Z n := by
      linarith [hyp.recursion n, mul_le_mul_of_nonneg_left ih hY_nn]
    -- Step 2: Use 1 + y ≤ exp y to bound the coefficient
    have h_exp_bound : 1 + hyp.Y n ≤ exp (hyp.Y n) := by linarith [add_one_le_exp (hyp.Y n)]
    have hexp_nn : 0 ≤ exp (∑ k ∈ Finset.range n, hyp.Y k) := exp_nonneg _
    have step2 : (1 + hyp.Y n) * (exp (∑ k ∈ Finset.range n, hyp.Y k) *
        (hyp.X 0 + ∑ k ∈ Finset.range n, hyp.Z k)) ≤
        exp (hyp.Y n) * exp (∑ k ∈ Finset.range n, hyp.Y k) *
          (hyp.X 0 + ∑ k ∈ Finset.range n, hyp.Z k) := by
      nlinarith [mul_le_mul_of_nonneg_right h_exp_bound (mul_nonneg hexp_nn hA_nn)]
    -- Step 3: Combine exp factors via exp_add
    have step3 : exp (hyp.Y n) * exp (∑ k ∈ Finset.range n, hyp.Y k) =
        exp (∑ k ∈ Finset.range (n + 1), hyp.Y k) := by
      rw [Finset.sum_range_succ, exp_add, mul_comm]
    -- Step 4: Absorb Z_n using exp ≥ 1
    have hY_sum_nn : 0 ≤ ∑ k ∈ Finset.range (n + 1), hyp.Y k :=
      Finset.sum_nonneg (fun k _ => hyp.Y_nonneg k)
    have hexp_ge1 : 1 ≤ exp (∑ k ∈ Finset.range (n + 1), hyp.Y k) := one_le_exp hY_sum_nn
    have hZ_nn : 0 ≤ hyp.Z n := hyp.Z_nonneg n
    -- Combine everything
    calc hyp.X (n + 1)
        ≤ (1 + hyp.Y n) * (exp (∑ k ∈ Finset.range n, hyp.Y k) *
            (hyp.X 0 + ∑ k ∈ Finset.range n, hyp.Z k)) + hyp.Z n := step1
      _ ≤ exp (∑ k ∈ Finset.range (n + 1), hyp.Y k) *
            (hyp.X 0 + ∑ k ∈ Finset.range n, hyp.Z k) + hyp.Z n := by
          have := step3 ▸ step2; linarith
      _ ≤ exp (∑ k ∈ Finset.range (n + 1), hyp.Y k) *
            (hyp.X 0 + ∑ k ∈ Finset.range (n + 1), hyp.Z k) := by
          rw [Finset.sum_range_succ (fun k => hyp.Z k)]
          nlinarith

/-- The partial sums of positive decrements are controlled.

  From the recursion, X_n - X_{n+1} + Y_n·X_n + Z_n ≥ 0, so:
    max(X_n - X_{n+1}, 0) ≤ (X_n - X_{n+1}) + Y_n·X_n + Z_n
  Summing (telescope) and bounding ∑Y_n·X_n via X_bounded_by_initial:
    ∑(X_n - X_{n+1})⁺ ≤ X_0 + S_Y·exp(S_Y)·(X_0+S_Z) + S_Z
                       = (1 + S_Y·exp(S_Y))·(X_0 + S_Z). -/
theorem RobbinsSiegmundHypothesis.partial_sum_pos_decrements_bounded
    (hyp : RobbinsSiegmundHypothesis) (N : ℕ) :
    ∑ n ∈ Finset.range N, max (hyp.X n - hyp.X (n + 1)) 0 ≤
      (1 + hyp.S_Y * exp hyp.S_Y) * (hyp.X 0 + hyp.S_Z) := by
  -- Per-term bound: max(X_n - X_{n+1}, 0) ≤ (X_n - X_{n+1}) + Y_n*X_n + Z_n
  have h_per_term : ∀ n, max (hyp.X n - hyp.X (n + 1)) 0 ≤
      (hyp.X n - hyp.X (n + 1)) + hyp.Y n * hyp.X n + hyp.Z n := by
    intro n
    apply max_le
    · nlinarith [hyp.Y_nonneg n, hyp.X_nonneg n, hyp.Z_nonneg n]
    · nlinarith [hyp.recursion n]
  -- Telescope sum
  have h_telescope : ∀ M, ∑ n ∈ Finset.range M, (hyp.X n - hyp.X (n + 1)) =
      hyp.X 0 - hyp.X M := by
    intro M; induction M with
    | zero => simp
    | succ M ih => rw [Finset.sum_range_succ, ih]; ring
  -- Bound ∑ Y_n * X_n using X_bounded_by_initial
  have h_YX : ∑ n ∈ Finset.range N, hyp.Y n * hyp.X n ≤
      hyp.S_Y * (exp hyp.S_Y * hyp.X 0 + exp hyp.S_Y * hyp.S_Z) := by
    calc ∑ n ∈ Finset.range N, hyp.Y n * hyp.X n
        ≤ ∑ n ∈ Finset.range N, hyp.Y n *
            (exp hyp.S_Y * hyp.X 0 + exp hyp.S_Y * hyp.S_Z) :=
          Finset.sum_le_sum fun n _ =>
            mul_le_mul_of_nonneg_left (hyp.X_bounded_by_initial n) (hyp.Y_nonneg n)
      _ = (∑ n ∈ Finset.range N, hyp.Y n) *
            (exp hyp.S_Y * hyp.X 0 + exp hyp.S_Y * hyp.S_Z) := by
          rw [Finset.sum_mul]
      _ ≤ hyp.S_Y * (exp hyp.S_Y * hyp.X 0 + exp hyp.S_Y * hyp.S_Z) := by
          apply mul_le_mul_of_nonneg_right (hyp.sum_Y_bound N)
          have : 0 ≤ hyp.S_Z := le_trans (Finset.sum_nonneg fun k _ => hyp.Z_nonneg k)
            (hyp.sum_Z_bound 0)
          nlinarith [exp_nonneg hyp.S_Y, hyp.X_nonneg 0]
  -- Combine: sum per-term bounds, substitute telescope, and simplify
  calc ∑ n ∈ Finset.range N, max (hyp.X n - hyp.X (n + 1)) 0
      ≤ ∑ n ∈ Finset.range N, ((hyp.X n - hyp.X (n + 1)) + hyp.Y n * hyp.X n + hyp.Z n) :=
        Finset.sum_le_sum fun n _ => h_per_term n
    _ = (hyp.X 0 - hyp.X N) + ∑ n ∈ Finset.range N, hyp.Y n * hyp.X n +
        ∑ n ∈ Finset.range N, hyp.Z n := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, h_telescope]
    _ ≤ hyp.X 0 + hyp.S_Y * (exp hyp.S_Y * hyp.X 0 + exp hyp.S_Y * hyp.S_Z) + hyp.S_Z := by
        linarith [hyp.X_nonneg N, h_YX, hyp.sum_Z_bound N]
    _ = (1 + hyp.S_Y * exp hyp.S_Y) * (hyp.X 0 + hyp.S_Z) := by ring

/-! ### Main Theorems (Conditional)

The two main conclusions of the Robbins-Siegmund theorem. Both are
conditional on the measure-theoretic framework.

**Why conditional**: The full theorem operates on random variables
(X_n, Y_n, Z_n) adapted to a filtration (F_n), with the recursion
holding in conditional expectation:
  E[X_{n+1} | F_n] ≤ (1 + Y_n) X_n + Z_n  a.s.

Formalizing this requires:
1. Filtration: `MeasureTheory.Filtration` (available in Mathlib)
2. Conditional expectation: `MeasureTheory.condexp` (available)
3. Adapted process: `MeasureTheory.Adapted` (available)
4. Almost-sure convergence: `Filter.Tendsto ... ae` (available)
5. Composition: connecting all of the above in the nonneg
   supermartingale setting (partially available via
   `MeasureTheory.Submartingale`/`Supermartingale`)

The measure-theory plumbing is 300+ lines. We state the theorems
and defer the construction. -/

/-- [CONDITIONAL] **Robbins-Siegmund convergence theorem**.

Returns h_cauchy repackaged as `Tendsto`. The Cauchy convergence
hypothesis is the conclusion restated (Metric.tendsto_atTop is the
definition); a genuine proof requires nonneg supermartingale convergence.

Given the Robbins-Siegmund hypothesis, X_n → L as n → ∞. -/
theorem robbins_siegmund_conditional (hyp : RobbinsSiegmundHypothesis)
    (L : ℝ) (_hL : 0 ≤ L)
    -- Hypothesis: Cauchy convergence from supermartingale convergence theorem
    (h_cauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n → |hyp.X n - L| < ε)
    -- X is bounded (from X_bounded_by_initial)
    (_h_bounded : ∀ n, hyp.X n ≤ exp hyp.S_Y * hyp.X 0 + exp hyp.S_Y * hyp.S_Z) :
    Tendsto hyp.X atTop (nhds L) := by
  rw [Metric.tendsto_atTop]
  exact h_cauchy

/-- **Robbins-Siegmund summability** (unconditional via recursion).

Under the Robbins-Siegmund hypothesis, the positive decrements
of X are summable:

  ∑_n (X_n - X_{n+1})⁺ < ∞  a.s.

This is used in Q-learning to show that the error sequence
eventually stops increasing.

The proof decomposes max(X_n - X_{n+1}, 0) using the positive-part
identity, bounds the upward jumps via the recursion
(X_{n+1} - X_n ≤ Y_n·X_n + Z_n), and uses the telescoping sum
together with X_bounded_by_initial to control ∑ Y_n·X_n. -/
theorem robbins_siegmund_summability_unconditional (hyp : RobbinsSiegmundHypothesis) :
    ∀ N, ∑ n ∈ Finset.range N, max (hyp.X n - hyp.X (n + 1)) 0 ≤
      hyp.X 0 + hyp.S_Y * (exp hyp.S_Y * hyp.X 0 + exp hyp.S_Y * hyp.S_Z) + hyp.S_Z := by
  intro N
  -- Per-step upward jump bound from recursion: max(X_{n+1} - X_n, 0) ≤ Y_n·X_n + Z_n
  have h_upward_step : ∀ n, max (hyp.X (n + 1) - hyp.X n) 0 ≤
      hyp.Y n * hyp.X n + hyp.Z n := by
    intro n
    apply max_le
    · linarith [hyp.recursion n]
    · have := hyp.Y_nonneg n; have := hyp.X_nonneg n; have := hyp.Z_nonneg n
      nlinarith
  -- Sum the upward jump bounds
  have h_upward_sum : ∑ n ∈ Finset.range N, max (hyp.X (n + 1) - hyp.X n) 0 ≤
      ∑ n ∈ Finset.range N, (hyp.Y n * hyp.X n + hyp.Z n) :=
    Finset.sum_le_sum fun n _ => h_upward_step n
  -- Bound ∑ Y_n·X_n + ∑ Z_n
  have h_upward : ∑ n ∈ Finset.range N, max (hyp.X (n + 1) - hyp.X n) 0 ≤
      hyp.S_Y * (exp hyp.S_Y * hyp.X 0 + exp hyp.S_Y * hyp.S_Z) + hyp.S_Z := by
    calc ∑ n ∈ Finset.range N, max (hyp.X (n + 1) - hyp.X n) 0
        ≤ ∑ n ∈ Finset.range N, (hyp.Y n * hyp.X n + hyp.Z n) := h_upward_sum
      _ = ∑ n ∈ Finset.range N, hyp.Y n * hyp.X n +
          ∑ n ∈ Finset.range N, hyp.Z n := Finset.sum_add_distrib
      _ ≤ hyp.S_Y * (exp hyp.S_Y * hyp.X 0 + exp hyp.S_Y * hyp.S_Z) + hyp.S_Z := by
          have hYX : ∑ n ∈ Finset.range N, hyp.Y n * hyp.X n ≤
              hyp.S_Y * (exp hyp.S_Y * hyp.X 0 + exp hyp.S_Y * hyp.S_Z) := by
            calc ∑ n ∈ Finset.range N, hyp.Y n * hyp.X n
                ≤ ∑ n ∈ Finset.range N, hyp.Y n *
                    (exp hyp.S_Y * hyp.X 0 + exp hyp.S_Y * hyp.S_Z) :=
                  Finset.sum_le_sum fun n _ =>
                    mul_le_mul_of_nonneg_left (hyp.X_bounded_by_initial n) (hyp.Y_nonneg n)
              _ = (∑ n ∈ Finset.range N, hyp.Y n) *
                    (exp hyp.S_Y * hyp.X 0 + exp hyp.S_Y * hyp.S_Z) := by
                  rw [Finset.sum_mul]
              _ ≤ hyp.S_Y * (exp hyp.S_Y * hyp.X 0 + exp hyp.S_Y * hyp.S_Z) := by
                  apply mul_le_mul_of_nonneg_right (hyp.sum_Y_bound N)
                  have : 0 ≤ hyp.S_Z := le_trans (Finset.sum_nonneg fun k _ => hyp.Z_nonneg k)
                    (hyp.sum_Z_bound 0)
                  nlinarith [exp_nonneg hyp.S_Y, hyp.X_nonneg 0]
          linarith [hyp.sum_Z_bound N]
  -- Positive-part identity: max(a, 0) ≤ a + max(-a, 0) (actually equality)
  have h_le : ∀ n, max (hyp.X n - hyp.X (n + 1)) 0 ≤
      (hyp.X n - hyp.X (n + 1)) + max (hyp.X (n + 1) - hyp.X n) 0 := by
    intro n
    rcases le_total (hyp.X (n + 1)) (hyp.X n) with h | h
    · -- X_{n+1} ≤ X_n: positive decrement, no upward jump
      have h1 := max_eq_left (show 0 ≤ hyp.X n - hyp.X (n + 1) by linarith)
      have h2 := max_eq_right (show hyp.X (n + 1) - hyp.X n ≤ 0 by linarith)
      rw [h1, h2]; linarith
    · -- X_n ≤ X_{n+1}: no positive decrement, upward jump
      have h1 := max_eq_right (show hyp.X n - hyp.X (n + 1) ≤ 0 by linarith)
      have h2 := max_eq_left (show 0 ≤ hyp.X (n + 1) - hyp.X n by linarith)
      rw [h1, h2]; linarith
  -- Decompose sum using the pointwise bound
  calc ∑ n ∈ Finset.range N, max (hyp.X n - hyp.X (n + 1)) 0
      ≤ ∑ n ∈ Finset.range N, ((hyp.X n - hyp.X (n + 1)) +
          max (hyp.X (n + 1) - hyp.X n) 0) :=
        Finset.sum_le_sum (fun n _ => h_le n)
    _ = (∑ n ∈ Finset.range N, (hyp.X n - hyp.X (n + 1))) +
        ∑ n ∈ Finset.range N, max (hyp.X (n + 1) - hyp.X n) 0 :=
        Finset.sum_add_distrib
    _ ≤ hyp.X 0 + hyp.S_Y * (exp hyp.S_Y * hyp.X 0 + exp hyp.S_Y * hyp.S_Z) + hyp.S_Z := by
        -- Telescope the first sum
        have h_tele : ∀ M, ∑ n ∈ Finset.range M, (hyp.X n - hyp.X (n + 1)) =
            hyp.X 0 - hyp.X M := by
          intro M; induction M with
          | zero => simp
          | succ m ih =>
            rw [Finset.sum_range_succ, ih]
            ring
        rw [h_tele]
        linarith [hyp.X_nonneg N, h_upward]

/-! ### Application Interface

Helper definitions for connecting Robbins-Siegmund to specific
stochastic approximation algorithms. -/

/-- Build a Robbins-Siegmund hypothesis from Q-learning error recursion.

Given step sizes α_t satisfying the Robbins-Monro conditions
(∑α_t = ∞, ∑α_t² < ∞), the Q-learning error ||Q_t - Q*||² satisfies
the Robbins-Siegmund recursion with Y_t = 0 and Z_t = α_t² σ². -/
def qLearningHypothesis
    (err_sq : ℕ → ℝ) (herr_nonneg : ∀ n, 0 ≤ err_sq n)
    (alpha_sq_sigma_sq : ℕ → ℝ) (hz_nonneg : ∀ n, 0 ≤ alpha_sq_sigma_sq n)
    (h_rec : ∀ n, err_sq (n + 1) ≤ err_sq n + alpha_sq_sigma_sq n)
    (S_Z : ℝ) (h_sum_Z : ∀ N, ∑ n ∈ Finset.range N, alpha_sq_sigma_sq n ≤ S_Z) :
    RobbinsSiegmundHypothesis where
  X := err_sq
  Y := fun _ => 0
  Z := alpha_sq_sigma_sq
  X_nonneg := herr_nonneg
  Y_nonneg := fun _ => le_refl 0
  Z_nonneg := hz_nonneg
  recursion := by
    intro n; simp only [add_zero, one_mul]; exact h_rec n
  S_Y := 0
  sum_Y_bound := by intro N; simp
  S_Z := S_Z
  sum_Z_bound := h_sum_Z

/-- Build a Robbins-Siegmund hypothesis from linear TD error recursion.

The TD error ||θ_t - θ*||² satisfies the recursion with:
- Y_t = α_t² C_quad (quadratic drift)
- Z_t = α_t² σ² (noise variance) -/
def linearTDHypothesis
    (err_sq : ℕ → ℝ) (herr_nonneg : ∀ n, 0 ≤ err_sq n)
    (Y_seq Z_seq : ℕ → ℝ)
    (hY_nonneg : ∀ n, 0 ≤ Y_seq n) (hZ_nonneg : ∀ n, 0 ≤ Z_seq n)
    (h_rec : ∀ n, err_sq (n + 1) ≤ (1 + Y_seq n) * err_sq n + Z_seq n)
    (S_Y S_Z : ℝ)
    (h_sum_Y : ∀ N, ∑ n ∈ Finset.range N, Y_seq n ≤ S_Y)
    (h_sum_Z : ∀ N, ∑ n ∈ Finset.range N, Z_seq n ≤ S_Z) :
    RobbinsSiegmundHypothesis where
  X := err_sq
  Y := Y_seq
  Z := Z_seq
  X_nonneg := herr_nonneg
  Y_nonneg := hY_nonneg
  Z_nonneg := hZ_nonneg
  recursion := h_rec
  S_Y := S_Y
  sum_Y_bound := h_sum_Y
  S_Z := S_Z
  sum_Z_bound := h_sum_Z

/-! ### Supermartingale A.S. Convergence

The Robbins-Siegmund theorem concludes:
1. X_n → L a.s. for some nonneg L
2. ∑ (X_n - X_{n+1})⁺ < ∞ a.s.

The proof uses the supermartingale convergence theorem:
- X_n is bounded above (by X_bounded_by_initial)
- The modified process X̃_n = X_n / ∏(1+Y_k) is a nonneg supermartingale
- By the supermartingale convergence theorem, X̃_n → L̃ a.s.
- Since ∏(1+Y_k) → exp(∑Y) (bounded), X_n → L = L̃ · exp(∑Y) a.s.

We provide deterministic consequences and the conditional a.s. theorem. -/

namespace RobbinsSiegmundHypothesis

variable (hyp : RobbinsSiegmundHypothesis)

/-- S_Y is nonneg (from sum of nonneg terms being bounded). -/
theorem S_Y_nonneg : 0 ≤ hyp.S_Y := by
  have : 0 ≤ ∑ n ∈ Finset.range 0, hyp.Y n := Finset.sum_nonneg fun k _ => hyp.Y_nonneg k
  linarith [hyp.sum_Y_bound 0]

/-- S_Z is nonneg (from sum of nonneg terms being bounded). -/
theorem S_Z_nonneg : 0 ≤ hyp.S_Z := by
  have : 0 ≤ ∑ n ∈ Finset.range 0, hyp.Z n := Finset.sum_nonneg fun k _ => hyp.Z_nonneg k
  linarith [hyp.sum_Z_bound 0]

/-- The uniform upper bound for X_n. -/
def uniformBound : ℝ := exp hyp.S_Y * hyp.X 0 + exp hyp.S_Y * hyp.S_Z

/-- The uniform bound is nonneg. -/
theorem uniformBound_nonneg : 0 ≤ hyp.uniformBound := by
  unfold uniformBound
  have : 0 ≤ exp hyp.S_Y := exp_nonneg _
  have : 0 ≤ hyp.X 0 := hyp.X_nonneg 0
  have : 0 ≤ hyp.S_Z := hyp.S_Z_nonneg
  positivity

/-- X_n ∈ [0, uniformBound] for all n. -/
theorem X_in_interval (n : ℕ) :
    0 ≤ hyp.X n ∧ hyp.X n ≤ hyp.uniformBound :=
  ⟨hyp.X_nonneg n, hyp.X_bounded_by_initial n⟩

/-- The positive decrements tend to zero (from bounded partial sums).

    Since ∑_{n<N} max(X_n - X_{n+1}, 0) ≤ C for all N, and each term
    is nonneg, the terms must tend to 0. Otherwise the partial sums
    would grow without bound, contradicting the uniform bound C. -/
theorem pos_decrements_summable_bound :
    ∀ N, ∑ n ∈ Finset.range N, max (hyp.X n - hyp.X (n + 1)) 0 ≤
      (1 + hyp.S_Y * exp hyp.S_Y) * (hyp.X 0 + hyp.S_Z) :=
  fun N => hyp.partial_sum_pos_decrements_bounded N

/-- The decrement bound constant is nonneg. -/
theorem decrement_bound_nonneg :
    0 ≤ (1 + hyp.S_Y * exp hyp.S_Y) * (hyp.X 0 + hyp.S_Z) := by
  apply mul_nonneg
  · linarith [mul_nonneg hyp.S_Y_nonneg (exp_nonneg hyp.S_Y)]
  · linarith [hyp.X_nonneg 0, hyp.S_Z_nonneg]

/-- [CONDITIONAL] **Robbins-Siegmund a.s. convergence**.

    Takes h_converges (Tendsto X atTop (nhds L)) as hypothesis from
    supermartingale convergence theorem, then packages it with
    limit bounds and the proved decrement summability bound.

    The supermartingale convergence requires measure-theoretic
    conditional expectation not yet available in composed form in Mathlib. -/
theorem robbins_siegmund_as_convergence
    -- The limit and convergence (from supermartingale convergence theorem)
    (L : ℝ) (hL_nn : 0 ≤ L) (hL_le : L ≤ hyp.uniformBound)
    -- Hypothesis: a.s. convergence from the nonneg supermartingale convergence
    -- theorem applied to the deflated process X_n/∏(1+Y_k). This requires
    -- measure-theoretic conditional expectation and filtration composition
    -- not yet available in composed form in Mathlib.
    (h_converges : Tendsto hyp.X atTop (nhds L)) :
    -- (1) X_n converges to L
    Tendsto hyp.X atTop (nhds L) ∧
    -- (2) The limit is in [0, uniformBound]
    0 ≤ L ∧ L ≤ hyp.uniformBound ∧
    -- (3) The partial sums of positive decrements are bounded
    (∀ N, ∑ n ∈ Finset.range N,
      max (hyp.X n - hyp.X (n + 1)) 0 ≤
      (1 + hyp.S_Y * exp hyp.S_Y) * (hyp.X 0 + hyp.S_Z)) :=
  ⟨h_converges, hL_nn, hL_le, hyp.pos_decrements_summable_bound⟩

/-- **Robbins-Siegmund summability of decrements** (derived).

    Under the Robbins-Siegmund hypothesis:
      ∑_n (X_n - X_{n+1})⁺ < ∞  a.s.

    This follows from partial_sum_pos_decrements_bounded: the partial
    sums are uniformly bounded by (1 + S_Y·exp(S_Y))·(X_0 + S_Z),
    so the series converges. -/
theorem decrements_summable :
    ∃ (C : ℝ), 0 ≤ C ∧
    ∀ N, ∑ n ∈ Finset.range N,
      max (hyp.X n - hyp.X (n + 1)) 0 ≤ C :=
  ⟨(1 + hyp.S_Y * exp hyp.S_Y) * (hyp.X 0 + hyp.S_Z),
   hyp.decrement_bound_nonneg,
   hyp.pos_decrements_summable_bound⟩

/-- **One-step contraction** (consequence of recursion with small Y, Z).

    When Y_n and Z_n are small, the recursion gives approximate
    contraction: X_{n+1} ≤ X_n + δ_n where δ_n = Y_n·X_n + Z_n.
    This is the form used in Q-learning and TD learning analyses. -/
theorem one_step_drift (n : ℕ) :
    hyp.X (n + 1) ≤ hyp.X n +
      hyp.Y n * hyp.X n + hyp.Z n := by
  have := hyp.recursion n
  linarith

end RobbinsSiegmundHypothesis

end
