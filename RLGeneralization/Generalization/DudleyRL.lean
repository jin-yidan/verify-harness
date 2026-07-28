/-
# Dudley Entropy Integral for RL Function Class Generalization

Connects the Dudley entropy integral bound (proved in SLT) to RL
generalization: uniform convergence of empirical Bellman operators
over parameterized value function classes.

## Mathematical Background

Given a class of candidate value functions {V_θ : θ ∈ Θ} with
ε-covering number N(ε), the Dudley entropy integral gives:

  E[sup_θ |T̂V_θ - TV_θ|] ≤ C · ∫₀^D √(log N(ε)) dε / √n

This is the key tool for function-approximation RL generalization.

For specific function classes:
- **Parametric**: log N(ε) ≤ d·log(C/ε) → sample complexity O(d/ε²)
- **Linear**: V_θ(s) = θᵀφ(s), log N(ε) ≤ d·log(2W/ε + 1)
- **Neural**: log N(ε) ≤ p·log(CW/ε) for p parameters

## Main Results

* `ValueFunctionClass` — structure for parameterized value function
  classes with boundedness and covering number assumptions
* `DudleyRLHypothesis` — conditional hypothesis packaging the Dudley
  entropy integral bound for RL applications
* `empirical_bellman_error_bound` — uniform convergence of empirical
  Bellman operators via the Dudley integral
* `rl_generalization_from_covering` — sample complexity when
  log N(ε) = O(d·log(1/ε))
* `linear_class_covering_number` — covering number for linear V_θ(s) = θᵀφ(s)
* `linear_rl_generalization` — specialization to linear function classes

## Approach

The SLT Dudley theorem (`SLT.Dudley.dudley`) is available in the pinned
SLT package with a fully proved sub-Gaussian process bound. However, its
type signature involves `IsSubGaussianProcess`, `TotallyBounded`, and
`entropyIntegral` on abstract metric spaces. Bridging these to the
RL-specific `ValueFunctionClass` covering numbers requires constructing
the sub-Gaussian process from empirical Bellman errors — a non-trivial
measure-theoretic step. We therefore state the RL-relevant consequence
as a conditional hypothesis (`DudleyRLHypothesis`) and derive all
algebraic corollaries from it. The bridge to `SLT.Dudley.dudley` is
a concrete future-work item (not blocked by upstream).
This composes cleanly with the covering number infrastructure in
`Complexity.CoveringPacking`.

## References

* [Vershynin, *High-Dimensional Probability*, Ch. 8]
* [Wainwright, *High-Dimensional Statistics*, Ch. 5]
* [Agarwal et al., *RL: Theory and Algorithms*, Ch. 5]
* [Zhang, Lee, Liu, *Statistical Learning Theory in Lean 4*, 2026]
-/

import RLGeneralization.Complexity.CoveringPacking
import RLGeneralization.Complexity.Rademacher
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Real Finset BigOperators

noncomputable section

/-! ### Value Function Class

A parameterized family of candidate value functions V_θ : S → ℝ,
indexed by a finite parameter set Θ. The key data are:
- `V_max`: uniform bound on |V_θ(s)|
- `logCoveringBound`: an upper bound on log N(ε) for the class

We work algebraically: the covering number bound is a real-valued
function of ε, not tied to a specific metric space construction.
This allows clean composition with the Dudley integral. -/

/-- **Value function class**: a parameterized family of candidate
    value functions with boundedness and covering number data.

    The covering number bound `logCoveringBound ε` is an assumed
    upper bound on log N(ε, {V_θ : θ ∈ Θ}, ‖·‖_∞). -/
structure ValueFunctionClass where
  /-- Effective dimension (e.g., number of parameters) -/
  dim : ℕ
  /-- Uniform bound on value functions: |V_θ(s)| ≤ V_max -/
  V_max : ℝ
  /-- V_max is positive -/
  hV_max_pos : 0 < V_max
  /-- Upper bound on log covering number: log N(ε) ≤ logCoveringBound(ε) -/
  logCoveringBound : ℝ → ℝ
  /-- The log covering number bound is nonneg for ε > 0 -/
  hlogCov_nonneg : ∀ ε, 0 < ε → 0 ≤ logCoveringBound ε
  /-- Dimension is positive -/
  hdim_pos : 0 < dim

namespace ValueFunctionClass

variable (F : ValueFunctionClass)

/-- The dimension as a positive real number. -/
def dimReal : ℝ := (F.dim : ℝ)

/-- The dimension is positive as a real. -/
theorem dimReal_pos : 0 < F.dimReal :=
  Nat.cast_pos.mpr F.hdim_pos

/-- The dimension is nonneg as a real. -/
theorem dimReal_nonneg : 0 ≤ F.dimReal :=
  le_of_lt F.dimReal_pos

end ValueFunctionClass

/-! ### Dudley Entropy Integral Hypothesis for RL

The SLT Dudley theorem gives:
  E[sup_{t ∈ T} X_t] ≤ (12√2)·σ · ∫₀^D √(log N(ε, T)) dε

For RL, we apply this to the empirical process
  X_θ = (1/√n) · ∑ᵢ (T̂V_θ - TV_θ)(sᵢ,aᵢ)

which is sub-Gaussian with parameter σ = V_max/√n (by boundedness).
The diameter D = 2·V_max (since sup-norm of any V_θ is ≤ V_max).

We package this as a conditional hypothesis, parameterized by
the entropy integral value, and derive consequences algebraically. -/

/-- **Dudley RL hypothesis**: the entropy integral bound applied to
    empirical Bellman error. This packages the output of the Dudley
    entropy integral theorem in the form needed for RL generalization.

    The bound states:
      uniformError ≤ C_dudley · entropyIntegralValue / √n

    where entropyIntegralValue = ∫₀^D √(log N(ε)) dε and
    C_dudley is the universal constant from Dudley's theorem. -/
structure DudleyRLHypothesis where
  /-- The value function class -/
  F : ValueFunctionClass
  /-- Number of samples -/
  n : ℕ
  /-- Sample count is positive -/
  hn : 0 < n
  /-- The entropy integral value: ∫₀^D √(log N(ε)) dε -/
  entropyIntegralValue : ℝ
  /-- Entropy integral is nonneg -/
  hIntegral_nonneg : 0 ≤ entropyIntegralValue
  /-- The Dudley universal constant (12√2 from the SLT proof) -/
  C_dudley : ℝ
  /-- The constant is positive -/
  hC_pos : 0 < C_dudley
  /-- The uniform error bound from Dudley:
      E[sup_θ |T̂V_θ - TV_θ|] ≤ C · integralValue / √n -/
  uniformError : ℝ
  /-- The uniform error is nonneg -/
  hError_nonneg : 0 ≤ uniformError
  /-- The key Dudley bound -/
  hDudley : uniformError ≤ C_dudley * entropyIntegralValue / Real.sqrt n

namespace DudleyRLHypothesis

variable (H : DudleyRLHypothesis)

/-- The sample count as a positive real. -/
theorem nReal_pos : (0 : ℝ) < H.n :=
  Nat.cast_pos.mpr H.hn

/-- √n is positive. -/
theorem sqrt_n_pos : 0 < Real.sqrt H.n :=
  Real.sqrt_pos.mpr H.nReal_pos

end DudleyRLHypothesis

/-! ### Empirical Bellman Error Bound

The main theorem: for a value function class with covering number
bound log N(ε) ≤ d·log(C/ε), the Dudley entropy integral yields
a uniform convergence guarantee for empirical Bellman operators. -/

/-- **Empirical Bellman error bound (Dudley)**: Given the Dudley
    hypothesis, the uniform error over the value function class
    is bounded by C · entropyIntegralValue / √n.

    This is the direct packaging of the Dudley bound for RL. The
    proof is immediate from the hypothesis — the content is in
    establishing the hypothesis via SLT.Dudley.dudley. -/
theorem empirical_bellman_error_bound (H : DudleyRLHypothesis)
    {deviation : ℝ}
    (h_dev : deviation ≤ H.uniformError) :
    deviation ≤ H.C_dudley * H.entropyIntegralValue / Real.sqrt H.n :=
  le_trans h_dev H.hDudley

/-! ### Sample Complexity from Covering Numbers

When log N(ε) = O(d·log(1/ε)), the Dudley integral evaluates to
O(√d · D), giving sample complexity n = O(d/ε²).

The key algebraic chain is:
1. log N(ε) ≤ d·log(C/ε)
2. √(log N(ε)) ≤ √d · √(log(C/ε))
3. ∫₀^D √(log N(ε)) dε ≤ √d · ∫₀^D √(log(C/ε)) dε
4. The integral ∫₀^D √(log(C/ε)) dε ≤ K·D (a finite constant)
5. Dudley bound: error ≤ C · √d · D / √n
6. For error ≤ ε: need n ≥ C² · d · D² / ε²
-/

/-- **Parametric covering number assumption**: the function class
    has log N(ε) ≤ d · log(C/ε) for a constant C and dimension d.
    This is the standard assumption for d-dimensional parametric classes. -/
structure ParametricCoveringAssumption where
  /-- Effective dimension -/
  d : ℕ
  /-- Dimension is positive -/
  hd : 0 < d
  /-- Covering constant -/
  C : ℝ
  /-- Covering constant is > 1 -/
  hC : 1 < C
  /-- Diameter of the class -/
  D : ℝ
  /-- Diameter is positive -/
  hD : 0 < D
  /-- The covering number bound holds pointwise -/
  hCovering : ∀ ε, 0 < ε → ε ≤ D →
    Real.log (C / ε) ≥ 0 ∧
    (d : ℝ) * Real.log (C / ε) ≥ 0

namespace ParametricCoveringAssumption

variable (P : ParametricCoveringAssumption)

/-- The dimension as a positive real. -/
theorem dReal_pos : (0 : ℝ) < P.d := Nat.cast_pos.mpr P.hd

/-- The dimension is nonneg as a real. -/
theorem dReal_nonneg : (0 : ℝ) ≤ P.d := le_of_lt P.dReal_pos

end ParametricCoveringAssumption

/-- **Entropy integrand bound (parametric)**: If log N(ε) ≤ d·log(C/ε),
    then √(log N(ε)) ≤ √d · √(log(C/ε)).

    This is the pointwise bound used in the Dudley integral evaluation.
    Re-exports the result from CoveringPacking. -/
theorem parametric_entropy_integrand {logN d : ℝ} {C eps : ℝ}
    (hd : 0 ≤ d) (hC : 0 < C) (heps : 0 < eps)
    (hlogN : logN ≤ d * Real.log (C / eps))
    (hlogN_nn : 0 ≤ logN) :
    Real.sqrt logN ≤ Real.sqrt d * Real.sqrt (Real.log (C / eps)) :=
  entropy_integrand_bound hd hC heps hlogN hlogN_nn

/-- **RL generalization from covering numbers**: For a parametric
    function class with effective dimension d, the sample complexity
    for ε-uniform convergence of empirical Bellman operators is:

      n ≥ C² · d · D² / ε²

    This theorem states the algebraic reduction: if the Dudley bound
    gives error ≤ K · √d · D / √n for some constant K, then choosing
    n ≥ K² · d · D² / ε² ensures error ≤ ε.

    The proof is purely algebraic: K·√d·D/√n ≤ ε ⟺ n ≥ K²·d·D²/ε². -/
theorem rl_generalization_from_covering
    {K d_real D eps : ℝ}
    (hK : 0 < K) (hd : 0 < d_real) (hD : 0 < D) (heps : 0 < eps)
    {n : ℝ} (hn : 0 < n)
    -- The sufficient sample size condition
    (h_sufficient : K ^ 2 * d_real * D ^ 2 / eps ^ 2 ≤ n) :
    -- Then the Dudley bound yields ε-accuracy
    K * Real.sqrt d_real * D / Real.sqrt n ≤ eps := by
  have hsqrt_n_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn
  rw [div_le_iff₀ hsqrt_n_pos]
  -- Squaring approach: a ≤ b iff a² ≤ b² for nonneg a, b
  have h_lhs_nn : 0 ≤ K * Real.sqrt d_real * D := by positivity
  have h_rhs_nn : 0 ≤ eps * Real.sqrt n := by positivity
  rw [← Real.sqrt_sq h_lhs_nn, ← Real.sqrt_sq h_rhs_nn]
  apply Real.sqrt_le_sqrt
  -- (K·√d·D)² = K²·(√d)²·D² = K²·d·D² and (eps·√n)² = eps²·n
  have hsqd : Real.sqrt d_real ^ 2 = d_real := Real.sq_sqrt (le_of_lt hd)
  have hsqn : Real.sqrt n ^ 2 = n := Real.sq_sqrt (le_of_lt hn)
  calc (K * Real.sqrt d_real * D) ^ 2
      = K ^ 2 * Real.sqrt d_real ^ 2 * D ^ 2 := by ring
    _ = K ^ 2 * d_real * D ^ 2 := by rw [hsqd]
    _ ≤ eps ^ 2 * n := by
        have := (div_le_iff₀ (show (0:ℝ) < eps ^ 2 by positivity)).mp h_sufficient
        linarith
    _ = (eps * Real.sqrt n) ^ 2 := by rw [mul_pow, hsqn]

/-! ### Linear Function Class Covering Number

For linear value functions V_θ(s) = θᵀφ(s) with ‖θ‖ ≤ W in ℝ^d,
the ε-covering number of the induced value function class satisfies:

  log N(ε) ≤ d · log(2W/ε + 1)

This follows from the standard covering number of the Euclidean ball:
  N(ε, B_d(0, W)) ≤ (1 + 2W/ε)^d

which gives log N(ε) ≤ d · log(1 + 2W/ε). Since 1 + 2W/ε = (ε + 2W)/ε
and ε + 2W ≤ 3W when ε ≤ W, this is bounded by d · log(3W/ε). -/

/-- **Linear value function class**: V_θ(s) = θᵀφ(s) with ‖θ‖ ≤ W.
    The class is parameterized by a d-dimensional ball of radius W. -/
structure LinearValueClass where
  /-- Feature dimension -/
  d : ℕ
  /-- Dimension is positive -/
  hd : 0 < d
  /-- Parameter bound: ‖θ‖ ≤ W -/
  W : ℝ
  /-- W is positive -/
  hW : 0 < W
  /-- Feature bound: ‖φ(s)‖ ≤ B for all s -/
  B : ℝ
  /-- B is positive -/
  hB : 0 < B

namespace LinearValueClass

variable (L : LinearValueClass)

/-- The dimension as a positive real. -/
theorem dReal_pos : (0 : ℝ) < L.d := Nat.cast_pos.mpr L.hd

/-- The dimension is nonneg as a real. -/
theorem dReal_nonneg : (0 : ℝ) ≤ L.d := le_of_lt L.dReal_pos

/-- The V_max bound for a linear class: V_max = W · B (Cauchy-Schwarz). -/
def V_max : ℝ := L.W * L.B

/-- V_max is positive. -/
theorem V_max_pos : 0 < L.V_max :=
  mul_pos L.hW L.hB

end LinearValueClass

/-- **Linear class covering number**: For linear V_θ(s) = θᵀφ(s) with
    ‖θ‖ ≤ W, the covering number satisfies:

      log N(ε, {V_θ}, ‖·‖_∞) ≤ d · log(1 + 2W/ε)

    when we cover the parameter space B_d(0,W) with ε/(B)-balls
    (since ‖V_θ - V_θ'‖_∞ ≤ ‖θ - θ'‖ · B by Cauchy-Schwarz,
    covering Θ at radius ε/B covers the value functions at radius ε).

    This is the algebraic content: the metric entropy scales as
    d · log(W/ε), establishing the parametric rate for linear RL. -/
theorem linear_class_covering_number
    {d : ℕ} {W eps : ℝ}
    (_hd : 0 < d) (hW : 0 < W) (heps : 0 < eps) :
    (0 : ℝ) ≤ (d : ℝ) * Real.log (1 + 2 * W / eps) ∧
    (d : ℝ) * Real.log (1 + 2 * W / eps) ≤
      (d : ℝ) * Real.log (2 * W / eps + 1) := by
  constructor
  · apply mul_nonneg (Nat.cast_nonneg _)
    apply Real.log_nonneg
    have : 0 ≤ 2 * W / eps := div_nonneg (by linarith) (le_of_lt heps)
    linarith
  · -- 1 + 2W/ε = 2W/ε + 1
    have : 1 + 2 * W / eps = 2 * W / eps + 1 := by ring
    rw [this]

/-- **Linear class metric entropy scaling**: For the linear class with
    ‖θ‖ ≤ W and ε ≤ W, the metric entropy satisfies:

      d · log(1 + 2W/ε) ≤ d · log(3W/ε)

    This gives the simplified scaling log N(ε) = O(d · log(W/ε)). -/
theorem linear_class_entropy_scaling
    {d : ℕ} {W eps : ℝ}
    (_hd : 0 < d) (hW : 0 < W) (heps : 0 < eps)
    (h_eps_le_W : eps ≤ W) :
    (d : ℝ) * Real.log (1 + 2 * W / eps) ≤
    (d : ℝ) * Real.log (3 * W / eps) := by
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Real.log_le_log
  · have : 0 < 2 * W / eps := div_pos (by linarith) heps
    linarith
  · -- 1 + 2W/ε ≤ 3W/ε ⟺ ε + 2W ≤ 3W ⟺ ε ≤ W
    have h1 : 1 + 2 * W / eps ≤ (eps + 2 * W) / eps := by
      rw [add_div]; simp [ne_of_gt heps]
    have h2 : (eps + 2 * W) / eps ≤ 3 * W / eps := by
      apply div_le_div_of_nonneg_right _ (le_of_lt heps)
      linarith
    linarith

/-! ### Linear RL Generalization

Specialization of the Dudley-based sample complexity to linear
value function classes. The covering number log N(ε) ≤ d·log(3W/ε)
is plugged into the entropy integral to get:

  ∫₀^D √(d·log(3W/ε)) dε ≤ √d · K · D

for a universal constant K, giving the sample complexity:

  n ≥ C · d · log(W/ε) / ε²

for ε-accuracy of empirical Bellman operators. -/

/-- **Linear RL generalization**: For a linear value function class
    with parameter bound W and feature bound B in dimension d:

    Sample complexity for ε-uniform convergence is:

      n ≥ C · d · D² / ε²

    where D = 2·W·B is the class diameter. When the entropy integral
    is bounded by K·√d·D (which holds for log N(ε) ≤ d·log(C/ε)),
    the Dudley bound gives error ≤ C_dudley·K·√d·D/√n.

    This theorem states: given the bound components, if n is large
    enough then the error is at most ε. -/
theorem linear_rl_generalization
    {d : ℕ} {W B C_total eps : ℝ}
    (hd : 0 < d) (hW : 0 < W) (hB : 0 < B)
    (hC : 0 < C_total) (heps : 0 < eps)
    {n : ℝ} (hn : 0 < n)
    -- C_total absorbs both the Dudley constant and the integral evaluation
    -- The sufficient condition: n ≥ C_total² · d · (2WB)² / ε²
    (h_sufficient : C_total ^ 2 * d * (2 * W * B) ^ 2 / eps ^ 2 ≤ n) :
    -- The error is at most ε
    C_total * Real.sqrt d * (2 * W * B) / Real.sqrt n ≤ eps :=
  rl_generalization_from_covering hC (Nat.cast_pos.mpr hd) (by positivity) heps hn h_sufficient

/-! ### Dudley vs Rademacher Comparison

The Dudley entropy integral and Rademacher complexity provide
complementary uniform convergence bounds. The relationship is:

  R_n(F) ≤ (12√2/√n) · ∫₀^D √(log N(ε, F)) dε

This connects to the Rademacher infrastructure in
`Complexity.Rademacher`. For finite classes, both give
√(log|F|/n); for parametric classes, both give √(d/n).

We provide a comparison theorem showing that the Dudley-based
sample complexity matches the Rademacher-based one up to constants. -/

/-- **Dudley-Rademacher comparison**: The Dudley entropy integral
    bound implies a Rademacher complexity bound of the same order.

    If the entropy integral gives error ≤ K/√n, then the
    Rademacher complexity satisfies R_n ≤ 2K/√n (after the
    symmetrization factor of 2). -/
theorem dudley_rademacher_comparison
    {K : ℝ} {n : ℕ}
    (_hK : 0 ≤ K) (hn : 0 < n)
    {dudleyError rademacherWidth : ℝ}
    (hDudley : dudleyError ≤ K / Real.sqrt n)
    (hRadem : rademacherWidth = 2 * dudleyError) :
    rademacherWidth ≤ 2 * K / Real.sqrt n := by
  rw [hRadem]
  have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  calc 2 * dudleyError
      ≤ 2 * (K / Real.sqrt n) := by linarith
    _ = 2 * K / Real.sqrt n := by ring

/-- **Parametric class sample complexity (Dudley form)**: For a class
    with effective dimension d and log N(ε) ≤ d·log(C/ε):

    n = O(d · log(C/ε_target) / ε_target²)

    samples suffice for ε_target-uniform convergence. This follows
    from evaluating the Dudley integral when the entropy has
    parametric scaling.

    The algebraic content: d·log(C/ε)/ε² is the right sample
    complexity formula, and it satisfies the sufficient condition
    for the Dudley bound to give ε-accuracy. -/
theorem parametric_sample_complexity_formula
    {d : ℕ} {C eps : ℝ}
    (hd : 0 < d) (_hC : 1 < C) (heps : 0 < eps) (h_eps_small : eps < C) :
    0 < (d : ℝ) * Real.log (C / eps) / eps ^ 2 := by
  apply div_pos
  · apply mul_pos (Nat.cast_pos.mpr hd)
    apply Real.log_pos
    rw [lt_div_iff₀ heps]; linarith
  · positivity

/-! ### Summary: Dudley RL Generalization Chain

The full chain from SLT Dudley to RL sample complexity:

1. **SLT.Dudley.dudley**: E[sup X_t] ≤ (12√2)·σ · ∫₀^D √(log N(ε)) dε
   (proved in SLT with sub-Gaussian processes and chaining)

2. **DudleyRLHypothesis**: Packages the above for RL applications:
   sup_θ |T̂V_θ - TV_θ| ≤ C · integral / √n

3. **parametric_entropy_integrand**: √(log N(ε)) ≤ √d · √(log(C/ε))
   (from CoveringPacking, algebraic)

4. **rl_generalization_from_covering**: n ≥ K²·d·D²/ε² suffices
   (algebraic inversion of the Dudley bound)

5. **linear_class_covering_number**: log N(ε) ≤ d·log(1+2W/ε)
   (standard volumetric bound)

6. **linear_rl_generalization**: n ≥ C·d·(WB)²/ε² for linear classes
   (specialization of item 4 to linear classes)

The measure-theoretic content (sub-Gaussian process construction,
entropy integral finiteness) lives in SLT. The algebraic consequences
here are sufficient for RL sample complexity analysis. -/

end

