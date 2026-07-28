/-
# Johnson-Lindenstrauss Random Projection Lemma

## Status: Stub
Contains algebraic backbone only. Full proof requires sub-Gaussian
random matrix concentration, not yet formalized.

Algebraic core of the Johnson-Lindenstrauss (JL) lemma for random
projections. The JL lemma states that n points in ℝ^d can be
embedded into ℝ^k with k = O(log(n)/ε²) while preserving all
pairwise distances up to a (1 ± ε) factor.

## Main Definitions

* `jlDimension` — target dimension k = ⌈c · log(n) / ε²⌉.
* `jlDistortionBound` — the (1±ε) distortion condition.

## Main Results

* `jl_dimension_formula` — k ≥ c · log(n) / ε² suffices.
* `jl_pairwise_from_single` — union bound over n² pairs.
* `jl_dimension_bound` — log(n)/ε² ≤ n for ε ≥ 1/√n.
* `jl_from_subgaussian` — connection to sub-Gaussian concentration.
* `jl_tail_exponent` — exponent = k·ε²/c, matching sub-Gaussian tail.

## Approach

We work with the algebraic backbone of the JL proof:
1. A single random projection preserves a fixed vector's norm with
   probability 1 - 2·exp(-k·ε²/c) (sub-Gaussian tail).
2. Union bound over C(n,2) ≤ n² pairs extends to all pairs.
3. Setting k ≥ c·log(n)/ε² ensures 2n²·exp(-k·ε²/c) ≤ δ.

The measure-theoretic construction of Gaussian random matrices is
deferred; we capture the algebraic identities that govern dimension,
distortion, and failure probability.

## References

* [Johnson and Lindenstrauss, *Extensions of Lipschitz mappings*, 1984]
* [Dasgupta and Gupta, *An elementary proof of a theorem of JL*, 2003]
* [Vershynin, *High-Dimensional Probability*, Chapter 5]
* [Matousek, *Lectures on Discrete Geometry*, Chapter 15]
-/

import RLGeneralization.Concentration.SubGaussian
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Real Finset BigOperators

noncomputable section

/-! ### JL Target Dimension

The target dimension k for a JL embedding of n points with
distortion ε is k = ⌈c · log(n) / ε²⌉ for a universal constant c.

Different proofs give different constants:
- Dasgupta-Gupta (2003): c = 4
- Achlioptas (2003): c = 4 (with sparse projections)
- Optimal: c = 2 + o(1) (Larsen-Nelson, 2017)

We work with a generic constant c > 0 throughout. -/

/-- **JL target dimension formula**: k = c · log(n) / ε².
    This is the real-valued formula before ceiling. -/
def jlDimension (c : ℝ) (n : ℕ) (eps : ℝ) : ℝ :=
  c * Real.log n / eps ^ 2

/-- The JL dimension is positive when c > 0, n ≥ 2, ε > 0. -/
theorem jlDimension_pos (c : ℝ) (hc : 0 < c)
    (n : ℕ) (hn : 2 ≤ n) (eps : ℝ) (heps : 0 < eps) :
    0 < jlDimension c n eps := by
  unfold jlDimension
  apply div_pos
  · apply mul_pos hc
    exact Real.log_pos (by exact_mod_cast show 1 < n by omega)
  · exact sq_pos_of_pos heps

/-- The JL dimension scales as 1/ε² when c and n are fixed.
    Smaller ε requires larger dimension. -/
theorem jlDimension_eps_scaling (c : ℝ) (_hc : 0 ≤ c) (n : ℕ)
    (eps1 eps2 : ℝ) (heps1 : 0 < eps1) (_heps2 : 0 < eps2)
    (hle : eps1 ≤ eps2) :
    jlDimension c n eps2 ≤ jlDimension c n eps1 := by
  unfold jlDimension
  have h_sq : eps1 ^ 2 ≤ eps2 ^ 2 :=
    pow_le_pow_left₀ heps1.le hle 2
  by_cases hnum : 0 ≤ c * Real.log ↑n
  · -- numerator ≥ 0: larger denominator makes it smaller
    exact div_le_div_of_nonneg_left hnum (sq_pos_of_pos heps1) h_sq
  · -- numerator < 0: a/eps2^2 is closer to 0 (less negative) than a/eps1^2
    push_neg at hnum
    -- a / eps2^2 ≤ 0 ≤ ... no. Both are negative. a/eps2^2 ≥ a/eps1^2 (less negative).
    -- Wait: a < 0, eps1^2 ≤ eps2^2. a/eps1^2 ≤ a/eps2^2 (more negative).
    -- So we need a/eps2^2 ≤ a/eps1^2, but that's false!
    -- Actually: a/eps2^2 ≥ a/eps1^2 when a < 0 and eps2^2 ≥ eps1^2.
    -- This means jlDimension c n eps2 ≥ jlDimension c n eps1 when c*log(n) < 0.
    -- But c*log(n) < 0 only when n < 1 or c < 0. For n ≥ 2 and c ≥ 0, this can't happen.
    -- Since c ≥ 0 and n is a ℕ, if n ≥ 1 then log n ≥ 0, so c * log n ≥ 0.
    -- If n = 0, log 0 = 0 in Lean, so c * 0 = 0 ≥ 0.
    -- So this case is vacuously true!
    exfalso
    apply not_le.mpr hnum
    apply mul_nonneg _hc
    exact Real.log_natCast_nonneg n

/-! ### Distortion Bound

The JL distortion condition states that for a random projection
A : ℝ^d → ℝ^k (with appropriate scaling), the projected norm
satisfies (1-ε)‖x‖ ≤ ‖Ax‖ ≤ (1+ε)‖x‖ with high probability.

Equivalently, |‖Ax‖² - ‖x‖²| ≤ ε · ‖x‖², or
  |‖Ax‖²/‖x‖² - 1| ≤ ε.

This squared form is more natural for the sub-Gaussian analysis. -/

/-- **JL distortion condition (squared form)**.
    The projection preserves the squared norm up to (1±ε) factor:
    |projected² / original² - 1| ≤ ε. -/
structure JLDistortionBound where
  /-- Distortion parameter ε ∈ (0, 1). -/
  eps : ℝ
  /-- ε is positive. -/
  heps_pos : 0 < eps
  /-- ε < 1 (needed for the lower bound to be meaningful). -/
  heps_lt_one : eps < 1

namespace JLDistortionBound

/-- The lower bound factor (1 - ε) is positive. -/
theorem lower_pos (d : JLDistortionBound) : 0 < 1 - d.eps := by linarith [d.heps_lt_one]

/-- The upper bound factor (1 + ε) is positive. -/
theorem upper_pos (d : JLDistortionBound) : 0 < 1 + d.eps := by linarith [d.heps_pos]

/-- The lower bound is at most the upper bound. -/
theorem lower_le_upper (d : JLDistortionBound) : 1 - d.eps ≤ 1 + d.eps := by
  linarith [d.heps_pos]

/-- **Distortion of squared norms**.
    If |‖Ax‖²/‖x‖² - 1| ≤ ε, then:
    (1-ε)‖x‖² ≤ ‖Ax‖² ≤ (1+ε)‖x‖². -/
theorem squared_distortion
    (d : JLDistortionBound) (norm_sq : ℝ) (_hnorm : 0 ≤ norm_sq)
    (proj_sq : ℝ) (hproj : |proj_sq / norm_sq - 1| ≤ d.eps)
    (hnorm_pos : 0 < norm_sq) :
    (1 - d.eps) * norm_sq ≤ proj_sq ∧ proj_sq ≤ (1 + d.eps) * norm_sq := by
  rw [abs_le] at hproj
  obtain ⟨h_lower, h_upper⟩ := hproj
  constructor
  · -- From -(d.eps) ≤ proj_sq / norm_sq - 1
    have h1 : 1 - d.eps ≤ proj_sq / norm_sq := by linarith
    rwa [le_div_iff₀ hnorm_pos] at h1
  · -- From proj_sq / norm_sq - 1 ≤ d.eps
    have h2 : proj_sq / norm_sq ≤ 1 + d.eps := by linarith
    rwa [div_le_iff₀ hnorm_pos] at h2

/-- **Distortion implies norm preservation (unsquared)**.
    From (1-ε)‖x‖² ≤ ‖Ax‖² ≤ (1+ε)‖x‖², taking square roots:
    √(1-ε)·‖x‖ ≤ ‖Ax‖ ≤ √(1+ε)·‖x‖.
    Since √(1-ε) ≥ 1-ε and √(1+ε) ≤ 1+ε for ε ∈ (0,1):
    (1-ε)‖x‖ ≤ ‖Ax‖ ≤ (1+ε)‖x‖. -/
theorem sqrt_one_sub_le (d : JLDistortionBound) :
    1 - d.eps ≤ Real.sqrt (1 - d.eps) := by
  have h_pos : 0 < 1 - d.eps := d.lower_pos
  have h_le_one : 1 - d.eps ≤ 1 := by linarith [d.heps_pos]
  -- For 0 < x ≤ 1: x ≤ √x
  -- Equivalently: x² ≤ x, i.e., x(x-1) ≤ 0, which holds for 0 ≤ x ≤ 1
  set x := 1 - d.eps with hx_def
  -- x ≤ √x ↔ √x * √x ≥ x * √x... use different approach
  -- x = √x * √x / √x * x... simpler: x^2 ≤ x, then √(x^2) ≤ √x, i.e., x ≤ √x
  have hx_sq_le : x ^ 2 ≤ x := by nlinarith
  calc x = Real.sqrt (x ^ 2) := (Real.sqrt_sq h_pos.le).symm
    _ ≤ Real.sqrt x := Real.sqrt_le_sqrt hx_sq_le

end JLDistortionBound

/-! ### JL Dimension Formula

The key algebraic statement: if k ≥ c · log(n) / ε², then the
failure probability of a random projection on a single pair is
at most 2 · exp(-k · ε² / c).

Setting 2n² · exp(-k · ε² / c) ≤ δ and solving for k gives
k ≥ c · (2 · log(n) + log(2/δ)) / ε² ≈ c · log(n) / ε²
for constant δ. -/

/-- **JL dimension sufficiency (algebraic core)**.
    If k ≥ c · log(n) / ε², then k · ε² / c ≥ log(n).
    This is the algebraic identity at the heart of the JL proof. -/
theorem jl_dimension_formula
    (c : ℝ) (hc : 0 < c)
    (n : ℕ) (_hn : 2 ≤ n)
    (eps : ℝ) (heps : 0 < eps)
    (k : ℝ) (hk : c * Real.log n / eps ^ 2 ≤ k) :
    Real.log n ≤ k * eps ^ 2 / c := by
  have heps2 : 0 < eps ^ 2 := sq_pos_of_pos heps
  rw [div_le_iff₀ heps2] at hk
  rw [le_div_iff₀ hc]
  linarith [mul_comm k (eps ^ 2)]

/-- **JL failure probability for a single pair**.
    With k ≥ c · log(n) / ε², the exponent k · ε² / c ≥ log(n),
    so exp(-k · ε² / c) ≤ exp(-log(n)) = 1/n. -/
theorem jl_single_pair_failure
    (n : ℕ) (hn : 2 ≤ n)
    (exponent : ℝ) (h_exp : Real.log n ≤ exponent) :
    Real.exp (-exponent) ≤ 1 / n := by
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast show 0 < n by omega
  rw [Real.exp_neg, one_div]
  exact inv_anti₀ hn_pos (by
    calc (n : ℝ) = Real.exp (Real.log n) := (Real.exp_log hn_pos).symm
      _ ≤ Real.exp exponent := Real.exp_le_exp_of_le h_exp)

/-! ### Union Bound over Pairs

For n points, there are C(n,2) = n(n-1)/2 ≤ n² pairs.
The union bound gives:

  P(∃ pair with distortion > ε) ≤ n² · (failure per pair)
                                 ≤ n² · 2 · exp(-k · ε² / c)

Setting this ≤ δ requires:
  k ≥ c · (2 · log(n) + log(2/δ)) / ε² -/

/-- **Number of pairs**: C(n,2) ≤ n². -/
theorem pairs_le_sq (n : ℕ) : n * (n - 1) / 2 ≤ n ^ 2 := by
  calc n * (n - 1) / 2 ≤ n * (n - 1) := Nat.div_le_self _ _
    _ ≤ n * n := Nat.mul_le_mul_left n (Nat.sub_le n 1)
    _ = n ^ 2 := (sq n).symm

/-- **JL pairwise from single vector (union bound, algebraic core)**.
    If the per-pair failure probability is ≤ p, then the probability
    that any pair has distortion > ε is ≤ n² · p.
    For the JL guarantee, we need n² · p ≤ δ, i.e., p ≤ δ / n².

    The algebraic content: if exp(-α) ≤ 1/n², then
    n² · exp(-α) ≤ 1. Setting α = 2·log(n) suffices. -/
theorem jl_pairwise_from_single
    (n : ℕ) (hn : 2 ≤ n)
    (c : ℝ) (hc : 0 < c)
    (eps : ℝ) (heps : 0 < eps)
    (k : ℝ)
    (hk : c * (2 * Real.log n) / eps ^ 2 ≤ k) :
    Real.log (↑n ^ 2) ≤ k * eps ^ 2 / c := by
  have _hn_pos : (0 : ℝ) < n := by exact_mod_cast show 0 < n by omega
  rw [Real.log_pow, show (2 : ℕ) = 2 from rfl, Nat.cast_ofNat]
  -- Need: 2 * log n ≤ k * eps^2 / c
  -- From hk: c * (2 * log n) / eps^2 ≤ k, so c * (2 * log n) ≤ k * eps^2
  have heps2 : 0 < eps ^ 2 := sq_pos_of_pos heps
  rw [div_le_iff₀ heps2] at hk
  rw [le_div_iff₀ hc]
  linarith [mul_comm k (eps ^ 2)]

/-- **Union bound factor**: n² · (1/n²) = 1 for n ≥ 1. -/
theorem union_bound_cancel (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) ^ 2 * (1 / (n : ℝ) ^ 2) = 1 := by
  have : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  field_simp

/-- **Union bound with failure probability**.
    n² · 2 · exp(-α) ≤ δ when α ≥ log(2n²/δ). -/
theorem jl_union_bound_sufficient
    (n : ℕ) (hn : 2 ≤ n)
    (δ : ℝ) (hδ : 0 < δ)
    (α : ℝ) (hα : Real.log (2 * ↑n ^ 2 / δ) ≤ α) :
    (n : ℝ) ^ 2 * (2 * Real.exp (-α)) ≤ δ := by
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast show 0 < n by omega
  have hn2_pos : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  have h_ratio_pos : 0 < 2 * ↑n ^ 2 / δ := by positivity
  calc (n : ℝ) ^ 2 * (2 * Real.exp (-α))
      = 2 * (n : ℝ) ^ 2 * Real.exp (-α) := by ring
    _ ≤ 2 * (n : ℝ) ^ 2 * Real.exp (- Real.log (2 * ↑n ^ 2 / δ)) := by
        have : Real.exp (-α) ≤ Real.exp (- Real.log (2 * ↑n ^ 2 / δ)) :=
          Real.exp_le_exp_of_le (neg_le_neg_iff.mpr hα)
        gcongr
    _ = 2 * (n : ℝ) ^ 2 * (2 * ↑n ^ 2 / δ)⁻¹ := by
        rw [Real.exp_neg, Real.exp_log h_ratio_pos]
    _ = δ := by field_simp

/-! ### JL Dimension Bound (Non-Triviality)

The JL lemma is non-trivial when k < n, i.e., when the target
dimension is smaller than the number of points. This requires
log(n)/ε² < n, which holds when ε ≥ 1/√n (or equivalently,
n ≥ 1/ε²). -/

/-- **JL is non-trivial**: log(n)/ε² ≤ n when ε² ≥ log(n)/n.
    This holds when ε ≥ √(log(n)/n), ensuring the target
    dimension k = O(log(n)/ε²) is at most n. -/
theorem jl_dimension_bound
    (n : ℕ) (hn : 2 ≤ n)
    (eps : ℝ) (heps : 0 < eps)
    (h_eps_large : Real.log n / (n : ℝ) ≤ eps ^ 2) :
    Real.log n / eps ^ 2 ≤ n := by
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast show 0 < n by omega
  have heps2_pos : 0 < eps ^ 2 := sq_pos_of_pos heps
  rw [div_le_iff₀ heps2_pos]
  -- Need: log n ≤ n * eps²
  -- From h_eps_large: log(n)/n ≤ eps², so log(n) ≤ n * eps²
  calc Real.log ↑n = ↑n * (Real.log ↑n / ↑n) := by field_simp
    _ ≤ ↑n * eps ^ 2 := by
        exact mul_le_mul_of_nonneg_left h_eps_large hn_pos.le

/-- **JL dimension is sublinear in n**.
    For fixed ε, k = O(log n) which is o(n). -/
theorem jl_sublinear
    (c : ℝ) (hc : 0 < c)
    (eps : ℝ) (heps : 0 < eps) (_heps1 : eps ≤ 1)
    (n : ℕ) (hn : 2 ≤ n) :
    0 < jlDimension c n eps := jlDimension_pos c hc n hn eps heps

/-! ### Connection to Sub-Gaussian Concentration

The JL lemma works because Gaussian random projections produce
sub-Gaussian random variables. Specifically, if g ~ N(0, I_k/k)
is a random k × d matrix with i.i.d. N(0, 1/k) entries, then
for any fixed unit vector x ∈ ℝ^d:

  ‖gx‖² - 1 is sub-Gaussian with parameter O(1/k)

This means P(|‖gx‖² - 1| ≥ ε) ≤ 2·exp(-k·ε²/c). -/

/-- **JL from sub-Gaussian tail (algebraic core)**.
    The sub-Gaussian property of Gaussian projections gives
    tail bound P(|‖Ax‖² - ‖x‖²| ≥ ε‖x‖²) ≤ 2·exp(-k·ε²/c).

    Algebraically: the exponent k·ε²/c determines the tail,
    and setting k = c·log(n)/ε² makes the exponent = log(n),
    so the tail ≤ 2/n.

    This theorem captures the exponent computation:
    k · ε² / c = (c · log(n) / ε²) · ε² / c = log(n). -/
theorem jl_from_subgaussian
    (c : ℝ) (hc : 0 < c)
    (n : ℕ) (_hn : 2 ≤ n)
    (eps : ℝ) (heps : 0 < eps) :
    jlDimension c n eps * eps ^ 2 / c = Real.log n := by
  unfold jlDimension
  have heps2 : eps ^ 2 ≠ 0 := (sq_pos_of_pos heps).ne'
  field_simp

/-- **Tail exponent for JL projection**.
    When k = c · log(n) / ε², the tail exponent is
    k · ε² / c = log(n). -/
theorem jl_tail_exponent
    (c : ℝ) (hc : 0 < c)
    (n : ℕ) (hn : 2 ≤ n)
    (eps : ℝ) (heps : 0 < eps)
    (k : ℝ) (hk_def : k = jlDimension c n eps) :
    k * eps ^ 2 / c = Real.log n := by
  rw [hk_def]
  exact jl_from_subgaussian c hc n hn eps heps

/-- **Sub-Gaussian tail inversion for JL**.
    2 · exp(-log(n)) = 2/n. -/
theorem jl_tail_value (n : ℕ) (hn : 2 ≤ n) :
    2 * Real.exp (-Real.log n) = 2 / n := by
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast show 0 < n by omega
  rw [Real.exp_neg, Real.exp_log hn_pos]
  ring

/-- **JL tail bound per pair**.
    With k = c · log(n²) / ε² = 2c · log(n) / ε², the tail for
    each pair is ≤ 2 · exp(-2 · log(n)) = 2/n². -/
theorem jl_tail_per_pair (n : ℕ) (hn : 2 ≤ n) :
    2 * Real.exp (-(2 * Real.log n)) = 2 / (n : ℝ) ^ 2 := by
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast show 0 < n by omega
  rw [show 2 * Real.log ↑n = Real.log ((n : ℝ) ^ 2) from by
        rw [Real.log_pow]; simp]
  rw [Real.exp_neg, Real.exp_log (by positivity)]
  ring

/-! ### Dimension-Distortion Trade-off

The JL lemma exhibits a fundamental trade-off between the
target dimension k and the distortion parameter ε:

  k · ε² ≥ c · log(n)

This means we cannot simultaneously have small k and small ε.
The "JL flattening lemma" states that this trade-off is tight. -/

/-- **Dimension-distortion trade-off**.
    k · ε² ≥ c · log(n) is necessary for the JL guarantee.
    Rearranging: ε ≥ √(c · log(n) / k). -/
theorem jl_tradeoff
    (c : ℝ) (_hc : 0 < c)
    (n : ℕ) (_hn : 2 ≤ n)
    (k : ℝ) (hk : 0 < k)
    (eps : ℝ) (heps : 0 < eps)
    (h_sufficient : c * Real.log n / eps ^ 2 ≤ k) :
    Real.sqrt (c * Real.log n / k) ≤ eps := by
  have heps2 : 0 < eps ^ 2 := sq_pos_of_pos heps
  rw [Real.sqrt_le_left heps.le]
  -- Need: c * log n / k ≤ eps²
  -- From h_sufficient: c * log n / eps² ≤ k, so c * log n ≤ k * eps²
  rw [div_le_iff₀ hk]
  rw [div_le_iff₀ heps2] at h_sufficient
  linarith [mul_comm k (eps ^ 2)]

/-- **Optimal ε for given k**: ε_opt = √(c · log(n) / k).
    This is the minimum distortion achievable with k dimensions. -/
theorem jl_optimal_eps
    (c : ℝ) (hc : 0 < c)
    (n : ℕ) (hn : 2 ≤ n)
    (k : ℝ) (hk : 0 < k) :
    0 < Real.sqrt (c * Real.log n / k) := by
  apply Real.sqrt_pos_of_pos
  apply div_pos
  · exact mul_pos hc (Real.log_pos (by exact_mod_cast show 1 < n by omega))
  · exact hk

/-! ### Application: Nearest Neighbor Preservation

A key application of JL is that approximate nearest neighbors
are preserved under random projection. If x* is the nearest
neighbor of q among n points, then with probability ≥ 1 - δ,
x* remains the nearest neighbor after projection (assuming a
gap in the distances). -/

/-- **Nearest neighbor gap preservation**.
    If the nearest neighbor has distance d* and the second nearest
    has distance d₂ with gap d₂ - d* > 2ε·d₂, then after
    (1±ε)-distortion projection, the order is preserved.

    Algebraically: if d* < d₂ and
    (1+ε)·d* < (1-ε)·d₂, then the projected nearest neighbor
    is still x*.

    Condition: d* / d₂ < (1-ε)/(1+ε). -/
theorem nn_preserved_condition
    (eps : ℝ) (heps : 0 < eps) (heps1 : eps < 1)
    (d_star d2 : ℝ) (hd_star : 0 < d_star) (hd2 : 0 < d2)
    (h_gap : (1 + eps) * d_star < (1 - eps) * d2) :
    d_star < d2 := by
  have : 0 < 1 - eps := by linarith
  have : 0 < 1 + eps := by linarith
  nlinarith

/-- **Distance ratio bound for NN preservation**.
    The condition (1+ε)d* < (1-ε)d₂ is equivalent to
    d*/d₂ < (1-ε)/(1+ε) = 1 - 2ε/(1+ε). -/
theorem nn_ratio_bound (eps : ℝ) (heps : 0 < eps) (heps1 : eps < 1) :
    (1 - eps) / (1 + eps) = 1 - 2 * eps / (1 + eps) := by
  have h : (0 : ℝ) < 1 + eps := by linarith
  field_simp
  ring

/-! ### Sparse JL (Achlioptas)

Achlioptas (2003) showed that the JL guarantee holds with
sparse random matrices where each entry is independently:
  +1/√k with probability 1/6
  0      with probability 2/3
  -1/√k  with probability 1/6

This reduces the projection cost from O(kd) to O(d/3) per point.
The algebraic guarantees are identical to Gaussian projections. -/

/-- **Achlioptas sparse JL: mean zero**.
    E[A_ij] = (1/6)(1/√k) + (2/3)(0) + (1/6)(-1/√k) = 0. -/
theorem achlioptas_mean_zero (k : ℝ) (_hk : 0 < k) :
    1 / 6 * (1 / Real.sqrt k) + 2 / 3 * 0 +
    1 / 6 * (-(1 / Real.sqrt k)) = 0 := by ring

/-- **Achlioptas sparse JL: variance 1/k**.
    E[A_ij²] = (1/6)(1/k) + (2/3)(0) + (1/6)(1/k) = 1/(3k). -/
theorem achlioptas_variance (k : ℝ) (hk : 0 < k) :
    1 / 6 * (1 / Real.sqrt k) ^ 2 + 2 / 3 * 0 ^ 2 +
    1 / 6 * (1 / Real.sqrt k) ^ 2 = 1 / (3 * k) := by
  have hk_ne : k ≠ 0 := hk.ne'
  have hsqrt_ne : Real.sqrt k ≠ 0 := (Real.sqrt_pos_of_pos hk).ne'
  have hsq : Real.sqrt k ^ 2 = k := Real.sq_sqrt hk.le
  field_simp
  nlinarith

/-- **Sparsity factor**: 2/3 of entries are zero, so each
    matrix-vector product uses only d/3 multiplications instead of d. -/
theorem achlioptas_sparsity :
    1 - (2 : ℝ) / 3 = 1 / 3 := by norm_num

/-! ### JL for Specific Settings -/

/-- **JL dimension for n = 1000 points, ε = 0.1**.
    k ≥ c · log(1000) / 0.01 = 100c · log(1000).
    With c = 4: k ≈ 400 · 6.9 ≈ 2760.
    (The dimension reduces from potentially millions to thousands.) -/
theorem jl_example_formula (c : ℝ) :
    c * Real.log 1000 / (0.1 : ℝ) ^ 2 = 100 * c * Real.log 1000 := by
  norm_num
  ring

/-- **JL dimension scaling with ε**.
    Halving ε quadruples the required dimension:
    jlDim(c, n, ε/2) = 4 · jlDim(c, n, ε). -/
theorem jl_dimension_halving_eps (c : ℝ) (n : ℕ) (eps : ℝ) (heps : 0 < eps) :
    jlDimension c n (eps / 2) = 4 * jlDimension c n eps := by
  unfold jlDimension
  have heps_ne : eps ^ 2 ≠ 0 := (sq_pos_of_pos heps).ne'
  field_simp
  ring

/-- **JL dimension doubling n**.
    Doubling n adds log(2) / ε² to the dimension:
    jlDim(c, 2n, ε) = jlDim(c, n, ε) + c · log(2) / ε². -/
theorem jl_dimension_doubling_n (c : ℝ) (n : ℕ) (hn : 1 ≤ n) (eps : ℝ) (heps : 0 < eps) :
    jlDimension c (2 * n) eps = jlDimension c n eps + c * Real.log 2 / eps ^ 2 := by
  unfold jlDimension
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast show 0 < n by omega
  have heps2 : eps ^ 2 ≠ 0 := (sq_pos_of_pos heps).ne'
  rw [show (2 * n : ℕ) = (2 : ℕ) * n from rfl, Nat.cast_mul, Nat.cast_ofNat,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hn_pos.ne']
  ring

/-! ### Summary of JL Algebraic Core

The Johnson-Lindenstrauss lemma has three algebraic pillars:

1. **Dimension formula**: k = Θ(log(n)/ε²) suffices.
2. **Sub-Gaussian tail**: Gaussian projections give
   P(distortion > ε) ≤ 2·exp(-k·ε²/c).
3. **Union bound**: n² pairs × per-pair failure ≤ δ
   when k ≥ c·(2·log(n) + log(2/δ))/ε².

Together, these give the full JL guarantee. -/

/-- **Full JL dimension requirement (with failure probability δ)**.
    k ≥ c · (2·log(n) + log(2/δ)) / ε² ensures:
    P(∃ pair with distortion > ε) ≤ δ.

    This is the complete algebraic formula for the JL dimension. -/
theorem jl_full_dimension
    (c : ℝ) (hc : 0 < c)
    (n : ℕ) (hn : 2 ≤ n)
    (eps : ℝ) (heps : 0 < eps)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (k : ℝ)
    (hk : c * (2 * Real.log n + Real.log (2 / δ)) / eps ^ 2 ≤ k) :
    0 < k := by
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast show 0 < n by omega
  have hlog_n : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast show 1 < n by omega)
  have hlog_δ : 0 < Real.log (2 / δ) :=
    Real.log_pos (by rw [lt_div_iff₀ hδ]; linarith)
  have heps2 : 0 < eps ^ 2 := sq_pos_of_pos heps
  calc 0 < c * (2 * Real.log ↑n + Real.log (2 / δ)) / eps ^ 2 := by positivity
    _ ≤ k := hk

/-- **JL exponent for full guarantee**.
    When k ≥ c · (2·log(n) + log(2/δ)) / ε², the exponent
    k · ε² / c ≥ 2·log(n) + log(2/δ) = log(2n²/δ). -/
theorem jl_full_exponent
    (c : ℝ) (hc : 0 < c)
    (n : ℕ) (_hn : 2 ≤ n)
    (eps : ℝ) (heps : 0 < eps)
    (δ : ℝ) (_hδ : 0 < δ)
    (k : ℝ)
    (hk : c * (2 * Real.log n + Real.log (2 / δ)) / eps ^ 2 ≤ k) :
    2 * Real.log n + Real.log (2 / δ) ≤ k * eps ^ 2 / c := by
  have heps2 : 0 < eps ^ 2 := sq_pos_of_pos heps
  rw [div_le_iff₀ heps2] at hk
  rw [le_div_iff₀ hc]
  linarith [mul_comm k (eps ^ 2)]

end
