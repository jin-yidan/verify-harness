/-
# Multiplicative Exponential Bound

Tight upper bound on x·exp(-x): the global maximum is 1/e at x=1.

## Main Results

* `mul_exp_neg_le` — x·exp(-x) ≤ exp(-1) for all x
* `mul_exp_neg_scaled_le` — x·exp(-ax) ≤ exp(-1)/a for a > 0

## References

* Standard calculus: f(x)=x·e^{-x} has f'(x)=(1-x)e^{-x}, max at x=1
* Used in sample complexity, bandit tail bounds, learning rate analysis
-/
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

open Real

/-- **Multiplicative exponential bound**: x·exp(-x) ≤ 1/e for all real x.

    Proof: from exp(y) ≥ 1+y with y=x-1, we get x ≤ exp(x-1),
    then multiply both sides by exp(-x) > 0. -/
theorem mul_exp_neg_le (x : ℝ) :
    x * Real.exp (-x) ≤ Real.exp (-1) := by
  have h1 : x ≤ Real.exp (x - 1) := by linarith [Real.add_one_le_exp (x - 1)]
  have h2 : (0 : ℝ) ≤ Real.exp (-x) := le_of_lt (Real.exp_pos _)
  calc x * Real.exp (-x)
      ≤ Real.exp (x - 1) * Real.exp (-x) :=
        mul_le_mul_of_nonneg_right h1 h2
    _ = Real.exp (-1) := by rw [← Real.exp_add]; ring_nf

/-- **Scaled multiplicative exponential bound**: x·exp(-ax) ≤ (1/e)/a for a > 0.

    Follows from `mul_exp_neg_le` applied to ax, then dividing by a. -/
theorem mul_exp_neg_scaled_le {a : ℝ} (ha : 0 < a) (x : ℝ) :
    x * Real.exp (-(a * x)) ≤ Real.exp (-1) / a := by
  have h := mul_exp_neg_le (a * x)
  rw [le_div_iff₀ ha]
  calc x * Real.exp (-(a * x)) * a
      = a * x * Real.exp (-(a * x)) := by ring
    _ ≤ Real.exp (-1) := h
