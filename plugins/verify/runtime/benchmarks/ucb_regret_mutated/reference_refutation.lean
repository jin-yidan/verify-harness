import Mathlib.Tactic

/-- Counterexample to the mutated Step 4 inference: at L = ln n = 1,
Δ = 1/2, the proof's own threshold s = ⌈4L/Δ²⌉ = 16 satisfies the
hypothesis s ≥ 4L/Δ², yet the required conclusion 8L/s ≤ Δ²
(the squares form of 2√(2L/s) ≤ Δ) is false: 1/2 > 1/4. -/
theorem mutated_threshold_counterexample :
    (16 : ℚ) ≥ 4 * 1 / (1/2)^2 ∧ ¬ (8 * 1 / 16 ≤ ((1:ℚ)/2)^2) := by
  constructor <;> norm_num

#print axioms mutated_threshold_counterexample
