import RLGeneralization.PolicyOptimization.CPI

open Finset BigOperators

/-- A policy mixture dominates its weighted second component pointwise:
`α · π_new(a|s) ≤ ((1-α)·π + α·π_new)(a|s)` whenever `α ≤ 1`. Specializes to
the ε-greedy exploration lower bound ε/|A| when `π_new` is uniform at `(s,a)`. -/
theorem weighted_new_le_mixture_prob {M : FiniteMDP} (π π_new : M.StochasticPolicy)
    (α : ℝ) (hα1 : α ≤ 1) (s : M.S) (a : M.A) :
    α * π_new.prob s a ≤ M.mixtureProb π π_new α s a := by
  unfold FiniteMDP.mixtureProb
  nlinarith [π.prob_nonneg s a]

