import RLGeneralization.Bandits.UCB

open Finset BigOperators Real

namespace BanditInstance

/-- **UCB index three-way split**: if a suboptimal arm's UCB index (with bonus
    `√(2L/n)`) beats the optimal arm's index, then at least one of three events
    holds: the optimal arm is underestimated below its lower confidence bound,
    the suboptimal arm is overestimated above its upper confidence bound, or
    the suboptimal arm is undersampled (`n < 8L/Δ²`). -/
theorem ucb_index_three_way_split
    (L : ℝ) (μ μstar μhat μhatstar : ℝ) (hgap : μ < μstar)
    (n nstar : ℕ) (hn : 1 ≤ n)
    (h_beat : μhatstar + Real.sqrt (2 * L / ↑nstar) ≤ μhat + Real.sqrt (2 * L / ↑n)) :
    μhatstar ≤ μstar - Real.sqrt (2 * L / ↑nstar) ∨
    μ + Real.sqrt (2 * L / ↑n) ≤ μhat ∨
    (n : ℝ) < 8 * L / (μstar - μ) ^ 2 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  have hw : Real.sqrt (2 * L / ↑n) ≤ (μstar - μ) / 2 :=
    confidence_threshold L (μstar - μ) (by linarith) n hn h3
  linarith

end BanditInstance

