import RLGeneralization.Bandits.UCB

open Finset BigOperators Real

namespace BanditInstance

variable {K : ℕ} [NeZero K] (B : BanditInstance K)

/-- **Regret decomposition identity**: pseudo-regret equals the gap-weighted
    pull counts, `R_T = Σ_a Δ_a · N_T(a)`. The exact-equality form of the
    standard bandit regret decomposition (Lemma 4.5 of Lattimore–Szepesvári). -/
theorem pseudoRegret_eq_sum_gap_mul_pullCount (T : ℕ) (I : Fin T → Fin K) :
    B.pseudoRegret T I = ∑ a : Fin K, (pullCount T I a : ℝ) * B.gap a := by
  classical
  rw [B.pseudoRegret_eq_sum_gap]
  calc ∑ t : Fin T, B.gap (I t)
      = ∑ a : Fin K, ∑ t ∈ Finset.univ.filter (fun t => I t = a), B.gap (I t) :=
        (Finset.sum_fiberwise Finset.univ I (fun t => B.gap (I t))).symm
    _ = ∑ a : Fin K, ∑ _t ∈ Finset.univ.filter (fun t => I t = a), B.gap a := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun t ht => ?_
        rw [(Finset.mem_filter.mp ht).2]
    _ = ∑ a : Fin K, (pullCount T I a : ℝ) * B.gap a := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_const, nsmul_eq_mul]
        rfl

end BanditInstance

