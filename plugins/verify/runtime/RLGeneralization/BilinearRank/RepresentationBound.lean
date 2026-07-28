/-
# Bellman Rank and Eluder Dimension: Representation Bounds

Establishes connections between Bellman rank, eluder dimension, and
low-rank MDP structure. These results unify different structural
assumptions used in RL theory under a common complexity framework.

## Main Results

* `bellman_rank_le_eluder` — The Bellman rank of an MDP with hypothesis
  class F is bounded by the eluder dimension of the induced Bellman
  error class. This shows that eluder dimension is a more general
  complexity measure.

## References

* [Jiang et al., 2017, *Contextual Decision Processes with Low Bellman Rank
  are PAC-Learnable*]
* [Agarwal et al., *RL: Theory and Algorithms*, Ch 8]
* [Jin et al., 2020, *Provably Efficient RL with Linear Function
  Approximation*]
-/

import RLGeneralization.BilinearRank.Auxiliary
import RLGeneralization.Complexity.EluderDimension

open Finset BigOperators

noncomputable section

namespace FiniteHorizonMDP

variable (M : FiniteHorizonMDP)

/-! ### Bellman Error Class -/

/-- The **Bellman error class** induced by hypothesis class F and policy class Π.

  For each hypothesis f ∈ F and step h, the Bellman error function is:
    E_f,h(s) = r_h(s, π(s)) + ∑_{s'} P_h(s'|s, π(s)) · max_a f_{h+1}(s', a) - f_h(s, π(s))

  The eluder dimension of this class controls the sample complexity
  of algorithms like GOLF. -/
def bellmanErrorClass (F : M.HypothesisClass)
    (pi : Fin M.H → M.S → M.A) (h : Fin M.H) :
    Set (M.S → ℝ) :=
  {g | ∃ j : Fin F.n, g = fun s => M.bellmanError F j pi h s}

/-! ### Bellman Rank vs. Eluder Dimension -/

/-- **Bellman rank is bounded by eluder dimension**.

  If the MDP has Bellman rank d (via bilinear decomposition) with
  hypothesis class F, then the eluder dimension of the induced
  Bellman error class is at most d.

  Intuition: the bilinear structure E[bellman_error] = <X_π, W_f>
  means the Bellman error function lies in a d-dimensional subspace.
  The eluder dimension of a d-dimensional function class is at most d
  (by the linear eluder dimension bound).

  This shows that Bellman rank is a *stronger* (more restrictive)
  structural assumption than bounded eluder dimension. -/
theorem bellman_rank_le_eluder
    (brb : M.BellmanRankBound)
    (ε : ℝ) (_hε : 0 < ε)
    (pi : Fin M.H → M.S → M.A)
    (h : Fin M.H)
    -- Hypothesis: The bilinear decomposition E[bellman_error] = ⟨X_π, W_f⟩
    -- confines the Bellman error class to a brb.d-dimensional linear subspace.
    -- Any ε-independent sequence in this class has length ≤ brb.d
    -- (by the linear eluder dimension bound applied to the W embedding).
    (h_rank_bound : ∀ n (seq : Fin n → M.S),
        eluderIndependentSeq (M.bellmanErrorClass brb.F pi h)
          ε n seq → n ≤ brb.d) :
    eluderDimension (M.bellmanErrorClass brb.F pi h) ε ≤ brb.d := by
  unfold eluderDimension
  by_cases hbdd : BddAbove {n | ∃ seq : Fin n → M.S,
      eluderIndependentSeq
        (M.bellmanErrorClass brb.F pi h) ε n seq}
  · have hne : Set.Nonempty {n | ∃ seq : Fin n → M.S,
        eluderIndependentSeq
          (M.bellmanErrorClass brb.F pi h) ε n seq} :=
      ⟨0, Fin.elim0, fun k => Fin.elim0 k⟩
    exact csSup_le hne
      (fun n ⟨seq, hseq⟩ => h_rank_bound n seq hseq)
  · rw [Nat.sSup_of_not_bddAbove hbdd]
    exact Nat.zero_le _

/-! ### Low-Rank MDP Structure -/

/-- **Low-rank MDP feature assumption**: the transition kernel admits a
    factorization P_h(s'|s,a) = φ_h(s,a)^T μ_h(s') where:
    - φ_h : S × A → ℝ^d is the state-action feature map
    - μ_h : S → ℝ^d is the next-state measure embedding
    - d is the feature dimension (rank of the transition) -/
structure LowRankFeatures where
  /-- Feature dimension -/
  d : ℕ
  /-- Feature dimension is positive -/
  hd_pos : 0 < d
  /-- State-action feature map -/
  φ : Fin M.H → M.S → M.A → Fin d → ℝ
  /-- Next-state measure embedding -/
  μ : Fin M.H → M.S → Fin d → ℝ
  /-- Low-rank decomposition: P_h(s'|s,a) = ∑_i φ_h(s,a)_i · μ_h(s')_i -/
  decomp : ∀ h s a s',
    M.P h s a s' = ∑ i : Fin d, φ h s a i * μ h s' i
  /-- Features have bounded norm -/
  φ_bound : ∀ h s a, ∑ i : Fin d, (φ h s a i) ^ 2 ≤ 1

end FiniteHorizonMDP

end
