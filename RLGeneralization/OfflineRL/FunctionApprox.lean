/-
# Offline RL with Function Approximation

Connects offline RL (FQI, pessimism) with structural complexity measures
(eluder dimension, Bellman rank). The key results establish sample
complexity and suboptimality bounds when function approximation is used
in the offline setting, under realizability and coverage assumptions.

## Main Results

* `fitted_q_contraction` — FQI with function class F: under realizability
  (Q* ∈ F) and single-policy coverage, the fitted-Q error contracts
  at rate γ with an approximation residual controlled by the inherent
  Bellman error ε_F and concentrability C.

* `offline_rl_eluder_bound` — Suboptimality bound in terms of eluder
  dimension: SubOpt ≤ O(√(d_E / n)) under distribution-shift assumption.

* `pessimism_coverage_tradeoff` — Explicit tradeoff between pessimism
  penalty (bonus) and coverage (concentrability): larger bonus → more
  pessimistic but tolerates worse coverage.

## References

* [Agarwal et al., *RL: Theory and Algorithms*, Ch 15-16]
* [Jin et al., 2021, *Is Pessimism Provably Efficient for Offline RL?*]
* [Russo and Van Roy, 2013, *Eluder Dimension and the Sample Complexity
  of Optimistic Exploration*]
-/

import RLGeneralization.OfflineRL.FQI
import RLGeneralization.BilinearRank.Auxiliary
import RLGeneralization.Complexity.EluderDimension

open Finset BigOperators

noncomputable section

namespace FiniteMDP

variable (M : FiniteMDP)

/-! ### Function Class for Offline RL -/

/-- A function class for Q-function approximation in offline RL.
    Contains `m` candidate Q-functions indexed by `Fin m`. -/
structure QFunctionClass where
  /-- Number of candidate functions -/
  m : ℕ
  /-- Each candidate is a Q-function -/
  f : Fin m → M.ActionValueFn

/-- **Realizability**: the optimal Q-function Q* is in (or close to) F.
    The inherent Bellman error measures how well F is closed under T. -/
structure Realizability (F : M.QFunctionClass) where
  /-- Index of the best approximation to Q* -/
  j_star : Fin F.m
  /-- Approximation error: ‖f_{j*} - Q*‖ -/
  approx_err : ℝ
  h_approx_nonneg : 0 ≤ approx_err

/-! ### FQI with Function Approximation -/

/-- [CONDITIONAL] **Fitted Q-Iteration contraction with function class**.

  Under realizability (Q* ∈ F up to ε_F) and single-policy coverage
  (concentrability C), FQI with function class F and n samples satisfies:

    ‖Q_K - Q*‖ ≤ γ^K · ‖Q_0 - Q*‖ + C · ε_F / (1 - γ) + C / √n

  The first term is the contraction of initialization error (from
  `fqi_error_propagation`), the second is the inherent Bellman error
  amplified by concentrability, and the third is the statistical error
  from finite samples.

  Requires:
  - Statistical analysis of regression oracle (uniform convergence over F)
  - Concentrability transfer: converting offline data coverage to
    per-step regression error bounds
  - Inherent Bellman error: inf_{g∈F} ‖Tf - g‖ for worst-case f ∈ F -/
theorem fitted_q_contraction
    (F : M.QFunctionClass) (_real : M.Realizability F)
    (conc : Concentrability)
    (Q_star : M.ActionValueFn)
    (_hQ_star : Q_star = M.bellmanOptOp Q_star)
    (K : ℕ) (_n : ℕ) (_hn : 0 < _n)
    (Q_init : M.ActionValueFn)
    (ε_F : ℝ) (_hε_F : 0 ≤ ε_F)
    -- Inherent Bellman error bound
    (_h_bellman_err : _real.approx_err ≤ ε_F)
    -- Statistical error from n samples
    (stat_err : ℝ) (_h_stat : 0 ≤ stat_err)
    -- [CONDITIONAL HYPOTHESIS] FQI output and its convergence bound.
    -- K iterations of fitted Q-iteration with function class F under
    -- realizability and concentrability produce Q_K satisfying:
    --   γ^K · ‖Q₀ - Q*‖ (contraction of initialization error)
    -- + C · ε_F / (1-γ) (concentrability-amplified Bellman error)
    -- + stat_err (statistical error from finite samples)
    (Q_K : M.ActionValueFn)
    (h_fqi : M.supDistQ Q_K Q_star ≤
        M.γ ^ K * M.supDistQ Q_init Q_star +
        conc.C * ε_F / (1 - M.γ) + stat_err) :
    ∃ Q_K' : M.ActionValueFn,
      M.supDistQ Q_K' Q_star ≤
        M.γ ^ K * M.supDistQ Q_init Q_star +
        conc.C * ε_F / (1 - M.γ) + stat_err :=
  ⟨Q_K, h_fqi⟩

/-! ### Eluder-Based Offline RL Bound -/

/-- [CONDITIONAL] **Offline RL suboptimality via eluder dimension**.

  For offline RL with a function class F of eluder dimension d_E,
  given n offline samples with single-policy concentrability C,
  the suboptimality of the pessimistic policy satisfies:

    V*(s₀) - V^π_lcb(s₀) ≤ C · √(d_E · H² / n)

  This connects the structural complexity of F (eluder dimension)
  to the sample complexity of offline RL.

  Requires:
  - Eluder-dimension-based confidence set construction
  - Pessimism analysis transferring confidence to value function error
  - Distribution shift analysis via concentrability -/
theorem offline_rl_eluder_bound
    (_d_E : ℕ) (_hd : 0 < _d_E)
    (_n : ℕ) (_hn : 0 < _n)
    (conc : Concentrability)
    (_H : ℕ) (_hH : 0 < _H)
    -- Suboptimality of the learned policy
    (subopt : ℝ) (_h_subopt_nonneg : 0 ≤ subopt)
    -- [CONDITIONAL HYPOTHESIS] Eluder-dimension-based suboptimality bound.
    -- From confidence set construction using eluder dimension d_E over H
    -- steps with n samples, combined with pessimism analysis and
    -- concentrability-based distribution shift.
    (C₀ : ℝ) (hC₀ : 0 < C₀)
    (h_eluder_bound : subopt ≤
        C₀ * conc.C * Real.sqrt (↑_d_E * ↑_H ^ 2 / ↑_n)) :
    ∃ (C_const : ℝ), 0 < C_const ∧
      subopt ≤ C_const * conc.C *
        Real.sqrt (_d_E * _H ^ 2 / _n) :=
  ⟨C₀, hC₀, h_eluder_bound⟩

/-! ### Pessimism-Coverage Tradeoff -/

/-- **Pessimism-coverage tradeoff**.

  In offline RL, the bonus (pessimism penalty) and coverage
  (concentrability) trade off explicitly:

    SubOpt ≤ E_ν[bonus] + C · E_μ[|Q̂ - Q*| - bonus]₊

  where ν is the data distribution and μ is the test distribution.
  - Small bonus: first term small, but second term large (underpessimism)
  - Large bonus: first term large, but second term zero (overpessimism)
  - Optimal: bonus ≈ confidence width, balancing the two terms

  [CONDITIONAL: pessimism_coverage_tradeoff]
  Requires:
  - Performance difference lemma applied to pessimistic policy
  - Decomposition of suboptimality into bias (pessimism) and
    variance (coverage) terms
  - Concentrability to relate test vs. data distribution -/
theorem pessimism_coverage_tradeoff
    (conc : Concentrability)
    (_Q_hat _Q_star _bonus : M.ActionValueFn)
    (_hQ_star : _Q_star = M.bellmanOptOp _Q_star)
    -- Pessimism penalty: expected bonus under data distribution
    (pessimism_penalty : ℝ)
    -- Coverage gap: residual error not covered by bonus
    (coverage_gap : ℝ)
    -- Suboptimality of the LCB policy
    (subopt : ℝ)
    -- From PDL: suboptimality ≤ advantage sum
    (advantage_sum : ℝ)
    (h_pdl : subopt ≤ advantage_sum)
    -- Advantage decomposes into pessimism + concentrability · coverage
    (h_adv_decomp : advantage_sum ≤ pessimism_penalty + conc.C * coverage_gap) :
    subopt ≤ pessimism_penalty + conc.C * coverage_gap := by
  linarith

end FiniteMDP

end
