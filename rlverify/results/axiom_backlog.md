# Axiom Backlog

Standard results used as axioms during verification. Each entry is a candidate for full formalization in the Lean library. Once formalized, future verifications will hit them as library matches automatically.

**Statement requirement** (added 2026-06-10 after the `cfpo_warmup_free_report.md` retraction): an axiom's Lean statement must bind every variable to what its name suggests via hypotheses. A statement like `axiom foo ... (E : ℕ) : (E : ℝ) ≤ bound` asserts the bound for *every* natural number and is inconsistent regardless of what `E` is called. Every new axiom must pass the back-translation audit (see `/verify-full-process` Phase 3) before it may support a VERIFIED MODULO AXIOMS verdict.

## Formalized

- **matrix_sqrt_lipschitz** (scalar) — |√a - √b| ≤ (2√λ)⁻¹ |a - b| for a,b ≥ λ > 0
  - Reference: Bhatia, Matrix Analysis Ch. X
  - Formalized in: `RLGeneralization/LinearMDP/SqrtLipschitz.lean`
  - Status: FORMALIZED (scalar version)

- **matrix_sqrt_lipschitz** (full matrix) — ‖Λ^{1/2} - Λ'^{1/2}‖ ≤ (2√λ_min)⁻¹ ‖Λ - Λ'‖
  - Reference: Bhatia, Matrix Analysis Ch. X; Higham, Functions of Matrices Thm 6.1
  - Formalized in: `RLGeneralization/LinearMDP/MatrixSqrtLipschitzFull.lean`
  - Status: FORMALIZED (Frobenius and spectral norm versions via eigenvalue decomposition)

- **epoch_count_bound** — Epoch count from determinant doubling: E ≤ (3/2)dH log(2K)
  - Reference: Abbasi-Yadkori et al. (2011) Lemma 11; Jin et al. (2020) Lemma B.4
  - Formalized in: `RLGeneralization/LinearMDP/EpochCountBound.lean`
  - Status: FORMALIZED

- **ball_covering_number** — ε-covering of B_d(R): N_ε ≤ (1+2R/ε)^d and log N_ε ≤ d·log(1+2R/ε)
  - Reference: Vershynin, "High-Dimensional Probability", Corollary 4.2.13
  - Formalized in: `RLGeneralization/Complexity/CoveringPacking.lean`
  - Status: FORMALIZED (`covering_number_ball_bound`, `metric_entropy_ball_bound`)

- **elliptical_potential** — Σ min(1, φ_t^T Λ_t⁻¹ φ_t) ≤ 2d log(1 + T/(λd))
  - Reference: Dani et al. (2008); Abbasi-Yadkori et al. (2011) Lemma 19
  - Formalized in: `RLGeneralization/LinearMDP/EllipticalPotential.lean`
  - Status: FORMALIZED (`elliptical_potential_lemma_unconditional`, fully unconditional)

- **extended_value_difference** — V^π - V̂ = Σ_h (Bellman residual), telescoping identity
  - Reference: Shani et al. (2020) Lemma 1; Jiang & Li (2016)
  - Formalized in: `RLGeneralization/MDP/ExtendedValueDifference.lean`
  - Status: FORMALIZED (`extended_value_difference`, `regret_via_value_difference`, `value_difference_abs_bound`)

- **omd_regret** — Hedge/OMD regret ≤ log|A|/η + η·Σ y²
  - Reference: Sherman et al. (2023) Lemma 25; Shalev-Shwartz (2012) Ch. 2
  - Formalized in: `RLGeneralization/Bandits/OMDRegret.lean`
  - Status: FORMALIZED (`hedge_regret_bound`, `omd_total_regret`, `omd_tuned`)

- **matrix_norm_det_inequality** — If N ≽ M ≻ 0 then ‖v‖²_N ≤ (det N / det M)·‖v‖²_M
  - Reference: Cohen et al. (2019) Lemma 27
  - Formalized in: `RLGeneralization/LinearMDP/MatrixNormDetInequality.lean`
  - Status: FORMALIZED (`eigenvalue_product_dominates`, `norm_det_inequality_eigen`, `det_doubling_norm_bound`)

- **reward_confidence_set** — ‖θ - θ̂‖_Λ ≤ β (self-normalized martingale bound)
  - Reference: Abbasi-Yadkori et al. (2011) Theorem 2
  - Formalized in: `RLGeneralization/Concentration/SelfNormalizedComplete.lean`
  - Status: FORMALIZED (`self_normalized_full_bound`, `reward_confidence_set`, `confidenceRadiusSq'`)

- **dynamics_confidence_set** — ‖(ψ - ψ̂)V‖_Λ ≤ β_p (V-dependent self-normalized bound)
  - Reference: Abbasi-Yadkori et al. (2011); Cohen et al. (2019)
  - Formalized in: `RLGeneralization/Concentration/SelfNormalizedComplete.lean`
  - Status: FORMALIZED (`dynamics_confidence_set`, `dynamics_beta_from_reward_beta`)

- **multiplicative_concentration** — Σ E[X_t] ≤ 2·Σ X_t + C·log(1/δ), trajectory-level
  - Reference: Rosenberg (2020) Lemma D.4; Freedman (1975)
  - Formalized in: `RLGeneralization/Concentration/TrajectoryConcentrationComplete.lean`
  - Status: FORMALIZED (`multiplicative_concentration`, `freedman_trajectory`, `azuma_hoeffding_trajectory`)

- **sa_contraction_convergence** — Deterministic core: if e(t+1) ≤ (1-c·α\_t)·e(t) with c > 0, 0 ≤ c·α\_t ≤ 1, e ≥ 0, and Σα\_t = ∞, then e(t) → 0
  - Reference: Tsitsiklis (1994), Machine Learning 16(3):185–202, Theorem 1; Bertsekas & Tsitsiklis, Neuro-Dynamic Programming (1996), Prop. 4.4
  - Used by: Stochastic Value Iteration convergence proof (Step 4); Q-learning; SARSA; TD
  - Formalized in: library corpus (`sa_contraction_convergence`)
  - Status: FORMALIZED (deterministic contraction convergence; stochastic extension with martingale noise requires measure-theoretic conditional expectation not yet in Mathlib)

- **von_neumann_minimax** — ∃ p ∈ Δ(P), q ∈ Δ(O): sup\_θ E\_p[R(·,θ)] = inf\_π E\_q[R(π,·)]
  - Reference: von Neumann (1928), "Zur Theorie der Gesellschaftsspiele", Math. Annalen 100(1):295–320
  - Used by: Minimax Regret Bounds paper (Theorem 1, Corollary 1)
  - Formalized in: `RLGeneralization/RLVerify/minimax_duality.lean` (`von_neumann_minimax`, proved via geometric Hahn-Banach separation)
  - Status: FORMALIZED

## Pending

(none)

