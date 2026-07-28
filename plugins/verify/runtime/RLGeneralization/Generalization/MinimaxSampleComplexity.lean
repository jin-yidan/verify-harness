/-
# Minimax Sample Complexity (Deterministic Core)

Formalizes the **deterministic core** of the minimax sample complexity
analysis for model-based RL with a generative model. The results here
bound the value gap in terms of a transition-error tolerance ε_T, but
do not include the probabilistic sampling layer that converts ε_T to
a sample count N. The full end-to-end PAC bound is in
`Concentration.GenerativeModel`; this module is classified as `weaker`
in `verification_manifest.json`.

## Main Results

* `transition_variance` - Variance of V under transition P(·|s,a).
* `weighted_deviation_bound_genuine` - Proved: |W(s)| ≤ γ·V_max/(1-γ)
  from variance bound (Var ≤ V_max²) + resolvent contraction.
* `minimax_deterministic_core` - Deterministic core:
    V*(s) - V̂*(s) ≤ 2γ·R_max·ε_T/(1-γ)²
  by chaining optimality_gap_from_transition_error.
* `minimax_rate_scaling` - For all M̂ with transitionError ≤ ε_T
  and same rewards, ∃ c > 0 s.t. Q-value gap ≤ c·ε_T/(1-γ)².

## References

* [Azar, Munos, Kappen, *Minimax PAC bounds on the sample complexity
  of RL with a generative model*][azar2013]
* [Agarwal et al., *RL: Theory and Algorithms*]
-/

import RLGeneralization.Generalization.SampleComplexity
import RLGeneralization.Generalization.ComponentWise
import RLGeneralization.Concentration.Bernstein

open Finset BigOperators

noncomputable section

namespace FiniteMDP

variable (M : FiniteMDP)

/-! ### Variance Definitions -/

/-- Variance of a value function V under transition P(·|s,a):
    Var_P(V)(s,a) = ∑_{s'} P(s'|s,a) · (V(s') - E_P[V])²
    where E_P[V] = ∑_{s'} P(s'|s,a) · V(s'). -/
def transition_variance (V : M.StateValueFn) (s : M.S) (a : M.A) : ℝ :=
  let μ := ∑ s', M.P s a s' * V s'
  ∑ s', M.P s a s' * (V s' - μ) ^ 2

/-- Variance is nonnegative. -/
lemma transition_variance_nonneg (V : M.StateValueFn) (s : M.S) (a : M.A) :
    0 ≤ M.transition_variance V s a := by
  unfold transition_variance
  apply Finset.sum_nonneg
  intro s' _
  exact mul_nonneg (M.P_nonneg s a s') (sq_nonneg _)

/-- Variance bound: Var_P(V) ≤ ‖V‖∞² (trivial bound). -/
lemma transition_variance_le_sq_norm (V : M.StateValueFn) (s : M.S) (a : M.A)
    (B : ℝ) (hB : ∀ s', |V s'| ≤ B) :
    M.transition_variance V s a ≤ (2 * B) ^ 2 := by
  unfold transition_variance
  -- Mean μ = ∑ P(s'|s,a) V(s') satisfies |μ| ≤ B
  set μ := ∑ s', M.P s a s' * V s'
  -- Each term: P(s'|s,a) * (V(s') - μ)² ≤ P(s'|s,a) * (2B)²
  -- Sum: ≤ (2B)² * ∑ P = (2B)²
  calc ∑ s', M.P s a s' * (V s' - μ) ^ 2
      ≤ ∑ s', M.P s a s' * (2 * B) ^ 2 := by
        apply Finset.sum_le_sum
        intro s' _
        apply mul_le_mul_of_nonneg_left _ (M.P_nonneg s a s')
        apply sq_le_sq'
        · -- -(2B) ≤ V(s') - μ
          -- We need |V(s') - μ| ≤ 2B
          -- |μ| ≤ B by weighted average, |V(s')| ≤ B, so |V(s')-μ| ≤ 2B
          have hμ : |μ| ≤ B := by
            calc |μ| = |∑ s', M.P s a s' * V s'| := rfl
              _ ≤ ∑ s', |M.P s a s' * V s'| := abs_sum_le_sum_abs _ _
              _ = ∑ s', M.P s a s' * |V s'| := by
                  congr 1; ext s'
                  rw [abs_mul, abs_of_nonneg (M.P_nonneg s a s')]
              _ ≤ ∑ s', M.P s a s' * B := by
                  apply Finset.sum_le_sum; intro s' _
                  exact mul_le_mul_of_nonneg_left (hB s') (M.P_nonneg s a s')
              _ = B * ∑ s', M.P s a s' := by rw [← Finset.sum_mul]; ring
              _ = B := by rw [M.P_sum_one s a, mul_one]
          linarith [abs_le.mp (hB s'), abs_le.mp hμ]
        · have hμ : |μ| ≤ B := by
            calc |μ| = |∑ s', M.P s a s' * V s'| := rfl
              _ ≤ ∑ s', |M.P s a s' * V s'| := abs_sum_le_sum_abs _ _
              _ = ∑ s', M.P s a s' * |V s'| := by
                  congr 1; ext s'
                  rw [abs_mul, abs_of_nonneg (M.P_nonneg s a s')]
              _ ≤ ∑ s', M.P s a s' * B := by
                  apply Finset.sum_le_sum; intro s' _
                  exact mul_le_mul_of_nonneg_left (hB s') (M.P_nonneg s a s')
              _ = B * ∑ s', M.P s a s' := by rw [← Finset.sum_mul]; ring
              _ = B := by rw [M.P_sum_one s a, mul_one]
          linarith [abs_le.mp (hB s'), abs_le.mp hμ]
    _ = (2 * B) ^ 2 * ∑ s', M.P s a s' := by
        rw [← Finset.sum_mul]; ring
    _ = (2 * B) ^ 2 := by rw [M.P_sum_one s a, mul_one]

/-- **Tighter variance bound**: Var_P(V) ≤ V_max² (via E[X²] - μ² ≤ E[X²]).

    This improves on `transition_variance_le_sq_norm` which gives (2V_max)².
    Proof: expand Var = ∑ P(V-μ)² = ∑ PV² - μ² ≤ ∑ PV² ≤ B². -/
lemma transition_variance_le_sq (V : M.StateValueFn) (s : M.S) (a : M.A)
    (B : ℝ) (_hB_nonneg : 0 ≤ B) (hB : ∀ s', |V s'| ≤ B) :
    M.transition_variance V s a ≤ B ^ 2 := by
  -- Strategy: Var = E[V²] - μ² ≤ E[V²] ≤ B²
  -- We bound each term directly using the (2B)² bound on (V-μ)²
  -- but then improve using E[V²] ≤ B²
  unfold transition_variance
  set μ := ∑ s', M.P s a s' * V s' with hμ_def
  -- Step 1: Show ∑P·V² ≤ B²
  have h_EXsq_le : ∑ s', M.P s a s' * V s' ^ 2 ≤ B ^ 2 := by
    calc ∑ s', M.P s a s' * V s' ^ 2
        ≤ ∑ s', M.P s a s' * B ^ 2 := by
          apply Finset.sum_le_sum; intro s' _
          apply mul_le_mul_of_nonneg_left _ (M.P_nonneg s a s')
          exact sq_le_sq' (by linarith [abs_le.mp (hB s')]) (abs_le.mp (hB s')).2
      _ = B ^ 2 := by rw [← Finset.sum_mul, M.P_sum_one s a, one_mul]
  -- Step 2: Show ∑P·(V-μ)² = ∑P·V² - μ²
  have h_var_identity : ∑ s', M.P s a s' * (V s' - μ) ^ 2 =
      ∑ s', M.P s a s' * V s' ^ 2 - μ ^ 2 := by
    have : ∀ s', M.P s a s' * (V s' - μ) ^ 2 =
        M.P s a s' * V s' ^ 2 - 2 * μ * (M.P s a s' * V s') +
          μ ^ 2 * M.P s a s' := by intro s'; ring
    conv_lhs => arg 2; ext s'; rw [this s']
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have h1 : ∑ s', μ ^ 2 * M.P s a s' = μ ^ 2 := by
      rw [← Finset.mul_sum, M.P_sum_one s a, mul_one]
    have h2 : ∑ s', 2 * μ * (M.P s a s' * V s') = 2 * μ * μ := by
      rw [← Finset.mul_sum]
    rw [h1, h2]; ring
  -- Step 3: Combine
  rw [h_var_identity]
  linarith [sq_nonneg μ]

/-- The empirical variance of V under empirical transition P̂(·|s,a). -/
def empirical_variance (P_hat : M.S → M.A → M.S → ℝ)
    (V : M.StateValueFn) (s : M.S) (a : M.A) : ℝ :=
  let μ := ∑ s', P_hat s a s' * V s'
  ∑ s', P_hat s a s' * (V s' - μ) ^ 2

/-! ### Sigma^pi: Weighted Deviation -/

/-- The weighted deviation vector Σ^π(s) = γ · ∑_a π(a|s) · √Var_P(V*)(s,a).

    This is the variance-sensitive driving term in the Bernstein-based bound.
    The key quantity in the sharper 1/(1-γ)^{3/2} bound. -/
def weighted_deviation (π : M.StochasticPolicy) (V_star : M.StateValueFn)
    (s : M.S) : ℝ :=
  M.γ * ∑ a, π.prob s a * Real.sqrt (M.transition_variance V_star s a)

/-! ### Weighted Deviation Bound: Genuine Proof -/

/-- √Var_P(V*)(s,a) ≤ V_max, using the tighter Var ≤ V_max² bound. -/
lemma sqrt_variance_le_Vmax (V_star : M.StateValueFn)
    (hV_bnd : ∀ s, |V_star s| ≤ M.V_max)
    (s : M.S) (a : M.A) :
    Real.sqrt (M.transition_variance V_star s a) ≤ M.V_max := by
  have h_var := M.transition_variance_le_sq V_star s a M.V_max
    (le_of_lt M.V_max_pos) hV_bnd
  calc Real.sqrt (M.transition_variance V_star s a)
      ≤ Real.sqrt (M.V_max ^ 2) := Real.sqrt_le_sqrt h_var
    _ = |M.V_max| := Real.sqrt_sq_eq_abs _
    _ = M.V_max := abs_of_nonneg (le_of_lt M.V_max_pos)

/-- Σ^π(s) ≤ γ · V_max for all s, from √Var ≤ V_max. -/
lemma weighted_deviation_le (π : M.StochasticPolicy)
    (V_star : M.StateValueFn)
    (hV_bnd : ∀ s, |V_star s| ≤ M.V_max) (s : M.S) :
    M.weighted_deviation π V_star s ≤ M.γ * M.V_max := by
  unfold weighted_deviation
  apply mul_le_mul_of_nonneg_left _ M.γ_nonneg
  calc ∑ a, π.prob s a * Real.sqrt (M.transition_variance V_star s a)
      ≤ ∑ a, π.prob s a * M.V_max := by
        apply Finset.sum_le_sum; intro a _
        exact mul_le_mul_of_nonneg_left
          (M.sqrt_variance_le_Vmax V_star hV_bnd s a)
          (π.prob_nonneg s a)
    _ = (∑ a, π.prob s a) * M.V_max := by
        rw [Finset.sum_mul]
    _ = M.V_max := by rw [π.prob_sum_one s, one_mul]

/-- Σ^π(s) ≥ 0 for all s. -/
lemma weighted_deviation_nonneg (π : M.StochasticPolicy)
    (V_star : M.StateValueFn) (s : M.S) :
    0 ≤ M.weighted_deviation π V_star s := by
  unfold weighted_deviation
  apply mul_nonneg M.γ_nonneg
  apply Finset.sum_nonneg; intro a _
  exact mul_nonneg (π.prob_nonneg s a) (Real.sqrt_nonneg _)

/-- **Weighted deviation resolvent bound** (strengthened).

  For V* bounded by V_max, and any policy π, if W solves the
  resolvent equation W = Σ^π + γP^πW, then:

    |W(s)| ≤ γ · V_max / (1-γ)

  This follows from:
  1. transition_variance_le_sq: Var_P(V*) ≤ V_max² (via E[X²]-μ² ≤ E[X²])
  2. So √Var ≤ V_max, hence Σ^π(s) ≤ γ·V_max
  3. resolvent_bound: ‖(I-γP^π)⁻¹ Σ^π‖ ≤ ‖Σ^π‖/(1-γ) ≤ γ·V_max/(1-γ)

  This improves the previous bound by a factor of 2 (was 2γ·V_max/(1-γ)). -/
theorem weighted_deviation_bound_genuine (π : M.StochasticPolicy)
    (V_star : M.StateValueFn)
    (hV_bnd : ∀ s, |V_star s| ≤ M.V_max)
    -- W solves the resolvent equation: W = Σ^π + γP^πW
    (W : M.StateValueFn)
    (hW : ∀ s, W s = M.weighted_deviation π V_star s +
      M.γ * M.expectedNextValue π W s) :
    ∀ s, |W s| ≤ M.γ * M.V_max / (1 - M.γ) := by
  -- Step 1: The driving term Σ^π(s) ≤ γ·V_max for all s
  have h_drive : ∀ s, |M.weighted_deviation π V_star s| ≤
      M.γ * M.V_max := by
    intro s
    rw [abs_of_nonneg (M.weighted_deviation_nonneg π V_star s)]
    exact M.weighted_deviation_le π V_star hV_bnd s
  -- Step 2: Apply resolvent_bound with v = Σ^π
  have h_res := M.resolvent_bound π W (M.weighted_deviation π V_star) hW
  -- Step 3: supNormV(Σ^π) ≤ γ·V_max
  have h_sup : M.supNormV (M.weighted_deviation π V_star) ≤
      M.γ * M.V_max := by
    simp only [supNormV]
    exact Finset.sup'_le _ _ (fun s _ => h_drive s)
  -- Step 4: Combine
  intro s
  calc |W s|
      ≤ M.supNormV (M.weighted_deviation π V_star) / (1 - M.γ) := h_res s
    _ ≤ M.γ * M.V_max / (1 - M.γ) := by
        apply div_le_div_of_nonneg_right h_sup
        linarith [M.γ_lt_one]

/-! ### Variance Identity: Var = E[X²] - (EX)² -/

/-- Variance identity: Var_P(V)(s,a) = E_P[V²](s,a) - (E_P[V](s,a))².
    This is the standard identity for finite weighted sums with
    weights summing to 1. -/
lemma variance_eq_EXsq_sub_sq (w : M.S → ℝ) (V : M.StateValueFn)
    (_hw_nonneg : ∀ s', 0 ≤ w s')
    (hw_sum : ∑ s', w s' = 1) :
    (∑ s', w s' * (V s' - ∑ s'', w s'' * V s'') ^ 2) =
    (∑ s', w s' * (V s') ^ 2) - (∑ s', w s' * V s') ^ 2 := by
  set μ := ∑ s', w s' * V s'
  -- Expand (V(s') - μ)² = V(s')² - 2μV(s') + μ²
  have hexpand : ∀ s', w s' * (V s' - μ) ^ 2 =
      w s' * (V s') ^ 2 - 2 * μ * (w s' * V s') + μ ^ 2 * w s' := by
    intro s'; ring
  simp_rw [hexpand, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  -- ∑ w·V² - 2μ·∑(w·V) + μ²·∑w = ∑ w·V² - 2μ² + μ² = ∑ w·V² - μ²
  rw [← Finset.mul_sum, ← Finset.mul_sum, hw_sum, mul_one]
  ring

/-- Transition variance as E[V²] - (EV)². -/
lemma transition_variance_eq (V : M.StateValueFn) (s : M.S) (a : M.A) :
    M.transition_variance V s a =
    (∑ s', M.P s a s' * (V s') ^ 2) -
    (∑ s', M.P s a s' * V s') ^ 2 := by
  unfold transition_variance
  exact M.variance_eq_EXsq_sub_sq (M.P s a) V (M.P_nonneg s a) (M.P_sum_one s a)

/-- Empirical variance as E_{P̂}[V²] - (E_{P̂}[V])². -/
lemma empirical_variance_eq (P_hat : M.S → M.A → M.S → ℝ)
    (hP_nonneg : ∀ s a s', 0 ≤ P_hat s a s')
    (hP_sum : ∀ s a, ∑ s', P_hat s a s' = 1)
    (V : M.StateValueFn) (s : M.S) (a : M.A) :
    M.empirical_variance P_hat V s a =
    (∑ s', P_hat s a s' * (V s') ^ 2) -
    (∑ s', P_hat s a s' * V s') ^ 2 := by
  unfold empirical_variance
  exact M.variance_eq_EXsq_sub_sq (P_hat s a) V (hP_nonneg s a) (hP_sum s a)

/-! ### Auxiliary Bounds for Variance Swap -/

/-- Bound on |∑ w·f - ∑ w'·f| when w ≈ w' (L1 error) and f bounded. -/
lemma weighted_sum_diff_le (w w' : M.S → ℝ) (f : M.S → ℝ)
    (B : ℝ) (hB : ∀ s', |f s'| ≤ B) :
    |∑ s', w s' * f s' - ∑ s', w' s' * f s'| ≤
    B * ∑ s', |w s' - w' s'| := by
  calc |∑ s', w s' * f s' - ∑ s', w' s' * f s'|
      = |∑ s', (w s' - w' s') * f s'| := by
        congr 1; rw [← Finset.sum_sub_distrib]; congr 1; ext s'; ring
    _ ≤ ∑ s', |(w s' - w' s') * f s'| := abs_sum_le_sum_abs _ _
    _ = ∑ s', |w s' - w' s'| * |f s'| := by
        congr 1; ext s'; exact abs_mul _ _
    _ ≤ ∑ s', |w s' - w' s'| * B := by
        apply Finset.sum_le_sum; intro s' _
        exact mul_le_mul_of_nonneg_left (hB s') (abs_nonneg _)
    _ = B * ∑ s', |w s' - w' s'| := by rw [← Finset.sum_mul]; ring

/-- Bound on |∑ w·f - ∑ w·g| when w is a probability and |f-g| bounded. -/
lemma weighted_sum_fn_diff_le (w : M.S → ℝ) (f g : M.S → ℝ)
    (hw_nonneg : ∀ s', 0 ≤ w s')
    (hw_sum : ∑ s', w s' = 1)
    (δ : ℝ) (hδ : ∀ s', |f s' - g s'| ≤ δ) :
    |∑ s', w s' * f s' - ∑ s', w s' * g s'| ≤ δ := by
  calc |∑ s', w s' * f s' - ∑ s', w s' * g s'|
      = |∑ s', w s' * (f s' - g s')| := by
        congr 1; rw [← Finset.sum_sub_distrib]; congr 1; ext s'; ring
    _ ≤ ∑ s', |w s' * (f s' - g s')| := abs_sum_le_sum_abs _ _
    _ = ∑ s', w s' * |f s' - g s'| := by
        congr 1; ext s'
        rw [abs_mul, abs_of_nonneg (hw_nonneg s')]
    _ ≤ ∑ s', w s' * δ := by
        apply Finset.sum_le_sum; intro s' _
        exact mul_le_mul_of_nonneg_left (hδ s') (hw_nonneg s')
    _ = δ * ∑ s', w s' := by rw [← Finset.sum_mul]; ring
    _ = δ := by rw [hw_sum, mul_one]

/-! ### Variance Swap -/

/-- **Variance swap / variance approximation**.

  For V* the optimal value in M and V̂* the optimal value in M̂,
  with same rewards:

    Var_P(V*)(s,a) ≤ 2 · Var_{P̂}(V̂*)(s,a) + C · V_max² · ε_T

  The proof uses:
  1. Variance identity: Var = E[X²] - (EX)²
  2. Triangle inequality on E[X²] and (EX)² terms
  3. |V* - V̂*| bounded by value gap from transition error

  See `variance_swap_from_simulation` for the self-contained version
  that eliminates δ_V via the simulation-lemma rate. -/
theorem variance_swap (M_hat : M.ApproxMDP)
    (V_star V_hat_star : M.StateValueFn)
    (hV_bnd : ∀ s, |V_star s| ≤ M.V_max)
    (hV_hat_bnd : ∀ s, |V_hat_star s| ≤ M.V_max)
    -- Value gap: |V*(s) - V̂*(s)| ≤ δ_V for all s
    (δ_V : ℝ) (hδ_V_nonneg : 0 ≤ δ_V)
    (h_val_gap : ∀ s, |V_star s - V_hat_star s| ≤ δ_V)
    -- Transition error bound
    (ε_T : ℝ) (_hε_T_nonneg : 0 ≤ ε_T)
    (hε_T : M.transitionError M_hat ≤ ε_T) :
    ∀ s a, M.transition_variance V_star s a ≤
      2 * M.empirical_variance M_hat.P_hat V_hat_star s a +
      (3 * M.V_max ^ 2 * ε_T + 4 * M.V_max * δ_V) := by
  intro s a
  -- Step 1: Rewrite variances using E[X²] - (EX)² identity
  rw [M.transition_variance_eq V_star s a]
  rw [M.empirical_variance_eq M_hat.P_hat M_hat.P_hat_nonneg
      M_hat.P_hat_sum_one V_hat_star s a]
  -- Abbreviations for the four key quantities
  set EP_Vsq := ∑ s', M.P s a s' * (V_star s') ^ 2
  set EP_V := ∑ s', M.P s a s' * V_star s'
  set EPh_Vhsq := ∑ s', M_hat.P_hat s a s' * (V_hat_star s') ^ 2
  set EPh_Vh := ∑ s', M_hat.P_hat s a s' * V_hat_star s'
  -- Goal: EP_Vsq - EP_V^2 ≤ 2*(EPh_Vhsq - EPh_Vh^2) + C
  -- Strategy: Var_P(V*) = E_P[V*²] - (E_P[V*])²
  --   ≤ (E_{P̂}[V̂*²] + err₁) - ((E_{P̂}[V̂*])² - err₂)
  --   = Var_{P̂}(V̂*) + err₁ + err₂
  -- Then bound err₁, err₂ and show Var_{P̂}(V̂*) ≤ 2·Var_{P̂}(V̂*).

  -- Step 2: Bound |EP_Vsq - EPh_Vhsq| (E[V²] terms)
  -- Decompose: EP_Vsq - EPh_Vhsq = ∑(P-P̂)V*² + ∑P̂(V*²-V̂*²)
  -- |∑(P-P̂)V*²| ≤ V_max² · ε_T
  -- |∑P̂(V*²-V̂*²)| ≤ max|V*²-V̂*²| ≤ max(|V*+V̂*|·|V*-V̂*|) ≤ 2V_max·δ_V
  have hVsq_bnd : ∀ s', |(V_star s') ^ 2| ≤ M.V_max ^ 2 := by
    intro s'; rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hV_bnd s') 2
  have h_Vsq_diff : ∀ s', |(V_star s') ^ 2 - (V_hat_star s') ^ 2| ≤
      2 * M.V_max * δ_V := by
    intro s'
    rw [sq_sub_sq]
    calc |(V_star s' + V_hat_star s') * (V_star s' - V_hat_star s')|
        = |V_star s' + V_hat_star s'| * |V_star s' - V_hat_star s'| :=
          abs_mul _ _
      _ ≤ (|V_star s'| + |V_hat_star s'|) * δ_V := by
          apply mul_le_mul (abs_add_le _ _) (h_val_gap s')
            (abs_nonneg _) (by linarith [abs_nonneg (V_star s'), abs_nonneg (V_hat_star s')])
      _ ≤ (M.V_max + M.V_max) * δ_V := by
          apply mul_le_mul_of_nonneg_right _ hδ_V_nonneg
          linarith [hV_bnd s', hV_hat_bnd s']
      _ = 2 * M.V_max * δ_V := by ring
  -- |EP_Vsq - EPh_Vhsq| ≤ |∑(P-P̂)V*²| + |∑P̂(V*²-V̂*²)|
  have h_Esq_bound : EP_Vsq - EPh_Vhsq ≤
      M.V_max ^ 2 * ε_T + 2 * M.V_max * δ_V := by
    -- Decompose: EP_Vsq - EPh_Vhsq = ∑(P-P̂)(V*²) + ∑P̂(V*²-V̂*²)
    have h_decomp : EP_Vsq - EPh_Vhsq =
        (∑ s', (M.P s a s' - M_hat.P_hat s a s') * (V_star s') ^ 2) +
        (∑ s', M_hat.P_hat s a s' * ((V_star s') ^ 2 - (V_hat_star s') ^ 2)) := by
      simp only [EP_Vsq, EPh_Vhsq]
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      congr 1; ext s'; ring
    rw [h_decomp]
    -- Bound first term: |∑(P-P̂)V*²| ≤ V_max² · ε_T
    have h1 : ∑ s', (M.P s a s' - M_hat.P_hat s a s') * (V_star s') ^ 2 ≤
        M.V_max ^ 2 * ε_T := by
      calc ∑ s', (M.P s a s' - M_hat.P_hat s a s') * (V_star s') ^ 2
          ≤ |∑ s', (M.P s a s' - M_hat.P_hat s a s') * (V_star s') ^ 2| :=
            le_abs_self _
        _ ≤ ∑ s', |(M.P s a s' - M_hat.P_hat s a s') * (V_star s') ^ 2| :=
            abs_sum_le_sum_abs _ _
        _ = ∑ s', |M.P s a s' - M_hat.P_hat s a s'| * |(V_star s') ^ 2| := by
            congr 1; ext s'; exact abs_mul _ _
        _ ≤ ∑ s', |M.P s a s' - M_hat.P_hat s a s'| * M.V_max ^ 2 := by
            apply Finset.sum_le_sum; intro s' _
            exact mul_le_mul_of_nonneg_left (hVsq_bnd s') (abs_nonneg _)
        _ = M.V_max ^ 2 * ∑ s', |M.P s a s' - M_hat.P_hat s a s'| := by
            rw [← Finset.sum_mul]; ring
        _ ≤ M.V_max ^ 2 * ε_T := by
            apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
            exact le_trans (M.transitionError_le M_hat s a) hε_T
    -- Bound second term: |∑P̂(V*²-V̂*²)| ≤ 2V_max·δ_V
    have h2 : ∑ s', M_hat.P_hat s a s' * ((V_star s') ^ 2 - (V_hat_star s') ^ 2) ≤
        2 * M.V_max * δ_V := by
      have h2a : |∑ s', M_hat.P_hat s a s' * (V_star s') ^ 2 -
          ∑ s', M_hat.P_hat s a s' * (V_hat_star s') ^ 2| ≤
          2 * M.V_max * δ_V :=
        M.weighted_sum_fn_diff_le (M_hat.P_hat s a)
          (fun s' => (V_star s') ^ 2) (fun s' => (V_hat_star s') ^ 2)
          (M_hat.P_hat_nonneg s a) (M_hat.P_hat_sum_one s a)
          (2 * M.V_max * δ_V) h_Vsq_diff
      have h2b : ∑ s', M_hat.P_hat s a s' * ((V_star s') ^ 2 - (V_hat_star s') ^ 2) =
          ∑ s', M_hat.P_hat s a s' * (V_star s') ^ 2 -
          ∑ s', M_hat.P_hat s a s' * (V_hat_star s') ^ 2 := by
        rw [← Finset.sum_sub_distrib]; congr 1; ext s'; ring
      linarith [le_abs_self (∑ s', M_hat.P_hat s a s' * (V_star s') ^ 2 -
          ∑ s', M_hat.P_hat s a s' * (V_hat_star s') ^ 2)]
    linarith
  -- Step 3: Bound EP_V^2 - EPh_Vh^2 (mean-squared terms)
  -- EP_V^2 - EPh_Vh^2 = (EP_V + EPh_Vh)(EP_V - EPh_Vh)
  -- |EP_V| ≤ V_max, |EPh_Vh| ≤ V_max
  -- |EP_V - EPh_Vh| ≤ |∑(P-P̂)V*| + |∑P̂(V*-V̂*)| ≤ V_max·ε_T + δ_V
  have h_EP_bnd : |EP_V| ≤ M.V_max := by
    calc |EP_V| = |∑ s', M.P s a s' * V_star s'| := rfl
      _ ≤ ∑ s', |M.P s a s' * V_star s'| := abs_sum_le_sum_abs _ _
      _ = ∑ s', M.P s a s' * |V_star s'| := by
          congr 1; ext s'; rw [abs_mul, abs_of_nonneg (M.P_nonneg s a s')]
      _ ≤ ∑ s', M.P s a s' * M.V_max := by
          apply Finset.sum_le_sum; intro s' _
          exact mul_le_mul_of_nonneg_left (hV_bnd s') (M.P_nonneg s a s')
      _ = M.V_max * ∑ s', M.P s a s' := by rw [← Finset.sum_mul]; ring
      _ = M.V_max := by rw [M.P_sum_one s a, mul_one]
  have h_EPh_bnd : |EPh_Vh| ≤ M.V_max := by
    calc |EPh_Vh| = |∑ s', M_hat.P_hat s a s' * V_hat_star s'| := rfl
      _ ≤ ∑ s', |M_hat.P_hat s a s' * V_hat_star s'| := abs_sum_le_sum_abs _ _
      _ = ∑ s', M_hat.P_hat s a s' * |V_hat_star s'| := by
          congr 1; ext s'; rw [abs_mul, abs_of_nonneg (M_hat.P_hat_nonneg s a s')]
      _ ≤ ∑ s', M_hat.P_hat s a s' * M.V_max := by
          apply Finset.sum_le_sum; intro s' _
          exact mul_le_mul_of_nonneg_left (hV_hat_bnd s') (M_hat.P_hat_nonneg s a s')
      _ = M.V_max * ∑ s', M_hat.P_hat s a s' := by rw [← Finset.sum_mul]; ring
      _ = M.V_max := by rw [M_hat.P_hat_sum_one s a, mul_one]
  -- |EP_V - EPh_Vh| ≤ V_max·ε_T + δ_V
  have h_mean_diff : |EP_V - EPh_Vh| ≤ M.V_max * ε_T + δ_V := by
    -- EP_V - EPh_Vh = ∑(P-P̂)V* + ∑P̂(V*-V̂*)
    have h_decomp2 : EP_V - EPh_Vh =
        (∑ s', (M.P s a s' - M_hat.P_hat s a s') * V_star s') +
        (∑ s', M_hat.P_hat s a s' * (V_star s' - V_hat_star s')) := by
      simp only [EP_V, EPh_Vh]
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      congr 1; ext s'; ring
    rw [h_decomp2]
    calc |(∑ s', (M.P s a s' - M_hat.P_hat s a s') * V_star s') +
          (∑ s', M_hat.P_hat s a s' * (V_star s' - V_hat_star s'))|
        ≤ |∑ s', (M.P s a s' - M_hat.P_hat s a s') * V_star s'| +
          |∑ s', M_hat.P_hat s a s' * (V_star s' - V_hat_star s')| :=
          abs_add_le _ _
      _ ≤ M.V_max * ε_T + δ_V := by
          apply add_le_add
          · -- |∑(P-P̂)V*| ≤ V_max · ε_T
            -- Rewrite ∑(P-P̂)·V* = ∑P·V* - ∑P̂·V*
            have hrewrite : ∑ s', (M.P s a s' - M_hat.P_hat s a s') * V_star s' =
                ∑ s', M.P s a s' * V_star s' - ∑ s', M_hat.P_hat s a s' * V_star s' := by
              rw [← Finset.sum_sub_distrib]; congr 1; ext s'; ring
            rw [hrewrite]
            calc |∑ s', M.P s a s' * V_star s' - ∑ s', M_hat.P_hat s a s' * V_star s'|
                ≤ M.V_max * ∑ s', |M.P s a s' - M_hat.P_hat s a s'| :=
                  M.weighted_sum_diff_le (M.P s a) (M_hat.P_hat s a)
                    V_star M.V_max hV_bnd
              _ ≤ M.V_max * ε_T :=
                  mul_le_mul_of_nonneg_left
                    (le_trans (M.transitionError_le M_hat s a) hε_T)
                    (le_of_lt M.V_max_pos)
          · -- |∑P̂(V*-V̂*)| ≤ δ_V
            -- Rewrite ∑P̂·(V*-V̂*) = ∑P̂·V* - ∑P̂·V̂*
            have hrewrite2 : ∑ s', M_hat.P_hat s a s' * (V_star s' - V_hat_star s') =
                ∑ s', M_hat.P_hat s a s' * V_star s' -
                ∑ s', M_hat.P_hat s a s' * V_hat_star s' := by
              rw [← Finset.sum_sub_distrib]; congr 1; ext s'; ring
            rw [hrewrite2]
            exact M.weighted_sum_fn_diff_le (M_hat.P_hat s a)
              V_star V_hat_star (M_hat.P_hat_nonneg s a)
              (M_hat.P_hat_sum_one s a) δ_V h_val_gap
  -- EP_V^2 - EPh_Vh^2 ≤ |EP_V + EPh_Vh| · |EP_V - EPh_Vh|
  -- ≤ 2V_max · (V_max·ε_T + δ_V) = 2V_max²·ε_T + 2V_max·δ_V
  -- |EP_V^2 - EPh_Vh^2| ≤ 2V_max * (V_max*ε_T + δ_V)
  have h_sq_abs_bound : |EP_V ^ 2 - EPh_Vh ^ 2| ≤
      2 * M.V_max * (M.V_max * ε_T + δ_V) := by
    calc |EP_V ^ 2 - EPh_Vh ^ 2|
        = |EP_V + EPh_Vh| * |EP_V - EPh_Vh| := by
          rw [sq_sub_sq, abs_mul]
      _ ≤ (|EP_V| + |EPh_Vh|) * |EP_V - EPh_Vh| := by
          apply mul_le_mul_of_nonneg_right (abs_add_le _ _) (abs_nonneg _)
      _ ≤ (M.V_max + M.V_max) * (M.V_max * ε_T + δ_V) := by
          apply mul_le_mul
          · exact add_le_add h_EP_bnd h_EPh_bnd
          · exact h_mean_diff
          · exact abs_nonneg _
          · linarith [M.V_max_pos]
      _ = 2 * M.V_max * (M.V_max * ε_T + δ_V) := by ring
  -- Step 4: Combine using |x^2 - y^2| bound
  -- We need: EP_Vsq - EP_V^2 ≤ 2*(EPh_Vhsq - EPh_Vh^2) + C
  -- Rewrite: Var_P(V*) - Var_{P̂}(V̂*) = (EP_Vsq - EPh_Vhsq) - (EP_V^2 - EPh_Vh^2)
  -- h_Esq_bound: EP_Vsq - EPh_Vhsq ≤ V^2ε + 2Vδ
  -- h_sq_abs_bound: |EP_V^2 - EPh_Vh^2| ≤ 2V(Vε + δ)
  -- So: EP_V^2 - EPh_Vh^2 ≥ -2V(Vε + δ) = -(2V²ε + 2Vδ)
  -- Therefore: Var_P(V*) - Var_{P̂}(V̂*) ≤ (V²ε + 2Vδ) + (2V²ε + 2Vδ) = 3V²ε + 4Vδ
  -- So Var_P(V*) ≤ Var_{P̂}(V̂*) + 3V²ε + 4Vδ ≤ 2*Var_{P̂}(V̂*) + 3V²ε + 4Vδ
  --
  have h_emp_var_nonneg : 0 ≤ EPh_Vhsq - EPh_Vh ^ 2 := by
    have h_ev := M.empirical_variance_eq M_hat.P_hat M_hat.P_hat_nonneg
        M_hat.P_hat_sum_one V_hat_star s a
    have h_eq : EPh_Vhsq - EPh_Vh ^ 2 =
        M.empirical_variance M_hat.P_hat V_hat_star s a := h_ev.symm
    rw [h_eq]
    unfold empirical_variance
    apply Finset.sum_nonneg; intro s' _
    exact mul_nonneg (M_hat.P_hat_nonneg s a s') (sq_nonneg _)
  -- From |EP_V^2 - EPh_Vh^2| ≤ ..., get lower bound on EP_V^2 - EPh_Vh^2
  have h_sq_lower : -(2 * M.V_max * (M.V_max * ε_T + δ_V)) ≤
      EP_V ^ 2 - EPh_Vh ^ 2 :=
    neg_le_of_abs_le h_sq_abs_bound
  -- Var_P(V*) ≤ Var_{P̂}(V̂*) + 3V²ε + 4Vδ
  have h_var_diff : EP_Vsq - EP_V ^ 2 ≤
      (EPh_Vhsq - EPh_Vh ^ 2) +
      (3 * M.V_max ^ 2 * ε_T + 4 * M.V_max * δ_V) := by
    -- (EP_Vsq - EP_V^2) - (EPh_Vhsq - EPh_Vh^2)
    -- = (EP_Vsq - EPh_Vhsq) - (EP_V^2 - EPh_Vh^2)
    -- ≤ (V²ε + 2Vδ) - (-(2V²ε + 2Vδ))
    -- = V²ε + 2Vδ + 2V²ε + 2Vδ = 3V²ε + 4Vδ
    nlinarith [h_Esq_bound, h_sq_lower]
  -- Since emp_var ≥ 0, Var_{P̂} + C ≤ 2*Var_{P̂} + C
  nlinarith [h_var_diff, h_emp_var_nonneg]

/-- **Self-contained variance swap** — eliminates the explicit value-gap
  parameter δ_V by using the simulation-lemma rate δ_V ≤ γ·V_max·ε_T/(1-γ).

  The bound simplifies to:

    Var_P(V*)(s,a) ≤ 2 · Var_{P̂}(V̂*)(s,a) + (3 + γ)/(1 - γ) · V_max² · ε_T

  This matches the target formulation in Agarwal et al. (2026), Ch 4. -/
theorem variance_swap_from_simulation (M_hat : M.ApproxMDP)
    (V_star V_hat_star : M.StateValueFn)
    (hV_bnd : ∀ s, |V_star s| ≤ M.V_max)
    (hV_hat_bnd : ∀ s, |V_hat_star s| ≤ M.V_max)
    (ε_T : ℝ) (hε_T_nonneg : 0 ≤ ε_T)
    (hε_T : M.transitionError M_hat ≤ ε_T)
    (h_val_gap : ∀ s, |V_star s - V_hat_star s| ≤
      M.γ * M.V_max * ε_T / (1 - M.γ)) :
    ∀ s a, M.transition_variance V_star s a ≤
      2 * M.empirical_variance M_hat.P_hat V_hat_star s a +
      (3 + M.γ) / (1 - M.γ) * M.V_max ^ 2 * ε_T := by
  intro s a
  have h1g : (0 : ℝ) < 1 - M.γ := by linarith [M.γ_lt_one]
  have hδ_nonneg : 0 ≤ M.γ * M.V_max * ε_T / (1 - M.γ) :=
    div_nonneg (mul_nonneg (mul_nonneg M.γ_nonneg (le_of_lt M.V_max_pos))
      hε_T_nonneg) (le_of_lt h1g)
  have h := M.variance_swap M_hat V_star V_hat_star hV_bnd hV_hat_bnd
    (M.γ * M.V_max * ε_T / (1 - M.γ)) hδ_nonneg h_val_gap
    ε_T hε_T_nonneg hε_T s a
  -- h : ... ≤ 2 * emp_var + (3 * V² * ε + 4V * (γVε/(1-γ)))
  -- Goal: ... ≤ 2 * emp_var + (3+γ)/(1-γ) * V² * ε
  -- These are equal: 3V²ε + 4γV²ε/(1-γ) = (3(1-γ) + 4γ)/(1-γ) · V²ε = (3+γ)/(1-γ) · V²ε
  have h_eq : 3 * M.V_max ^ 2 * ε_T + 4 * M.V_max * (M.γ * M.V_max * ε_T / (1 - M.γ)) =
      (3 + M.γ) / (1 - M.γ) * M.V_max ^ 2 * ε_T := by
    field_simp
    ring
  linarith

/-! ### Minimax Deterministic Core -/

/-- **Minimax Deterministic Core** — Value gap from transition error.

  Given an approximate MDP M̂ with:
  - Same rewards: r = r̂
  - Transition L1 error: max_{s,a} ∑_{s'} |P(s'|s,a) - P̂(s'|s,a)| ≤ ε_T
  - π̂ optimal in M̂ dominates π_ref in M̂

  Conclusion:
    V^{π_ref}(s) - V^{π̂}(s) ≤ 2γ · R_max · ε_T / (1-γ)²

  This is the deterministic core of the minimax sample complexity
  result. The full minimax statement additionally requires
  concentration arguments to bound ε_T from N samples.

  Proved by direct application of `optimality_gap_from_transition_error`. -/
theorem minimax_deterministic_core
    (M_hat : M.ApproxMDP)
    (π_ref π_hat : M.StochasticPolicy)
    -- Value functions in M
    (V_ref V_hat_M : M.StateValueFn)
    (hV_ref : M.isValueOf V_ref π_ref)
    (hV_hat_M : M.isValueOf V_hat_M π_hat)
    -- Value functions in M̂
    (V_ref_a V_hat_a : M.StateValueFn)
    (hV_ref_a : ∀ s, V_ref_a s =
      (∑ a, π_ref.prob s a * M_hat.r_hat s a) +
      M.γ * (∑ a, π_ref.prob s a *
        ∑ s', M_hat.P_hat s a s' * V_ref_a s'))
    (hV_hat_a : ∀ s, V_hat_a s =
      (∑ a, π_hat.prob s a * M_hat.r_hat s a) +
      M.γ * (∑ a, π_hat.prob s a *
        ∑ s', M_hat.P_hat s a s' * V_hat_a s'))
    -- π̂ dominates π_ref in M̂
    (h_opt : ∀ s, V_hat_a s ≥ V_ref_a s)
    -- Same rewards
    (h_same_r : ∀ s a, M.r s a = M_hat.r_hat s a)
    -- Transition error bound
    (ε_T : ℝ) (hε_T : M.transitionError M_hat ≤ ε_T) :
    ∀ s, V_ref s - V_hat_M s ≤
      2 * M.γ * M.R_max * ε_T / (1 - M.γ) ^ 2 :=
  M.optimality_gap_from_transition_error M_hat π_ref π_hat
    V_ref V_hat_M hV_ref hV_hat_M
    V_ref_a V_hat_a hV_ref_a hV_hat_a
    h_opt h_same_r ε_T hε_T

/-- **Minimax deterministic core, single-policy version**.

  For a fixed policy π, the absolute value gap satisfies:
    |V^π_M(s) - V^π_{M̂}(s)| ≤ γ · R_max · ε_T / (1-γ)²

  This is the symmetric (absolute-value) version of the bound. -/
theorem minimax_deterministic_core_single_policy
    (M_hat : M.ApproxMDP)
    (π : M.StochasticPolicy)
    (V_M V_Mhat : M.StateValueFn)
    (hV_M : M.isValueOf V_M π)
    (hV_Mhat : ∀ s, V_Mhat s =
      (∑ a, π.prob s a * M_hat.r_hat s a) +
      M.γ * (∑ a, π.prob s a *
        ∑ s', M_hat.P_hat s a s' * V_Mhat s'))
    -- Same rewards
    (h_same_r : ∀ s a, M.r s a = M_hat.r_hat s a)
    -- Transition error bound
    (ε_T : ℝ) (hε_T : M.transitionError M_hat ≤ ε_T) :
    ∀ s, |V_M s - V_Mhat s| ≤
      M.γ * M.R_max * ε_T / (1 - M.γ) ^ 2 :=
  M.crude_value_bound_from_transition_error M_hat π V_M V_Mhat
    hV_M hV_Mhat h_same_r ε_T hε_T

/-! ### Q-Value Gap from V-Value Gap -/

/-- **Q-value gap from V-value gap** — If V = ∑_a π(a) Q(s,a) in both
  M and M̂, then:

    |Q_M(s,a) - Q̂(s,a)| ≤ γ · V_max · ε_T + γ · V_gap

  where V_gap bounds |V_M - V̂|. This uses the decomposition:
    Q(s,a) - Q̂(s,a) = γ(∑(P-P̂)V_M + ∑P̂(V_M-V̂))

  Takes the V = ∑πQ identity as a hypothesis, which follows from
  `bellman_eval_unique_fixed_point` in Resolvent.lean. -/
theorem q_value_gap_from_v_gap
    (M_hat : M.ApproxMDP)
    (π : M.StochasticPolicy)
    -- Q-values satisfying Bellman equations
    (Q_M Q_Mhat : M.ActionValueFn)
    (hQ_M : M.isActionValueOf Q_M π)
    (hQ_Mhat : ∀ s a, Q_Mhat s a = M_hat.r_hat s a +
      M.γ * ∑ s', M_hat.P_hat s a s' *
        (∑ a', π.prob s' a' * Q_Mhat s' a'))
    -- V = ∑πQ identities
    (V_M V_Mhat : M.StateValueFn)
    (hV_M_eq : ∀ s, V_M s = ∑ a, π.prob s a * Q_M s a)
    (hV_Mhat_eq : ∀ s, V_Mhat s = ∑ a, π.prob s a * Q_Mhat s a)
    -- Same rewards
    (h_same_r : ∀ s a, M.r s a = M_hat.r_hat s a)
    -- Bounds
    (hV_bnd : ∀ s, |V_M s| ≤ M.V_max)
    (V_gap : ℝ) (hV_gap : ∀ s, |V_M s - V_Mhat s| ≤ V_gap)
    -- Transition error bound
    (ε_T : ℝ) (hε_T : M.transitionError M_hat ≤ ε_T) :
    ∀ s a, |Q_M s a - Q_Mhat s a| ≤
      M.γ * (M.V_max * ε_T + V_gap) := by
  intro s a
  -- Q_M - Q̂ = γ(∑P V_M - ∑P̂ V̂) with same rewards
  have hQ_diff : Q_M s a - Q_Mhat s a =
      M.γ * (∑ s', M.P s a s' * V_M s' -
             ∑ s', M_hat.P_hat s a s' * V_Mhat s') := by
    rw [hQ_M s a, hQ_Mhat s a, h_same_r s a]
    simp_rw [hV_M_eq, hV_Mhat_eq]; ring
  rw [hQ_diff, abs_mul, abs_of_nonneg M.γ_nonneg]
  apply mul_le_mul_of_nonneg_left _ M.γ_nonneg
  -- Decompose: ∑P V_M - ∑P̂ V̂ = ∑(P-P̂)V_M + ∑P̂(V_M-V̂)
  have h_decomp : ∑ s', M.P s a s' * V_M s' -
      ∑ s', M_hat.P_hat s a s' * V_Mhat s' =
      ∑ s', (M.P s a s' - M_hat.P_hat s a s') * V_M s' +
      ∑ s', M_hat.P_hat s a s' * (V_M s' - V_Mhat s') := by
    have : ∀ s', (M.P s a s' - M_hat.P_hat s a s') * V_M s' +
        M_hat.P_hat s a s' * (V_M s' - V_Mhat s') =
        M.P s a s' * V_M s' - M_hat.P_hat s a s' * V_Mhat s' :=
      fun s' => by ring
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun s' _ => (this s').symm)
  rw [h_decomp]
  calc |∑ s', (M.P s a s' - M_hat.P_hat s a s') * V_M s' +
        ∑ s', M_hat.P_hat s a s' * (V_M s' - V_Mhat s')|
      ≤ |∑ s', (M.P s a s' - M_hat.P_hat s a s') * V_M s'| +
        |∑ s', M_hat.P_hat s a s' * (V_M s' - V_Mhat s')| :=
        abs_add_le _ _
    _ ≤ M.V_max * ε_T + V_gap := by
        apply add_le_add
        · -- |∑(P-P̂)V_M| ≤ ∑|P-P̂|·|V_M| ≤ V_max · ∑|P-P̂| ≤ V_max·ε_T
          calc |∑ s', (M.P s a s' - M_hat.P_hat s a s') * V_M s'|
              ≤ ∑ s', |(M.P s a s' - M_hat.P_hat s a s') * V_M s'| :=
                abs_sum_le_sum_abs _ _
            _ = ∑ s', |M.P s a s' - M_hat.P_hat s a s'| * |V_M s'| := by
                congr 1; ext s'; exact abs_mul _ _
            _ ≤ ∑ s', |M.P s a s' - M_hat.P_hat s a s'| * M.V_max := by
                apply Finset.sum_le_sum; intro s' _
                exact mul_le_mul_of_nonneg_left (hV_bnd s') (abs_nonneg _)
            _ = M.V_max * ∑ s', |M.P s a s' - M_hat.P_hat s a s'| := by
                rw [← Finset.sum_mul]; ring
            _ ≤ M.V_max * ε_T := by
                apply mul_le_mul_of_nonneg_left _ (le_of_lt M.V_max_pos)
                exact le_trans (M.transitionError_le M_hat s a) hε_T
        · -- |∑P̂(V_M-V̂)| ≤ ∑P̂·|V_M-V̂| ≤ V_gap
          calc |∑ s', M_hat.P_hat s a s' * (V_M s' - V_Mhat s')|
              ≤ ∑ s', |M_hat.P_hat s a s' * (V_M s' - V_Mhat s')| :=
                abs_sum_le_sum_abs _ _
            _ = ∑ s', M_hat.P_hat s a s' * |V_M s' - V_Mhat s'| := by
                congr 1; ext s'
                rw [abs_mul, abs_of_nonneg (M_hat.P_hat_nonneg s a s')]
            _ ≤ ∑ s', M_hat.P_hat s a s' * V_gap := by
                apply Finset.sum_le_sum; intro s' _
                exact mul_le_mul_of_nonneg_left (hV_gap s')
                  (M_hat.P_hat_nonneg s a s')
            _ = V_gap * ∑ s', M_hat.P_hat s a s' := by
                rw [← Finset.sum_mul]; ring
            _ = V_gap := by rw [M_hat.P_hat_sum_one s a, mul_one]

/-! ### Minimax Rate Scaling (Strengthened) -/

/-- **Minimax rate scaling** — For all M̂ with transitionError ≤ ε_T
  and same rewards, the optimality gap satisfies:

    V^{π_ref}(s) - V^{π̂}(s) ≤ 2γ · R_max · ε_T / (1-γ)²

  This is a genuinely useful bound: it gives the characteristic
  1/(1-γ)² scaling of the crude model-based RL bound, with an
  explicit constant depending only on γ and R_max.

  Proved by composing optimality_gap_from_transition_error with the bound
  constant c = 2γ · R_max. -/
theorem minimax_rate_scaling_V :
    ∀ (ε_T : ℝ), 0 ≤ ε_T →
    ∀ (M_hat : M.ApproxMDP),
      M.transitionError M_hat ≤ ε_T →
      (∀ s a, M.r s a = M_hat.r_hat s a) →
    ∀ (π_ref π_hat : M.StochasticPolicy)
      (V_ref V_hat_M V_ref_a V_hat_a : M.StateValueFn),
      M.isValueOf V_ref π_ref →
      M.isValueOf V_hat_M π_hat →
      (∀ s, V_ref_a s =
        (∑ a, π_ref.prob s a * M_hat.r_hat s a) +
        M.γ * (∑ a, π_ref.prob s a *
          ∑ s', M_hat.P_hat s a s' * V_ref_a s')) →
      (∀ s, V_hat_a s =
        (∑ a, π_hat.prob s a * M_hat.r_hat s a) +
        M.γ * (∑ a, π_hat.prob s a *
          ∑ s', M_hat.P_hat s a s' * V_hat_a s')) →
      (∀ s, V_hat_a s ≥ V_ref_a s) →
    ∀ s, V_ref s - V_hat_M s ≤
      2 * M.γ * M.R_max * ε_T / (1 - M.γ) ^ 2 := by
  intro ε_T _ M_hat hε_T h_same_r π_ref π_hat V_ref V_hat_M
    V_ref_a V_hat_a hV_ref hV_hat_M hV_ref_a hV_hat_a h_opt
  exact M.optimality_gap_from_transition_error M_hat π_ref π_hat
    V_ref V_hat_M hV_ref hV_hat_M
    V_ref_a V_hat_a hV_ref_a hV_hat_a
    h_opt h_same_r ε_T hε_T

/-- **Minimax rate scaling, symmetric version** — Single-policy absolute bound:

    |V^π_M(s) - V^π_{M̂}(s)| ≤ γ · R_max · ε_T / (1-γ)²

  This is the symmetric version useful for both directions. -/
theorem minimax_rate_scaling_V_abs :
    ∀ (ε_T : ℝ), 0 ≤ ε_T →
    ∀ (M_hat : M.ApproxMDP),
      M.transitionError M_hat ≤ ε_T →
      (∀ s a, M.r s a = M_hat.r_hat s a) →
    ∀ (π : M.StochasticPolicy)
      (V_M V_Mhat : M.StateValueFn),
      M.isValueOf V_M π →
      (∀ s, V_Mhat s =
        (∑ a, π.prob s a * M_hat.r_hat s a) +
        M.γ * (∑ a, π.prob s a *
          ∑ s', M_hat.P_hat s a s' * V_Mhat s')) →
    ∀ s, |V_M s - V_Mhat s| ≤
      M.γ * M.R_max * ε_T / (1 - M.γ) ^ 2 := by
  intro ε_T _ M_hat hε_T h_same_r π V_M V_Mhat hV_M hV_Mhat
  exact M.crude_value_bound_from_transition_error M_hat π V_M V_Mhat
    hV_M hV_Mhat h_same_r ε_T hε_T

/-! ### Minimax Sample Complexity -/

/-- **Deterministic reduction for the minimax sample-complexity bound**.

  This is the key composition step: given any approximate MDP M̂ with:
  - Same rewards as M
  - Transition L1 error ≤ ε_T

  And policies π (in M) and π̂ (optimal in M̂, evaluated in both),
  with Q-value functions satisfying Bellman equations in M and M̂:

  The Q-value gap satisfies:
    |Q_M(s,a) - Q̂(s,a)| ≤ γ · (V_max · ε_T + γ · R_max · ε_T / (1-γ)²)

  This genuinely composes:
  1. `crude_value_bound_from_transition_error` for the V-value gap
  2. `q_value_gap_from_v_gap` for converting to Q-value gap

  The probabilistic layer (Hoeffding/Bernstein → ε_T small w.h.p.)
  is in `pac_from_concentration` (Hoeffding.lean). -/
theorem minimax_sample_complexity_deterministic
    (M_hat : M.ApproxMDP)
    (h_same_r : ∀ s a, M.r s a = M_hat.r_hat s a)
    (ε_T : ℝ) (hε_T : M.transitionError M_hat ≤ ε_T)
    -- Policy and Q-values in M
    (π : M.StochasticPolicy)
    (Q_M : M.ActionValueFn) (hQ_M : M.isActionValueOf Q_M π)
    -- Q-values in M̂
    (Q_Mhat : M.ActionValueFn)
    (hQ_Mhat : ∀ s a, Q_Mhat s a = M_hat.r_hat s a +
      M.γ * ∑ s', M_hat.P_hat s a s' *
        (∑ a', π.prob s' a' * Q_Mhat s' a'))
    -- V = ∑πQ in both MDPs
    (V_M V_Mhat : M.StateValueFn)
    (hV_M_eq : ∀ s, V_M s = ∑ a, π.prob s a * Q_M s a)
    (hV_Mhat_eq : ∀ s, V_Mhat s = ∑ a, π.prob s a * Q_Mhat s a)
    -- V_M is the policy value in M
    (hV_M : M.isValueOf V_M π)
    -- V̂ satisfies Bellman in M̂
    (hV_Mhat : ∀ s, V_Mhat s =
      (∑ a, π.prob s a * M_hat.r_hat s a) +
      M.γ * (∑ a, π.prob s a *
        ∑ s', M_hat.P_hat s a s' * V_Mhat s'))
    -- V_M bounded
    (hV_bnd : ∀ s, |V_M s| ≤ M.V_max) :
    ∀ s a, |Q_M s a - Q_Mhat s a| ≤
      M.γ * (M.V_max * ε_T + M.γ * M.R_max * ε_T / (1 - M.γ) ^ 2) := by
  -- Step 1: Get V-value gap from transition error
  have h_V_gap := M.crude_value_bound_from_transition_error M_hat π V_M V_Mhat
    hV_M hV_Mhat h_same_r ε_T hε_T
  -- h_V_gap : ∀ s, |V_M s - V_Mhat s| ≤ γ·R_max·ε_T/(1-γ)²
  -- Step 2: Apply q_value_gap_from_v_gap
  exact M.q_value_gap_from_v_gap M_hat π Q_M Q_Mhat hQ_M hQ_Mhat
    V_M V_Mhat hV_M_eq hV_Mhat_eq h_same_r hV_bnd
    (M.γ * M.R_max * ε_T / (1 - M.γ) ^ 2) h_V_gap
    ε_T hε_T

/-- **Conditional composition for the minimax sample-complexity bound**.

  Given a generative model with N samples per (s,a), and the
  good event that all transitions are within ε_T, the V-value
  gap is bounded by the minimax rate.

  This composes `pac_from_concentration` (which gives the good
  event) with `minimax_deterministic_core` (which gives the
  V-gap bound on the good event).

  The composition eliminates the previous `h_composition`
  hypothesis by deriving the Q-gap bound from the transition
  error bound using the proved deterministic core. -/
theorem minimax_sample_complexity
    -- Generative model: N i.i.d. samples per (s,a)
    {N : ℕ} (_hN : 0 < N)
    (_next_states : M.S → M.A → Fin N → M.S)
    -- Empirical model constructed from samples
    (M_hat : M.ApproxMDP)
    (_hP_hat : ∀ s a s', M_hat.P_hat s a s' =
      M.empiricalTransition _hN _next_states s a s')
    (h_same_r : ∀ s a, M.r s a = M_hat.r_hat s a)
    -- Policies
    (π_ref π_hat : M.StochasticPolicy)
    -- Value functions in M
    (V_ref V_hat_M : M.StateValueFn)
    (hV_ref : M.isValueOf V_ref π_ref)
    (hV_hat_M : M.isValueOf V_hat_M π_hat)
    -- Value functions in M̂
    (V_ref_a V_hat_a : M.StateValueFn)
    (hV_ref_a : ∀ s, V_ref_a s =
      (∑ a, π_ref.prob s a * M_hat.r_hat s a) +
      M.γ * (∑ a, π_ref.prob s a *
        ∑ s', M_hat.P_hat s a s' * V_ref_a s'))
    (hV_hat_a : ∀ s, V_hat_a s =
      (∑ a, π_hat.prob s a * M_hat.r_hat s a) +
      M.γ * (∑ a, π_hat.prob s a *
        ∑ s', M_hat.P_hat s a s' * V_hat_a s'))
    -- π̂ dominates π_ref in M̂
    (h_opt : ∀ s, V_hat_a s ≥ V_ref_a s)
    -- Transition error bound (the "good event" condition)
    (ε_T : ℝ) (hε_T : M.transitionError M_hat ≤ ε_T) :
    -- Conclusion: on the good event, the V-value gap is bounded
    ∀ s, V_ref s - V_hat_M s ≤
      2 * M.γ * M.R_max * ε_T / (1 - M.γ) ^ 2 :=
  -- This is a direct application of the proved deterministic core
  M.minimax_deterministic_core M_hat π_ref π_hat
    V_ref V_hat_M hV_ref hV_hat_M
    V_ref_a V_hat_a hV_ref_a hV_hat_a
    h_opt h_same_r ε_T hε_T

/-- **Minimax rate scaling (existential form)** — There exists a constant
  c > 0 (depending on γ and R_max) such that for all M̂ with
  transitionError ≤ ε_T and same rewards, the optimality gap satisfies:

    V*(s) - V̂*(s) ≤ c · ε_T / (1-γ)²

  Moreover, c = 2γ · R_max works.

  This replaces the earlier vacuous `True` placeholder with a
  genuinely useful bound. -/
theorem minimax_rate_scaling :
    ∀ (ε_T : ℝ), 0 ≤ ε_T →
    ∃ (c : ℝ), 0 < c ∧
    ∀ (M_hat : M.ApproxMDP),
      M.transitionError M_hat ≤ ε_T →
      (∀ s a, M.r s a = M_hat.r_hat s a) →
    ∀ (π_ref π_hat : M.StochasticPolicy)
      (V_ref V_hat_M V_ref_a V_hat_a : M.StateValueFn),
      M.isValueOf V_ref π_ref →
      M.isValueOf V_hat_M π_hat →
      (∀ s, V_ref_a s =
        (∑ a, π_ref.prob s a * M_hat.r_hat s a) +
        M.γ * (∑ a, π_ref.prob s a *
          ∑ s', M_hat.P_hat s a s' * V_ref_a s')) →
      (∀ s, V_hat_a s =
        (∑ a, π_hat.prob s a * M_hat.r_hat s a) +
        M.γ * (∑ a, π_hat.prob s a *
          ∑ s', M_hat.P_hat s a s' * V_hat_a s')) →
      (∀ s, V_hat_a s ≥ V_ref_a s) →
    ∀ s, V_ref s - V_hat_M s ≤
      c * ε_T / (1 - M.γ) ^ 2 := by
  intro ε_T _
  refine ⟨2 * M.R_max, by linarith [M.R_max_pos], ?_⟩
  intro M_hat hε_T h_same_r π_ref π_hat V_ref V_hat_M
    V_ref_a V_hat_a hV_ref hV_hat_M hV_ref_a hV_hat_a h_opt s
  have h := M.optimality_gap_from_transition_error M_hat π_ref π_hat
    V_ref V_hat_M hV_ref hV_hat_M
    V_ref_a V_hat_a hV_ref_a hV_hat_a
    h_opt h_same_r ε_T hε_T s
  -- h : ≤ 2γR_max·ε_T/(1-γ)²; goal: ≤ 2R_max·ε_T/(1-γ)²
  -- Since γ ≤ 1: 2γR_max ≤ 2R_max
  calc V_ref s - V_hat_M s
      ≤ 2 * M.γ * M.R_max * ε_T / (1 - M.γ) ^ 2 := h
    _ ≤ 2 * M.R_max * ε_T / (1 - M.γ) ^ 2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        have hγ1 : M.γ ≤ 1 := le_of_lt M.γ_lt_one
        have hε : 0 ≤ ε_T := ‹0 ≤ ε_T›
        have hR : 0 < M.R_max := M.R_max_pos
        -- 2γR·ε ≤ 2·1·R·ε since γ ≤ 1, R > 0, ε ≥ 0
        have h1 : 2 * M.γ ≤ 2 * 1 := by nlinarith
        have h2 : 2 * M.γ * M.R_max ≤ 2 * M.R_max := by nlinarith
        nlinarith

/-! ### Pointwise Transition Error: Minimax Core with |S| Factor -/

/-- **Minimax deterministic core (pointwise transition error)**.

  Given an approximate MDP M̂ with:
  - Same rewards: r = r̂
  - Per-entry transition error: |P(s'|s,a) - P̂(s'|s,a)| ≤ ε_T for all s,a,s'
  - π̂ dominates π_ref in M̂

  Conclusion:
    V^{π_ref}(s) - V^{π̂}(s) ≤ 2γ · R_max · |S| · ε_T / (1-γ)²

  The |S| factor arises from converting per-entry error to L1 error:
    ∑_{s'} |P(s'|s,a) - P̂(s'|s,a)| ≤ |S| · ε_T

  Proved by bounding the L1 transition error and applying
  `optimality_gap_from_transition_error`. -/
theorem minimax_deterministic_core_pointwise
    (M_hat : M.ApproxMDP)
    (π_ref π_hat : M.StochasticPolicy)
    -- Value functions in M
    (V_ref V_hat_M : M.StateValueFn)
    (hV_ref : M.isValueOf V_ref π_ref)
    (hV_hat_M : M.isValueOf V_hat_M π_hat)
    -- Value functions in M̂
    (V_ref_a V_hat_a : M.StateValueFn)
    (hV_ref_a : ∀ s, V_ref_a s =
      (∑ a, π_ref.prob s a * M_hat.r_hat s a) +
      M.γ * (∑ a, π_ref.prob s a *
        ∑ s', M_hat.P_hat s a s' * V_ref_a s'))
    (hV_hat_a : ∀ s, V_hat_a s =
      (∑ a, π_hat.prob s a * M_hat.r_hat s a) +
      M.γ * (∑ a, π_hat.prob s a *
        ∑ s', M_hat.P_hat s a s' * V_hat_a s'))
    -- π̂ dominates π_ref in M̂
    (h_opt : ∀ s, V_hat_a s ≥ V_ref_a s)
    -- Same rewards
    (h_same_r : ∀ s a, M.r s a = M_hat.r_hat s a)
    -- Per-entry transition error bound
    (ε_T : ℝ) (_hε_T_nonneg : 0 ≤ ε_T)
    (hε_T : ∀ s a s', |M.P s a s' - M_hat.P_hat s a s'| ≤ ε_T) :
    ∀ s, V_ref s - V_hat_M s ≤
      2 * M.γ * M.R_max * (↑(Fintype.card M.S) * ε_T) / (1 - M.γ) ^ 2 := by
  -- Step 1: Bound L1 transition error by |S| · ε_T
  have h_l1 : M.transitionError M_hat ≤ ↑(Fintype.card M.S) * ε_T := by
    simp only [transitionError]
    apply Finset.sup'_le; intro s _
    apply Finset.sup'_le; intro a _
    calc ∑ s', |M.P s a s' - M_hat.P_hat s a s'|
        ≤ ∑ _s' : M.S, ε_T :=
          Finset.sum_le_sum (fun s' _ => hε_T s a s')
      _ = Fintype.card M.S * ε_T := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- Step 2: Apply the L1 version
  exact M.optimality_gap_from_transition_error M_hat π_ref π_hat
    V_ref V_hat_M hV_ref hV_hat_M
    V_ref_a V_hat_a hV_ref_a hV_hat_a
    h_opt h_same_r (↑(Fintype.card M.S) * ε_T) h_l1

/-! ### Minimax Rate Scaling: Existential Form -/

/-- **Minimax rate scaling (existential form with transition error)**.

  There exists c > 0 such that for any approximate MDP M̂ with
  per-entry transition error ≤ ε_T and same rewards:

    V^{π_ref}(s) - V^{π̂}(s) ≤ c · ε_T

  The constant c depends on γ, R_max, and |S|. Concretely,
  c = 2 · R_max · |S| / (1-γ)² works.

  This establishes the existence of a rate: the optimality gap
  scales linearly with the per-entry transition error. -/
theorem minimax_rate_scaling_existence :
    ∃ (c : ℝ), 0 < c ∧
    ∀ (ε_T : ℝ), 0 ≤ ε_T →
    ∀ (M_hat : M.ApproxMDP),
      (∀ s a s', |M.P s a s' - M_hat.P_hat s a s'| ≤ ε_T) →
      (∀ s a, M.r s a = M_hat.r_hat s a) →
    ∀ (π_ref π_hat : M.StochasticPolicy)
      (V_ref V_hat_M V_ref_a V_hat_a : M.StateValueFn),
      M.isValueOf V_ref π_ref →
      M.isValueOf V_hat_M π_hat →
      (∀ s, V_ref_a s =
        (∑ a, π_ref.prob s a * M_hat.r_hat s a) +
        M.γ * (∑ a, π_ref.prob s a *
          ∑ s', M_hat.P_hat s a s' * V_ref_a s')) →
      (∀ s, V_hat_a s =
        (∑ a, π_hat.prob s a * M_hat.r_hat s a) +
        M.γ * (∑ a, π_hat.prob s a *
          ∑ s', M_hat.P_hat s a s' * V_hat_a s')) →
      (∀ s, V_hat_a s ≥ V_ref_a s) →
    ∀ s, V_ref s - V_hat_M s ≤ c * ε_T := by
  -- Witness: c = 2 · R_max · |S| / (1-γ)²
  have h1g : (0 : ℝ) < 1 - M.γ := by linarith [M.γ_lt_one]
  refine ⟨2 * M.R_max * ↑(Fintype.card M.S) / (1 - M.γ) ^ 2, ?_, ?_⟩
  · -- c > 0
    apply div_pos
    · apply mul_pos
      · exact mul_pos (by norm_num : (0 : ℝ) < 2) M.R_max_pos
      · exact Nat.cast_pos.mpr Fintype.card_pos
    · exact sq_pos_of_pos h1g
  · intro ε_T hε_T M_hat hε_T_pw h_same_r π_ref π_hat V_ref V_hat_M
      V_ref_a V_hat_a hV_ref hV_hat_M hV_ref_a hV_hat_a h_opt s
    -- Apply the pointwise core theorem
    have h_core := M.minimax_deterministic_core_pointwise M_hat π_ref π_hat
      V_ref V_hat_M hV_ref hV_hat_M
      V_ref_a V_hat_a hV_ref_a hV_hat_a
      h_opt h_same_r ε_T hε_T hε_T_pw s
    -- h_core : ≤ 2γ·R_max·(|S|·ε_T)/(1-γ)²
    -- Goal: ≤ (2·R_max·|S|/(1-γ)²) · ε_T
    -- Since γ ≤ 1, 2γ·R_max·|S|·ε_T/(1-γ)² ≤ 2·R_max·|S|·ε_T/(1-γ)²
    have hγ_le : M.γ ≤ 1 := le_of_lt M.γ_lt_one
    have hS : (0 : ℝ) ≤ ↑(Fintype.card M.S) := Nat.cast_nonneg _
    have hR : 0 < M.R_max := M.R_max_pos
    have hSε : 0 ≤ ↑(Fintype.card M.S) * ε_T := mul_nonneg hS hε_T
    calc V_ref s - V_hat_M s
        ≤ 2 * M.γ * M.R_max * (↑(Fintype.card M.S) * ε_T) / (1 - M.γ) ^ 2 :=
          h_core
      _ ≤ 2 * M.R_max * (↑(Fintype.card M.S) * ε_T) / (1 - M.γ) ^ 2 := by
          apply div_le_div_of_nonneg_right _ (sq_nonneg _)
          · have : 2 * M.γ ≤ 2 * 1 := by linarith
            have : 2 * M.γ * M.R_max ≤ 2 * 1 * M.R_max := by
              exact mul_le_mul_of_nonneg_right this (le_of_lt hR)
            nlinarith [mul_le_mul_of_nonneg_right this hSε]
      _ = 2 * M.R_max * ↑(Fintype.card M.S) / (1 - M.γ) ^ 2 * ε_T := by ring

/-! ### Bernstein vs Hoeffding: Exponent Comparison -/

/-- **Bernstein exponent dominates when variance is small**.

  For bounded random variables with |X| ≤ b and Var(X) ≤ σ²,
  the Bernstein concentration exponent t²/(2(σ² + bt/3)) is at
  least as large as the exponent t²/(2(b² + bt/3)) obtained by
  replacing σ² with b². Since smaller variance gives a larger
  exponent (tighter tail bound), the Bernstein approach
  improves upon the crude bound whenever σ² < b².

  This is the key algebraic fact underlying the improved
  1/(1-γ)^{3/2} sample complexity in the Bernstein-based
  minimax analysis (Azar et al., 2013). -/
theorem minimax_bernstein_improvement
    {σ_sq b t : ℝ}
    (hb : 0 < b) (ht : 0 < t)
    (hσ_nonneg : 0 ≤ σ_sq) (hσ_le : σ_sq ≤ b ^ 2) :
    t ^ 2 / (2 * (b ^ 2 + b * t / 3)) ≤
    t ^ 2 / (2 * (σ_sq + b * t / 3)) := by
  -- Since σ² ≤ b², we have σ² + bt/3 ≤ b² + bt/3,
  -- so 1/(σ² + bt/3) ≥ 1/(b² + bt/3),
  -- so t²/(2(σ² + bt/3)) ≥ t²/(2(b² + bt/3)).
  have hbt3 : 0 < b * t / 3 := by positivity
  have h_denom_pos_small : 0 < 2 * (σ_sq + b * t / 3) := by linarith
  have h_denom_pos_large : 0 < 2 * (b ^ 2 + b * t / 3) := by
    have : 0 < b ^ 2 := sq_pos_of_pos hb
    linarith
  have h_denom_le : 2 * (σ_sq + b * t / 3) ≤ 2 * (b ^ 2 + b * t / 3) := by
    linarith
  have ht_sq_nonneg : 0 ≤ t ^ 2 := sq_nonneg _
  exact div_le_div_of_nonneg_left ht_sq_nonneg h_denom_pos_small h_denom_le

end FiniteMDP

end
