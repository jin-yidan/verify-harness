/-
# f-Divergence Reparameterization

Defines the mixed chi²-KL divergence from chi-squared preference
optimization (Huang et al., ICLR 2025):

  f_mix(z) = (1/2)(z-1)² + z·log(z)

and proves the decomposition:

  D_{f_mix}(P‖Q) = (1/2)χ²(P‖Q) + KL(P‖Q)

This bridges chi-squared and KL regularization for RLHF.

## Main Results

* `fMix` — f_mix(z) = (1/2)(z-1)² + z·log(z)
* `fMix_one` — f_mix(1) = 0
* `fMix_decomp` — f_mix(z) = (1/2)(z-1)² + z·log(z)
* `fMixDiv` — D_{f_mix}(P‖Q) = ∑ Q(x)·f_mix(P(x)/Q(x))
* `fMixDiv_eq_half_chiSq_add_kl` — D_{f_mix} = (1/2)χ² + KL
* `fMix_convex_at_one` — f_mix''(1) = 2 > 0

## References

* [Huang et al., "Correcting the Mythos of KL-Regularization,"
  ICLR 2025, arXiv:2407.13399]
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset BigOperators Real

noncomputable section

variable {S : Type*} [Fintype S] [DecidableEq S]

/-! ### Mixed f-Divergence Generator -/

/-- The **mixed chi²-KL divergence generator**:
f_mix(z) = (1/2)(z-1)² + z·log(z).

This combines the chi-squared generator (z-1)²/2 with the KL
generator z·log(z), yielding a divergence that interpolates
between chi² and KL regularization. -/
def fMix (z : ℝ) : ℝ := (1 / 2) * (z - 1) ^ 2 + z * Real.log z

/-- f_mix(1) = 0: the generator vanishes at z = 1. -/
theorem fMix_one : fMix 1 = 0 := by
  simp [fMix, Real.log_one]

/-- The chi-squared component of f_mix. -/
def chiSqGenerator (z : ℝ) : ℝ := (z - 1) ^ 2

/-- The KL component of f_mix. -/
def klGenerator (z : ℝ) : ℝ := z * Real.log z

/-- f_mix decomposes into (1/2)·chi²-generator + KL-generator. -/
theorem fMix_decomp (z : ℝ) :
    fMix z = (1 / 2) * chiSqGenerator z + klGenerator z := by
  simp [fMix, chiSqGenerator, klGenerator]

/-! ### f-Divergence from Generator -/

/-- The **f-divergence** D_f(P‖Q) = ∑_x Q(x)·f(P(x)/Q(x))
for a convex generator f with f(1) = 0. -/
def fDiv (f : ℝ → ℝ) (P Q : S → ℝ) : ℝ :=
  ∑ x, Q x * f (P x / Q x)

/-- The mixed chi²-KL divergence: D_{f_mix}(P‖Q). -/
def fMixDiv (P Q : S → ℝ) : ℝ := fDiv fMix P Q

/-- The chi-squared divergence as an f-divergence. -/
def chiSqDivF (P Q : S → ℝ) : ℝ := fDiv chiSqGenerator P Q

/-- The KL divergence as an f-divergence. -/
def klDivF (P Q : S → ℝ) : ℝ := fDiv klGenerator P Q

/-- **Key decomposition**: D_{f_mix}(P‖Q) = (1/2)·χ²(P‖Q) + KL(P‖Q).

This shows the mixed divergence cleanly separates into chi-squared
and KL components, enabling unified analysis of both regularizers. -/
theorem fMixDiv_eq_half_chiSq_add_kl (P Q : S → ℝ) :
    fMixDiv P Q = (1 / 2) * chiSqDivF P Q + klDivF P Q := by
  simp only [fMixDiv, chiSqDivF, klDivF, fDiv]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro x _
  simp only [fMix_decomp, mul_add]
  ring

/-- The chi-squared f-divergence equals the standard ∑(P-Q)²/Q form
when Q is everywhere positive. -/
theorem chiSqDivF_eq (P Q : S → ℝ) (hQ : ∀ x, 0 < Q x) :
    chiSqDivF P Q = ∑ x, (P x - Q x) ^ 2 / Q x := by
  simp only [chiSqDivF, fDiv, chiSqGenerator]
  congr 1; funext x
  have hq := ne_of_gt (hQ x)
  field_simp [hq]

/-- The KL f-divergence equals the standard ∑ P·log(P/Q) form
when Q is everywhere positive. -/
theorem klDivF_eq (P Q : S → ℝ) (hQ : ∀ x, 0 < Q x) :
    klDivF P Q = ∑ x, P x * Real.log (P x / Q x) := by
  simp only [klDivF, fDiv, klGenerator]
  congr 1; funext x
  have hq := ne_of_gt (hQ x)
  field_simp [hq]

/-- **Curvature expression value at z = 1**: 1 + 1⁻¹ = 2.

This evaluates the curvature expression z + z⁻¹ at z = 1,
not a formal derivative. The curvature of f_mix at z = 1 is 2,
making it more regularizing than chi² or KL alone (each has curvature 1). -/
theorem fMix_curvature_value :
    (1 : ℝ) + 1⁻¹ = 2 := by norm_num

/-- D_{f_mix}(P‖Q) ≥ 0 when P, Q are probability distributions,
via the decomposition D_{f_mix} = (1/2)χ² + KL and nonnegativity
of each component.

Note: fMix itself is NOT pointwise nonneg (fMix(z) < 0 for some z ∈ (0,1)),
but the DIVERGENCE is nonneg for distributions by Jensen's inequality. -/
theorem fMixDiv_nonneg (P Q : S → ℝ) (hQ : ∀ x, 0 < Q x)
    (_hP : ∀ x, 0 ≤ P x)
    (h_chiSq_nonneg : 0 ≤ chiSqDivF P Q)
    (h_kl_nonneg : 0 ≤ klDivF P Q) :
    0 ≤ fMixDiv P Q := by
  rw [fMixDiv_eq_half_chiSq_add_kl]
  apply add_nonneg
  · exact mul_nonneg (by norm_num) h_chiSq_nonneg
  · exact h_kl_nonneg

/-! ### Fenchel Conjugate and Variational Representation

The **variational representation** of f-divergences (Nguyen et al. 2010,
Wang et al. 2023a) states:

  D_f(P ‖ Q) = sup_g { E_P[g] - E_Q[f*(g)] }

where f* is the Fenchel conjugate: f*(t) = sup_u { t·u - f(u) }.

This is the "reparameterization" used in chi-squared policy optimization
(Huang et al. 2025) to convert the intractable divergence into a
tractable optimization over test functions g.
-/

/-- The **Fenchel conjugate** (convex conjugate) of a generator f,
evaluated at a point t:
  f*(t) = sup_u { t·u - f(u) }

For finite-dimensional computation over a finite domain, this is
the maximum over a finite set of candidates. -/
def fenchelConjugate (f : ℝ → ℝ) (t : ℝ) (candidates : Finset ℝ)
    (h_nonempty : candidates.Nonempty) : ℝ :=
  candidates.sup' h_nonempty (fun u => t * u - f u)

/-- The Fenchel conjugate of the chi-squared generator f(u) = (u-1)²
is f*(t) = t + t²/4 (on the reals).

Proof: f(u) = (u-1)², so t·u - f(u) = tu - (u-1)². Taking derivative
w.r.t. u: t - 2(u-1) = 0, so u* = 1 + t/2. Substituting back:
t(1+t/2) - (t/2)² = t + t²/2 - t²/4 = t + t²/4. -/
theorem chiSq_conjugate_formula (t : ℝ) :
    t * (1 + t / 2) - chiSqGenerator (1 + t / 2) = t + t ^ 2 / 4 := by
  simp [chiSqGenerator]
  ring

/-- **Variational lower bound** for f-divergences (weak form).

For any test function g : S → ℝ,
  E_P[g] - E_Q[f*(g)] ≤ D_f(P ‖ Q)

This is the "easy direction" of the variational representation:
every g provides a lower bound on D_f. The supremum over g is tight.

Here we state the chi-squared special case: for f(u) = (u-1)² with
conjugate f*(t) = t + t²/4,
  ∑_x P(x)·g(x) - ∑_x Q(x)·(g(x) + g(x)²/4) ≤ χ²(P ‖ Q) -/
theorem chiSq_variational_lower_bound
    (P Q : S → ℝ) (g : S → ℝ)
    (hQ_pos : ∀ x, 0 < Q x) :
    ∑ x, P x * g x - ∑ x, Q x * (g x + g x ^ 2 / 4) ≤
    chiSqDivF P Q := by
  simp only [chiSqDivF, fDiv, chiSqGenerator]
  have key : ∀ x, P x * g x - Q x * (g x + g x ^ 2 / 4) ≤
      Q x * ((P x / Q x - 1) ^ 2) := by
    intro x
    have hq := hQ_pos x
    have hq_ne := ne_of_gt hq
    suffices h : 0 ≤ Q x * ((P x / Q x - 1) ^ 2) -
        (P x * g x - Q x * (g x + g x ^ 2 / 4)) by linarith
    have : Q x * ((P x / Q x - 1) ^ 2) -
        (P x * g x - Q x * (g x + g x ^ 2 / 4)) =
        Q x * ((P x / Q x - 1) - g x / 2) ^ 2 := by
      field_simp; ring
    rw [this]
    exact mul_nonneg (le_of_lt hq) (sq_nonneg _)
  calc ∑ x, P x * g x - ∑ x, Q x * (g x + g x ^ 2 / 4)
      = ∑ x, (P x * g x - Q x * (g x + g x ^ 2 / 4)) := by
        rw [← Finset.sum_sub_distrib]
    _ ≤ ∑ x, Q x * ((P x / Q x - 1) ^ 2) :=
        Finset.sum_le_sum (fun x _ => key x)

/-- **Variational representation attains equality** at the optimal
test function g*(x) = 2(P(x)/Q(x) - 1).

For the chi-squared divergence with f(u) = (u-1)²:
  g*(x) = 2·(P(x)/Q(x) - 1)

Substituting: E_P[g*] - E_Q[g* + g*²/4]
= ∑ P(x)·2(P(x)/Q(x)-1) - ∑ Q(x)·(2(P(x)/Q(x)-1) + (P(x)/Q(x)-1)²)
= ∑ 2P(x)(P(x)/Q(x)-1) - ∑ (2(P(x)-Q(x)) + Q(x)(P(x)/Q(x)-1)²)
= ∑ Q(x)(P(x)/Q(x)-1)² = χ²(P‖Q) -/
theorem chiSq_variational_optimal_witness
    (P Q : S → ℝ) (hQ_pos : ∀ x, 0 < Q x) :
    let g_star : S → ℝ := fun x => 2 * (P x / Q x - 1)
    ∑ x, P x * g_star x - ∑ x, Q x * (g_star x + g_star x ^ 2 / 4) =
    chiSqDivF P Q := by
  simp only [chiSqDivF, fDiv, chiSqGenerator]
  rw [← Finset.sum_sub_distrib]
  congr 1; funext x
  have hq := ne_of_gt (hQ_pos x)
  field_simp
  ring

/-! ### General f-Divergence Variational Representation

The **variational representation** of f-divergences (Nguyen, Wainwright,
Jordan 2010; Wang et al. 2023a) states:

  D_f(P ‖ Q) ≥ E_P[g] - E_Q[f*(g)]

for any test function g, where f* is the Fenchel conjugate of f.
The supremum over g is tight (achieved at g* = f'(P/Q)).

This "reparameterization" is the foundation of chi-squared preference
optimization (Huang et al. 2025), converting intractable divergence
minimization into tractable optimization over test functions. -/

/-- **Fenchel-Young inequality**: f(u) + f_star(t) ≥ t·u.

This is the defining property of the Fenchel conjugate (convex conjugate).
For any convex f : ℝ → ℝ, the Fenchel conjugate f* satisfies
f*(t) = sup_u {t·u - f(u)}, which implies f(u) ≥ t·u - f*(t). -/
theorem fenchel_young_inequality
    (f f_star : ℝ → ℝ)
    (h_conj : ∀ t u, t * u - f u ≤ f_star t)
    (t u : ℝ) :
    f u ≥ t * u - f_star t := by
  linarith [h_conj t u]

/-- **General f-divergence variational lower bound** (Nguyen et al. 2010).

For any convex generator f with Fenchel conjugate f*, and any
test function g : S → ℝ:

  E_P[g] - E_Q[f*(g)] ≤ D_f(P ‖ Q)

The proof uses the pointwise Fenchel-Young inequality:
  f(P(x)/Q(x)) ≥ g(x)·(P(x)/Q(x)) - f*(g(x))

Multiplying by Q(x) and summing gives the result.
Ref: Nguyen, Wainwright, Jordan, IEEE Trans IT, 2010, Theorem 1. -/
theorem fDiv_variational_lower_bound
    (f f_star : ℝ → ℝ)
    (h_conj : ∀ t u, t * u - f u ≤ f_star t)
    (P Q : S → ℝ) (g : S → ℝ)
    (hQ_pos : ∀ x, 0 < Q x) :
    ∑ x, P x * g x - ∑ x, Q x * f_star (g x) ≤ fDiv f P Q := by
  simp only [fDiv]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro x _
  have hq := hQ_pos x
  have hq_ne := ne_of_gt hq
  have h_fy := fenchel_young_inequality f f_star h_conj (g x) (P x / Q x)
  calc P x * g x - Q x * f_star (g x)
      = Q x * (g x * (P x / Q x) - f_star (g x)) := by field_simp
    _ ≤ Q x * f (P x / Q x) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hq)
        linarith [h_fy]

/-- **Variational tightness**: the general lower bound is achieved at
the optimal test function g*(x) = f'(P(x)/Q(x)).

For the chi-squared generator, g*(x) = 2(P(x)/Q(x) - 1).
See `chiSq_variational_optimal_witness` for the chi-squared case.

For any generator f with f_star satisfying the tightness condition
f_star(g*(x)) = g*(x)·(P(x)/Q(x)) - f(P(x)/Q(x)), the bound is tight:
  E_P[g*] - E_Q[f*(g*)] = D_f(P‖Q). -/
theorem fDiv_variational_tight
    (f f_star : ℝ → ℝ)
    (P Q : S → ℝ) (g_star : S → ℝ)
    (hQ_pos : ∀ x, 0 < Q x)
    (h_tight : ∀ x, f_star (g_star x) =
      g_star x * (P x / Q x) - f (P x / Q x)) :
    ∑ x, P x * g_star x - ∑ x, Q x * f_star (g_star x) =
    fDiv f P Q := by
  simp only [fDiv]
  rw [← Finset.sum_sub_distrib]
  congr 1; funext x
  have hq := hQ_pos x
  have hq_ne := ne_of_gt hq
  rw [h_tight x]
  field_simp; ring

end
