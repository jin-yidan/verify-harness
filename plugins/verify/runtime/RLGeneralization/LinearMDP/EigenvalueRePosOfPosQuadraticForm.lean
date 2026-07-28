import Mathlib

open Matrix Complex Finset

/-- **Positive quadratic form implies every eigenvalue has positive real part.**
If a real square matrix `A` (not necessarily symmetric) has a positive
quadratic form, i.e. `0 < x ⬝ᵥ A *ᵥ x` for every nonzero real vector `x`
(equivalently: the symmetric part of `A` is positive definite), then every
complex eigenvalue `μ` of `A` satisfies `0 < μ.re`.  In other words `-A` is a
Hurwitz matrix.  This is the spectral bridge from positive definite quadratic
forms to Hurwitz stability used in TD(0) / stochastic-approximation
convergence proofs. -/
theorem eigenvalue_re_pos_of_pos_quadratic_form {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (A *ᵥ x))
    (μ : ℂ) (v : Fin n → ℂ) (hv : v ≠ 0)
    (heig : (A.map (algebraMap ℝ ℂ)) *ᵥ v = μ • v) :
    0 < μ.re := by
  -- real and imaginary parts of `v`
  set u : Fin n → ℝ := fun i => (v i).re with hu
  set w : Fin n → ℝ := fun i => (v i).im with hw
  -- the quadratic form is nonnegative on every vector
  have hnn : ∀ x : Fin n → ℝ, 0 ≤ x ⬝ᵥ (A *ᵥ x) := by
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · exact (hA x hx).le
  -- scalar form of the eigenvalue equation
  have heig' : ∀ i, (∑ j, (A i j : ℂ) * v j) = μ * v i := by
    intro i
    have h := congrFun heig i
    simpa [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply,
      smul_eq_mul] using h
  -- multiply by `conj (v i)` and sum over `i`
  have hsum : (∑ i, (starRingEnd ℂ) (v i) * ∑ j, (A i j : ℂ) * v j)
      = μ * ∑ i, (starRingEnd ℂ) (v i) * v i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [heig' i]; ring
  -- the right factor is the (real, nonnegative) squared norm of `v`
  have hT : (∑ i, (starRingEnd ℂ) (v i) * v i)
      = ((∑ i, Complex.normSq (v i) : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm, Complex.mul_conj]
  -- real part of the left-hand side: sum of the two real quadratic forms
  have hre : (∑ i, (starRingEnd ℂ) (v i) * ∑ j, (A i j : ℂ) * v j).re
      = u ⬝ᵥ (A *ᵥ u) + w ⬝ᵥ (A *ᵥ w) := by
    have hterm : ∀ i, ((starRingEnd ℂ) (v i) * ∑ j, (A i j : ℂ) * v j).re
        = u i * (∑ j, A i j * u j) + w i * (∑ j, A i j * w j) := by
      intro i
      have hres : (∑ j, (A i j : ℂ) * v j).re = ∑ j, A i j * u j := by
        rw [Complex.re_sum]
        exact Finset.sum_congr rfl fun j _ => by simp [Complex.mul_re, hu]
      have hims : (∑ j, (A i j : ℂ) * v j).im = ∑ j, A i j * w j := by
        rw [Complex.im_sum]
        exact Finset.sum_congr rfl fun j _ => by simp [Complex.mul_im, hw]
      rw [Complex.mul_re, hres, hims]
      simp only [Complex.conj_re, Complex.conj_im, hu, hw]
      ring
    rw [Complex.re_sum]
    simp only [hterm]
    simp [dotProduct, Matrix.mulVec, Finset.sum_add_distrib]
  -- take real parts in the summed eigenvalue identity
  have hkey : u ⬝ᵥ (A *ᵥ u) + w ⬝ᵥ (A *ᵥ w)
      = μ.re * ∑ i, Complex.normSq (v i) := by
    have h := congrArg Complex.re hsum
    rw [hre, hT] at h
    simpa [Complex.mul_re] using h
  -- positivity of the squared norm of `v`
  have hTpos : 0 < ∑ i, Complex.normSq (v i) := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
    exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _)
      ⟨i, Finset.mem_univ i, Complex.normSq_pos.mpr (by simpa using hi)⟩
  -- the real quadratic forms cannot both vanish since `v ≠ 0`
  have hQpos : 0 < u ⬝ᵥ (A *ᵥ u) + w ⬝ᵥ (A *ᵥ w) := by
    have huw : u ≠ 0 ∨ w ≠ 0 := by
      by_contra h
      push_neg at h
      obtain ⟨hu0, hw0⟩ := h
      apply hv
      funext i
      have h1 : (v i).re = 0 := by simpa [hu] using congrFun hu0 i
      have h2 : (v i).im = 0 := by simpa [hw] using congrFun hw0 i
      exact Complex.ext (by simpa using h1) (by simpa using h2)
    rcases huw with h | h
    · exact add_pos_of_pos_of_nonneg (hA u h) (hnn w)
    · exact add_pos_of_nonneg_of_pos (hnn u) (hA w h)
  -- conclude: `0 < μ.re * T` with `T > 0` forces `0 < μ.re`
  rw [hkey] at hQpos
  by_contra hcon
  push_neg at hcon
  nlinarith [hQpos, hTpos]

-- Anti-vacuity check: the hypotheses are satisfiable, e.g. by `A = 1`, `n = 1`.
example : ∀ x : Fin 1 → ℝ, x ≠ 0 → 0 < x ⬝ᵥ ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ x) := by
  intro x hx
  have h0 : x 0 ≠ 0 := by
    intro h
    apply hx
    funext i
    fin_cases i
    simpa using h
  have hq : x ⬝ᵥ ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ x) = x 0 * x 0 := by
    simp [Matrix.one_mulVec, dotProduct]
  rw [hq]
  exact mul_self_pos.mpr h0

