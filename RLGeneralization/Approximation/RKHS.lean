/-
# Reproducing Kernel Hilbert Spaces (RKHS)

## Status: Stub
Blocked on reproducing kernel Hilbert space construction, which
requires inner product space completions not yet in Mathlib in
the needed form. Contains structures and algebraic properties only.

Formalizes the algebraic structure of reproducing kernel Hilbert spaces:
kernel definitions, the reproducing property, representer theorem,
and kernel ridge regression.

## Mathematical Background

A reproducing kernel Hilbert space (RKHS) H_k on a set X is a Hilbert space
of functions f : X → ℝ equipped with a kernel k : X × X → ℝ satisfying:
1. k(x, ·) ∈ H_k for all x ∈ X   (feature map)
2. f(x) = ⟨f, k(x, ·)⟩_H for all f ∈ H_k  (reproducing property)

The representer theorem shows that the minimizer of a regularized empirical
risk over H_k has a finite expansion: f*(·) = ∑ α_i k(x_i, ·).

## Main Definitions

* `ReproducingKernel` - A positive-definite kernel structure
* `KernelMatrix` - The Gram matrix K_{ij} = k(x_i, x_j)
* `kernelMatrix_symmetric` - K is symmetric
* `regularizedKernelMatrix_symmetric` - K + lambda*I is symmetric
* `RegularizationBias` - Structure encoding bias bound: approx_error <= lambda * rkhs_norm_sq

**Note**: There is no standalone `rkhs_approximation_error` theorem.
The bias bound (approx_error <= lambda * rkhs_norm_sq) is encoded as
a field (`hbias`) of the `RegularizationBias` structure rather than
as a separately proved theorem.

## Approach

We work with finite-dimensional kernel matrices (Gram matrices) on
n data points, avoiding the full functional-analytic construction of
RKHS which requires completion of pre-Hilbert spaces. The algebraic
properties (symmetry, positive definiteness, representer form) are
all expressible in finite dimensions.

## Blocked

- Full RKHS construction (requires Hilbert space completion, not in scope)
- Mercer's theorem (requires spectral theory for compact operators)
- Universal kernel characterization (requires Stone-Weierstrass + topology)

## References

* [Schölkopf and Smola, *Learning with Kernels*][scholkopf2002]
* [Aronszajn, *Theory of Reproducing Kernels*, 1950][aronszajn1950]
* [Shalev-Shwartz and Ben-David, *Understanding Machine Learning*][shalev2014]
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open Finset BigOperators Matrix

noncomputable section

/-! ### Kernel Definition -/

/-- **Reproducing kernel**: a symmetric positive-definite kernel
    on a finite input space. We encode the finite-dimensional
    algebraic structure directly.

    A kernel k : X → X → ℝ is:
    - Symmetric: k(x, y) = k(y, x)
    - Positive definite: ∑ᵢⱼ αᵢ αⱼ k(xᵢ, xⱼ) ≥ 0 for all α -/
structure ReproducingKernel (X : Type*) [Fintype X] where
  /-- The kernel function k(x, y) -/
  k : X → X → ℝ
  /-- Symmetry: k(x, y) = k(y, x) -/
  k_symm : ∀ x y, k x y = k y x
  /-- Positive definiteness: ∑ᵢⱼ αᵢ αⱼ k(xᵢ, xⱼ) ≥ 0 -/
  k_pd : ∀ α : X → ℝ, 0 ≤ ∑ x, ∑ y, α x * α y * k x y

namespace ReproducingKernel

variable {X : Type*} [Fintype X] (K : ReproducingKernel X)

/-! ### Kernel Properties -/

/-- The quadratic form ∑ αᵢ αⱼ k(xᵢ, xⱼ) is symmetric in the kernel
    arguments, following directly from kernel symmetry. -/
theorem quadratic_form_symm (α : X → ℝ) :
    ∑ x, ∑ y, α x * α y * K.k x y =
    ∑ x, ∑ y, α x * α y * K.k y x := by
  congr 1; ext x; congr 1; ext y; rw [K.k_symm]

end ReproducingKernel

/-! ### Kernel (Gram) Matrix -/

/-- **Kernel matrix** (Gram matrix): given n data points and a kernel,
    K_{ij} = k(x_i, x_j). We work directly with `Fin n` as the index. -/
def kernelMatrix {X : Type*} [Fintype X] (K : ReproducingKernel X) :
    Matrix X X ℝ :=
  Matrix.of (fun i j => K.k i j)

/-- The kernel matrix is symmetric. -/
theorem kernelMatrix_symmetric {X : Type*} [Fintype X]
    (K : ReproducingKernel X) :
    (kernelMatrix K)ᵀ = kernelMatrix K := by
  ext i j
  simp only [kernelMatrix, Matrix.transpose_apply, Matrix.of_apply]
  exact K.k_symm j i

/-- The Gram-matrix quadratic form is nonnegative. This is the matrix-level
    restatement of kernel positive definiteness. -/
theorem kernelMatrix_quadratic_nonneg {X : Type*} [Fintype X]
    (K : ReproducingKernel X) (α : X → ℝ) :
    0 ≤ ∑ x, ∑ y, α x * α y * kernelMatrix K x y := by
  simpa [kernelMatrix] using K.k_pd α

/-! ### Regularized Kernel Matrix

Kernel ridge regression solves min_α ‖Kα - y‖² + λ‖α‖²_K,
yielding α* = (K + λI)^{-1} y. The regularized matrix K + λI is
invertible when λ > 0 and K is PSD. -/

/-- **Regularized kernel matrix**: K + λI. -/
def regularizedKernelMatrix {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ)
    (lambda : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  K + lambda • (1 : Matrix (Fin n) (Fin n) ℝ)

/-- The regularized matrix K + λI is symmetric when K is symmetric. -/
theorem regularizedKernelMatrix_symmetric {n : ℕ}
    (K : Matrix (Fin n) (Fin n) ℝ) (lambda : ℝ) (hK : Kᵀ = K) :
    (regularizedKernelMatrix K lambda)ᵀ = regularizedKernelMatrix K lambda := by
  unfold regularizedKernelMatrix
  rw [Matrix.transpose_add, hK, Matrix.transpose_smul, Matrix.transpose_one]

/-! ### Kernel Ridge Regression: Algebraic Form

The kernel ridge regression solution is:

  f*(x) = ∑ᵢ α*ᵢ k(xᵢ, x)  where  α* = (K + λI)⁻¹ y

This is the finite-dimensional representer theorem: the optimal
function in the RKHS lies in the span of the kernel basis functions. -/

/-- **Representer form**: the kernel ridge regression prediction at a
    new point x is the inner product of the coefficient vector with the
    kernel column. This is the algebraic representer theorem. -/
def kernelRidgePrediction {n : ℕ} (alpha : Fin n → ℝ)
    (k_col : Fin n → ℝ) : ℝ :=
  ∑ i, alpha i * k_col i

/-- The kernel-ridge coefficient vector `α = (K + λI)⁻¹ y`. -/
def kernelRidgeCoeffs {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ)
    (lambda : ℝ) (y : Fin n → ℝ) : Fin n → ℝ :=
  (regularizedKernelMatrix K lambda)⁻¹.mulVec y

/-- The prediction is linear in the coefficients. -/
theorem kernelRidgePrediction_add {n : ℕ} (alpha beta : Fin n → ℝ)
    (k_col : Fin n → ℝ) :
    kernelRidgePrediction (alpha + beta) k_col =
    kernelRidgePrediction alpha k_col + kernelRidgePrediction beta k_col := by
  unfold kernelRidgePrediction
  simp [Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- The prediction is linear in scaling. -/
theorem kernelRidgePrediction_smul {n : ℕ} (c : ℝ) (alpha : Fin n → ℝ)
    (k_col : Fin n → ℝ) :
    kernelRidgePrediction (c • alpha) k_col =
    c * kernelRidgePrediction alpha k_col := by
  unfold kernelRidgePrediction
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
  rw [← Finset.mul_sum]

/-- Evaluating the KRR predictor at a kernel column uses the coefficient vector
    `α = (K + λI)⁻¹ y`. -/
theorem kernelRidgePrediction_coeffs {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ)
    (lambda : ℝ) (y k_col : Fin n → ℝ) :
    kernelRidgePrediction (kernelRidgeCoeffs K lambda y) k_col =
      ∑ i, ((regularizedKernelMatrix K lambda)⁻¹.mulVec y) i * k_col i := by
  rfl

/-! ### RKHS Approximation Error

The bias-variance tradeoff in kernel ridge regression:

  ‖f - f_λ‖² ≤ λ · ‖f‖²_H

where f_λ is the regularized solution and ‖f‖_H is the RKHS norm.
This algebraic relationship captures the regularization bias.

**Blocked**: The full functional-analytic proof requires:
- RKHS as a complete Hilbert space (Hilbert space completion)
- Spectral decomposition of compact integral operators
- Mercer's theorem for the eigenfunction expansion
These are beyond current Mathlib infrastructure. We capture the
algebraic structure of the bound. -/

/-- **Regularization bias structure**: encodes the algebraic relationship
    ‖f - f_λ‖² ≤ λ · ‖f‖²_H. -/
structure RegularizationBias where
  /-- Regularization parameter λ > 0 -/
  lambda : ℝ
  /-- RKHS norm squared ‖f‖²_H -/
  rkhs_norm_sq : ℝ
  /-- Approximation error ‖f - f_λ‖² -/
  approx_error : ℝ
  /-- λ > 0 -/
  hlambda : 0 < lambda
  /-- RKHS norm is nonneg -/
  hrkhs_nonneg : 0 ≤ rkhs_norm_sq
  /-- The bias bound holds -/
  hbias : approx_error ≤ lambda * rkhs_norm_sq
  /-- Approximation error is nonneg -/
  herror_nonneg : 0 ≤ approx_error

/-- The regularization bias bound is nonneg. -/
theorem RegularizationBias.bound_nonneg (b : RegularizationBias) :
    0 ≤ b.lambda * b.rkhs_norm_sq :=
  mul_nonneg (le_of_lt b.hlambda) b.hrkhs_nonneg

/-- Decreasing λ decreases the bias bound. -/
theorem RegularizationBias.bias_monotone (lambda1 lambda2 rkhs_sq : ℝ)
    (hle : lambda1 ≤ lambda2) (hrkhs : 0 ≤ rkhs_sq) :
    lambda1 * rkhs_sq ≤ lambda2 * rkhs_sq :=
  mul_le_mul_of_nonneg_right hle hrkhs

/-! ### Common Kernels

We define common kernels as algebraic structures, verifying the
symmetry property. Positive definiteness is taken as a hypothesis
for non-trivial kernels (polynomial, RBF) since proving it requires
analysis beyond our scope. -/

/-- **Linear kernel**: k(x, y) = x^T y = ∑ xᵢ yᵢ. -/
def linearKernel (d : ℕ) : (Fin d → ℝ) → (Fin d → ℝ) → ℝ :=
  fun x y => ∑ i, x i * y i

/-- Kernel induced by a finite-dimensional feature map. -/
def featureKernel {X : Type*} [Fintype X] (d : ℕ) (φ : X → Fin d → ℝ) :
    X → X → ℝ :=
  fun x y => linearKernel d (φ x) (φ y)

/-- The linear kernel is symmetric. -/
theorem linearKernel_symm (d : ℕ) (x y : Fin d → ℝ) :
    linearKernel d x y = linearKernel d y x := by
  unfold linearKernel
  congr 1; ext i; ring

/-- The linear kernel self-product is nonneg (‖x‖² ≥ 0). -/
theorem linearKernel_self_nonneg (d : ℕ) (x : Fin d → ℝ) :
    0 ≤ linearKernel d x x := by
  unfold linearKernel
  apply Finset.sum_nonneg
  intro i _
  exact mul_self_nonneg (x i)

/-- A feature kernel is symmetric. -/
theorem featureKernel_symm {X : Type*} [Fintype X] (d : ℕ)
    (φ : X → Fin d → ℝ) (x y : X) :
    featureKernel d φ x y = featureKernel d φ y x := by
  unfold featureKernel
  rw [linearKernel_symm]

/-- A feature kernel becomes a `ReproducingKernel` once its
    positive-definiteness is supplied. -/
def featureKernelReproducingKernel {X : Type*} [Fintype X] (d : ℕ)
    (φ : X → Fin d → ℝ)
    (hpd : ∀ α : X → ℝ, 0 ≤ ∑ x, ∑ y, α x * α y * featureKernel d φ x y) :
    ReproducingKernel X where
  k := featureKernel d φ
  k_symm := featureKernel_symm d φ
  k_pd := hpd

/-- **Polynomial kernel of degree 2**: k(x, y) = (x^T y + c)², c ≥ 0.
    This is always symmetric and PD for c ≥ 0. -/
def polyKernel2 (d : ℕ) (c : ℝ) : (Fin d → ℝ) → (Fin d → ℝ) → ℝ :=
  fun x y => (linearKernel d x y + c) ^ 2

/-- The degree-2 polynomial kernel is symmetric. -/
theorem polyKernel2_symm (d : ℕ) (c : ℝ) (x y : Fin d → ℝ) :
    polyKernel2 d c x y = polyKernel2 d c y x := by
  unfold polyKernel2
  rw [linearKernel_symm]

/-- The degree-2 polynomial kernel is nonneg. -/
theorem polyKernel2_nonneg (d : ℕ) (c : ℝ) (x y : Fin d → ℝ) :
    0 ≤ polyKernel2 d c x y :=
  sq_nonneg _

end
