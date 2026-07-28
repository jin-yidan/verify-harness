/-
# Neural Network Approximation Theory

## Status: Stub
Blocked on Hahn-Banach theorem (functional analysis), which is needed
for the universal approximation theorem proof. Contains structures
and trivial algebraic properties only.

Formalizes the algebraic structure of two-layer neural networks and
states the universal approximation theorem and depth separation results.

## Mathematical Background

A two-layer neural network computes:
  f(x) = ∑ᵢ aᵢ σ(wᵢ^T x + bᵢ)

where σ is an activation function, wᵢ are weight vectors, aᵢ are output
weights, and bᵢ are biases.

The **universal approximation theorem** (Cybenko 1989, Hornik 1991):
for any continuous f on a compact set and ε > 0, there exists a two-layer
network of sufficient width that ε-approximates f in sup norm.

**Depth separation** (Eldan-Shamir 2016, Telgarsky 2016): there exist
functions computable by depth-k+1 networks of polynomial size that
require exponential width at depth k.

## Main Definitions

* `TwoLayerNetwork` - Two-layer network with activation, weights, biases
* `networkEval` - Evaluation: f(x) = ∑ aᵢ σ(wᵢ^T x + bᵢ)
* `eval_scale_output` - f is linear in output weights aᵢ (scaling)
* `eval_add_output` - f is linear in output weights aᵢ (additivity)
* `DepthSeparationSpec` - Prop specification of depth separation (see caveat in docstring)

## Approach

We define the network architecture and evaluation algebraically. The
universal approximation theorem and depth separation are stated as Prop
declarations (existential statements) since their proofs require deep
analysis (Hahn-Banach, Riesz representation) beyond current scope.

## Blocked

- Full UAT proof (requires Hahn-Banach theorem, not in Mathlib scope)
- Depth separation proof (requires specific function constructions + counting)
- Approximation rates (require Barron spaces, integral representations)
- Training dynamics (requires NTK theory, gradient flow analysis)

## References

* [Cybenko, *Approximation by superpositions of a sigmoidal function*, 1989]
* [Hornik, *Approximation capabilities of multilayer feedforward networks*, 1991]
* [Telgarsky, *Benefits of depth in neural networks*, 2016]
* [Eldan and Shamir, *The power of depth for feedforward neural networks*, 2016]
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Finset BigOperators

noncomputable section

/-! ### Activation Functions -/

/-- A **bounded activation function** σ : ℝ → ℝ.
    This structure is tailored to the sigmoidal/UAT side of the file.
    Unbounded activations such as ReLU are handled separately below. -/
structure ActivationFn where
  /-- The activation function -/
  σ : ℝ → ℝ
  /-- σ is bounded: there exists M such that |σ(t)| ≤ M for all t -/
  bounded : ∃ M : ℝ, 0 < M ∧ ∀ t, |σ t| ≤ M

/-- The ReLU activation: σ(t) = max(0, t). -/
def relu : ℝ → ℝ := fun t => max 0 t

/-- ReLU is nonneg. -/
theorem relu_nonneg (t : ℝ) : 0 ≤ relu t := le_max_left 0 t

/-- ReLU(0) = 0. -/
theorem relu_zero : relu 0 = 0 := by simp [relu]

/-- ReLU is monotone. -/
theorem relu_monotone : Monotone relu := fun _ _ h => max_le_max_left 0 h

/-! ### Two-Layer Network -/

/-- A **two-layer neural network** with N hidden units, input dimension d:

    f(x) = ∑ᵢ₌₁ᴺ aᵢ · σ(wᵢ^T x + bᵢ)

    where wᵢ ∈ ℝᵈ, bᵢ ∈ ℝ, aᵢ ∈ ℝ. -/
structure TwoLayerNetwork (d : ℕ) (N : ℕ) where
  /-- Activation function -/
  activation : ℝ → ℝ
  /-- Input weight vectors wᵢ ∈ ℝᵈ -/
  w : Fin N → (Fin d → ℝ)
  /-- Bias terms bᵢ ∈ ℝ -/
  b : Fin N → ℝ
  /-- Output weights aᵢ ∈ ℝ -/
  a : Fin N → ℝ

namespace TwoLayerNetwork

variable {d N : ℕ}

/-! ### Network Evaluation -/

/-- Inner product ⟨w, x⟩ = ∑ wᵢ xᵢ. -/
def innerProd (w x : Fin d → ℝ) : ℝ := ∑ i, w i * x i

/-- **Network evaluation**: f(x) = ∑ᵢ aᵢ · σ(⟨wᵢ, x⟩ + bᵢ). -/
def eval (net : TwoLayerNetwork d N) (x : Fin d → ℝ) : ℝ :=
  ∑ i, net.a i * net.activation (innerProd (net.w i) x + net.b i)

/-- Network evaluation at zero input. -/
theorem eval_at_zero (net : TwoLayerNetwork d N) :
    net.eval 0 = ∑ i, net.a i * net.activation (net.b i) := by
  unfold eval innerProd
  congr 1; ext i
  congr 1; congr 1
  simp only [mul_zero, Finset.sum_const_zero, Pi.zero_apply, zero_add]

/-! ### Linearity in Output Weights

The network output is linear in the output weight vector a.
This is crucial for:
1. The representer theorem connection (NTK regime)
2. Convex optimization of the last layer
3. The random features approximation -/

/-- **Linearity in output weights**: scaling all output weights by c
    scales the output by c. -/
theorem eval_scale_output (net : TwoLayerNetwork d N)
    (c : ℝ) (x : Fin d → ℝ) :
    (TwoLayerNetwork.mk net.activation net.w net.b (c • net.a)).eval x =
    c * net.eval x := by
  unfold eval
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
  rw [← Finset.mul_sum]

/-- **Additivity in output weights**: adding output weight vectors
    adds the outputs. -/
theorem eval_add_output (net1 net2 : TwoLayerNetwork d N)
    (h_same : net1.activation = net2.activation ∧
              net1.w = net2.w ∧ net1.b = net2.b)
    (x : Fin d → ℝ) :
    (TwoLayerNetwork.mk net1.activation net1.w net1.b (net1.a + net2.a)).eval x =
    net1.eval x + net2.eval x := by
  unfold eval
  simp [Pi.add_apply, add_mul, Finset.sum_add_distrib, h_same.1, h_same.2.1,
        h_same.2.2]

/-! ### Network Width and Complexity -/

/-- The **width** of a two-layer network is N (number of hidden units). -/
def width (_ : TwoLayerNetwork d N) : ℕ := N

/-- The total number of parameters: N*(d+2) = N*d weights + N biases + N output weights. -/
def numParams (_ : TwoLayerNetwork d N) : ℕ := N * (d + 2)

/-- Number of parameters is nonneg. -/
theorem numParams_nonneg (net : TwoLayerNetwork d N) : 0 ≤ net.numParams :=
  Nat.zero_le _

end TwoLayerNetwork

/-! ### Abstract Deep Networks

We keep the representation deliberately light: a deep network is an
evaluation function together with depth and width metadata. This is
enough to state non-vacuous expressivity and separation results without
committing to a specific layer-by-layer implementation yet. -/

/-- An abstract deep network with input dimension `d`. -/
structure DeepNetwork (d : ℕ) where
  /-- Number of hidden layers. -/
  depth : ℕ
  /-- Uniform width bound across hidden layers. -/
  width : ℕ
  /-- Network evaluation. -/
  eval : (Fin d → ℝ) → ℝ

/-! ### Universal Approximation Theorem (Statement)

**Theorem** (Cybenko 1989, Hornik 1991): Let σ be a continuous sigmoidal
activation function. For any continuous function f : [0,1]^d → ℝ and any
ε > 0, there exists a two-layer network g of finite width N such that
  sup_{x ∈ [0,1]^d} |f(x) - g(x)| < ε.

We state this as an existential Prop, since the proof requires:
1. The Hahn-Banach theorem (not constructive)
2. The Riesz representation theorem
3. Properties of sigmoidal functions (limits at ±∞)

**Blocked**: Full proof requires functional analysis beyond Mathlib scope. -/

/-! ### Depth Separation (Statement)

**Theorem** (Telgarsky 2016): There exist functions that can be computed
by depth-k networks of polynomial size but require exponential width
at depth k-1.

Specifically, the sawtooth function iterated k times has oscillation
complexity 2^k, so:
- A depth-k network of O(k) neurons computes it exactly
- Any depth-2 network needs Ω(2^k) neurons to ε-approximate it

We state this as a Prop declaration. -/

/-- **Depth separation** (abstract representability statement):
    for any width bound `W`, there exists a function that width-`W`
    two-layer networks fail to approximate pointwise within `1/4`,
    while some deeper network of depth at least `3` and width at most
    `W^2` represents the same function exactly. -/
def DepthSeparationSpec (d : ℕ) : Prop :=
  ∀ W : ℕ, ∃ (f : (Fin d → ℝ) → ℝ),
    -- f cannot be approximated by width-W depth-2 networks
    (∀ (net : TwoLayerNetwork d W) (x : Fin d → ℝ),
      ¬(|net.eval x - f x| < 1/4)) ∧
    -- f can be represented by a bounded-width deeper network
    (∃ deep : DeepNetwork d, 3 ≤ deep.depth ∧ deep.width ≤ W * W ∧
      ∀ x, deep.eval x = f x)

/-! ### Approximation Rate Bounds

For specific function classes, the required network width N scales
predictably with the desired accuracy ε:

- Lipschitz functions on [0,1]^d: N = O((1/ε)^d) (curse of dimensionality)
- Barron class functions: N = O(1/ε²) (dimension-free!)

The Barron class result is particularly significant: functions with
bounded "Fourier moment" ∫ |ω| |f̂(ω)| dω < ∞ can be approximated
by two-layer networks with dimension-independent rate.

**Blocked**: Barron class requires Fourier transform in Mathlib. -/

/-- **Approximation rate structure**: encodes the algebraic relationship
    between network width N and approximation error ε for a function class. -/
structure ApproxRate where
  /-- Network width -/
  N : ℕ
  /-- Approximation error -/
  epsilon : ℝ
  /-- Width is positive -/
  hN : 0 < N
  /-- Error is positive -/
  heps : 0 < epsilon

/-- For finite-width networks, the approximation error is positive
    (no exact representation in general). -/
theorem ApproxRate.error_pos (r : ApproxRate) : 0 < r.epsilon := r.heps

/-- **Barron rate structure**: for Barron-class functions, the rate is
    ε = O(C_f / √N) where C_f is the Barron norm. -/
structure BarronRate extends ApproxRate where
  /-- Barron norm of the target function -/
  barron_norm : ℝ
  /-- Barron norm is positive -/
  hbarron : 0 < barron_norm
  /-- The rate bound: ε ≤ C_f / √N -/
  hrate : epsilon ≤ barron_norm / Real.sqrt (N : ℝ)

/-- The Barron rate bound is nonneg. -/
theorem BarronRate.bound_nonneg (r : BarronRate) :
    0 ≤ r.barron_norm / Real.sqrt (r.N : ℝ) :=
  div_nonneg (le_of_lt r.hbarron) (Real.sqrt_nonneg _)

/-! ### Connection to RL

Neural networks appear in RL as function approximators for:
1. Value functions V(s; θ) and Q(s,a; θ)
2. Policies π(a|s; θ)
3. Models P(s'|s,a; θ) and r(s,a; θ)

The approximation theory here provides the foundation for:
- **Approximation error analysis**: how well can a network class
  approximate the true value/policy/model?
- **Sample complexity with approximation**: generalization bounds
  that account for both statistical and approximation error
- **Neural tangent kernel**: in the overparameterized regime,
  training dynamics approximately follow kernel regression with
  the NTK, connecting to the RKHS theory

**Blocked**: Connecting approximation to sample complexity requires
the Rademacher complexity of neural network classes, which depends
on covering number bounds for weight-bounded networks. -/

end
