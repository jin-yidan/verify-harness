import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic

/-!
# Contraction Mapping Bounds

Standalone bounds for contraction mappings in metric spaces,
independent of MDP structure.

## Main Results

* `contraction_iterate_dist_le` — dist(f^n(x), x*) ≤ γ^n · dist(x, x*)
* `approx_fixed_point_bound` — dist(v, x*) ≤ dist(v, f(v)) / (1-γ)
-/

/-- **Contraction iterate bound**: if f is a γ-contraction on a metric space
    with fixed point x*, then dist(f^n(x), x*) ≤ γ^n · dist(x, x*).

    This is the quantitative convergence rate for Banach iteration,
    underlying value iteration, Q-learning, policy iteration, and FQI. -/
theorem contraction_iterate_dist_le {α : Type*} [MetricSpace α]
    {f : α → α} {γ : ℝ} (hγ_nonneg : 0 ≤ γ)
    (hf : ∀ x y, dist (f x) (f y) ≤ γ * dist x y)
    {x_star : α} (hfp : f x_star = x_star)
    (x : α) (n : ℕ) :
    dist (f^[n] x) x_star ≤ γ ^ n * dist x x_star := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Function.iterate_succ', Function.comp_apply]
    calc dist (f (f^[n] x)) x_star
        = dist (f (f^[n] x)) (f x_star) := by rw [hfp]
      _ ≤ γ * dist (f^[n] x) x_star := hf _ _
      _ ≤ γ * (γ ^ n * dist x x_star) := by
          apply mul_le_mul_of_nonneg_left ih hγ_nonneg
      _ = γ ^ (n + 1) * dist x x_star := by ring

/-- **Approximate fixed point bound** (Banach a priori estimate):
    dist(v, x*) ≤ dist(v, f(v)) / (1-γ).

    Any point v is within "Bellman residual / gap" of the fixed point.
    The key stopping criterion for value iteration: if ‖V - TV‖ < ε(1-γ),
    then ‖V - V*‖ < ε. -/
theorem approx_fixed_point_bound {α : Type*} [MetricSpace α]
    {f : α → α} {γ : ℝ} (hγ_nn : 0 ≤ γ) (hγ_lt : γ < 1)
    (hf : ∀ x y, dist (f x) (f y) ≤ γ * dist x y)
    {x_star : α} (hfp : f x_star = x_star) (v : α) :
    dist v x_star ≤ dist v (f v) / (1 - γ) := by
  have h1γ : (0 : ℝ) < 1 - γ := by linarith
  rw [le_div_iff₀ h1γ]
  have h_tri : dist v x_star ≤ dist v (f v) + dist (f v) x_star :=
    dist_triangle v (f v) x_star
  have h_contr : dist (f v) x_star ≤ γ * dist v x_star := by
    calc dist (f v) x_star = dist (f v) (f x_star) := by rw [hfp]
      _ ≤ γ * dist v x_star := hf v x_star
  linarith
