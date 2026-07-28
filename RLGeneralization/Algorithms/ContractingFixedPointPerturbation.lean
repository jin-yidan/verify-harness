import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic

/-!
# Contracting Fixed Point Perturbation

If f is a γ-contraction with fixed point x and g has fixed point y,
then dist(x, y) ≤ dist(f(y), g(y)) / (1 - γ).
-/

open Finset BigOperators

theorem contracting_fixed_point_perturbation {α : Type*} [MetricSpace α] {f g : α → α} {γ : ℝ} (hγ_nn : 0 ≤ γ) (hγ_lt : γ < 1) (hf_contr : ∀ x y, dist (f x) (f y) ≤ γ * dist x y) {x y : α} (hfx : f x = x) (hgy : g y = y) : dist x y ≤ dist (f y) (g y) / (1 - γ) := by
  have h_pos : (0 : ℝ) < 1 - γ := by linarith
  rw [le_div_iff₀ h_pos]
  have h1 : dist x y = dist (f x) (g y) := by rw [hfx, hgy]
  have h2 : dist (f x) (g y) ≤ dist (f x) (f y) + dist (f y) (g y) := dist_triangle _ _ _
  have h3 : dist (f x) (f y) ≤ γ * dist x y := hf_contr x y
  have h4 : dist x y ≤ γ * dist x y + dist (f y) (g y) := by linarith
  nlinarith [@dist_nonneg α _ x y]
