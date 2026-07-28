import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Orthogonal Projection Nonexpansive

Orthogonal projection onto a closed submodule is nonexpansive:
‖proj_K(v) - proj_K(u)‖ ≤ ‖v - u‖.
-/

open Finset BigOperators

open Submodule in
theorem orthogonalProjection_nonexpansive
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (K : Submodule ℝ E) [CompleteSpace K]
    (v u : E) :
    ‖(orthogonalProjection K v : E) - (orthogonalProjection K u : E)‖ ≤ ‖v - u‖ := by
  have h : (orthogonalProjection K v : E) - (orthogonalProjection K u : E) =
      (orthogonalProjection K (v - u) : E) := by simp [map_sub]
  rw [h]
  set w := v - u
  have pythag := norm_sq_eq_add_norm_sq_projection w K
  have hnorm : ‖(orthogonalProjection K w : E)‖ = ‖orthogonalProjection K w‖ := by
    simp [Submodule.coe_norm]
  rw [← hnorm] at pythag
  nlinarith [sq_nonneg ‖Kᗮ.orthogonalProjection w‖, norm_nonneg (orthogonalProjection K w : E), norm_nonneg w]
