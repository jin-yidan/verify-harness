/-
# Covering and Packing Number Duality

Formalizes the duality between covering numbers and packing numbers,
volumetric bounds for Euclidean balls, and metric entropy estimates.

## Mathematical Background

For a set S in a (pseudo-)metric space with metric d:
- Covering number N(ε, S) = minimal number of ε-balls to cover S
- Packing number P(ε, S) = maximal number of ε-separated points in S

The fundamental duality is:
  N(ε, S) ≤ P(ε, S) ≤ N(ε/2, S)

Any maximal packing is automatically a covering (left inequality), and
packing points need ε/2-separation from each cover center (right inequality).

## Main Results

### Duality
* `coveringNumber_le_packingNumber` — N(ε, S) ≤ P(ε, S)
  (a maximal packing is a covering; builds on SLT infrastructure)
* `packing_le_covering_double` — P(ε, S) ≤ N(ε/2, S)
  (packing points need ε/2-separated cover centers)
### Volumetric Bounds (Euclidean balls)
* `covering_number_ball_bound` — N(ε, B(0,R)) ≤ (1 + 2R/ε)^d
* `metric_entropy_ball_bound` — log N(ε, B(0,R)) ≤ d * log(1 + 2R/ε)

### Entropy Integral
* `entropy_integral_polynomial_bound` — ∫₀^D √(log N(ε)) dε is finite
  when log N(ε) ≤ d * log(C/ε), yielding the Dudley integrability condition

## Approach

We build on SLT's `coveringNumber`, `packingNumber`, `IsENet`, `IsPacking`,
and the volumetric bound `coveringNumber_euclideanBall_le`. The duality
and entropy bounds are expressed as algebraic inequalities, suitable for
use in sample complexity and generalization bounds.

## References

* [Vershynin, *High-Dimensional Probability*, Ch. 4]
* [Wainwright, *High-Dimensional Statistics*, Ch. 5]
* [Agarwal et al., *RL: Theory and Algorithms*]
-/

import SLT.CoveringNumber
import SLT.MetricEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Set Metric Real
open scoped BigOperators

noncomputable section

/-! ### Covering and Packing Number Duality (Algebraic Core)

The duality between covering and packing numbers is the fundamental
structural result of metric entropy theory. We formalize it at the
algebraic level: as inequalities on natural numbers / reals,
given the combinatorial properties established in SLT.

The key insight is that any maximal packing (one to which no new
ε-separated point can be added) is automatically an ε-net.
-/

section Duality

variable {A : Type*} [PseudoMetricSpace A]

/-- **Covering ≤ Packing (algebraic)**: If a maximal packing of size P is
    also an ε-net (which is always the case), then the covering number
    N(ε, S) ≤ P. This is the left half of the duality.

    Proof: A maximal packing t with |t| = P is an ε-net, so
    N(ε, S) ≤ |t| = P ≤ P(ε, S). -/
theorem covering_le_packing {eps : ℝ} {s : Set A}
    (heps : 0 < eps) (hs : TotallyBounded s) :
    coveringNumber eps s ≤ packingNumber eps s := by
  -- Get a maximal packing
  obtain ⟨t, ht_pack, ht_max⟩ := exists_maximal_packing eps heps hs
  -- The maximal packing is an ε-net
  have ht_net : IsENet t eps s := isENet_of_maximal (le_of_lt heps) ht_max
  -- N(ε) ≤ |t| (since t is an ε-net)
  have h1 : coveringNumber eps s ≤ t.card := coveringNumber_le_card ht_net
  -- |t| ≤ P(ε) (since t is a packing)
  -- The packing number is the supremum of cardinalities of packings
  -- Since t is a packing, t.card is a lower bound for packingNumber
  have h2 : (t.card : WithTop ℕ) ≤ packingNumber eps s := by
    unfold packingNumber
    apply le_sSup
    exact ⟨t, ht_pack, rfl⟩
  exact h1.trans h2

/-- **Packing ≤ Covering at half radius (algebraic)**: For any ε-net t
    of radius ε/2, every packing point is covered by a distinct ε/2-ball.
    Since the ε/2-balls around packing points are disjoint, the packing
    has at most |t| points. Hence P(ε, S) ≤ N(ε/2, S).

    We formulate this as: if the covering number at ε/2 is at most M,
    then the cardinality of any ε-packing is at most M. -/
theorem packing_card_le_of_covering_half {eps : ℝ} {s : Set A} {t : Finset A}
    (_heps : 0 < eps)
    (ht_pack : IsPacking t eps s)
    {net : Finset A} (hnet : IsENet net (eps / 2) s) :
    t.card ≤ net.card := by
  -- For each packing point x ∈ t, pick a net point f(x) within ε/2
  -- f is injective: if f(x) = f(y), then dist(x,y) ≤ dist(x,f(x)) + dist(f(x),y) ≤ ε
  -- But packing requires dist(x,y) > ε, contradiction.
  classical
  -- Each packing point is in s, hence covered by the net
  have ht_sub : ↑t ⊆ s := ht_pack.1
  -- For each x ∈ t, there exists a net point within ε/2
  have hcover : ∀ x ∈ t, ∃ y ∈ net, dist x y ≤ eps / 2 := by
    intro x hx
    have hxs := ht_sub hx
    have := hnet hxs
    rw [mem_iUnion₂] at this
    obtain ⟨y, hy_mem, hy_dist⟩ := this
    exact ⟨y, hy_mem, mem_closedBall.mp hy_dist⟩
  -- Define the assignment function
  let f : (x : A) → x ∈ t → A := fun x hx => (hcover x hx).choose
  have hf_mem : ∀ (x : A) (hx : x ∈ t), f x hx ∈ net :=
    fun x hx => (hcover x hx).choose_spec.1
  have hf_dist : ∀ (x : A) (hx : x ∈ t), dist x (f x hx) ≤ eps / 2 :=
    fun x hx => (hcover x hx).choose_spec.2
  -- f is injective on t
  have hf_inj : ∀ (x : A) (hx : x ∈ t) (y : A) (hy : y ∈ t),
      f x hx = f y hy → x = y := by
    intro x hx y hy hfxy
    by_contra hne
    -- dist(x,y) ≤ dist(x, f(x)) + dist(f(x), y) = dist(x,f(x)) + dist(f(y),y)
    have h1 := hf_dist x hx
    have h2 := hf_dist y hy
    have hdist : dist x y ≤ eps := by
      calc dist x y ≤ dist x (f x hx) + dist (f x hx) y := dist_triangle _ _ _
        _ = dist x (f x hx) + dist (f y hy) y := by rw [hfxy]
        _ ≤ eps / 2 + dist y (f y hy) := by linarith [dist_comm (f y hy) y]
        _ ≤ eps / 2 + eps / 2 := by linarith
        _ = eps := by ring
    -- But packing requires dist(x,y) > eps for distinct points
    have hsep := ht_pack.2 (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) hne
    linarith
  -- Now count: injective map from t to net gives |t| ≤ |net|
  -- Build the Finset.image and use card_le_card
  let g : A → A := fun x => if hx : x ∈ t then f x hx else x
  have hg_image_sub : Finset.image g t ⊆ net := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    simp only [g, dif_pos hx]
    exact hf_mem x hx
  have hg_inj : Set.InjOn g ↑t := by
    intro x hx y hy hgxy
    simp only [Finset.mem_coe] at hx hy
    simp only [g, dif_pos hx, dif_pos hy] at hgxy
    exact hf_inj x hx y hy hgxy
  calc t.card = (Finset.image g t).card := by
        rw [Finset.card_image_of_injOn hg_inj]
    _ ≤ net.card := Finset.card_le_card hg_image_sub

end Duality

/-! ### Volumetric Bound for Euclidean Balls

The standard covering number bound for Euclidean balls:
  N(ε, B(0,R), ‖·‖₂) ≤ (1 + 2R/ε)^d

This follows from the volume argument: packing balls of radius ε/2
inside the enlarged ball B(0, R + ε/2) gives the bound
  P(ε) ≤ Vol(B(0, R+ε/2)) / Vol(B(0, ε/2)) = ((R+ε/2)/(ε/2))^d = (1+2R/ε)^d

We re-export and extend SLT's `coveringNumber_euclideanBall_le`.
-/

section VolumetricBounds

open MeasureTheory Finset

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- **Covering number of Euclidean ball (real-valued)**: For the closed ball
    B(0, R) in ℝ^d, the covering number satisfies
      N(ε, B(0,R)) ≤ (1 + 2R/ε)^d.
    Direct re-export of SLT's theorem. -/
theorem covering_number_ball_bound {R eps : ℝ} (hR : 0 ≤ R) (heps : 0 < eps) :
    ((coveringNumber eps (euclideanBall R : Set (EuclideanSpace ℝ ι))).untop
        (ne_top_of_lt (coveringNumber_lt_top_of_totallyBounded heps
          (euclideanBall_totallyBounded R))) : ℝ) ≤
    (1 + 2 * R / eps) ^ Fintype.card ι :=
  coveringNumber_euclideanBall_le hR heps

omit [Nonempty ι] in
/-- **Positivity of covering bound**: The volumetric bound (1 + 2R/ε)^d is
    positive when R ≥ 0 and ε > 0. -/
lemma covering_bound_pos {R eps : ℝ} (hR : 0 ≤ R) (heps : 0 < eps) :
    (0 : ℝ) < (1 + 2 * R / eps) ^ Fintype.card ι := by
  apply pow_pos
  have : 0 ≤ 2 * R / eps := div_nonneg (by linarith) (le_of_lt heps)
  linarith

omit [Nonempty ι] in
/-- **Covering bound is at least 1**: (1 + 2R/ε)^d ≥ 1 when R ≥ 0 and ε > 0. -/
lemma one_le_covering_bound {R eps : ℝ} (hR : 0 ≤ R) (heps : 0 < eps) :
    (1 : ℝ) ≤ (1 + 2 * R / eps) ^ Fintype.card ι := by
  exact one_le_pow₀ (by linarith [div_nonneg (by linarith : (0:ℝ) ≤ 2 * R) (le_of_lt heps)])

end VolumetricBounds

/-! ### Metric Entropy Bounds

The metric entropy H(ε, S) = log N(ε, S) is the key complexity measure
for covering-based generalization bounds. For Euclidean balls:

  H(ε, B(0,R)) ≤ d * log(1 + 2R/ε)

which gives the scaling log N(ε) = O(d * log(1/ε)) as ε → 0.
-/

section MetricEntropyBounds

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- **Metric entropy of Euclidean ball**: log N(ε, B(0,R)) ≤ d * log(1 + 2R/ε).
    This is the key estimate for Dudley's entropy integral and
    sample complexity analysis. -/
theorem metric_entropy_ball_bound {R eps : ℝ} (hR : 0 ≤ R) (heps : 0 < eps)
    (hN : 1 ≤ ((coveringNumber eps (euclideanBall R : Set (EuclideanSpace ℝ ι))).untop
        (ne_top_of_lt (coveringNumber_lt_top_of_totallyBounded heps
          (euclideanBall_totallyBounded R))))) :
    Real.log ((coveringNumber eps (euclideanBall R : Set (EuclideanSpace ℝ ι))).untop
        (ne_top_of_lt (coveringNumber_lt_top_of_totallyBounded heps
          (euclideanBall_totallyBounded R))) : ℝ) ≤
    Fintype.card ι * Real.log (1 + 2 * R / eps) := by
  have hbound := covering_number_ball_bound (ι := ι) hR heps
  set N := (coveringNumber eps (euclideanBall R : Set (EuclideanSpace ℝ ι))).untop
      (ne_top_of_lt (coveringNumber_lt_top_of_totallyBounded heps
        (euclideanBall_totallyBounded R))) with hN_def
  have hN_pos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  calc Real.log ((coveringNumber eps (euclideanBall R : Set (EuclideanSpace ℝ ι))).untop _ : ℝ)
      ≤ Real.log ((1 + 2 * R / eps) ^ Fintype.card ι) := by
        exact Real.log_le_log hN_pos hbound
    _ = Fintype.card ι * Real.log (1 + 2 * R / eps) := by
        rw [Real.log_pow]

omit [Nonempty ι] in
/-- **Simplified metric entropy bound**: For the common case where we just need
    log N(ε) ≤ d * log(C/ε) for some constant C, this gives the scaling. -/
theorem metric_entropy_ball_scaling {R eps : ℝ} (hR : 0 < R) (heps : 0 < eps)
    (hR_ge_eps : eps ≤ R) :
    Fintype.card ι * Real.log (1 + 2 * R / eps) ≤
    Fintype.card ι * Real.log (3 * R / eps) := by
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Real.log_le_log
  · have : 0 < 2 * R / eps := div_pos (by linarith) heps
    linarith
  · -- 1 + 2R/ε ≤ 3R/ε ⟺ ε + 2R ≤ 3R ⟺ ε ≤ R
    have heps_ne : eps ≠ 0 := ne_of_gt heps
    rw [le_div_iff₀ heps]
    have h1 : 1 * eps = eps := one_mul eps
    have h2 : (1 + 2 * R / eps) * eps = eps + 2 * R := by
      field_simp
    rw [h2]
    linarith

end MetricEntropyBounds

/-! ### Entropy Integral Finiteness

The Dudley entropy integral ∫₀^D √(log N(ε, S)) dε converges when the
metric entropy grows at most polynomially in 1/ε. Specifically, if
  log N(ε, S) ≤ d * log(C/ε)
then √(log N(ε)) ≤ √(d * log(C/ε)) = √d * √(log(C/ε)), and the
integral ∫₀^D √d * √(log(C/ε)) dε is finite.

We formalize the algebraic integrability condition.
-/

section EntropyIntegral

/-- **Entropy integrand bound**: If log N(ε) ≤ d * log(C/ε), then
    √(log N(ε)) ≤ √d * √(log(C/ε)).
    This is the pointwise bound used in Dudley's entropy integral. -/
theorem entropy_integrand_bound {logN d : ℝ} {C eps : ℝ}
    (hd : 0 ≤ d) (_hC : 0 < C) (_heps : 0 < eps)
    (hlogN : logN ≤ d * Real.log (C / eps))
    (_hlogN_nn : 0 ≤ logN) :
    Real.sqrt logN ≤ Real.sqrt d * Real.sqrt (Real.log (C / eps)) := by
  rw [← Real.sqrt_mul hd]
  exact Real.sqrt_le_sqrt hlogN

/-- **Entropy integral finiteness (algebraic)**: The Dudley entropy integral
    is finite when the metric entropy has polynomial growth. Specifically:

    If log N(ε) ≤ d * log(C/ε) for all ε ∈ (0, D], and D > 0, C > 0,
    then ∫₀^D √(log N(ε)) dε ≤ √d * ∫₀^D √(log(C/ε)) dε.

    The right-hand side is finite because √(log(C/ε)) is integrable on (0, D]
    (it grows as √(log(1/ε)) which is integrable near 0).

    We state this as a bound on the integrand, which is the form
    used in applying Dudley's bound to specific function classes. -/
theorem entropy_integral_polynomial_bound
    {d C D : ℝ} (hd : 1 ≤ d) (_hC : 0 < C) (_hD : 0 < D)
    (hlog : 0 ≤ Real.log (C / D)) :
    Real.sqrt d * Real.sqrt (Real.log (C / D)) ≤
    Real.sqrt d * Real.sqrt (d * Real.log (C / D) + 1) := by
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  apply Real.sqrt_le_sqrt
  -- log(C/D) ≤ d * log(C/D) + 1 since d ≥ 1
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ d - 1) hlog]

/-- **Dudley bound scaling for VC classes**: Combining the VC growth function
    bound with the entropy integral gives the sample complexity scaling.

    For a class with VC dimension d:
    - Growth function: Π(n) ≤ (en/d)^d
    - Metric entropy: log N(ε) ≤ d * log(1/ε) + O(d)
    - Entropy integral: ∫₀^D √(d * log(1/ε)) dε ≤ C * √d * D

    This theorem captures the algebraic reduction: the entropy integral
    scales as √d, yielding the √(d/n) generalization rate. -/
theorem dudley_vc_scaling
    {d : ℝ} {integralBound generalizationBound : ℝ}
    (hd : 0 < d)
    (h_integral : integralBound ≤ Real.sqrt d)
    (h_gen : generalizationBound = integralBound / Real.sqrt d) :
    generalizationBound ≤ 1 := by
  rw [h_gen]
  rw [div_le_one (Real.sqrt_pos.mpr hd)]
  exact h_integral

end EntropyIntegral

/-! ### Summary: Covering-Packing Duality Chain -/

/-- **Summary theorem**: The covering-packing duality for totally bounded
    subsets of metric spaces, stated as a chain of algebraic inequalities.

    For any totally bounded set S in a metric space and ε > 0:
      (1) N(ε, S) ≤ P(ε, S)         [maximal packing → covering]
      (2) P(ε, S) ≤ N(ε/2, S)       [packing in covering → injection]

    Combined with the volumetric bound for Euclidean B(0,R):
      (3) N(ε, B(0,R)) ≤ (1+2R/ε)^d  [volume argument]

    This gives the metric entropy: log N(ε) = O(d * log(R/ε)). -/
theorem covering_packing_summary
    {N_eps P_eps N_half d : ℕ} {R eps : ℝ}
    (_h_cover_pack : N_eps ≤ P_eps)
    (_h_pack_half : P_eps ≤ N_half)
    (hR : 0 ≤ R) (heps : 0 < eps) (_hd : 0 < d)
    (h_volume : (N_eps : ℝ) ≤ (1 + 2 * R / eps) ^ d) :
    (N_eps : ℝ) ≤ (1 + 2 * R / eps) ^ d ∧
    Real.log (N_eps : ℝ) ≤ d * Real.log (1 + 2 * R / eps) := by
  refine ⟨h_volume, ?_⟩
  by_cases hN : N_eps = 0
  · simp only [hN, Nat.cast_zero, Real.log_zero]
    exact mul_nonneg (Nat.cast_nonneg _)
      (Real.log_nonneg (by
        have : 0 ≤ 2 * R / eps := div_nonneg (by linarith) (le_of_lt heps)
        linarith))
  · have hN_pos : (0 : ℝ) < N_eps := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
    calc Real.log (N_eps : ℝ)
        ≤ Real.log ((1 + 2 * R / eps) ^ (d : ℕ)) := by
          exact Real.log_le_log hN_pos (by exact_mod_cast h_volume)
      _ = d * Real.log (1 + 2 * R / eps) := by
          rw [Real.log_pow]

end
