/-
# Bennett's Inequality

Bennett's inequality for bounded random variables, and the Bennett-Bernstein
comparison showing Bennett is always at least as tight as Bernstein.

## Main results

* `bennettFun` : the Bennett function h(u) = (1+u)log(1+u) - u
* `bennettFun_zero` : h(0) = 0
* `bennettFun_nonneg` : h(u) ≥ 0 for u ≥ 0
* `bennettFun_monotoneOn` : h is monotone increasing on [0,∞)
* `bennettFun_ge_bernstein` : h(u) ≥ u²/(2(1+u/3)) for u ≥ 0
  (Bennett ≥ Bernstein comparison)
* `bennett_exponent_ge_bernstein_exponent` : the full exponent comparison
  nσ²·h(t/(nσ²)) ≥ t²/(2(nσ² + bt/3))

## Strategy

The Bennett function properties are purely analytic (no probability needed).
The key tool is `monotoneOn_of_deriv_nonneg`: to show a function is nonneg
on [0,∞) with value 0 at 0, we show its derivative is nonneg, which reduces
to showing the derivative's derivative is nonneg, etc.

## References

* [Boucheron, Lugosi, Massart, *Concentration Inequalities*], Theorem 2.9
* [Agarwal, Jiang, Kakade, Sun, *RL: Theory and Algorithms*]
-/

import RLGeneralization.Concentration.Bernstein
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue

open Real Set

noncomputable section

/-! ### The Bennett Function -/

/-- **The Bennett function** h(u) = (1+u)·log(1+u) - u.

This appears in Bennett's concentration inequality:
  P(∑Xᵢ ≥ t) ≤ exp(-nσ² · h(t/(nσ²)))

where h(u) = (1+u)log(1+u) - u. The function is nonneg,
increasing, and convex on [0,∞), and satisfies h(u) ≥ u²/(2(1+u/3))
(which recovers Bernstein's bound). -/
def bennettFun (u : ℝ) : ℝ := (1 + u) * log (1 + u) - u

/-! ### Basic Properties of h -/

/-- h(0) = 0. -/
theorem bennettFun_zero : bennettFun 0 = 0 := by
  simp [bennettFun, log_one]

/-- For y > 0: log(y) ≥ 1 - 1/y. From exp(x) ≥ 1+x applied to x = -log(y). -/
private lemma log_ge_one_sub_inv {y : ℝ} (hy : 0 < y) : 1 - y⁻¹ ≤ log y := by
  have h := add_one_le_exp (-log y)
  rw [exp_neg, exp_log hy] at h
  linarith

/-- h(u) ≥ 0 for u ≥ 0.

Proof: log(1+u) ≥ 1 - 1/(1+u) = u/(1+u), so (1+u)·log(1+u) ≥ u. -/
theorem bennettFun_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ bennettFun u := by
  unfold bennettFun
  have h1 : 0 < 1 + u := by linarith
  have h2 : 1 - (1 + u)⁻¹ ≤ log (1 + u) := log_ge_one_sub_inv h1
  have h3 : (1 + u) * (1 - (1 + u)⁻¹) = u := by
    rw [mul_sub, mul_one, mul_inv_cancel₀ (ne_of_gt h1)]; ring
  linarith [mul_le_mul_of_nonneg_left h2 (le_of_lt h1)]

/-- log(1+x) ≤ x for x ≥ 0. From 1+x ≤ exp(x). -/
private lemma log_one_add_le {x : ℝ} (hx : 0 ≤ x) : log (1 + x) ≤ x := by
  calc log (1 + x) ≤ log (exp x) :=
        log_le_log (by linarith : (0 : ℝ) < 1 + x) (by linarith [add_one_le_exp x])
    _ = x := log_exp x

/-! ### Derivative of the Bennett Function -/

/-- The derivative of h at u is log(1+u), for u > -1. -/
lemma hasDerivAt_bennettFun {u : ℝ} (hu : -1 < u) :
    HasDerivAt bennettFun (log (1 + u)) u := by
  unfold bennettFun
  have h1 : (0 : ℝ) < 1 + u := by linarith
  have h1' : (1 : ℝ) + u ≠ 0 := ne_of_gt h1
  have h2 : HasDerivAt (fun x => 1 + x) 1 u := (hasDerivAt_id u).const_add 1
  have h3 : HasDerivAt (fun x => log (1 + x)) (1 / (1 + u)) u :=
    HasDerivAt.log h2 h1'
  have h4 : HasDerivAt (fun x => (1 + x) * log (1 + x))
      (1 * log (1 + u) + (1 + u) * (1 / (1 + u))) u := h2.mul h3
  have h6 : HasDerivAt (fun x => (1 + x) * log (1 + x) - x)
      (1 * log (1 + u) + (1 + u) * (1 / (1 + u)) - 1) u :=
    h4.sub (hasDerivAt_id u)
  have h7 : 1 * log (1 + u) + (1 + u) * (1 / (1 + u)) - 1 = log (1 + u) := by
    rw [one_mul, mul_one_div_cancel h1']; ring
  rw [h7] at h6
  exact h6

/-! ### Monotonicity of h -/

private lemma bennettFun_continuousOn : ContinuousOn bennettFun (Ici 0) := by
  unfold bennettFun
  apply ContinuousOn.sub
  · apply ContinuousOn.mul
    · exact continuousOn_const.add continuousOn_id
    · apply ContinuousOn.log (continuousOn_const.add continuousOn_id)
      intro x hx
      simp only [mem_Ici] at hx
      change 1 + x ≠ 0; linarith
  · exact continuousOn_id

/-- h is monotone increasing on [0,∞).

Proof: h'(u) = log(1+u) ≥ 0 for u ≥ 0, so h is increasing. -/
theorem bennettFun_monotoneOn : MonotoneOn bennettFun (Ici 0) :=
  monotoneOn_of_deriv_nonneg (convex_Ici 0) bennettFun_continuousOn
    (fun x hx => by
      rw [interior_Ici] at hx
      have := hasDerivAt_bennettFun (by linarith [mem_Ioi.mp hx])
      exact this.differentiableAt.differentiableWithinAt)
    (fun x hx => by
      rw [interior_Ici] at hx
      have hx' := mem_Ioi.mp hx
      rw [(hasDerivAt_bennettFun (by linarith)).deriv]
      exact log_nonneg (by linarith : (1 : ℝ) ≤ 1 + x))

/-! ### Bennett ≥ Bernstein Comparison

We prove h(u) ≥ u²/(2(1+u/3)) = 3u²/(2(3+u)) for u ≥ 0.

**Strategy**: Define ψ(u) = h(u) - 3u²/(2(3+u)). We show ψ(0) = 0 and ψ'(u) ≥ 0.
The derivative ψ'(u) = log(1+u) - 3u(6+u)/(2(3+u)²). We show ψ'(0) = 0 and
ψ''(u) = 1/(1+u) - 27/(3+u)³ ≥ 0 (since (3+u)³ ≥ 27(1+u) by nlinarith).

This "double MVT" argument cleanly reduces the analytic inequality to a
polynomial inequality handled by `nlinarith`. -/

/-- The derivative of ψ = h - 3u²/(2(3+u)). Equals log(1+u) - 3u(6+u)/(2(3+u)²). -/
private def psiDeriv (u : ℝ) : ℝ := log (1 + u) - 3 * u * (6 + u) / (2 * (3 + u) ^ 2)

private lemma psiDeriv_zero : psiDeriv 0 = 0 := by
  simp [psiDeriv, log_one]

/-- HasDerivAt for psiDeriv (i.e., ψ'').

We rewrite psiDeriv as log(1+u) + 27/2·(3+u)⁻² - 3/2, differentiate
each piece, and transfer back via `congr_of_eventuallyEq`. -/
private lemma hasDerivAt_psiDeriv {u : ℝ} (hu : 0 ≤ u) :
    HasDerivAt psiDeriv (1 / (1 + u) - 27 / (3 + u) ^ 3) u := by
  have h1 : (1 : ℝ) + u ≠ 0 := by positivity
  have h3 : (3 : ℝ) + u ≠ 0 := by positivity
  -- Derivatives of the three pieces
  have hlog : HasDerivAt (fun x => log (1 + x)) (1 / (1 + u)) u :=
    HasDerivAt.log ((hasDerivAt_id u).const_add 1) h1
  have hinv : HasDerivAt (fun x => (3 + x)⁻¹) (-1 / (3 + u) ^ 2) u := by
    simpa using ((hasDerivAt_id u).const_add 3).inv h3
  have hinvsq : HasDerivAt (fun x => ((3 + x)⁻¹) ^ 2) (-2 / (3 + u) ^ 3) u := by
    convert hinv.pow 2 using 1
    simp only [Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one]; field_simp
  -- Combine: alt(x) = log(1+x) + 27/2·(3+x)⁻² - 3/2
  have halt : HasDerivAt
      (fun x => log (1 + x) + 27 / 2 * ((3 + x)⁻¹) ^ 2 + (-(3 : ℝ) / 2))
      (1 / (1 + u) + 27 / 2 * (-2 / (3 + u) ^ 3) + 0) u :=
    (hlog.add (hinvsq.const_mul (27 / 2))).add (hasDerivAt_const u _)
  rw [show 1 / (1 + u) + 27 / 2 * (-2 / (3 + u) ^ 3) + 0 =
      1 / (1 + u) - 27 / (3 + u) ^ 3 from by ring] at halt
  -- Transfer to psiDeriv via local equality
  apply halt.congr_of_eventuallyEq
  filter_upwards [(isOpen_ne.preimage (continuous_const.add continuous_id)).mem_nhds h3]
    with x (hx : (3 : ℝ) + x ≠ 0)
  unfold psiDeriv; field_simp; ring

/-- ψ''(u) = 1/(1+u) - 27/(3+u)³ ≥ 0 for u ≥ 0.

This reduces to (3+u)³ ≥ 27(1+u), which expands to 9u²+u³ ≥ 0. -/
private lemma psiDeriv_deriv_nonneg {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ 1 / (1 + u) - 27 / (3 + u) ^ 3 := by
  have h1 : (0 : ℝ) < 1 + u := by linarith
  have h3 : (0 : ℝ) < (3 + u) ^ 3 := by positivity
  rw [div_sub_div _ _ (ne_of_gt h1) (ne_of_gt h3)]
  apply div_nonneg
  · -- (3+u)³ - 27(1+u) = 9u² + u³ ≥ 0
    nlinarith [sq_nonneg u]
  · positivity

private lemma psiDeriv_continuousOn : ContinuousOn psiDeriv (Ici 0) := by
  -- Prove continuity of the alternative form log(1+x) + 27/2·(3+x)⁻² - 3/2
  have h_alt_cont : ContinuousOn
      (fun x : ℝ => log (1 + x) + 27 / 2 * ((3 + x)⁻¹) ^ 2 - 3 / 2) (Ici 0) := by
    apply ContinuousOn.sub
    · apply ContinuousOn.add
      · apply ContinuousOn.log (continuousOn_const.add continuousOn_id)
        intro x hx; simp only [Set.mem_Ici] at hx
        change 1 + x ≠ 0; linarith
      · apply ContinuousOn.mul continuousOn_const
        apply ContinuousOn.pow
        apply ContinuousOn.inv₀ (continuousOn_const.add continuousOn_id)
        intro x hx; simp only [Set.mem_Ici] at hx
        change 3 + x ≠ 0; linarith
    · exact continuousOn_const
  apply h_alt_cont.congr
  intro x hx; simp only [Set.mem_Ici] at hx
  unfold psiDeriv
  have h3 : (3 : ℝ) + x ≠ 0 := by linarith
  field_simp; ring

/-- ψ' is monotone increasing on [0,∞) (since ψ'' ≥ 0). -/
private lemma psiDeriv_monotoneOn : MonotoneOn psiDeriv (Ici 0) :=
  monotoneOn_of_deriv_nonneg (convex_Ici 0) psiDeriv_continuousOn
    (fun x hx => by
      rw [interior_Ici] at hx
      exact (hasDerivAt_psiDeriv (mem_Ioi.mp hx).le).differentiableAt.differentiableWithinAt)
    (fun x hx => by
      rw [interior_Ici] at hx
      rw [(hasDerivAt_psiDeriv (mem_Ioi.mp hx).le).deriv]
      exact psiDeriv_deriv_nonneg (mem_Ioi.mp hx).le)

/-- ψ'(u) ≥ 0 for u ≥ 0 (since ψ'(0) = 0 and ψ' is increasing). -/
private lemma psiDeriv_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ psiDeriv u := by
  rw [← psiDeriv_zero]
  exact psiDeriv_monotoneOn (mem_Ici.mpr le_rfl) (mem_Ici.mpr hu) hu

/-! ### ψ itself: h(u) - 3u²/(2(3+u)) ≥ 0 -/

/-- ψ(u) = h(u) - 3u²/(2(3+u)). -/
private def psi (u : ℝ) : ℝ := bennettFun u - 3 * u ^ 2 / (2 * (3 + u))

private lemma psi_zero : psi 0 = 0 := by
  simp [psi, bennettFun, log_one]

/-- HasDerivAt for the rational part 3u²/(2(3+u)). -/
private lemma hasDerivAt_rational {u : ℝ} (hu : 0 ≤ u) :
    HasDerivAt (fun x => 3 * x ^ 2 / (2 * (3 + x)))
      (3 * u * (6 + u) / (2 * (3 + u) ^ 2)) u := by
  have h3 : (3 : ℝ) + u ≠ 0 := by positivity
  have h23 : 2 * (3 + u) ≠ 0 := by positivity
  -- Write as (3/2) · u² · (3+u)⁻¹
  -- u² has derivative 2u
  -- (3+u)⁻¹ has derivative -(3+u)⁻²
  -- Product rule: (3/2)[2u·(3+u)⁻¹ + u²·(-(3+u)⁻²)]
  -- = (3/2)[2u/(3+u) - u²/(3+u)²]
  -- = (3/2)·u·[2(3+u) - u]/(3+u)²
  -- = (3/2)·u·(6+u)/(3+u)²
  -- = 3u(6+u)/(2(3+u)²)
  have hu2 : HasDerivAt (fun x => x ^ 2) (2 * u) u := by
    have := (hasDerivAt_id u).pow 2
    simp only [Nat.cast_ofNat, id_eq] at this
    convert this using 1; ring
  have hinv : HasDerivAt (fun x => (3 + x)⁻¹) (-1 / (3 + u) ^ 2) u := by
    simpa using ((hasDerivAt_id u).const_add 3).inv h3
  -- u² · (3+u)⁻¹
  have hprod : HasDerivAt (fun x => x ^ 2 * (3 + x)⁻¹)
      (2 * u * (3 + u)⁻¹ + u ^ 2 * (-1 / (3 + u) ^ 2)) u :=
    hu2.mul hinv
  -- Scale by 3/2
  have hscale : HasDerivAt (fun x => 3 / 2 * (x ^ 2 * (3 + x)⁻¹))
      (3 / 2 * (2 * u * (3 + u)⁻¹ + u ^ 2 * (-1 / (3 + u) ^ 2))) u :=
    hprod.const_mul (3 / 2)
  -- Show 3u²/(2(3+u)) = 3/2 · (u² · (3+u)⁻¹) locally
  have hfun_eq : (fun x => 3 * x ^ 2 / (2 * (3 + x))) =ᶠ[nhds u]
      (fun x => 3 / 2 * (x ^ 2 * (3 + x)⁻¹)) := by
    filter_upwards [(isOpen_ne.preimage (continuous_const.add continuous_id)).mem_nhds h3]
      with x (hx : (3 : ℝ) + x ≠ 0)
    field_simp
  -- Show derivative values are equal
  have hval_eq : 3 / 2 * (2 * u * (3 + u)⁻¹ + u ^ 2 * (-1 / (3 + u) ^ 2)) =
      3 * u * (6 + u) / (2 * (3 + u) ^ 2) := by
    field_simp; ring
  rw [hval_eq] at hscale
  exact hscale.congr_of_eventuallyEq hfun_eq

/-- HasDerivAt for ψ: ψ'(u) = psiDeriv(u). -/
private lemma hasDerivAt_psi {u : ℝ} (hu : 0 ≤ u) :
    HasDerivAt psi (psiDeriv u) u := by
  unfold psi psiDeriv
  have h_bennett : HasDerivAt bennettFun (log (1 + u)) u :=
    hasDerivAt_bennettFun (by linarith)
  have h_rat : HasDerivAt (fun x => 3 * x ^ 2 / (2 * (3 + x)))
      (3 * u * (6 + u) / (2 * (3 + u) ^ 2)) u := hasDerivAt_rational hu
  exact h_bennett.sub h_rat

private lemma psi_continuousOn : ContinuousOn psi (Ici 0) := by
  unfold psi
  apply ContinuousOn.sub
  · exact bennettFun_continuousOn
  · apply ContinuousOn.div
    · exact (continuousOn_const.mul (continuousOn_id.pow 2))
    · exact continuousOn_const.mul (continuousOn_const.add continuousOn_id)
    · intro x hx; simp only [Set.mem_Ici] at hx
      change 2 * (3 + x) ≠ 0; positivity

/-- ψ is monotone increasing on [0,∞) (since ψ' = psiDeriv ≥ 0). -/
private lemma psi_monotoneOn : MonotoneOn psi (Ici 0) :=
  monotoneOn_of_deriv_nonneg (convex_Ici 0) psi_continuousOn
    (fun x hx => by
      rw [interior_Ici] at hx
      exact (hasDerivAt_psi (mem_Ioi.mp hx).le).differentiableAt.differentiableWithinAt)
    (fun x hx => by
      rw [interior_Ici] at hx
      rw [(hasDerivAt_psi (mem_Ioi.mp hx).le).deriv]
      exact psiDeriv_nonneg (mem_Ioi.mp hx).le)

/-- ψ(u) ≥ 0 for u ≥ 0. -/
private lemma psi_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ psi u := by
  rw [← psi_zero]
  exact psi_monotoneOn (mem_Ici.mpr le_rfl) (mem_Ici.mpr hu) hu

/-! ### Main Comparison Theorem -/

/-- **Bennett ≥ Bernstein**: h(u) ≥ u²/(2(1 + u/3)) for u ≥ 0.

Equivalently, h(u) ≥ 3u²/(2(3+u)). This shows that Bennett's inequality
is always at least as tight as Bernstein's inequality.

The proof uses a "double MVT" argument:
1. Define ψ(u) = h(u) - 3u²/(2(3+u)), show ψ(0) = 0
2. Show ψ'(u) ≥ 0 by showing ψ'(0) = 0 and ψ''(u) ≥ 0
3. ψ''(u) = 1/(1+u) - 27/(3+u)³ ≥ 0 reduces to (3+u)³ ≥ 27(1+u),
   which is 9u² + u³ ≥ 0 — handled by `nlinarith`. -/
theorem bennettFun_ge_bernstein {u : ℝ} (hu : 0 ≤ u) :
    u ^ 2 / (2 * (1 + u / 3)) ≤ bennettFun u := by
  have h3 : (0 : ℝ) < 3 + u := by linarith
  -- u²/(2(1+u/3)) = u²/(2·(3+u)/3) = 3u²/(2(3+u))
  have h_eq : u ^ 2 / (2 * (1 + u / 3)) = 3 * u ^ 2 / (2 * (3 + u)) := by
    field_simp
  rw [h_eq]
  -- This is equivalent to 0 ≤ bennettFun u - 3u²/(2(3+u)) = psi u
  have := psi_nonneg hu
  unfold psi at this
  linarith

/-! ### Bennett Exponent and Tail Bound -/

/-- The **Bennett exponent**: for parameters v (= n*sigma^2) and t,
the Bennett bound gives tail probability at most exp(-v * h(t/v)). -/
def bennettExponent (v t : ℝ) : ℝ := v * bennettFun (t / v)

/-- The **Bernstein exponent** t^2/(2(v + b*t/3)).
When b = 1, this is t^2/(2(v + t/3)), matching Bernstein's inequality
for bounded random variables. -/
def bernsteinExponent (v b t : ℝ) : ℝ := t ^ 2 / (2 * (v + b * t / 3))

/-- **Bennett exponent >= Bernstein exponent**.

For v > 0 (= n*sigma^2), t >= 0:
  v * h(t/v) >= t^2/(2(v + t/3))

This is the key algebraic fact showing Bennett's bound is always at
least as tight as Bernstein's bound.

Proof: Apply `bennettFun_ge_bernstein` with u = t/v, then multiply by v. -/
theorem bennett_exponent_ge_bernstein {v t : ℝ} (hv : 0 < v)
    (ht : 0 ≤ t) :
    t ^ 2 / (2 * (v + t / 3)) ≤ v * bennettFun (t / v) := by
  have hu : 0 ≤ t / v := div_nonneg ht (le_of_lt hv)
  have hge := bennettFun_ge_bernstein hu
  -- Multiply both sides by v > 0
  have hstep : v * ((t / v) ^ 2 / (2 * (1 + t / v / 3))) ≤
      v * bennettFun (t / v) :=
    mul_le_mul_of_nonneg_left hge (le_of_lt hv)
  -- Simplify: v * (t/v)^2/(2(1+t/(3v))) = t^2/(2(v + t/3))
  have h_simplify : v * ((t / v) ^ 2 / (2 * (1 + t / v / 3))) =
      t ^ 2 / (2 * (v + t / 3)) := by
    field_simp
  linarith

/-- **Bennett's tail bound** (algebraic form).

For independent zero-mean random variables with |X_i| <= b a.s. and
(1/n)*sum(Var(X_i)) <= sigma^2, the Bennett bound states:

  P(sum(X_i) >= t) <= exp(-v * h(t/v))

where v = n*sigma^2 and h(u) = (1+u)*log(1+u) - u.

This result records the algebraic consequence: the Bennett exponent
is always at least the Bernstein exponent, so Bennett's bound is
always at least as tight as Bernstein's. -/
theorem bennett_ge_bernstein_bound {v t : ℝ} (hv : 0 < v) (ht : 0 ≤ t) :
    exp (-(v * bennettFun (t / v))) ≤ exp (-(t ^ 2 / (2 * (v + t / 3)))) := by
  apply exp_le_exp.mpr
  linarith [bennett_exponent_ge_bernstein hv ht]

/-- **Bernstein tail bound in Bennett notation**.

Given independent centered bounded random variables (hypotheses matching
`bernstein_sum` from Bernstein.lean), the Bernstein tail bound is:

  P(∑ Xᵢ ≥ t) ≤ exp(-t²/(2V + 2bt/3))

This is the weaker (Bernstein) form of Bennett's inequality. The full
Bennett bound exp(-v·h(t/v)) is strictly tighter by `bennett_ge_bernstein_bound`
but requires a Bennett-specific MGF proof (the exact MGF bound
E[exp(λX)] ≤ exp(σ²/b²·(exp(λb)-λb-1)) rather than the Bernstein MGF). -/
theorem bernstein_tail_bound
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} {N : ℕ} (hN : 0 < N)
    (hX_meas : ∀ i, Measurable (X i))
    (h_indep : ProbabilityTheory.iIndepFun X μ)
    {b : ℝ} (hb : 0 < b)
    (h_bound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ b)
    (h_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    {V : ℝ} (hV : 0 ≤ V)
    (h_var_sum : ∑ i ∈ Finset.range N, ∫ ω, (X i ω) ^ 2 ∂μ ≤ V)
    {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t ≤ ∑ i ∈ Finset.range N, X i ω} ≤
      exp (-t^2 / (2 * V + 2 * b * t / 3)) :=
  bernstein_sum hN hX_meas h_indep hb h_bound h_mean hV h_var_sum ht

end
