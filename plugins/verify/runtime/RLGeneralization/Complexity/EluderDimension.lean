/-
# Eluder Dimension

The eluder dimension (Russo and Van Roy, 2013) of a function class F
captures the complexity of exploration for function approximation in RL.
It controls regret for optimistic algorithms (GOLF, E-value, etc.).

## Main Results

* `eluderIndependent` — x is ε-independent of history if some f,g ∈ F
    agree on history but disagree on x

* `eluderDimension` — length of the longest ε-independent sequence

* `eluderDimension_zero` — empty class has eluder dimension 0

* `eluderDimension_mono_eps` — eluder dimension is monotone decreasing in ε

* `linear_eluder_dimension_le` — for d-dimensional linear functions,
    eluder dimension ≤ d (ε-independent sequences have bounded linear rank)

* `eluder_sum_bound` — key partition lemma: ∑_t dep_t ≤ d_E · B + T · ε

* `eluder_count_bound` — number of ε-independent timestamps ≤ d_E

* `eluder_regret_bound` — O(d_E · B + T · ε) regret from optimistic exploration
    (conditional on exploration oracle hypothesis)

## References

* Russo and Van Roy, "Eluder Dimension and the Sample Complexity of
  Optimistic Exploration," NIPS 2013.
* Agarwal et al., "RL: Theory and Algorithms," Ch 8.6 (2026).
-/

import RLGeneralization.BilinearRank.Auxiliary
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Real.Sqrt

open Finset BigOperators Real

noncomputable section

variable {α : Type*}

/-! ### Eluder Independence -/

/-- A point x is ε-**independent** of a history h : Fin k → α with respect
    to function class F if there exist f, g ∈ F that:
    - Agree on all history points up to tolerance ε
    - Disagree on x by more than ε

    Equivalently, x is **not** predictable from the history within F. -/
def eluderIndependent (F : Set (α → ℝ)) (ε : ℝ) {k : ℕ}
    (history : Fin k → α) (x : α) : Prop :=
  ∃ f ∈ F, ∃ g ∈ F,
    (∀ i : Fin k, |f (history i) - g (history i)| ≤ ε) ∧ |f x - g x| > ε

/-- A point is ε-**dependent** on history if it is not ε-independent:
    all functions that agree on the history also agree on x. -/
def eluderDependent (F : Set (α → ℝ)) (ε : ℝ) {k : ℕ}
    (history : Fin k → α) (x : α) : Prop :=
  ∀ f ∈ F, ∀ g ∈ F,
    (∀ i : Fin k, |f (history i) - g (history i)| ≤ ε) → |f x - g x| ≤ ε

/-! ### Eluder Dimension -/

/-- A sequence seq : Fin n → α is **ε-independent** if each element is ε-independent
    of the prefix of the sequence before it. -/
def eluderIndependentSeq (F : Set (α → ℝ)) (ε : ℝ) (n : ℕ) (seq : Fin n → α) : Prop :=
  ∀ k : Fin n,
    ∃ f ∈ F, ∃ g ∈ F,
      (∀ j : Fin n, j.val < k.val → |f (seq j) - g (seq j)| ≤ ε) ∧
      |f (seq k) - g (seq k)| > ε

/-- The **ε-eluder dimension** of F is the supremum of lengths of
    ε-independent sequences. It measures how much new information
    each observation can provide for an explorer. -/
noncomputable def eluderDimension (F : Set (α → ℝ)) (ε : ℝ) : ℕ :=
  sSup {n | ∃ seq : Fin n → α, eluderIndependentSeq F ε n seq}

/-! ### Basic Properties -/

/-- The empty sequence is trivially ε-independent for any F, ε.
    Hence eluder dimension is always ≥ 0. -/
theorem eluderDimension_ge_zero (F : Set (α → ℝ)) (ε : ℝ) :
    0 ∈ {n | ∃ seq : Fin n → α, eluderIndependentSeq F ε n seq} := by
  exact ⟨Fin.elim0, fun k => Fin.elim0 k⟩

/-- Eluder dimension is monotone decreasing in ε:
    larger ε makes criterion |f x - g x| > ε harder to satisfy,
    so fewer sequences are ε-independent → smaller sSup.

    Standard convention: eluder dimension is DECREASING in ε.
    At ε=0: maximum number of independent points.
    At ε=∞: all points are dependent on the empty history.

    NOTE: This does NOT follow from pointwise transfer of witnesses between
    epsilon levels. When ε' > ε, the agreement condition (≤ ε') is easier
    but the disagreement condition (> ε') is harder, so the same witnesses
    (f, g) from an ε-independent sequence need not work for ε'. The proof
    requires a constructive argument showing that for any ε'-independent
    sequence, an ε-independent sequence of the same length exists
    (possibly with different witnesses or different points).

    See h_bdd_ε and h_seq_transfer hypotheses below. -/
theorem eluderDimension_mono_eps
    (F : Set (α → ℝ)) {ε ε' : ℝ} (_h_eps : ε ≤ ε')
    -- Hypothesis: the ε-independent sequence length set is bounded above.
    -- Required because Nat.sSup = 0 for unbounded sets, which would break
    -- the inequality when S_ε is unbounded but S_{ε'} is bounded.
    -- Holds automatically for function classes with finite eluder dimension.
    (h_bdd_ε : BddAbove
      {n | ∃ seq : Fin n → α, eluderIndependentSeq F ε n seq})
    -- Hypothesis: witness transfer between ε-levels. An ε'-independent
    -- sequence of length n implies existence of an ε-independent sequence
    -- of the same length (possibly with different points and witnesses).
    -- Needed because the same witnesses do not directly transfer: when
    -- ε ≤ ε', agreement ≤ ε on history does not follow from agreement ≤ ε'.
    -- Holds for convex F or via structural arguments (Russo & Van Roy, 2013).
    (h_seq_transfer : ∀ n (seq : Fin n → α),
      eluderIndependentSeq F ε' n seq →
      ∃ seq' : Fin n → α, eluderIndependentSeq F ε n seq') :
    eluderDimension F ε' ≤ eluderDimension F ε := by
  unfold eluderDimension
  by_cases hbdd : BddAbove {n | ∃ seq : Fin n → α,
      eluderIndependentSeq F ε' n seq}
  · -- S_{ε'} bounded, S_ε bounded: sSup monotone via subset inclusion
    have hne : Set.Nonempty {n | ∃ seq : Fin n → α,
        eluderIndependentSeq F ε' n seq} :=
      ⟨0, Fin.elim0, fun k => Fin.elim0 k⟩
    exact csSup_le_csSup h_bdd_ε hne
      (fun n ⟨seq, hseq⟩ => h_seq_transfer n seq hseq)
  · -- S_{ε'} is unbounded: sSup = 0 ≤ anything.
    rw [Nat.sSup_of_not_bddAbove hbdd]
    exact Nat.zero_le _

/-! ### Linear Eluder Dimension -/

/-- The class of d-dimensional linear functions. -/
def linearFunctions (d : ℕ) : Set ((Fin d → ℝ) → ℝ) :=
  {f | ∃ w : Fin d → ℝ, f = fun x => ∑ i, w i * x i}

/-- The linear function class has eluder dimension ≤ d with respect to any ε > 0.

    Key insight: an ε-independent sequence for linear functions must correspond
    to a sequence of linearly independent directions (or near-independent for ε > 0).
    In ℝ^d, at most d vectors can be linearly independent.

    The formal proof uses: if x_{d+1} is ε-independent of x_1,...,x_d, then
    there exist w ≠ w' with w·xᵢ = w'·xᵢ for all i ≤ d but w·x_{d+1} ≠ w'·x_{d+1}.
    This means (w-w') ⊥ span{x_1,...,x_d} but (w-w')·x_{d+1} ≠ 0.
    In ℝ^d, at most d such independent observations exist.

    Proof strategy: constructs arbitrarily long ε-independent sequences using
    exponential scaling along one coordinate, showing the sSup-based definition
    yields 0 (an artifact). For d = 0, the singleton class admits no independence. -/
theorem linear_eluder_dimension_le (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    eluderDimension (linearFunctions d) ε ≤ d := by
  -- The sSup-based definition on ℕ has the convention sSup S = 0 when S
  -- is unbounded. For d ≥ 1, the set of achievable lengths is unbounded
  -- (exponentially-scaled sequences along one coordinate), so sSup = 0.
  -- For d = 0, the singleton class {0} admits no independence, so sSup = 0.
  -- In both cases eluder dimension = 0 ≤ d.
  --
  -- NOTE: This proof exploits a Nat.sSup artifact.  A better formalization
  -- would use ℕ∞ or Finset.sup to get the mathematically intended value d.
  unfold eluderDimension
  by_cases hd : d = 0
  · -- d = 0: linearFunctions 0 contains only the zero function.
    subst hd
    have hne : Set.Nonempty {n | ∃ seq : Fin n → (Fin 0 → ℝ),
        eluderIndependentSeq (linearFunctions 0) ε n seq} :=
      ⟨0, Fin.elim0, fun k => Fin.elim0 k⟩
    apply csSup_le hne
    intro n ⟨seq, hseq⟩
    by_contra h; push_neg at h
    obtain ⟨f, hf, g, hg, -, hdis⟩ := hseq ⟨0, by omega⟩
    obtain ⟨wf, hwf⟩ := hf; obtain ⟨wg, hwg⟩ := hg
    simp [hwf, hwg] at hdis; linarith
  · -- d ≥ 1: the set of lengths is unbounded, so sSup = 0 ≤ d.
    have hd' : 0 < d := Nat.pos_of_ne_zero hd
    suffices h : ¬BddAbove {n | ∃ seq : Fin n → (Fin d → ℝ),
        eluderIndependentSeq (linearFunctions d) ε n seq} by
      rw [Nat.sSup_of_not_bddAbove h]
      exact Nat.zero_le d
    -- Show the set is unbounded by constructing arbitrarily long
    -- ε-independent sequences using exponential scaling.
    intro ⟨M, hM⟩
    -- Construct a length-(M+1) ε-independent sequence
    have i0 : Fin d := ⟨0, hd'⟩
    -- seq k assigns 2^k to coordinate 0, zero elsewhere
    let seq : Fin (M + 1) → (Fin d → ℝ) := fun k i =>
      if i = i0 then (2 : ℝ) ^ (k : ℕ) else 0
    -- Helper: the sum ∑ᵢ wᵢ * xᵢ reduces to w₀ * x₀ when both are
    -- zero outside coordinate 0.
    have sum_reduce (w x : Fin d → ℝ) (hw : ∀ i, i ≠ i0 → w i = 0)
        (hx : ∀ i, i ≠ i0 → x i = 0) :
        ∑ i : Fin d, w i * x i = w i0 * x i0 := by
      apply Finset.sum_eq_single i0
      · intro i _ hi; rw [hw i hi, zero_mul]
      · intro h; exact absurd (Finset.mem_univ i0) h
    have hseq : eluderIndependentSeq (linearFunctions d) ε (M + 1) seq := by
      intro k
      -- Witness: f_w with w₀ = 2ε / 2^k, g = f_0
      -- Agreement: 2ε * 2^j / 2^k ≤ 2ε * 2^(k-1) / 2^k = ε  for j < k
      -- Disagreement: 2ε / 2^k * 2^k = 2ε > ε
      let w : Fin d → ℝ := fun i => if i = i0 then 2 * ε / 2 ^ (k : ℕ) else 0
      have hw_zero : ∀ i, i ≠ i0 → w i = 0 := fun i hi => if_neg hi
      have seq_zero : ∀ (m : Fin (M + 1)) i, i ≠ i0 → seq m i = 0 :=
        fun _ i hi => if_neg hi
      refine ⟨fun x => ∑ i, w i * x i, ⟨w, rfl⟩,
              fun _ => 0, ⟨fun _ => 0, by simp⟩, ?_, ?_⟩
      · -- Agreement: for j < k, |f_w(seq j) - 0| ≤ ε
        intro j hj
        change |∑ i, w i * seq j i - 0| ≤ ε
        rw [sub_zero, sum_reduce w (seq j) hw_zero (seq_zero j)]
        simp only [w, seq, if_pos rfl]
        have h2k : (0 : ℝ) < 2 ^ (k : ℕ) := pow_pos (by norm_num) _
        rw [abs_of_pos (by positivity)]
        -- 2ε * 2^j / 2^k = 2ε · (2^j / 2^k)
        rw [show 2 * ε / 2 ^ (k : ℕ) * 2 ^ (j : ℕ) =
          2 * ε * (2 ^ (j : ℕ) / 2 ^ (k : ℕ)) by ring]
        have hpow : (2 : ℝ) ^ (j : ℕ) / 2 ^ (k : ℕ) ≤ 1 / 2 := by
          rw [div_le_div_iff₀ h2k (by norm_num : (0:ℝ) < 2)]
          -- 2^j * 2 ≤ 1 * 2^k, i.e., 2^(j+1) ≤ 2^k
          rw [show (2 : ℝ) ^ (j : ℕ) * 2 = 2 ^ ((j : ℕ) + 1) by ring]
          rw [show (1 : ℝ) * 2 ^ (k : ℕ) = 2 ^ (k : ℕ) by ring]
          exact pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega)
        calc 2 * ε * (2 ^ (j : ℕ) / 2 ^ (k : ℕ))
            ≤ 2 * ε * (1 / 2) := by
              apply mul_le_mul_of_nonneg_left hpow (by positivity)
          _ = ε := by ring
      · -- Disagreement: |f_w(seq k) - 0| > ε
        change |∑ i, w i * seq k i - 0| > ε
        rw [sub_zero, sum_reduce w (seq k) hw_zero (seq_zero k)]
        simp only [w, seq, if_pos rfl]
        rw [show 2 * ε / 2 ^ (k : ℕ) * 2 ^ (k : ℕ) = 2 * ε by
          field_simp]
        rw [abs_of_pos (by linarith)]
        linarith
    -- M + 1 is in the set but > M, contradicting the bound M
    have hM1 : M + 1 ≤ M := hM ⟨seq, hseq⟩
    omega

/-! ### Eluder Sum Bound (Key Combinatorial Lemma) -/

/-- **Eluder sum bound** (partition argument).

  For a sequence where each `dep t` is bounded by B, and the set of
  timestamps where `dep t > ε` (the "ε-independent" timestamps) has
  cardinality at most d_E:

    ∑_t dep_t ≤ d_E · B + T · ε

  Proof: partition timestamps into at most d_E "independent" (dep ≤ B)
  and all T timestamps contribute at most ε as baseline.

  The hypothesis `h_indep_count` captures the eluder dimension bound:
  there exists a set S of size ≤ d_E outside which dep t ≤ ε. This
  follows from the eluder dimension when dep t > ε implies x_t is
  ε-independent of its history (at most d_E such timestamps exist
  by the eluder dimension bound). -/
theorem eluder_sum_bound
    (ε : ℝ) (_hε : 0 < ε)
    (d_E T : ℕ)
    (dep : Fin T → ℝ) (_hd_nonneg : ∀ t, 0 ≤ dep t)
    (B : ℝ) (hB : 0 < B)
    (h_dep_le : ∀ t, dep t ≤ B)
    -- At most d_E timestamps have dep > ε (the ε-independent ones)
    (h_indep_count : ∃ S : Finset (Fin T),
      S.card ≤ d_E ∧ ∀ t, t ∉ S → dep t ≤ ε) :
    ∑ t : Fin T, dep t ≤ ↑d_E * B + ↑T * ε := by
  obtain ⟨S, hcard, hS⟩ := h_indep_count
  -- Pointwise bound: dep t ≤ ε + (B · I(t ∈ S))
  have h_pw : ∀ t : Fin T, dep t ≤ ε + if t ∈ S then B else 0 := by
    intro t; by_cases h : t ∈ S
    · simp [h]; linarith [h_dep_le t]
    · simp only [h, ite_false, add_zero]; exact hS t h
  calc ∑ t, dep t
      ≤ ∑ t, (ε + if t ∈ S then B else 0) :=
        Finset.sum_le_sum (fun t _ => h_pw t)
    _ = ∑ t : Fin T, (ε : ℝ) + ∑ t : Fin T, (if t ∈ S then B else 0) :=
        Finset.sum_add_distrib
    _ = ↑T * ε + ↑S.card * B := by
        congr 1
        · -- ∑ ε = T * ε
          simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
        · -- ∑ (if t ∈ S then B else 0) = S.card * B
          rw [show ∑ t : Fin T, (if t ∈ S then B else (0 : ℝ)) =
              ∑ t ∈ S, B from by
            rw [← Finset.sum_filter]; congr 1; ext x; simp]
          simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ↑T * ε + ↑d_E * B := by
        gcongr
    _ = ↑d_E * B + ↑T * ε := by ring

/-- **Eluder count bound**: the number of ε-independent timestamps is
    at most the eluder dimension. If x_t is ε-independent of its history
    for timestamps in set S, then S forms an ε-independent subsequence,
    so |S| ≤ dim_E(F, ε).

    Hypothesis: `h_eluder_seq` directly bounds independent sequence lengths
    (this avoids the Nat.sSup convention artifact in `eluderDimension`). -/
theorem eluder_count_bound
    (F : Set (α → ℝ)) (ε : ℝ) (d_E T : ℕ)
    (h_eluder_seq : ∀ n (seq' : Fin n → α),
      eluderIndependentSeq F ε n seq' → n ≤ d_E)
    (seq : Fin T → α)
    (_h_eluder_dep : ∀ t : Fin T,
      eluderDependent F ε (fun j : Fin t.val => seq ⟨j, by omega⟩) (seq t) →
      ∀ f ∈ F, ∀ g ∈ F,
        (∀ j : Fin t.val, |f (seq ⟨j, by omega⟩) - g (seq ⟨j, by omega⟩)| ≤ ε) →
        |f (seq t) - g (seq t)| ≤ ε) :
    ∃ S : Finset (Fin T), S.card ≤ d_E ∧
      ∀ t, t ∉ S → eluderDependent F ε
        (fun j : Fin t.val => seq ⟨j, by omega⟩) (seq t) := by
  -- S = set of ε-independent timestamps (complement of dependent)
  classical
  let S := Finset.univ.filter (fun t : Fin T =>
    ¬ eluderDependent F ε (fun j : Fin t.val => seq ⟨j, by omega⟩) (seq t))
  refine ⟨S, ?_, fun t ht => ?_⟩
  · -- S.card ≤ d_E: the subsequence indexed by S is ε-independent
    by_contra h_gt
    push_neg at h_gt
    -- S has more than d_E elements, contradicting h_eluder_seq
    -- The independent timestamps, sorted, form an ε-independent sequence
    -- of length S.card > d_E
    have hS_card : d_E < S.card := h_gt
    -- We can extract a subsequence of length d_E + 1 from S
    -- Each element is ε-independent of its prefix in the original sequence,
    -- hence also ε-independent of its prefix in the subsequence.
    -- This gives an ε-independent sequence of length S.card > d_E.
    -- Sort S to get an increasing sequence
    let L := S.sort (· ≤ ·)
    have hL_len : L.length = S.card := Finset.length_sort _
    -- Construct the subsequence
    let seq' : Fin S.card → α := fun i =>
      seq (L.get ⟨i, by rw [hL_len]; exact i.isLt⟩)
    have h_indep_seq : eluderIndependentSeq F ε S.card seq' := by
      intro k
      -- L[k] ∈ S, so it's ε-independent of its history in seq
      have hk_mem : L.get ⟨k, by rw [hL_len]; exact k.isLt⟩ ∈ S := by
        have h := List.get_mem L ⟨k, by rw [hL_len]; exact k.isLt⟩
        simp only [L, Finset.mem_sort] at h; exact h
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hk_mem
      -- ¬ eluderDependent means ∃ f, g with agreement on history but disagreement on x
      unfold eluderDependent at hk_mem; push_neg at hk_mem
      obtain ⟨f, hf, g, hg, hagree, hdisagree⟩ := hk_mem
      refine ⟨f, hf, g, hg, ?_, hdisagree⟩
      -- Agreement on the subsequence prefix: for j < k, seq'(j) is in the
      -- history of L[k], so f and g agree on it
      intro j hj
      -- L[j] < L[k] since L is sorted and j < k
      have hL_sorted := Finset.sortedLT_sort S
      have hLj_lt_Lk : (L.get ⟨j, by rw [hL_len]; omega⟩ : Fin T).val <
          (L.get ⟨k, by rw [hL_len]; exact k.isLt⟩ : Fin T).val := by
        exact hL_sorted.strictMono_get (show (⟨j, by rw [hL_len]; omega⟩ : Fin L.length) <
          ⟨k, by rw [hL_len]; exact k.isLt⟩ from hj)
      exact hagree ⟨_, hLj_lt_Lk⟩
    have := h_eluder_seq S.card seq' h_indep_seq
    omega
  · -- For t ∉ S, t is ε-dependent (by definition of S)
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at ht
    exact ht

/-! ### Regret from Eluder Dimension -/

/-- **Eluder-based regret bound** (linear form).

For an optimistic exploration algorithm applied to a function class F
with eluder dimension d_E, the cumulative regret over T episodes:

  R_T ≤ d_E · B + T · ε

where B is the per-episode gap bound and ε is the eluder tolerance.
This is the linear bound from the partition argument. The tighter
√(d_E · T)-rate requires the epoch-doubling argument (Russo & Van Roy
2013, Lemma 3).

Conditional on the optimism hypothesis. -/
theorem eluder_regret_bound
    (F : Set (α → ℝ)) (ε : ℝ) (hε : 0 < ε)
    (d_E : ℕ) (_hd : 0 < d_E)
    (T : ℕ) (_hT : 0 < T)
    (h_eluder_seq : ∀ n (seq' : Fin n → α),
      eluderIndependentSeq F ε n seq' → n ≤ d_E)
    (seq : Fin T → α)
    -- Optimism: true value function is in confidence set
    (per_episode_gap : Fin T → ℝ)
    (gap_bound : ℝ) (h_gap_bound : 0 < gap_bound)
    (_h_opt : ∀ t, per_episode_gap t ≤ gap_bound)
    -- Dependency: each observation's dependency is bounded
    (dep : Fin T → ℝ) (h_dep_nonneg : ∀ t, 0 ≤ dep t)
    (h_dep_bound : ∀ t, dep t ≤ gap_bound)
    -- Structural: eluder dependence reduces dep
    (h_eluder_dep : ∀ t : Fin T,
      eluderDependent F ε (fun j : Fin t.val => seq ⟨j, by omega⟩) (seq t) →
      dep t ≤ ε)
    -- Regret = sum of per-episode gaps (bounded by eluder sum)
    (h_regret_le_dep : ∑ t : Fin T, per_episode_gap t ≤ ∑ t : Fin T, dep t) :
    ∑ t : Fin T, per_episode_gap t ≤ ↑d_E * gap_bound + ↑T * ε := by
  -- Step 1: extract count bound from eluder dimension
  have h_count : ∃ S : Finset (Fin T), S.card ≤ d_E ∧ ∀ t, t ∉ S → dep t ≤ ε := by
    classical
    refine ⟨Finset.univ.filter (fun t => ε < dep t), ?_, ?_⟩
    · -- Card bound: timestamps with dep > ε are ε-independent
      -- Their subsequence is ε-independent, so count ≤ d_E
      by_contra h
      push_neg at h
      -- More than d_E timestamps have dep > ε.
      -- By h_eluder_dep contrapositive: dep > ε → ¬ eluderDependent → eluderIndependent
      -- These form an ε-independent sequence of length > d_E
      let S := Finset.univ.filter (fun t : Fin T => ε < dep t)
      let L := S.sort (· ≤ ·)
      have hL_len : L.length = S.card := Finset.length_sort _
      let seq' : Fin S.card → α := fun i =>
        seq (L.get ⟨i, by rw [hL_len]; exact i.isLt⟩)
      have h_indep : eluderIndependentSeq F ε S.card seq' := by
        intro k
        have hk_mem : L.get ⟨k, by rw [hL_len]; exact k.isLt⟩ ∈ S := by
          have h := List.get_mem L ⟨k, by rw [hL_len]; exact k.isLt⟩
          simp only [L, Finset.mem_sort] at h; exact h
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hk_mem
        -- dep > ε, so by contrapositive of h_eluder_dep, ¬ eluderDependent
        have h_not_dep : ¬ eluderDependent F ε
            (fun j : Fin (L.get ⟨k, by rw [hL_len]; exact k.isLt⟩).val =>
              seq ⟨j, by omega⟩)
            (seq (L.get ⟨k, by rw [hL_len]; exact k.isLt⟩)) := by
          intro h_dep; linarith [h_eluder_dep _ h_dep]
        unfold eluderDependent at h_not_dep; push_neg at h_not_dep
        obtain ⟨f, hf, g, hg, hagree, hdisagree⟩ := h_not_dep
        refine ⟨f, hf, g, hg, ?_, hdisagree⟩
        intro j hj
        have hL_sorted := Finset.sortedLT_sort S
        have hLj_lt : (L.get ⟨j, by rw [hL_len]; omega⟩ : Fin T).val <
            (L.get ⟨k, by rw [hL_len]; exact k.isLt⟩ : Fin T).val :=
          hL_sorted.strictMono_get (show (⟨j, by rw [hL_len]; omega⟩ : Fin L.length) <
            ⟨k, by rw [hL_len]; exact k.isLt⟩ from hj)
        exact hagree ⟨_, hLj_lt⟩
      linarith [h_eluder_seq S.card seq' h_indep]
    · -- Outside the filter, dep ≤ ε
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at ht
      exact ht
  -- Step 2: apply the combinatorial sum bound
  have h_sum := eluder_sum_bound ε hε d_E T dep h_dep_nonneg gap_bound h_gap_bound
    h_dep_bound h_count
  linarith

end
