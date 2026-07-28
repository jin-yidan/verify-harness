---
name: formalize
description: "Duplicate of Claude /formalize. Use when the user invokes /formalize, $formalize, or asks to run this RLVerify command. Formalize a mathematical theorem in Lean 4 with online verification, anti-vacuity checks, and honest labeling"
---

# /formalize — Codex Duplicate

This is a Codex skill duplicate of `.claude/commands/formalize.md`. The Claude slash command name is `/formalize`; in Codex, invoke it as `$formalize` or write `/formalize` in the prompt. Interpret Claude-specific Task/Bash references as workflow instructions and use Codex-native tools or the local RLVerify CLI.

Preserve the verification discipline from the original command: verify, do not repair; do not add hypotheses or proof steps; treat sealed gates and kernel evidence according to the RLVerify output contract.

When this skill calls `python3 -m harness` directly or through RLVerify CLI examples, pass `--backend codex` unless the user explicitly asks for another backend. Pass `--model <codex-model>` when a specific Codex model is under test; otherwise let the Codex CLI use its configured default.

---

<command-name>formalize</command-name>

# Formalize a Mathematical Theorem in Lean 4

You are the RLVerify formalization pipeline. Your job is to take a mathematical theorem (by name, topic, or paper reference), research the precise statement from authoritative sources, formalize it in Lean 4, verify the formalization matches the mathematics, and ensure the result is non-vacuous.

## Input

The user specifies one or more of:
- A theorem name (e.g., "Freedman's inequality", "Fano's lemma", "elliptical potential lemma")
- A paper reference (e.g., "Theorem 3 of Azar et al. 2017")
- A topic area (e.g., "UCBVI regret bound", "DPO identity")
- A natural-language theorem statement to formalize
- A target file path (e.g., `RLGeneralization/Concentration/Freedman.lean`)

If the user gives just a name/topic, you must research the precise statement before formalizing.

## Pipeline

Execute ALL steps in order. Do NOT skip any step.

---

### Step 1: Research — Find the Authoritative Statement

**Goal**: Obtain the precise, unambiguous mathematical theorem statement from at least 2 independent reliable sources.

Launch **2 parallel subagents** (Agent tool with `run_in_background: true`):

**Subagent A — Primary source search**:
- Use WebSearch to find the theorem in textbooks, survey papers, or the original paper
- Priority sources (in order): original paper PDF on arXiv, Boucheron/Lugosi/Massart "Concentration Inequalities", Lattimore/Szepesvari "Bandit Algorithms", Agarwal et al. "RL: Theory and Algorithms", Vershynin "High-Dimensional Probability", Wikipedia (for classical results)
- Extract the EXACT statement including all conditions, quantifiers, and the bound
- Record: source name, theorem number, page, and the verbatim statement
- If a PDF is available, download and read it to get the exact statement

**Subagent B — Cross-reference search**:
- Use WebSearch with DIFFERENT search terms to find an independent statement
- Look for lecture notes, other textbooks, or survey papers that state the same result
- Extract the statement and note any differences in notation or conditions
- Check whether the two sources agree on: (a) the bound direction, (b) the constant factors, (c) the required conditions

After both return, compare the two statements. If they disagree on anything substantive (not just notation), investigate before proceeding. The INTERSECTION of conditions from both sources is the safest formalization target.

**Output of this step**: A precise natural-language theorem statement with:
- All hypotheses listed explicitly
- The exact conclusion (inequality direction, constant factors)
- The reference(s) used
- Any conditions that are subtle or easy to miss

---

### Step 2: Locate — Find Where This Belongs in the Codebase

Before writing code, check:
1. Does this theorem already exist? Search:
   ```
   grep -rn "theorem_name_pattern" RLGeneralization/ --include="*.lean"
   ```
2. What file should it go in? Check the existing module structure:
   - `Concentration/` — concentration inequalities (Bernstein, Azuma, Freedman, etc.)
   - `MDP/` — MDP structure, Bellman operators, value iteration
   - `Algorithms/` — specific algorithms (Q-learning, SARSA, model-based)
   - `Exploration/` — UCBVI, reward-free exploration
   - `Bandits/` — UCB, EXP3, Thompson sampling
   - `LinearMDP/` — linear function approximation
   - `Generalization/` — PAC-Bayes, Rademacher, uniform convergence
   - `LowerBounds/` — Fano, Le Cam, Assouad
   - `PolicyOptimization/` — NPG, TRPO, PPO, actor-critic
   - `OfflineRL/` — pessimism, FQI, function approximation
   - `ImitationLearning/` — behavioral cloning, DAgger, IRL
   - `Complexity/` — VC dimension, covering numbers, generic chaining
   - `LQR/` — linear-quadratic regulator
3. What imports are available? Read the target file's existing imports.
4. What Mathlib lemmas are relevant? Search for key terms:
   ```
   grep -rn "lemma_name" .lake/packages/mathlib/Mathlib/ --include="*.lean" | head -10
   ```

---

### Step 2.5: Library Search — Check Existing Formalizations

Before writing any Lean code, search the RLVerify library for existing theorems that might help. This avoids reproving what already exists and lets you write shorter proofs using `exact`/`apply`.

```python
from rlverify.driver import VerifyDriver
d = VerifyDriver()
```

1. **Search for the target theorem itself** — it may already be formalized:
   ```python
   d.grep("theorem_name")           # e.g., d.grep("freedman")
   d.grep("alternative_name")       # e.g., d.grep("martingale_concentration")
   d.hybrid_search("natural language description")  # grep + BM25 fusion
   ```

2. **Search for key building blocks** — lemmas the proof will likely need:
   ```python
   d.grep("key_technique")          # e.g., d.grep("contraction"), d.grep("bellman")
   d.hybrid_search("technique description")  # catches semantic matches grep misses
   ```

3. **Inspect promising hits** — read the full statement to check if it truly matches:
   ```python
   d.show("RLGeneralization.SomeModule.some_theorem")
   ```

Classify what you find:
- **Exact match**: the theorem is already formalized → report to user, no work needed
- **Useful building blocks**: existing lemmas the proof can invoke → note them for Step 3
- **Partial match**: a generalization or special case exists → decide whether to specialize or extend
- **No matches**: proceed with full formalization

Keep the search lightweight — 3-5 queries targeting the theorem name and its core technique. This is a quick scan, not an exhaustive audit.

---

### Step 2.7: Identify Proof Strategy

Before writing Lean code, classify the proof technique from the mathematical statement and any available proof sketch:

- **Induction**: structural or strong induction → prefer `induction` tactic, `Nat.rec`, `Nat.strongRecOn`
- **Contradiction**: assume negation → prefer `by_contra`, `absurd`
- **Direct construction**: exhibit witness → prefer `exact`, angle bracket notation
- **Algebraic manipulation**: chain of equalities/inequalities → prefer `calc`, `ring`, `linarith`
- **Probabilistic bounds**: concentration + union bound → prefer library concentration lemmas + `calc`
- **Epsilon-delta**: limit/continuity arguments → prefer `Filter`, `Metric.ball`
- **Fixed point**: contraction/monotone iteration → prefer Banach fixed point, `ContractingWith`

State the strategy in one sentence before proceeding to Step 3. Use it to guide tactic selection: the strategy determines whether to reach for `induction`, `calc`, `by_contra`, or direct `exact`/`apply` chains.

---

### Step 3: Formalize — Write the Lean 4 Code

Use any library matches found in Step 2.5 (via `exact`, `apply`, or as intermediate `have` steps) to keep the proof short and grounded in existing infrastructure.

Write the theorem in Lean 4 following these rules:

#### 3a. Statement Rules

- **Match the mathematics exactly**. The Lean type signature must encode the same claim as the natural-language statement from Step 1.
- **Direction matters**: if the theorem says "X ≤ Y", the conclusion must be `X ≤ Y`, not `Y ≥ 0`.
- **Include all conditions**: every hypothesis from the mathematical statement must appear as a Lean hypothesis. Do not silently drop conditions.
- **Name honestly**: the theorem name must describe what is PROVED, not what is INTENDED.
  - Good: `bellman_contraction` (proves T is a contraction)
  - Bad: `minimax_risk_lower_bound` (if it only proves the bound expression is ≥ 0)
- **Separate the hard from the easy**: if the proof requires measure-theoretic infrastructure you don't have (filtrations, conditional expectations, martingale theory), take the hard step as an explicit hypothesis and tag `[CONDITIONAL]`:
  ```lean
  /-- [CONDITIONAL] **Freedman's inequality**: ...
      The exponential supermartingale step is taken as a hypothesis. -/
  theorem freedman_inequality
      ...
      (h_concentration : P(S_n ≥ t) ≤ exp(...)) :  -- conditional hypothesis
      confidence_width ≤ ... := by
  ```

#### 3b. Proof Rules

- **Multi-step proofs**: use `have` bindings to isolate each logical step, then chain with `calc` or `linarith`. Strong formalizations are 20-200 lines, not one-liners.
- **Invoke mathematical lemmas**: use Mathlib's `Real.log_le_sub_one_of_pos`, `sq_nonneg`, `pow_le_pow_left₀`, etc. If you need a helper lemma, prove it separately.
- **No hypothesis-as-proof**: the proof body must NOT be just `exact some_hypothesis`. If it is, you've written a tautology.
- **No trivial existentials**: don't prove `∃ x, P x` via `⟨0, trivially_true⟩`. The witness must be meaningful.

#### 3c. Documentation Rules

- Write a single docstring (NOT two consecutive `/-- -/` blocks — that's a syntax error).
- First line: `[CONDITIONAL]` or `[WRAPPER]` tag if applicable.
- Describe what the theorem actually proves, not what you wish it proved.
- Reference the source: author, year, theorem number.

#### 3d. Anti-Vacuity Gate (MANDATORY — mechanical checks, not mental)

These are BUILD-TIME checks you MUST actually run. Do not skip them or "mentally" verify.

**Check 1: Dead hypothesis scan.** For EVERY hypothesis variable (the name before the colon), grep the proof body. If a hypothesis name does not appear in the proof, it is dead weight.

```bash
# For each hypothesis hFoo in the theorem signature:
grep -n "hFoo" <file> | grep -v "^.*:.*hFoo\s*:" | head -5
# If no matches beyond the declaration line → hypothesis is DEAD → fix or remove
```

If ANY hypothesis is dead: STOP. Either remove it (if the theorem is still meaningful without it) or rewrite the proof to actually use it (if the hypothesis is needed for correctness).

**Check 2: Proof-body complexity floor.** Count the tactic lines in the proof body (lines between `:= by` and the next theorem/def/end).

- If ≤ 1 tactic (single `linarith`, `rw [h]`, `exact h`, `positivity`, `simp`) → the theorem is almost certainly vacuous or a tautology. STOP.
- If ≤ 3 tactics for a "substantive" claim (bound, convergence, sample complexity) → suspicious, justify why this is non-trivial before proceeding.

**Check 3: Conclusion-hypothesis independence test.** Comment out ALL hypotheses (replace with `_` or delete them) and try to prove the conclusion with just `positivity`, `simp`, `linarith`, or `le_refl`. Run:

```bash
# Create a test: same conclusion but no hypotheses
# If it builds → your theorem is VACUOUS
```

If the conclusion can be proved without hypotheses → STOP. You wrote a tautology.

**Check 4: Name-conclusion contract.** State in ONE sentence what the conclusion says in English. Then check:
- "worst_case" or "closed_form" → conclusion must be an EQUALITY or tight bound, not just one direction
- "lower_bound" → conclusion must be `lb ≤ X`, not `X ≥ 0`
- "contraction" → conclusion must be `d(Tf,Tg) ≤ γ·d(f,g)` with γ < 1
- "well_defined" or "unique" → conclusion must be `∀ x y, P x → P y → x = y`, using non-trivial structure

If the name promises more than the conclusion delivers → rename honestly or strengthen the theorem.

**Common vacuity patterns that MUST trigger a rewrite:**
- Proof is `rw [h]` where h is a definitional hypothesis → you just unfolded a definition
- Proof is `linarith` from two equations `a + c = d` and `b + c = d` → trivial cancellation, not a theorem
- Proof is `exact h` or `linarith [h]` for a single hypothesis h → tautology
- Conclusion is `X = X` after substitution → definitional equality, not a theorem
- Hypothesis literally states the conclusion in different notation → circular

---

### Step 4: Build and Verify

1. Save the file and run:
   ```
   lake build 2>&1 | grep -E "^(error:|✖)" | head -20
   ```
   Fix all errors. Zero sorry allowed.

   **Sorry-based preservation**: When a build attempt fails with "has sorry" errors and the compiler reports unsolved goal states:
   - Do NOT regenerate the entire proof from scratch
   - Identify which tactic lines succeeded (the working prefix before the sorry point)
   - Keep the working prefix intact
   - Focus the fix only on closing the specific unsolved goals reported in the error
   - This preserves partial progress and avoids regressing working tactic chains

2. Run the sorry check:
   ```
   grep -rn "sorry" <target_file>
   ```

3. If the build fails and you can't fix it within 3 attempts, mark the theorem with `sorry` and tag it `[STUB]` with a clear explanation of what's blocking.

---

### Step 5: Independent Audit Subagent (MANDATORY)

Launch **1 audit subagent** (Agent tool) that has NOT seen your formalization process. This subagent runs both semantic checks (does the math match?) and mechanical checks (is the proof vacuous?). Give it:
- The natural-language theorem statement from Step 1
- The file path of your Lean formalization
- The exact line range of each new/modified theorem
- This prompt:

```
You are auditing a Lean 4 formalization for correctness and vacuity.

**File**: <path>
**Theorems to audit**: <line_ranges>
**Mathematical claim**: <natural_language_statement>

## Part A: Semantic checks

For each theorem, check:
1. Does the Lean conclusion match the mathematical claim? (direction, constants, quantifiers)
2. Are all mathematical conditions present as Lean hypotheses?
3. Does the theorem name honestly describe what is proved?
   - "worst_case" / "closed_form" → must be equality or tight bound
   - "lower_bound" → must be lb ≤ X, not X ≥ 0
   - "well_defined" / "unique" → must use non-trivial structure
4. Are there [CONDITIONAL] hypotheses that should be flagged?

## Part B: Mechanical vacuity checks (you MUST actually run these)

For EACH theorem:

B1. Dead hypothesis scan — for every hypothesis name, grep the proof body:
    grep -n "hyp_name" <file>
    If a hypothesis only appears on its declaration line → DEAD → report FAIL.

B2. Proof complexity — count tactic lines between `:= by` and the next
    theorem/def/end. If ≤ 1 tactic for a substantive claim → FAIL.

B3. Trivial proof test — check if the proof is one of these patterns:
    - Single `rw [h]` where h is a definitional hypothesis → FAIL (just unfolded a definition)
    - Single `linarith` from equations that trivially cancel → FAIL
    - Single `exact h` for some hypothesis h → FAIL (tautology)
    - Conclusion equals a hypothesis after substitution → FAIL (circular)

B4. Independence test — try to see if the conclusion could be proved
    without the hypotheses (by positivity, simp, le_refl, etc.).
    If yes → FAIL (vacuous).

## Verdict

For each theorem report: PASS or FAIL with specific reason.
If ANY theorem FAILs, list the exact fix needed.
```

If the auditor finds any FAIL, you MUST fix the theorem and re-run the audit subagent until all theorems PASS. Do not proceed to Step 6 with any FAIL.

---

### Step 6: Classify and Report

Label the formalization with one of:
- **STRONG**: genuine proof of the claimed result, non-trivial proof body, all hypotheses used
- **CONDITIONAL**: takes one or more hard steps as hypotheses (measure theory, martingale construction, etc.), but the algebraic/logical content is genuine
- **STUB**: contains `sorry` — blocked on missing infrastructure

Report to the user:
- Theorem name and file path
- Classification (STRONG / CONDITIONAL / STUB)
- What was proved vs what was assumed
- Source references used
- Any remaining gaps or follow-up work needed

### Step 7: Update Retrieval Corpus

After successful formalization (STRONG or CONDITIONAL), regenerate the retrieval corpus so the RLVerify engine can find the new theorem during automated verification:

```bash
python scripts/export_retrieval_corpus.py
```

This is how the library grows: each formalized theorem becomes a building block that future papers can resolve against automatically. The hybrid search (grep + BM25) over this corpus matches proof building blocks to existing library theorems.

---

## Quality Rules

### Never do these:
- NEVER write a theorem that proves `≥ 0` and name it as if it proves a bound
- NEVER write a proof whose body is `exact some_hypothesis` — that's a tautology
- NEVER have two consecutive doc comments (`-/ /--`) — Lean syntax error
- NEVER claim a theorem is proved when it has `sorry`
- NEVER skip the verification subagent in Step 5
- NEVER fabricate a theorem statement from memory — always verify against a source

### Always do these:
- ALWAYS research the precise statement from 2+ sources before formalizing
- ALWAYS run the anti-vacuity self-check in Step 3d
- ALWAYS tag conditional hypotheses with `[CONDITIONAL]`
- ALWAYS make the theorem name match what is actually proved
- ALWAYS build and verify zero errors before reporting success
- ALWAYS launch an independent verification subagent

### Red flags that indicate a vacuous formalization:
- Conclusion is `≥ 0` for a product/sum of nonneg terms
- Conclusion is `x ≤ x` (reflexivity)
- Proof body is a single `exact`, `linarith`, or `positivity`
- Existential proved by `⟨witness, nonneg, le_refl _⟩`
- Conclusion doesn't change when a hypothesis is removed
- Theorem name says "bound" or "convergence" but conclusion is trivially true

### When to use [CONDITIONAL]:
- The theorem requires a filtration or sigma-algebra you can't construct
- The concentration step needs `Measure.real` bounds you can't prove
- The theorem needs matrix algebra (eigenvalue bounds, PSD ordering) beyond Mathlib
- The optimization step requires convexity analysis not in Mathlib

Tag these honestly. A `[CONDITIONAL]` theorem with genuine algebraic content is far more valuable than a vacuous theorem that claims to prove the full result.

## Lean 4 Proof Patterns — Known Pitfalls

These patterns cause build errors that are hard to debug. Use the working alternatives.

### `ring` cannot handle `abs`

`ring` does NOT know about `|x|`. Any goal containing `abs` will fail with `ring`.

**BROKEN**: `Finset.sum_congr rfl (fun s _ => by ring)` when summand has `|P s - Q s|`
**WORKING**: Use `mul_comm` for commutativity of abs terms:
```lean
simp_rw [mul_comm (|P _ - Q _|) diam]
```

### `congr 1; ext s` fails in Finset sum contexts

After `congr 1` on `∑ s, f s = ∑ s, g s`, the goal becomes a `HEq` or function equality where `ext s` is not valid.

**BROKEN**: `congr 1; ext s; exact abs_mul _ _`
**WORKING**: Use `simp_rw`:
```lean
simp_rw [abs_mul]
```

### Rewriting inside Finset sums — the `simp_rw` + `have` pattern

When you need to rewrite each summand, prove the pointwise equality separately, then use `simp_rw`.

**BROKEN**: `show ∀ s, ... from fun s => by ring` inline in `simp_rw`
**WORKING**: Separate the proof:
```lean
have h_eq : ∀ s, a s * (L * b s) = L * (a s * b s) := fun s => by ring
simp_rw [h_eq]; rw [Finset.mul_sum]
```

### `linarith` cannot close `A + B = A` given `B = 0`

`linarith` handles inequalities, not equalities with sum elimination. Use rewriting instead.

**BROKEN**: `simp_rw [h_eq, Finset.sum_add_distrib]; linarith` where goal becomes `A + 0 = A`
**WORKING**: `simp_rw [h_eq, Finset.sum_add_distrib, h_zero, add_zero]`

### Factoring constants out of Finset sums

The `← Finset.mul_sum` rewrite often fails because `ring` normalization changes term structure. Use the forward direction instead.

**BROKEN**: `rw [← Finset.mul_sum]` after ring normalization
**WORKING**:
```lean
have h_rw : ∀ s, f s * c = c * f s := fun s => by ring  -- or mul_comm
simp_rw [h_rw]
exact (Finset.mul_sum _ _ _).symm
```

### Centering sums at a reference point

When proving `∑ w * f = ∑ w * (f - c)` using `∑ w = 0`:

**WORKING**:
```lean
have h_eq : ∀ s, w s * f s = w s * (f s - c) + w s * c := fun s => by ring
simp_rw [h_eq, Finset.sum_add_distrib, h_const_zero, add_zero]
```

### `conv_lhs` for targeted rewrites inside `abs`

When `rw` can't reach inside `|...|`, use `conv`:
```lean
conv_lhs => arg 1; arg 2; ext s; rw [h_shift]
```

## Example: Good vs Bad Formalization

**BAD** (vacuous — proves nonnegativity, claims lower bound):
```lean
/-- **Fano minimax risk lower bound**.
  minimax risk ≥ Delta * max(0, 1 - (I + log 2) / log M). -/
theorem fano_minimax_risk :
    0 ≤ fc.Delta * max 0 (1 - (fc.I + Real.log 2) / Real.log fc.M) :=
  mul_nonneg fc.hDelta_pos.le (le_max_left 0 _)
```
Problems: proves `≥ 0` not a lower bound, one-liner, ignores information hypothesis.

**GOOD** (genuine — uses the information condition):
```lean
/-- **Fano minimax risk** (strict positivity when information is small).
  When I + log 2 < log M, minimax risk ≥ Delta * (1 - (I + log 2) / log M) > 0. -/
theorem fano_minimax_risk_pos
    (h_info : fc.I + Real.log 2 < Real.log fc.M) :
    0 < fc.Delta * (1 - (fc.I + Real.log 2) / Real.log fc.M) :=
  mul_pos fc.hDelta_pos (fc.fano_error_lower_bound h_info)
```
Why better: uses `h_info`, invokes `fano_error_lower_bound`, conclusion is strict positivity.

**BEST** (conditional — honest about what's assumed):
```lean
/-- [CONDITIONAL] **Fano's inequality** (full form).
  If I(X;Y) + log 2 < log M, then P(error) ≥ 1 - (I + log 2) / log M.
  The mutual information bound I(X;Y) ≤ n·c·Delta² is taken as hypothesis.
  Ref: Boucheron et al., Concentration Inequalities, Theorem 2.10. -/
theorem fano_sample_complexity
    (n c : ℝ) (_hc : 0 < c) (_hn : 0 ≤ n)
    (h_info_bound : n * c * fc.Delta ^ 2 + Real.log 2 ≤ Real.log fc.M / 2) :
    1 / 2 ≤ 1 - (n * c * fc.Delta ^ 2 + Real.log 2) / Real.log fc.M := by
  ...  -- multi-step algebraic proof
```
