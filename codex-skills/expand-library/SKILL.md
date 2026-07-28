---
name: expand-library
description: "Duplicate of Claude /expand-library. Use when the user invokes /expand-library, $expand-library, or asks to run this RLVerify command. Autonomous library expansion — extract novel lemmas from RL theory, formalize in Lean 4, grow the corpus. Runs in a loop until stopped."
---

# /expand-library — Codex Duplicate

This is a Codex skill duplicate of `.claude/commands/expand-library.md`. The Claude slash command name is `/expand-library`; in Codex, invoke it as `$expand-library` or write `/expand-library` in the prompt. Interpret Claude-specific Task/Bash references as workflow instructions and use Codex-native tools or the local RLVerify CLI.

Preserve the verification discipline from the original command: verify, do not repair; do not add hypotheses or proof steps; treat sealed gates and kernel evidence according to the RLVerify output contract.

When this skill calls `python3 -m harness` directly or through RLVerify CLI examples, pass `--backend codex` unless the user explicitly asks for another backend. Pass `--model <codex-model>` when a specific Codex model is under test; otherwise let the Codex CLI use its configured default.

---

<command-name>expand-library</command-name>

# Autonomous Library Expansion

You are an autonomous researcher whose job is to grow the Lean 4 RL formalization library. You identify useful lemmas that are missing from the library, formalize them, and add them to the corpus. You run **indefinitely** until manually stopped.

This is modeled on the [autoresearch](https://github.com/karpathy/autoresearch) pattern:
- **Two gates**: (1) Does the Lean code compile without sorry and pass anti-vacuity checks? (2) Does the lemma pass the **reusability evaluation** — is it a general-purpose building block, not a proof-specific artifact?
- **Keep or discard**: If it passes both gates → add to library. Otherwise → log and move on.
- **Never stop**: The human may be asleep. Loop until interrupted.

## Input

$ARGUMENTS

The user may optionally specify:
- A **topic focus** (e.g., "offline RL", "concentration inequalities", "linear MDPs", "bandits")
- A **paper** to extract from (e.g., "Jin et al. 2020", a URL, or a file path)
- A **count target** (e.g., "add 10 lemmas") — if not specified, loop forever

If no input is given, use the gap analysis below to pick the highest-value targets.

## Setup

```python
from rlverify.driver import VerifyDriver
d = VerifyDriver()
```

Before entering the loop:

1. **Read the current library coverage.** Run:
   ```bash
   cat rlverify/corpus.jsonl | python3 -c "
   import json, sys, collections
   modules = collections.Counter()
   for line in sys.stdin:
       d = json.loads(line)
       src = d.get('source_file', '')
       mod = src.split('/')[1] if '/' in src and len(src.split('/')) > 1 else 'other'
       modules[mod] += 1
   for m, c in modules.most_common():
       print(f'  {m}: {c}')
   print(f'Total: {sum(modules.values())}')
   "
   ```

2. **Read the results log** (if it exists) to see what has already been attempted:
   ```bash
   cat rlverify/results/library_expansion.tsv 2>/dev/null || echo "No prior results."
   ```

4. **Initialize results log** if it doesn't exist. Create `rlverify/results/library_expansion.tsv` with header:
   ```
   commit	status	eval_score	module	theorem_name	source	description
   ```
   Columns:
   - `commit`: git short hash (7 chars) after adding the lemma, or `-------` for failures
   - `status`: `keep` (added to library), `discard` (compiled but failed reusability eval), `fail` (didn't compile), `vacuous` (failed anti-vacuity), `skip` (rejected pre-formalization at Step 2 — log these too), `removed` (kept earlier, removed after a problem surfaced post-commit)
   - `eval_score`: average reusability score from the evaluation subagent (0.0 for fail/vacuous, actual score for keep/discard)
   - `module`: target module (e.g., `Concentration`, `MDP`, `Bandits`)
   - `theorem_name`: the Lean theorem name
   - `source`: where the lemma came from (e.g., "Jin2020:Lemma3", "codebase:FQI.lean", "cross-paper")
   - `description`: one-line description of what was attempted

5. **Create a branch**: `git checkout -b library-expansion/<tag>` where `<tag>` is today's date (e.g., `jun8`). Confirm the branch doesn't already exist.

6. **Build the project** to confirm baseline compiles:
   ```bash
   lake build 2>&1 | tail -5
   ```

Report the setup summary and proceed to the loop.

---

## Gap Analysis — What to Formalize

Three complementary sources, in priority order. Use whichever produces candidates fastest — all are valid.

### Source 1: Domain Knowledge + Codebase Evidence

Use mathematical domain knowledge to identify standard results that a well-rounded RL theory library should have. Then validate with codebase evidence.

**How it works:**
1. **Identify candidates from domain knowledge.** Think about what standard results are commonly used across RL theory — fundamental inequalities, algebraic identities, information-theoretic tools, optimization building blocks, etc. Use `d.grep()` and `d.hybrid_search()` to check which of these the library is missing.
2. **Validate with codebase evidence.** Grep the codebase for patterns that would benefit from the candidate:
   ```bash
   grep -rn "relevant_pattern" RLGeneralization/ --include="*.lean" | grep -v ".lake" | cut -d: -f1 | sort -u
   ```
   More files using related patterns = stronger signal.
3. **Check the axiom backlog.** `rlverify/results/axiom_backlog.md` — `## Pending` items are known gaps from prior verifications.
4. **Scan for CONDITIONAL gaps.** `RLGeneralization/**/*.lean` — scan for `sorry`, `[CONDITIONAL]`, or comments like "needs X" to find building blocks that existing proofs need.

**What makes a gap high-value:** a standard textbook result that the library doesn't have, especially one where multiple existing files would benefit from it.

### Source 2: Paper Extraction and Online Research

Extract lemmas from RL theory papers, focusing on results that appear across multiple papers (widely-used building blocks, not paper-specific contributions).

**Paper extraction workflow:**

1. **Select a paper.** Pick from:
   - Papers in areas where the library has thin coverage (check module counts)
   - Seminal papers with many citations (their lemmas get reused)
   - Recent surveys that consolidate known results
   - Papers the user specifies

2. **Extract the paper.** Use the `/extract-proofs` skill, read the PDF directly, or use WebSearch to find the paper's proof structure. Identify:
   - Supporting lemmas cited from other works ("by Lemma X of [Y]")
   - Standard inequalities used without proof ("by Hoeffding's inequality")
   - Algebraic identities used in multiple proof steps

3. **Cross-reference extracted lemmas against the library.**
   ```python
   d.grep("lemma_keyword")
   ```
   Mark each as: already in library / missing but general / missing but paper-specific.

4. **Research widely-used missing lemmas.** For each candidate:
   - WebSearch to confirm it's a standard result (appears in multiple sources)
   - Verify the precise statement (conditions, constants, edge cases)
   - Check if it's in Mathlib already (search Mathlib docs)

**What to extract (good candidates):**
- Intermediate lemmas that the paper uses but didn't originate (e.g., "by the simulation lemma")
- Standard inequalities applied with specific parameters (formalize the general version)
- Algebraic identities used in multiple proof steps

**What NOT to extract (skip these):**
- The paper's main contribution (too specific to one proof)
- Lemmas that only make sense in that paper's framework
- Results that need infrastructure we don't have (check Mathlib first)

### Source 3: Systematic Coverage Audit

Periodically audit module coverage to find under-represented areas:
```bash
cat rlverify/corpus.jsonl | python3 -c "import json,sys,collections; ..."
```
Thin modules (< 30 theorems) may be missing standard building blocks.

### Choosing What to Work On

**Priority order (guaranteed consumer beats hypothetical consumer):**

1. **Axiom backlog** — `rlverify/results/axiom_backlog.md` `## Pending` items. These are gaps an actual verification run hit; the consumer exists by construction.
2. **`[CONDITIONAL]` / `sorry` gaps** in `RLGeneralization/**/*.lean` — a hypothesis some existing theorem carries because the building block was missing. Adding it lets you discharge the hypothesis (and when you do, wire the import — don't just claim it).
3. **Paper-extracted building blocks** (Source 2) — lemmas a real paper's proof needs, ideally one queued for `/verify-full-process`.
4. **Generic textbook inequalities** (Source 1 domain knowledge) — ONLY with a named consumer: cite at least one specific existing file whose proof would simplify, or a specific backlog/paper step that needs it. "Standard and useful" alone is not enough — Mathlib is the home for generic facts.

**Cap on generics**: at most 1 of every 3 consecutive attempts may come from
category 4. History: 31 of the first 42 additions were generic Concentration
inequalities, and none has been used by a verification run yet — the marginal
generic inequality is the lowest-value thing this loop produces.

For each candidate also check:
- **Feasibility**: Can we formalize this with current Mathlib? (Skip if blocked on missing infrastructure)
- **Novelty**: Not already in the library under a different name? (`d.grep()` to check)
- **Not already attempted**: Check `library_expansion.tsv` for prior failures and `skip` entries

Pick the highest-priority feasible candidate and proceed.

---

## The Experiment Loop

**LOOP FOREVER** (or until count target reached):

### Step 0: Build Candidate List (run once per batch, then loop Steps 1–10)

Before entering the formalization loop, build a **candidate list** using any combination of sources:

**From domain knowledge (Source 1):**
1. Identify standard results the library should have (inequalities, identities, optimization tools, information-theoretic building blocks)
2. Use `d.grep()` and `d.hybrid_search()` to check which candidates are missing
3. Grep the codebase for patterns that would benefit: `grep -rn "pattern" RLGeneralization/ --include="*.lean"`
4. Check `rlverify/results/axiom_backlog.md` for `## Pending` items
5. Scan `RLGeneralization/**/*.lean` for `sorry`, `[CONDITIONAL]`, or "needs X" gaps

**From papers (Source 2):**
1. Pick 2–3 papers in the target area (or user-specified papers)
2. For each paper, extract the building blocks it uses (intermediate results cited from other works, standard inequalities used without proof)
3. Use WebSearch or `/extract-proofs` to get precise statements
4. Cross-reference each against the library (`d.grep()`)
5. Mark as: already in library / missing + general-purpose / missing + paper-specific

**Build the candidate list:**
For each missing general-purpose lemma, record:
- Name, statement, source(s), reuse breadth
- Sort by reuse breadth (how broadly useful across RL theory)

Then enter the loop, picking from this list.

### Step 1: Pick Next Lemma

From the candidate list, select the next lemma to formalize. State:
- **Name**: snake_case identifier
- **Statement**: precise natural-language mathematical statement
- **Source**: paper(s) or codebase location where this gap was found
- **Cross-references**: which other proofs/papers also use this result
- **Module**: which `RLGeneralization/` subdirectory it belongs in
- **Why**: one sentence on why this is worth adding

### Step 2: Deep Redundancy Check (MANDATORY — this is the #1 failure mode)

Previous additions were removed because shallow keyword search missed existing results under different names. You MUST run ALL of the following checks before proceeding:

**2a. Keyword search (multiple angles):**
```python
d.grep("keyword1")
d.grep("keyword2")
d.grep("synonym_or_related_concept")
d.hybrid_search("natural language description of the lemma")  # catches semantic matches grep misses
```
Search for the mathematical concept, not just the proposed name. E.g., for "discrete variance" also search "wtVar", "variance", "second_moment", "E_sq".

**2b. Corpus pattern search — search for the MATHEMATICAL STATEMENT, not the name:**
```bash
grep -i "pattern1\|pattern2\|pattern3" rlverify/corpus.jsonl | python3 -c "import json,sys; [print(json.loads(l).get('id','')[:80]) for l in sys.stdin]"
```
For a weighted sum bound, search: "weighted\|sum.*le.*sup\|abs.*sum\|expect.*bound"

**2c. Codebase grep for the same mathematical pattern:**
```bash
grep -rn "conclusion_pattern" RLGeneralization/ --include="*.lean" | grep -v ".lake" | head -10
```
Look for theorems with the same conclusion shape (e.g., `|∑.*≤` for absolute sum bounds).

**2d. Mathlib check — verify it's not already in Mathlib:**

Search by **mathematical content**, not just the proposed theorem name. Use multiple keyword angles:
```bash
# Search by mathematical keywords (e.g., for a harmonic sum bound, search for "harmonic", "inv_succ", "1/k"):
grep -rn "keyword1\|keyword2\|keyword3" .lake/packages/mathlib/Mathlib/ 2>/dev/null | grep "theorem\|lemma" | head -10
# Also search by the conclusion pattern:
grep -rn "conclusion_pattern" .lake/packages/mathlib/Mathlib/ 2>/dev/null | head -10
```
The #1 Mathlib duplication failure mode is searching only for the proposed theorem name. Instead, search for the mathematical CONTENT (e.g., "harmonic", "inv_sq", "sum.*Ioc") and for the conclusion shape.

**2e. Usage check — would anything import this?**
Before writing: identify at least 1 existing file that could use this theorem. If nothing would import it, the bar is higher (it must be a clearly fundamental result).

**HARD RULE**: If any check finds an existing result that achieves the same bound/identity with the same or weaker hypotheses, **STOP** and log one TSV line with status `skip` and reason "redundant with X". Do not proceed to formalization.

**Log every examined candidate.** Candidates rejected at this step have historically gone unlogged, which (a) makes the TSV read as a 95%+ keep rate when the true funnel is much wider, and (b) causes the same dead-end candidates to be re-examined in later sessions. One `skip` line per rejected candidate, commit hash `-------`, eval_score `0.0`.

**2f. Type-directed gate (HARD GATE — runs once the statement elaborates):**

The textual checks 2a–2e are a pre-filter; they have missed duplicates under
different names before (e.g. `sqrt_add_le` duplicated SLT's
`sqrt_add_le_peeling`). As soon as the Lean statement elaborates
(`d.compile_statement` succeeds) and BEFORE any proof is written:

```python
r = d.library_search(statement)   # `<statement> := by exact?`, Mathlib + RLGeneralization + deps, ~15s
```

If `r.found` → **STOP**, log as `discard` with reason
`"redundant with <r.head_symbol> (<r.package>)"`. The search is type-directed
(the statement IS the query), so it catches what keyword search cannot. It
matches up to unification only — a not-found does NOT excuse skipping 2a–2e.

Re-run this gate once more immediately before `d.add_novel` (Step 7c) —
statements drift during proof iteration.

### Step 3: Research Statement

For non-trivial results, confirm the precise statement. Use WebSearch if needed (especially for exact conditions, constant factors, and edge cases). Cross-reference 2 sources when the statement involves subtle conditions.

For simple/standard results (Markov's inequality, Cauchy-Schwarz, etc.), the statement is well-known — proceed directly.

### Step 4: Formalize

Write the Lean 4 theorem in the appropriate file. Follow these rules from `/formalize`:

**Statement rules:**
- Match the mathematics exactly
- Direction matters: `X ≤ Y` not `Y ≥ 0`
- Include all conditions as hypotheses
- Name honestly: the name must describe what is PROVED

**Proof approach — try in this order:**
1. Direct proof using existing library + Mathlib (`exact`, `apply`, `calc`, `linarith`)
2. Break into helper lemmas, prove each, combine
3. If blocked on hard infrastructure (measure theory, matrix algebra), use `[CONDITIONAL]` with the hard step as a hypothesis

**File placement:**
- Use existing files when the lemma fits an existing module
- Create a new file only if no existing file covers the topic
- Follow the import pattern of neighboring files

### Step 5: Compile

```python
result = d.compile("""
import ...
...
theorem lemma_name ... := by
  ...
""")
```

If compilation fails:
- Read the error carefully
- Try up to **5 different approaches** (not just retries — genuinely different proof strategies)
- Common fixes: wrong import, type mismatch, missing coercion, tactic doesn't apply
- **Sorry-based preservation**: If `result.goals` is non-empty (sorry errors), keep the working tactic prefix and only fix the sorry'd portion
- If all 5 fail → check `result.goals` before giving up:

**Recursive decomposition (before giving up):**

If all 5 approaches fail and the last `result.goals` is non-empty:
1. Decompose into 2-3 sub-lemmas targeting those goals
2. Attempt each sub-lemma (up to 3 iterations)
3. If all sub-lemmas compile, compose them for the parent
4. Max recursion depth: 2. If sub-lemma decomposition also fails → log as `fail`

If recursive decomposition also fails (or no goals available) → log as `fail` with the best error message → go to Step 1

### Step 6: Anti-Vacuity Checks

**These are mandatory. Do not skip.**

**Check 1: Hypothesis minimality (compile-based).** For each hypothesis in the theorem signature, comment it out and re-compile. If the proof still compiles without a hypothesis, that hypothesis is unnecessary — remove it. This is more reliable than grepping for usage (a hypothesis can appear in the proof text but be unused by the tactic engine).

```python
# For each hypothesis h_name, try compiling without it.
# If it still compiles → remove the hypothesis.
```

Never use `set_option linter.unusedVariables false` or any other linter suppression to hide unused hypotheses.

**Check 2: Proof complexity floor.** Count tactic lines. If ≤ 1 tactic for a substantive claim → suspicious. If it's `exact h` or `linarith [h]` for a single hypothesis → log as `vacuous` → go to Step 1.

**Check 3: Independence test.** Could the conclusion be proved without hypotheses (by `positivity`, `simp`, `norm_num`)? If yes → log as `vacuous` → go to Step 1.

**Check 4: Name-conclusion contract.** Does the name match what's proved?

### Step 7: Reusability Evaluation (MANDATORY)

This is the second gate. A lemma that compiles and is non-vacuous can still be **not worth adding** if it's too specialized. The goal is a library of general-purpose building blocks, not a collection of proof-specific glue.

#### 7a: Self-Evaluation (5 questions)

Answer each question honestly. If ANY answer is "no" → **discard**.

1. **Generality test**: Is the statement expressed in general terms (arbitrary types, generic bounds) rather than specific values or specific proof notation?
   - YES: `∀ (f : S → ℝ), (∀ s, 0 ≤ f s) → 0 ≤ ∑ s, f s` (general)
   - NO: `0 ≤ ∑ s, π_star s * Q_hat s - V_bar s` (proof-specific variables)

2. **Reuse test**: Can you name at least 2 different proofs or theorem families that would plausibly need this result?
   - YES: Markov's inequality → used by UCB analysis, PAC-Bayes, sample complexity bounds, etc.
   - NO: "weighted sum of Bellman residuals for the specific MDP in Algorithm 3" → only that proof needs it

3. **Independence test**: Does the lemma stand on its own without needing to explain "this is step 3 of the proof of Theorem X"?
   - YES: "the contraction of the Bellman operator" (self-contained concept)
   - NO: "the key step that connects the regret decomposition to the bonus term" (meaningless outside one proof)

4. **Textbook test**: Could this lemma plausibly appear as a numbered lemma or exercise in a textbook?
   - YES: Jensen's inequality, Cauchy-Schwarz, covering number bounds
   - NO: "helper lemma that rearranges terms for the final inequality"

5. **Non-redundancy test**: Does the library already have something that proves the same thing (possibly under a different name or in a slightly different form)?
   ```python
   d.grep("key_concept_1")
   d.grep("key_concept_2")
   ```
   - If an existing theorem can produce this result with 1-2 lines of `apply`/`exact` → **discard** (it's an instantiation, not a library gap)

#### 7b: Adversarial Evaluation Panel (MANDATORY)

History check: a single approving evaluator is a rubber stamp — across the
first 42 additions, one-voter evaluation returned ADD 42/42 times and never
fired, while the two real failures (post-commit duplicate removals) sailed
through it. The gate must contain a voter whose job is to find reasons to
reject.

Launch **2 subagents in parallel** (single message, two Agent calls), neither
of which has seen your formalization process:

1. **Scorer** — the scoring rubric below (unchanged).
2. **Refuter** — explicitly tasked to make the case AGAINST adding. Its
   prompt (fill in the same statement/NL/source):

```
You are a skeptical reviewer for a Lean 4 RL theory library (1700+ theorems).
The candidate below is NOT yet in the library — if you find a theorem with the
candidate's own name, that is the candidate itself (or work-in-progress files
from its formalization), not prior art; an objection must cite a DIFFERENT
pre-existing result. Your job is to find disqualifying reasons NOT to add this
lemma. You may search the repo (library source under RLGeneralization/, corpus
at rlverify/corpus.jsonl, Mathlib under .lake/packages/mathlib/, SLT under
.lake/packages/SLT/) to substantiate objections. Look hard for:

- REDUNDANT: an existing Mathlib or library result that yields this in 1-2
  lines (name it). Think about alternate names and forms (contrapositive,
  symmetric version, special case of a general theorem).
- NOT RL-RELEVANT: a generic math fact with no plausible consumer among
  RL-theory proofs (regret bounds, sample complexity, concentration, MDP
  analysis). "It's true and general" is NOT sufficient — Mathlib is the home
  for generic facts; this library is for RL building blocks.
- WEAK FORM: hypotheses stronger than needed, or a conclusion weaker than the
  standard statement of this result (cite the standard form).
- MISNAMED/MISLEADING: name or docstring promises more than what is proved.

**Theorem statement (Lean 4)**: <lean_statement>
**Natural language**: <nl_description>
**Source**: <source>

Return JSON:
{"verdict": "REJECT|NO_OBJECTION", "objection_type": "redundant|not_rl_relevant|weak_form|misnamed|none",
 "reason": "one sentence; if redundant, NAME the existing result"}
Default to REJECT if you find a plausible objection — the cost of a false
rejection is low, the cost of cruft is permanent.
```

**Decision rule (ADD requires ALL of):**
- Scorer: average ≥ 3.5 AND no criterion = 1
- Refuter: `NO_OBJECTION`, OR its objection is factually wrong (you must
  refute it concretely — e.g. the named "existing result" does not exist or
  does not imply the candidate; record the refutation in the TSV description)

If either fails → log as `discard` with the panel's reason → go to Step 1.

**Panel calibration**: track the panel's discard rate in every progress
report. If after 10 consecutive attempts the panel has discarded 0
candidates, the gate is not discriminating — tighten the refuter prompt or
raise the score threshold before continuing.

**Validated** (see `rlverify/results/gate_ab_test.md`, 2026-06-10): on a
10-candidate labeled benchmark the panel caught 7/7 known duplicates (each
with a correctly named existing result) vs 0/7 for the historical
single-scorer gate, and retained 2/2 true positives via adjudication. The raw
refuter rejects nearly everything — the adjudication step (verify the cited
result actually exists and actually subsumes the candidate) is load-bearing
and must never be skipped in either direction.

Give the Scorer:

- The Lean theorem statement (signature only, no proof)
- The natural-language description
- The source (where the lemma came from)
- This prompt:

```
You are evaluating whether a Lean 4 theorem should be added to a reusable
RL theory library (1500+ theorems covering concentration inequalities, MDPs,
bandits, policy optimization, etc.).

**Theorem statement (Lean 4)**:
<lean_statement>

**Natural language**:
<nl_description>

**Source**: <source>

## Evaluation Criteria

Score each criterion 1-5:

1. **Generality** (1=proof-specific, 5=universally applicable)
   Does the statement use generic types/variables, or does it reference
   specific algorithms/constructions? A good library lemma works for ANY
   MDP, ANY policy, ANY distribution — not just the specific one in the
   source proof.

2. **Reuse potential** (1=one proof needs this, 5=dozens of proofs need this)
   How many different theorem families would benefit from having this
   as a building block? Consider: does this appear (explicitly or
   implicitly) in multiple textbooks or survey papers?

3. **Non-triviality** (1=trivial consequence of existing results, 5=genuinely new)
   Is the proof substantive (multi-step reasoning, combining multiple
   techniques), or is it a 1-2 line consequence of standard facts?
   Note: a short proof of a USEFUL fact is still worth adding. The
   question is whether the result itself is non-obvious enough to save
   future users from having to re-derive it.

4. **Statement quality** (1=poorly formalized, 5=clean and canonical)
   Is the Lean statement well-typed, properly parameterized, using
   standard conventions? Are the hypotheses minimal (no unnecessary
   assumptions)?

5. **Library fit** (1=doesn't belong, 5=fills a clear gap)
   Does this fill a gap in the existing library? Does it complement
   existing theorems (e.g., the library has the Bellman contraction
   but not the simulation lemma — adding the simulation lemma fills
   a natural gap)?

## Verdict

- **ADD** if average score ≥ 3.5 AND no criterion scores 1
- **SKIP** otherwise

Return a JSON object:
{"generality": N, "reuse": N, "nontriviality": N, "quality": N, "fit": N,
 "average": N.N, "verdict": "ADD|SKIP", "reason": "one sentence"}
```

Apply the decision rule above (Scorer + Refuter). If the panel rejects → log
as `discard` with the reason → go to Step 1. If it passes → proceed to Step 7c.

#### 7c: Add to Library

0. Re-run the type-directed gate on the FINAL statement (it may have drifted
   during proof iteration): `d.library_search(statement)` must return
   not-found, else log as `discard — redundant with <name> (<package>)`.
   Also run the back-translation audit (`/verify-full-process` Phase 3) on the
   candidate: a MISMATCH between the statement and its docstring/claimed
   content blocks the addition.

1. Write the file to the source tree (if not already done during compile):
   - File path: `RLGeneralization/<Module>/<TheoremName>.lean` (or append to existing file if it fits)
   - Include a docstring describing the result and its source

2. Add to the retrieval corpus (this also registers the import in `RLGeneralization.lean` and runs `lake build` on the new module automatically):
   ```python
   d.add_novel(
       name="lemma_name",
       code=full_lean_code,            # statement extracted automatically
       target_dir="Concentration",
       docstring="One-line NL description (indexed for search)",
       reusable=True,
       reuse_reason="Atomic general fact with plausible use in other proofs",
       generalized_from="<paper/claim/block provenance>",
   )
   ```

   `add_novel` refuses duplicates (a lemma with the same name/id already in the corpus), `axiom` declarations, and files with a bare `import RLGeneralization` (import cycle — use specific imports). If the build fails (e.g. name collision with an existing declaration), the addition is rolled back — rename and retry. After a session's additions, run `lake build RLGeneralization` once so the root module picks them up.

3. Git commit (no co-author tag):
   ```bash
   git add <file> RLGeneralization.lean
   git commit -m "Add <lemma_name>: <one-line description>"
   ```

5. Record the commit hash for the results log.

### Step 8: Log Result

Append one line to `rlverify/results/library_expansion.tsv`:
```
<commit>	<status>	<eval_score>	<module>	<theorem_name>	<source>	<description>
```

Example entries:
```
a1b2c3d	keep	4.2	MDP	geom_sum_le_inv_one_sub	codebase:FQI.lean+Puterman	Standalone geometric sum bound (used by 9+ fixtures)
b2c3d4e	keep	3.8	MDP	contraction_iterate_dist_le	Jin2020+Azar2017	Contraction iterate bound (cross-paper: VI, Q-learning, FQI)
c3d4e5f	fail	0.0	Bandits	exp3_regret_bound	Auer2002:Thm3.1	EXP3 regret bound (blocked on log-sum-exp)
d4e5f6g	vacuous	0.0	LowerBounds	fano_mutual_info	cross-paper	Proved 0 <= expr instead of actual bound
e5f6g7h	discard	2.4	Concentration	hoeffding_variant	Lattimore2020:Lemma5	eval: too similar to existing hoeffding_bound
```

### Step 9: Progress Report (every 5 lemmas)

Every 5 attempts, run the reuse report and print a summary:
```bash
python3 scripts/corpus_reuse_report.py
```
```
=== Library Expansion Progress ===
Attempts: N | Kept: X | Discarded (eval): Y | Failed (compile): Z | Vacuous: W | Skipped: S
Panel discard rate (last 10 attempts): D/10   <-- if 0/10, the gate is not discriminating; tighten it
Library size: <before> → <current> (+<delta>)
Avg eval score (kept): <score>
Reuse (from corpus_reuse_report.py):
  expansion lemmas matched in verification runs: M / total   <-- the metric that matters
  corpus-wide matches recorded: <n>
Latest additions:
  + <name1> (eval: 4.2): <description>
Recent discards/skips:
  - <name3> (eval: 2.4): <reason from evaluator>
Next target: <name> (<reason>)
===
```

**Reuse ground-truth cadence**: the `matched` counter only moves when a
verification run uses a premise. If corpus-wide matches haven't increased in
the last 20 attempts, pause expansion and tell the user a `/verify-full-process` run is
needed to generate reuse ground truth — adding lemmas faster than anything
consumes them is how the library becomes a dump.

### Step 10: Return to Step 1

Pick the next lemma and continue. **Do not stop.** Do not ask "should I continue?" The human will interrupt you when they want you to stop.

If you run out of candidates from the current batch:
1. **Extract more papers** — pick 2–3 new papers in under-covered areas (check module counts) and re-run Step 0
2. Re-scan the codebase — the library has grown, so previously-blocked `[CONDITIONAL]` results may now be provable
3. Try harder formulations of previously-failed lemmas (different decomposition, different proof strategy)
4. Search online for survey papers that consolidate standard results in a topic area

---

## Rules

### Never do these:
- NEVER stop to ask the human if you should continue (unless blocked on a decision you truly cannot make)
- NEVER add a lemma with `sorry` to the library
- NEVER name a theorem dishonestly (name must match conclusion)
- NEVER add hypotheses that aren't in the mathematical statement
- NEVER skip the anti-vacuity checks (Step 6)
- NEVER skip the reusability evaluation (Step 7) — every candidate must pass both gates
- NEVER add a lemma that the evaluation subagent scored below 3.5 average
- NEVER re-attempt a lemma that's already in `library_expansion.tsv` with the same approach (try a different approach or skip)
- NEVER add proof-specific glue — if you have to explain "this is used in the proof of X" to justify it, it doesn't belong
- NEVER use `set_option linter.unusedVariables false` or any linter suppression — fix the underlying issue instead
- NEVER claim a lemma "resolves" or "deduplicates" an existing axiom/gap in the TSV description unless you actually wire the import. Use "provides standalone version of" instead

### Always do these:
- ALWAYS run the full 5-part redundancy check (Step 2a–2e) before formalizing — this is the #1 failure mode
- ALWAYS search for the mathematical CONTENT in Mathlib, not just the proposed name (e.g., search "harmonic\|inv_succ\|1/k" not just "harmonic_sum_le")
- ALWAYS compile before evaluating (Gate 1: correctness)
- ALWAYS run the hypothesis minimality test (compile without each hypothesis) in anti-vacuity checks
- ALWAYS run all 4 anti-vacuity checks (Gate 1: non-vacuity)
- ALWAYS run the adversarial evaluation panel — Scorer AND Refuter (Gate 2: reusability)
- ALWAYS set `reusable=True` with a concrete `reuse_reason`; unpromoted and
  paper-specific results stay in run artifacts, not the shared corpus
- ALWAYS register new files in `RLGeneralization.lean` (done automatically by `d.add_novel()`)
- ALWAYS log every attempt to the TSV — including `skip` lines for candidates rejected at Step 2 (an unlogged skip gets re-examined next session)
- ALWAYS respect the generics cap: at most 1 in 3 consecutive attempts from the generic-inequality category, each with a named consumer
- ALWAYS git commit each successful addition (to enable keep/discard tracking)
- ALWAYS prioritize lemmas that score highest on the reuse potential criterion

### Quality over quantity:
- A library of 1520 honest, reusable theorems is better than 1600 with 80 that are proof-specific filler
- The evaluation subagent is a hard gate, not advisory — if it says SKIP, you skip
- If a lemma is borderline on reusability, err on the side of NOT adding it
- One `[CONDITIONAL]` theorem with genuine algebraic content and high reuse potential beats a vacuous theorem that claims full proof
- Prefer shorter, cleaner proofs that use existing library infrastructure
- The library should feel like a **textbook reference**, not a **dump of intermediate results**

## Recovery

If the build breaks (a committed lemma causes downstream errors):
1. `git revert HEAD` to undo the last commit
2. Log the revert in the TSV with status `fail` and description "reverted: <reason>"
3. Continue with the next lemma

If you hit an error you can't diagnose:
1. Log it in the TSV
2. Move on to the next lemma
3. Come back to it later with a fresh approach
