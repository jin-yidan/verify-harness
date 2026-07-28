---
name: verify-full-process
description: "Duplicate of Claude /verify-full-process. Use when the user invokes /verify-full-process, $verify-full-process, or asks to run this RLVerify command. Verify a theorem and proof sketch by formalizing the proof in Lean 4 with RLVerify, using triage, hypothesis audit, falsification, sketch, discharge, assemble, and honest VERIFIED or UNVERIFIED reporting."
---

# /verify-full-process — Codex Duplicate

This is a Codex skill duplicate of `.claude/commands/verify-full-process.md`. The Claude slash command name is `/verify-full-process`; in Codex, invoke it as `$verify-full-process` or write `/verify-full-process` in the prompt. Interpret Claude-specific Task/Bash references as workflow instructions and use Codex-native tools or the local RLVerify CLI.

Preserve the verification discipline from the original command: verify, do not repair; do not add hypotheses or proof steps; treat sealed gates and kernel evidence according to the RLVerify output contract.

When this skill calls `python3 -m harness` directly or through RLVerify CLI examples, pass `--backend codex` unless the user explicitly asks for another backend. Pass `--model <codex-model>` when a specific Codex model is under test; otherwise let the Codex CLI use its configured default.

---

# /verify-full-process — RLVerify: Verify a Proof's Correctness

Verify whether a theorem and its proof sketch are correct by attempting to formalize them in Lean 4. The tool reports VERIFIED (with complete code) or UNVERIFIED (with the specific failure point).

**CRITICAL PRINCIPLE: This tool VERIFIES — it does not REPAIR.** If the proof is wrong, incomplete, or has logical gaps, report the failure. Never add assumptions, hypotheses, or proof steps that aren't in the input to make it compile.

## Input

$ARGUMENTS

The input should contain:
- A theorem statement (natural language or from a paper)
- A proof sketch or strategy description

## Workflow

```python
from rlverify.driver import VerifyDriver
d = VerifyDriver()
d.begin("descriptive_fixture_name")   # FIRST driver call, before anything else
```

#### Session discipline (load-bearing)

- **`d.begin(...)` is the literal first driver call** — before any search,
  compile, or `add_novel`. Work done outside a session is invisible to the
  run record (the historic failure mode: lemmas added before `begin()`
  showed as GAP / "Novel added: (none)" in the final report).
- The session journals itself to `runs/<fixture>.inprogress.json` after
  every mutation. **A new Python process continues the same session with
  `d.resume("fixture_name")`** — never re-`begin` and re-enter results by
  hand. `d.finish()` removes the journal.
- `status()`/`finish()` reconcile novel blocks against the corpus: a block
  whose lemma was registered by `add_novel` (even from another process) is
  shown `✓ compiled`, not GAP.

#### Output discipline

The driver emits one standardized line per pipeline event:

```
[PHASE     ] BLOCK                        GLYPH STATUS — detail
```

Phases: `begin | resolve | gate | falsify | sketch | discharge | compile |
assemble | library`. Glyphs: `✓` success, `✗` failure/refuted, `~`
instantiation, `?` novel, `·` info/skipped, `⚠` warning.

- Call **`d.status()`** between phases (and whenever resuming a long session)
  — it renders the live per-block table: kind, falsification verdict,
  compiled state, match.
- **`d.finish()`** ends with a fixed-format summary block; its `Verdict :`
  line is the machine-readable result — quote it verbatim in the
  conversation report, and never report a verdict that contradicts it.
  (Exception: early-exit verdicts — WRONG / HYPOTHESIS_VIOLATION / CIRCULAR
  established before formalization — are yours to state; the driver only
  sees what was attempted in Lean. State them explicitly alongside the
  summary block.)

---

### Phase 0: Adversarial prose triage (prioritizes, never decides)

Before decomposing, spawn a SEALED subagent (Task tool) whose ENTIRE prompt
is the verbatim theorem+proof text plus exactly this instruction — no library
access, no driver, no conversation context:

```
You are an adversarial reviewer. You have no other context and no tools.
Assess each proof step: SOUND or SUSPECT, with a one-line reason each, then
list the most likely fatal flaws ranked by severity. Output JSON only:
{"suspects": [{"step": <n>, "suspicion": "<reason>",
               "severity": "high|medium|low"}], "all_clear": <bool>}
```

Record the output: `d.record_triage(suspects=[...], all_clear=...)`. If the
subagent returns malformed JSON, re-prompt once; if still malformed, record
`all_clear=False, suspects=[]` (fail toward more scrutiny, never less).

Hard constraints (load-bearing — do not weaken):

- **Triage PRIORITIZES; it never decides and never skips.** The Hypothesis
  Audit checklist runs IN FULL on every inter-block invocation, and the
  falsification gate covers every eligible block, regardless of triage
  output. Triage determines only the ORDER (flagged invocations audited
  first; flagged blocks gated first) so that early exits are reached sooner.
- **An `all_clear` triage carries ZERO weight** — documented shipped
  failures (cfpo's inconsistent axioms, minimax's compact→finite downgrade,
  E4's imported sorry) all passed prose review. Do not shorten any phase
  because triage found nothing.
- **A triage flag is never evidence.** Verdicts still require what Rule 7
  requires: a certificate, a named violated hypothesis, or a kernel result.
- **The Phase 6 report MUST include a reconciliation table**: each triage
  suspect → confirmed (with evidence) or cleared (with evidence); each
  pipeline-found flaw → whether triage flagged it. An unflagged-but-found
  flaw is recorded evidence that coverage survived triage; finding nothing
  after an all-clear is a visible signature to scrutinize.

Why sealed: an inline triage by the orchestrating agent is the same context
window later "confirming" its own guess — circular, like self-checked
back-translation. Independence is what makes agreement between triage and
the audit two signals instead of one.

---

### Phase 1–2: Extract and Resolve

Decompose the proof into atomic building blocks and resolve each against the library.

#### Decompose

Break the proof into atomic building blocks. Each must be:
- A single, self-contained mathematical fact
- Stated in general form (not tied to this proof's notation)
- Named descriptively in snake_case

Only extract building blocks that are CLAIMED in the proof. Do not infer or add steps the proof doesn't mention.

#### Dependency Ordering

For each block, also identify which OTHER blocks from this decomposition it depends on. Output format per block:
`{name, statement, role, depends_on: [list of block names this block needs]}`

After decomposing all blocks:
1. Build the dependency graph from the `depends_on` fields
2. Check for cycles. If circular dependencies exist → STOP with verdict UNVERIFIED/CIRCULAR. Caveat: this textual check only sees explicit citations — it MISSES cycles hidden by conditional conclusions (block A proved "on the event E" where E is block B's conclusion, and B cites A). The Hypothesis Audit's conditional-conclusion check (below) is the load-bearing detector for those.
3. Topologically sort blocks so each is formalized only after all its dependencies succeed

In Phase 3, process blocks in this topological order. When formalizing block B that depends on block A, block A's compiled Lean code is available as a proven lemma.

#### Hypothesis Audit (inter-block connections)

After decomposing, audit every point where one block invokes another. For each such invocation:

1. **List ALL hypotheses** of the invoked block (not just the ones the proof explicitly checks)
2. **Check each hypothesis** against the actual argument provided. A proof that checks one hypothesis (e.g., boundedness) while silently skipping another (e.g., independence) is a red flag, not a reassurance.
3. **Flag hypothesis substitution camouflage**: When the proof explicitly verifies condition A of a lemma but the critical condition is B, note this. A parenthetical like "which satisfies [easy condition]" after an application often masks an unchecked [hard condition].
4. **Track conditional conclusions (conditional-conclusion camouflage)**: when a block's conclusion holds only "on the event E" / "given X" / "whenever Y is bounded", record E as a hypothesis of EVERY downstream invocation of that block — an invocation that drops the conditioning is unjustified. If E is (or implies) the conclusion of a block that in turn invokes this one, the proof is CIRCULAR even though the textual `depends_on` graph is acyclic (citation arrows only point one way; the conditioning closes the loop). Canonical instance: a stochastic-approximation proof establishes noise convergence by a martingale argument "on the event {sup_n ‖θ_n‖ < ∞}", then invokes it unconditionally to prove that very boundedness — the Borkar–Meyn stability gap (the honest fix is an extra stability hypothesis, e.g. GAS of the scaled field h∞, which Rule 1 forbids adding).

Common missed hypotheses in probabilistic proofs:
- **Independence**: Concentration inequalities (Hoeffding, Azuma, Bernstein) require the random variables or the function being concentrated to be independent of the randomness being averaged over. Fixed points of empirical operators (V̂*, Q̂*) depend on ALL samples and violate this.
- **Measurability**: Functions of random variables must be measurable w.r.t. the correct σ-algebra.
- **Uniform vs. pointwise**: A bound that holds for a fixed quantity does not automatically hold uniformly over data-dependent quantities without a union bound or covering argument.

Common missed hypotheses in optimization proofs:
- **Maximizer identity**: When the proof writes "for the maximizing action a*", verify WHICH optimization problem a* solves. If two operators T̂ and T may have different maximizers, writing (T̂−T)f(s) as a single-action expression is wrong — use |max f − max g| ≤ max |f − g| instead.
- **Convexity/compactness**: Minimax theorems, duality, and exchange of sup/inf require specific structural conditions.

#### Resolve Each Block

For each building block, search the library:
1. `d.grep("keyword")` for exact identifier matches
2. `d.grep("related_term")` for broader matches
3. If a module has relevant theorems, list them with `d.show("theorem_id")`

Classify each block as:
- **library** — exact match exists, give the qualified name
- **instantiation** — a more general theorem exists that specializes to this
- **novel** — not in library, must be formalized from scratch and added to library

**statement_nl is mandatory in every `d.resolve(...)` call** and must include
the block's explicit constants and log arguments as written in the paper
(e.g. "radius sqrt(ln(2K/delta)/(2t))"). The driver runs a **near-match
log-argument scan** against the nearest library lemmas at resolve time: a
`differs:` line means a kernel-checked lemma carries a different log argument
(e.g. the library needs log(2KT/δ) where the block claims log(2K/δ)). Every
`differs` line MUST be adjudicated in the report with one sentence — why the
differing factor does or does not belong (e.g. "the event quantifies over
phases ⇒ T belongs ⇒ the block's missing T is the flaw"). The scan is
best-effort corroboration, not a soundness gate — **silence proves nothing**
(the library may simply hold no nearby lemma).

**External citations are #check-validated at resolve time.** A
`library=`/`instantiation=` id not in the corpus (e.g. a Mathlib name) is
checked via the warm REPL or a fresh `import Mathlib` compile: `#check ✓`
means the identifier exists (Phase 3 still verifies its hypotheses); `NOT
FOUND by #check` means the name is wrong — fix the citation before Phase 3,
the block renders `✗ bad citation` until then.

**ID-SHAPED warnings are disqualifying.** Search results and resolve()
flag corpus lemmas whose conclusion is verbatim one of their own
hypotheses (`[ID-SHAPED — assumes its conclusion]`). Such a lemma proves
nothing — citing one as a library match is camouflage (e.g. an
`azuma_hoeffding_trajectory` whose statement assumes the Azuma bound it
names). Treat the block as **novel** and formalize the real content.
`scripts/audit_corpus_vacuity.py` reports the full list
(`rlverify/results/vacuity_audit.md`).

**Type-directed gate (mandatory before classifying a block as novel)**: once
the block's Lean statement elaborates (`d.compile_statement`), run

```python
d.library_search(statement)   # compiles `<statement> := by exact?`, ~15s
```

with its default maximal imports (all of Mathlib + RLGeneralization + deps).
`found=True` means a library proof EXISTS — the block is **library** (or
**instantiation**), recorded under the reported name/package; do not
formalize it. `found=False` is weaker than it sounds: `exact?` matches up to
unification only and misses shape variants (n-ary vs binary, `Finset.range`
vs `Fintype`, `<` vs `≤`, ENNReal vs ℝ) — so keep the textual searches above
too. The wide import here does not change the proof-iteration rule (narrow
imports in Phase 3); it applies only to this gate.

#### Report

Output a resolution table:

| # | Block Name | Statement (NL) | Kind | Library Match / Notes |
|---|-----------|----------------|------|----------------------|

Then summarize:
- Total blocks: N
- Library matches: X (no work needed)
- Instantiations: Y (need specialization proof)
- Novel: Z (need full formalization)

List the imports needed for all library matches.

#### Rules for Extract

- Be thorough in searching — try multiple keywords per block
- A "library match" means the EXACT mathematical content is proven, not just related
- An "instantiation" means applying a general theorem with specific parameters gives this result
- Report honestly — don't claim library matches that don't exist

**Audit finding**: If a block appears mathematically false from prose reasoning
or an agent-authored counterexample, record it as `UNVERIFIED/SUSPECTED` and
continue toward an independently checked certificate or kernel refutation.
Only those stronger artifacts may produce `UNVERIFIED/WRONG`.

**Hypothesis-audit finding**: Record the lemma, hypothesis, argument, and reason,
but treat the model audit as `UNVERIFIED/SUSPECTED`. Upgrade to
`UNVERIFIED/HYPOTHESIS_VIOLATION` only after deterministic or kernel-backed
confirmation.

**Circularity finding**: A cycle found directly in the persisted dependency
graph is deterministic; a conditional cycle inferred by the model audit is
`UNVERIFIED/SUSPECTED` until independently confirmed. Name both ends and the
conditioning event, and preserve unaffected blocks for structural verification.

**Persist every early-exit verdict** — it must be machine-readable in the run
record, not just stated in conversation:

```python
d.resolve("block_name", violation="Library.Lemma.id",
          reason="applied at the random count N_t(a); the lemma requires a fixed n")
d.set_verdict("UNVERIFIED/HYPOTHESIS_VIOLATION",
              reason="block_name applies Library.Lemma.id at a sample-dependent count")
```

`d.resolve(violation=..., reason=...)` records the block as kind `violation`
(the cited lemma is correct; the application is wrong). `d.set_verdict`
accepts the six early-exit verdicts (WRONG / PROOF_INVALID / INCOMPLETE /
MISMATCH / HYPOTHESIS_VIOLATION / CIRCULAR) with a mandatory justification; it dominates
the session verdict line and lands in the runs/ JSON. VERIFIED verdicts can
never be set manually — they come from the kernel audit. Pass
`block="block_name"` to name the verdict-deciding block — this is what links
a kernel-backed refutation (below) to the verdict.

**Kernel-backed refutation (attempt for the verdict-deciding block).** An
early-exit verdict rests on audit reasoning — testimony. Upgrade it to kernel
evidence where feasible: formalize a small Lean counterexample to the invalid
*inference* and record it:

```python
d.refute("block_name", counterexample_code,
         description="<the refuted claim, verbatim>")
d.set_verdict("UNVERIFIED/PROOF_INVALID", reason="...", block="block_name")
```

The counterexample theorem must assert *premises-hold ∧ ¬conclusion* for a
concrete instance. Kernel closure authenticates that exact Lean proposition;
trusted scope matching separately decides whether it invalidates one submitted
inference (`PROOF_INVALID`) or refutes the complete theorem (`WRONG`). Rules:

- Attempt it for the **verdict-deciding block only**, time-boxed (≤5 compile
  iterations). Failure never changes the verdict — it stays audit-only,
  which is honest and fine.
- **Worth attempting when**: (a) the flaw already has an exact falsification
  certificate — the Lean counterexample is the certificate instance closed by
  `norm_num`/`decide` (minutes of work); (b) an invalid inference pattern
  refutable on a tiny finite instance (e.g. a 4-point measure space refuting
  a union-bound scope error). **Not worth**: asymptotic/existence/
  measure-theoretic flaws with no finite instance.
- Semantics: a scoped proof-step refutation certifies *"this inference step is
  invalid."* Only a well-defined, faithfully matched witness satisfying every
  theorem hypothesis and negating the complete conclusion certifies *"the
  theorem is false."*
- Refutations are paper-specific negative facts — never `add_novel` them
  (positive by-products discovered along the way go through Phase 5
  normally).
- The refutation statement gets the back-translation audit (Phase 3) like
  any verdict-bearing statement: the context-free rendering must instantiate
  the block's premises and negate its conclusion.

**Salvage rule (mandatory)**: Regardless of verdict — WRONG, INCOMPLETE, MISMATCH, or HYPOTHESIS_VIOLATION — any block that is **independent** of the failed block and **mathematically correct** MUST still be formalized (Phase 3) and evaluated for library addition (Phase 5). A broken proof can still contain correct, reusable lemmas — don't discard them. Only skip formalization for blocks that *depend on* the failed block. "Not attempted" is never an acceptable status for an independent correct block.

#### Falsification gate (novel + instantiation blocks)

Formalization is the most expensive way to discover a claim is false. Before
formalizing, run a numeric counterexample search on each novel/instantiation
block (library blocks are already Lean-proven — skip them). This
operationalizes the early-exit rule above: instead of relying on intuition to
spot a counterexample, search for one computationally.

Gate ONLY blocks that survived the hypothesis audit and are not downstream
of a failed block — gating dead blocks wastes work, and a REFUTED on a
blocked block would muddy verdict precedence (the upstream failure is the
verdict).

Write an ad-hoc `/tmp/falsify_<block>.py` per block following this template:

```python
# /tmp/falsify_<block>.py — gate for: <the inequality, verbatim>
import numpy as np
rng = np.random.default_rng(0)
N, TOL = 200_000, 1e-9
sampled = satisfied = violations = 0; worst = None; max_gap = 0.0
for _ in range(N):
    # sample instance: Dirichlet for distributions, log-uniform grids up to
    # 1e9 for scale parameters (T, K, d), uniform [a,b] for bounded reals,
    # n ≤ 4 states/atoms; EXACT enumeration for probability claims
    ...
    sampled += 1
    if not hypotheses(inst): continue
    satisfied += 1
    gap = lhs(inst) - rhs(inst)            # claim: lhs ≤ rhs
    if gap > TOL * max(1.0, abs(rhs(inst))):
        violations += 1
        if worst is None or gap > max_gap: worst, max_gap = inst, gap
print(f"{sampled=} {satisfied=} {violations=} {max_gap=}")
```

Then record the outcome with the contract from `rlverify.falsify`:

```python
from rlverify.falsify import FalsifyReport, reverify
d.record_falsification(FalsifyReport(block="...", verdict="...", ...))
```

**Record EVERY gate outcome, including SKIPPED** — a skip with its reason
is itself a record. `d.finish()` warns about any novel/instantiation block
with no recorded falsification outcome; an outcome that lives only in the
conversation is not evidence.

Outcomes (the dataclass enforces the first two rules):
- **REFUTED** — a violation was found AND `reverify()` confirmed it by direct
  substitution in pure Python (a separate code path from the numpy sampler;
  use `exact=True`/Fraction when the claim is rational arithmetic). This
  refutes the block, not automatically the complete theorem. It remains
  `SUSPECTED` until an independent deterministic checker or scoped kernel
  refutation validates it; then use `PROOF_INVALID` for a proof step and
  `WRONG` only for the complete theorem. Skip its dependents; the salvage rule
  still applies to independent blocks.
- **PASSED** — no violation in ≥1000 hypothesis-satisfying instances. Proceed
  to Phase 3 normally. A PASS carries **zero verification weight**: report it
  as "no counterexample in N instances", never "numerically verified".
- **VACUOUS** — sampling never (or rarely) satisfied the hypotheses. Proceed,
  but ALSO investigate satisfiability (feeds anti-vacuity check 4).
- **SKIPPED** — the claim is not numerically checkable. Skip for:
  ∃-statements; asymptotic/big-O/limit claims; measure-theoretic or
  topological claims (gate their finite corollaries instead); unsampleable
  hypotheses; high-probability claims that can't be finitized to exact
  enumeration. Caution even on a PASS: constant/log-factor errors may only
  manifest at astronomical scale — always put growing parameters on
  log-scale grids.

  **Before skipping a high-probability claim, check the finite-DP mold**:
  if the bad event is a union over (arm, time) of i.i.d. prefix-mean
  threshold crossings with bounded rewards, it is EXACTLY computable —
  Bernoulli is a valid refutation instance for any [0,1]-reward claim, and
  `rlverify.falsify.bernoulli_prefix_deviation` (pure-integer DP) gives the
  exact per-arm probability; arms multiply by independence. Restrict to the
  m = ⌊T/K⌋ phases completed deterministically so the finitized event is a
  SUBSET of the claimed bad event — and **state in the report why the
  subset relation holds** (this is the one step the DP cannot check).
  Certify irrational log thresholds with a rational upper bound via
  `exp_series_exceeds(L_up, target)` (an upper bound on L under-counts
  failures — sound for refutation). Discovery may use a float/numpy DP; the
  REFUTED witness should re-verify through the exact path, but remains
  audit-only until a trusted deterministic checker validates that witness
  (`reverify(..., exact=True)` with all-rational fields). Mind mean ties:
  μ choices must satisfy the claim's hypotheses (e.g. unique optimal arm).
  Union-bound/good-event claims in bandit proofs typically fit this mold;
  coupled MDP empirical-model claims (argmax over multinomial models)
  typically do not — skip those honestly. Constant-factor-only errors may
  still need astronomical m: if the DP passes at practical m, record
  SKIPPED-after-DP-pass with the m reached, not PASSED-as-evidence.

#### Sketch (machine-check the decomposition before proving anything)

Run this AFTER the hypothesis audit, both early exits, and the falsification
gate — never sketch a proof that already died, and NEVER repair a
decomposition to make a skeleton compile.

Write the complete proof as a skeleton:
- Each non-library block is a **lemma-style** stub above the main theorem:
  `private lemma block_i (...) : ... := sorry`. (`have`-style only for
  proof-local glue facts — lemma-style handles induction, variable binding,
  attributes, and reuse, and matches the final assembly byte-for-byte.)
- A block used "inside an induction" is stated as the fully-quantified step
  `∀ m, P m → P (m+1)`.
- Library blocks are imported and used directly.
- The main theorem is proven from the blocks with **explicit glue**: `exact`,
  `calc` naming each block, or `linarith [block1, block2, ...]`. Bare
  `nlinarith` / `simp_all` / `aesop` / `omega` without explicit block
  arguments are FORBIDDEN at sketch time — a skeleton they close certifies
  nothing.

```python
d.sketch(skeleton_code, expected_blocks=["block1", "block2", ...])
```

- **Success** ⇒ the decomposition is machine-checked: the conclusion really
  follows from the stated blocks (Lean checks this even with the blocks
  sorried). `d.sketch` additionally fails any skeleton whose glue does not
  actually use every expected block. Note: skeleton-OK ≠ blocks-OK — the
  sorried statements can still be false; Phase 3 discharges them.
- **Failure** is *diagnostic*, never an auto-verdict: distinguish a genuine
  decomposition gap (the blocks don't imply the conclusion — `result.goals`
  shows the missing implication) from a fixable glue/coercion bug. Fix glue
  bugs; report decomposition gaps honestly.

Use narrow imports — the skeleton compile costs the same ~4s as a single
block compile.

---

### Phase 3: Discharge Each Block

Discharge the sorried skeleton lemmas one at a time, in topological order
(cheapest / most-doubted first is a good heuristic within independent
groups). For each block, produce a compiling Lean 4 proof. The proof must follow the given argument — do not invent a different proof strategy or add assumptions not present in the input.

If discharging a block forces its signature to change (extra binder, sum
reindexing, coercion), update the skeleton and re-run `d.sketch` before
continuing — expect this; it is the main recurring cost of sketch-first.

#### For each block:

**Step 1: Search Library**
```python
d.grep("keyword1")
d.grep("keyword2")
d.hybrid_search("natural language description of what you need")
d.show("promising_theorem_id")
```

**Step 2: Write Statement**

Write the Lean 4 theorem signature. Rules:
- Return type must be `Prop`
- Use existing types from the library (e.g., `M.StochasticPolicy`, `FiniteMDP`)
- Include necessary hypotheses but no extras
- Add `variable` context if using library types

**Step 3: Write Proof**

Strategy priority:
1. `exact library_theorem args` — if a library theorem proves it directly
2. `apply library_theorem` + fill goals — if it proves most of it
3. `calc` block — for chain reasoning (A ≤ B ≤ C)
4. `have h1 := ...; have h2 := ...; linarith` — for combining inequalities
5. Tactic combinators: `simp`, `ring`, `linarith`, `norm_num`, `omega`

**Step 4: Compile and Iterate**
```python
result = d.compile(full_code)
```

Compile-speed note: use NARROW imports (the specific `RLGeneralization.X.Y` or
`Mathlib.*` modules you need). `import RLGeneralization` pulls the whole library
plus Mathlib and is ~6x slower per compile. To validate a signature before
attempting the proof, use `d.compile_statement(stmt, imports=[...])` — success
means the statement elaborates (the proof is stubbed). If narrow imports don't
provide the `Finset`/`BigOperators` namespaces, pass `opens=` (possibly
`opens=""`) to `compile_statement`/`formalize`/`assemble` — and pass the SAME
`opens` to `assemble` that you used in `formalize`.

If compilation fails:
- Read the error carefully
- Common fixes: missing imports, wrong argument order, universe issues
- Try up to 5 iterations per block
- If stuck, try a fundamentally different proof approach

**Goal-state preservation**: If the proof fails with unsolved goals,
`result.goals` contains the full goal states (hypotheses + ⊢ lines) per error:
1. Keep the working tactic prefix
2. Focus retry on closing the specific goals listed in `result.goals`
3. Do NOT regenerate the entire proof — only the incomplete portion

(Note: an explicit `sorry` compiles with no goal output — `result.goals` is
populated by *unsolved-goals errors*, i.e. when the tactic block ends early.)

**Recursive decomposition (when all 5 iterations fail):**

If the block fails after 5 iterations, do NOT immediately mark it as a gap. Instead:

1. Check `result.goals` from the last `d.compile()` call — these are the unsolved sorry goals
2. If goals are non-empty, decompose the failed block into 2-3 sub-lemmas, each targeting one of the listed goal states
3. Attempt each sub-lemma independently using the same formalize rules (up to 3 iterations each)
4. If ALL sub-lemmas succeed, compose them to solve the parent block and re-compile
5. If a sub-lemma also fails after 3 iterations, it may be recursively decomposed ONE more level (depth limit = 2: original block → sub-lemma → sub-sub-lemma)
6. If recursive decomposition also fails, THEN mark the original block as a gap

This preserves partial progress: even if the full block is too hard for one shot, sub-goals may be individually tractable.

#### Classification-specific handling:

- **Library match**: Write a short proof using `exact`/`apply`. Compile to confirm it type-checks. If the library theorem requires different hypotheses than what the proof provides → MISMATCH.
- **Instantiation**: Specialize the general library theorem. Write and compile the instantiation proof.
- **Novel**: Formalize EXACTLY what the proof sketch argues. If the proof's argument is incomplete or wrong, the formalization will fail — that's the signal.

For each block, report: compiled successfully / failed (with reason).

#### Anti-vacuity checks (mandatory for novel blocks)

A novel block that compiles can still be vacuous — proving something weaker
than the paper's claim, or proving it from hypotheses that make it trivial.
Before counting a novel block as verified, run:

1. **Hypothesis minimality (compile-based)**: for each hypothesis in the
   signature, comment it out and re-compile. If the proof still compiles, the
   hypothesis is unused — this often signals the formalized statement is weaker
   than the block's actual claim. Investigate before accepting. Never suppress
   linters to hide unused hypotheses.
2. **Independence test**: can the conclusion be proved without the hypotheses
   (`positivity`, `simp`, `norm_num` alone)? If yes, the formalization does not
   capture the claim — rewrite the statement.
3. **Statement-claim contract**: does the Lean statement say what the block's
   NL statement says? Quantifiers, direction of inequalities, and which
   variables are universally quantified all must match.
4. **Contradictory-hypothesis probe**: if the hypotheses look strong, check
   they are satisfiable (exhibit a trivial instance with `example : ∃ ...`).
   A theorem with unsatisfiable hypotheses verifies nothing.

#### Back-translation audit (mandatory for: the input's main theorem statement, every `axiom` declaration, every `d.add_novel` candidate, and every `d.refute` counterexample statement)

The statement-claim contract (check 3) is unreliable as a self-check — the
agent that chose the formalization will read its own statement as matching.
For the statements listed above, run an INDEPENDENT back-translation.
(Internal helper blocks are exempt unless another anti-vacuity check flagged
them.)

1. Spawn a subagent (Task tool) whose ENTIRE prompt is the back-translator
   prompt below plus the Lean statement(s) **and the custom definitions they
   reference** (the `def`s for any non-Mathlib symbols in the signature —
   without these the rendering is impossible). The subagent gets no paper
   text, no NL claim, no conversation context.

   **Back-translator subagent prompt (verbatim):**

   ```
   You are given Lean 4 declaration(s): one or more theorem/axiom statements
   plus the definitions they reference. You have NO other context. Do not
   guess what paper or topic this comes from.

   Render each statement into precise mathematical English, clause by clause:
   1. BINDERS — list every quantified variable IN ORDER with its quantifier
      (∀/∃) and type. State the quantifier nesting explicitly ("for all c
      there exists i such that for all θ ...").
   2. HYPOTHESES — restate each hypothesis exactly. If a variable is a bare
      ℝ/ℕ/type with no hypothesis relating it to anything else, you MUST say
      "an arbitrary real number, unconstrained" — do not assume it denotes
      anything.
   3. CONCLUSION — restate with the exact relation (≤ vs <, = vs ≤,
      direction), every numeric constant verbatim, and the exact operators
      (sup'/inf'/∑/max/min).
   4. For each ∃: state precisely what is claimed to exist and which
      properties bind it.

   Rules:
   - Variable and theorem NAMES ARE NOT EVIDENCE. Treat `epoch_count`,
     `norm_diff`, `regret` as opaque identifiers; describe only what the
     types and hypotheses enforce. If a name suggests meaning the statement
     does not enforce, ignore it.
   - Note encodings but render plain meaning: `Fin n → ℝ` = "a function from
     an n-element index set to the reals"; `Finset.univ.sup'` = "maximum
     over the (finite, nonempty) type"; `[Fintype X]` = "X is a FINITE type".
   - End with: "In plain terms, this asserts: <one sentence>."
   - If the statement read literally is trivially true, trivially false, or
     false for an easy instantiation, SAY SO with the instantiation.
   ```

2. Compare the returned English against the original claim with this rubric
   (you have the paper claim and the back-translation, NOT the Lean):

   ```
   For each category output MATCH, NOTE (benign formalization choice), or
   MISMATCH (blocking):

   1. QUANTIFIER ORDER & BINDING — same variables, same ∀/∃, same nesting?
      Any paper-universal made existential/fixed, or vice versa? Any variable
      the paper binds to a SPECIFIC object (an algorithm's epoch count, a
      maximizer, a fixed point) that the Lean statement leaves arbitrary?
      Arbitrary-where-specific is always MISMATCH.
   2. RELATION — ≤ vs <, = vs ≤, direction, sup vs inf, max vs min.
   3. CONSTANTS — every constant, exponent, log base, √ matches verbatim
      (2 vs 4, 2logK/β vs logK/β).
   4. HYPOTHESIS SET — every paper hypothesis present; NO extra or silently
      strengthened hypotheses (e.g., K ≥ 1 became log K ≥ 1) — extras
      violate Rule 1; none weakened.
   5. OBJECT TYPES — what the variables actually range over: finite vs
      compact vs arbitrary; matrix vs scalar stand-in; distribution vs
      weight function; the actual MDP/process vs an abstract sequence of
      reals. A scalar standing in for a structured object is MISMATCH unless
      the relation between the scalars IS the cited lemma and this is
      disclosed.

   Benign (NOTE, never MISMATCH): Fin n → ℝ for ℝⁿ; Finset ∑/sup' for finite
   ∑/max; (0 ≤ x : ℝ) for x : ℝ≥0; currying; [Fintype]/[Nonempty] instance
   arguments when the paper setting is finite/nonempty; a named hypothesis
   restating a standing assumption.

   Any MISMATCH → the formalization is unfaithful: fix the Lean statement
   and redo the back-translation, or carry the discrepancy into the verdict
   (the block cannot count as verifying the paper's claim). Never downgrade
   MISMATCH to NOTE to preserve a verdict.
   ```

3. Record the outcome in the run record — REQUIRED, not optional:

   ```python
   d.record_backtranslation("main",            # or block name / refutation
                            verdict="MATCH",   # MATCH | NOTE | MISMATCH
                            notes="...",
                            categories={"quantifiers": "MATCH", ...})
   ```

   `d.finish()` warns when the assembled main theorem, a kernel-backed
   refutation, or an `add_novel` candidate has no recorded back-translation
   — an audit that lives only in the conversation is not evidence. Also
   record the per-category outcomes in the block's report row. A MISMATCH on
   the main theorem or an axiom blocks the verdict (fix and re-audit, or
   downgrade); a MISMATCH on a library candidate blocks `d.add_novel` until
   the statement and docstring agree.

#### Rules for Formalize

- MUST compile. Iterate until it does or report a clear gap.
- Prefer using library theorems over reproving from scratch.
- Keep proofs short: < 20 lines of tactic proof preferred.
- No `sorry` in final output. If genuinely stuck, output the best attempt with the specific error.
- **Never add hypotheses not in the input.**
- **Never assume what should be proven.**

**On block failure:**
1. If the block is **mathematically false** (`PROOF_INVALID` unless it is the
   complete theorem) or **incomplete** (INCOMPLETE): skip formalization for that
   block and any blocks that depend on it.
2. **Still formalize all independent blocks.** A failure in one block does NOT excuse skipping independent blocks. Process every block in topological order; only skip a block if it depends on a failed block.
3. After all independent blocks are processed, proceed to Phase 6 with the appropriate verdict.

---

### Phase 4: Final Compile + Kernel Audit

The fully-discharged skeleton (no sorries left) IS the final file:
1. Imports at the top (only what's needed)
2. Helper lemmas (novel blocks, proven from the proof's own argument)
3. Main theorem with proof composing all blocks

Compile it with `d.assemble(...)`. On success the driver runs the
**kernel-level audit** automatically: `#print axioms <main_theorem>` reports
the exact axiom closure, transitively through all imports. This is the
verdict source — not the source-code regex:
- closure ⊆ `{propext, Classical.choice, Quot.sound}` → VERIFIED
- custom axioms in the closure → VERIFIED MODULO AXIOMS (each must satisfy
  the lifecycle below)
- `sorryAx` in the closure → UNVERIFIED, **no exceptions** — this catches a
  sorry hiding in an imported module, which compiles cleanly with no warning
  and no `sorry` token in your source.
If the kernel check itself fails (`closure.ok == False`), do NOT report
VERIFIED — fix the check first (usually a wrong/unqualified theorem name).

**When the main statement cannot even be STATED in Lean** (its conclusion
needs infrastructure missing from Mathlib — e.g. a.s. convergence of
stochastic iterates, weak convergence, Itô calculus), sketch/assemble/
kernel-closure are structurally impossible, not negligently skipped.
Record that explicitly:

```python
d.main_unformalizable("a.s. convergence of SA iterates needs "
                      "measure-theoretic stochastic-approximation "
                      "infrastructure absent from Mathlib")
```

status()/finish() then render Sketch/Kernel as `n/a — main statement not
formalizable (<reason>)` instead of the misleading "not run" / "closure not
obtained". This never weakens the verdict (typically INCOMPLETE) — it makes
the record honest about WHY there is no kernel closure. A later successful
`assemble()` clears it.

#### Axiom lifecycle (the ONLY permitted use of `axiom`)

A block may be temporarily axiomatized ONLY when ALL of these hold:
1. It is a **well-known named result** citable to a specific textbook or paper
   (e.g., von Neumann's minimax theorem, Brouwer's fixed point theorem) — never
   the input paper's own claim or an unnamed "standard argument".
2. The input proof correctly *invokes* it (hypotheses checked, per the
   Hypothesis Audit).
3. It is **registered** in `rlverify/results/axiom_backlog.md` with the
   statement, the reference, and what infrastructure formalizing it needs.
4. Its statement **passes the back-translation audit** (Phase 3). In
   particular, every variable in an axiom must be bound by hypotheses to what
   its name suggests — an axiom of the form `(E : ℕ) : (E : ℝ) ≤ bound`
   asserts the bound for EVERY natural number and is inconsistent (False is
   derivable), regardless of what `E` is called. An inconsistent axiom makes
   every downstream "proof" vacuous.

After the verdict, attempt to formalize each axiom (as a separate effort —
this does not block the verdict). If proved, replace the axiom, add the
theorem to the library, and move the backlog entry to "Formalized".

Any axiom outside these conditions → the block is a gap and the verdict is
UNVERIFIED (INCOMPLETE). Axioms never enter the library: `d.add_novel`
rejects code containing `axiom` declarations.

---

### Phase 5: Library Growth

**This phase is mandatory — evaluate every verified novel block, including those salvaged during early exit.** Even when the overall verdict is UNVERIFIED, independent correct blocks that compiled must be evaluated for library addition. Do not skip this phase.

For each novel block that compiled, decide: does it state a general mathematical fact that could appear in a different proof? If yes, first re-run the two gates (statements drift during proof iteration):

1. `d.library_search(statement)` must still return not-found — if it finds a
   proof now, the lemma is redundant; skip it.
2. The back-translation audit (Phase 3) on the candidate must come back with
   no MISMATCH between the statement and its docstring/claimed content.

Then add it using the **code mode** (preferred — pass the full compilable Lean file):
```python
d.add_novel(
    name="lemma_name",
    code=full_lean_code,           # statement is extracted automatically
    target_dir="Optimization",     # ALWAYS set this — pick the topic directory
    docstring="One-line NL description (indexed for search)",
    reusable=True,
    reuse_reason="General atomic fact plausibly useful in other proofs",
)
```
The `target_dir` maps to `RLGeneralization/{target_dir}/LemmaName.lean`. Choose a directory that fits the lemma's topic (e.g., `Optimization`, `Concentration`, `MDP`). Always pass a `docstring` (or include a `/-- ... -/` doc comment in the code) — without one the lemma is nearly invisible to natural-language search.

`add_novel` enforces, automatically:
- **Reusable-only promotion**: requires `reusable=True` plus a concrete
  `reuse_reason`; proof-specific glue remains in run artifacts but is not
  promoted to the shared library.
- **No duplicates**: refuses if the corpus already has the id or a lemma with the same name.
- **No axioms**: refuses code containing `axiom` declarations.
- **No root import**: the code must use specific imports (`RLGeneralization.X.Y` or `Mathlib.*`), never bare `import RLGeneralization` (it would create an import cycle once registered).
- **Build registration**: the new module is registered in `RLGeneralization.lean` and `lake build` is run; on failure (e.g., a name collision with an existing declaration) the addition is rolled back. After adding lemmas, run `lake build RLGeneralization` once so the root module is rebuilt and future `import RLGeneralization` sees them.

**The library contains only generalized, reusable building blocks — never paper-specific or proof-specific results.** Every addition must be decomposed to its most general form.

**Add** if the lemma is:
- A self-contained mathematical fact stated in **general terms** (not tied to this proof's specific variables, notation, or context)
- Decomposed to its atomic level — if a result combines two independent facts, add them separately
- Something another proof could plausibly need (e.g., an inequality, a property of a standard construction, a convergence result)
- Named descriptively for what it IS, not where it came from (e.g., `weighted_sum_le_sup` not `cfpo_step3_bound`)

**Skip** if the lemma is:
- A paper-specific assembled proof (e.g., a theorem that chains together multiple lemmas for one specific paper's argument)
- Proof-specific glue that combines other blocks for this particular argument
- A trivial restatement or renaming of an existing library theorem
- An intermediate step that only makes sense in this proof's context
- Tied to specific variable names, constants, or notation from the paper

Do NOT add instantiations — they're already covered by the general theorem in the library.

**Generalization check**: Before adding, ask: "Would I need to rename variables or strip context to make this useful elsewhere?" If yes, do that first. If the result can't be stated without referencing this proof's specific setup, skip it.

---

### Phase 6: Verdict

If a session was started with `d.begin(...)`, close it with `d.finish()` — it
writes the assembled Lean file (with `#print axioms <main>` appended, so the
verdict is independently reproducible via `lake env lean runs/<file>.lean`)
plus a JSON run record (blocks, kinds, statuses, verdict, kernel axioms,
falsifications) to `runs/`, which feeds aggregate statistics like the library
hit-rate. Call `d.finish()` only after Phase 5 — novel lemmas added after
`finish()` succeed but are not reflected in the run record (the driver warns).

Output ONE of:

**VERIFIED** — complete Lean 4 code compiles AND the kernel axiom closure
(`#print axioms`, reported by `d.assemble`) is ⊆ {propext, Classical.choice,
Quot.sound}, every step follows from the proof sketch.
- Show the complete code
- Show the building block resolution table
- A compile success alone is NOT VERIFIED — the kernel closure is the source
  of truth (it sees sorries and axioms hidden in imports).

**VERIFIED MODULO AXIOMS** — compiles, but the kernel closure contains custom
axioms, each satisfying ALL FOUR Axiom lifecycle conditions (Phase 4,
including the back-translation audit).
- List each kernel-reported axiom with its reference and backlog entry
- This is weaker than VERIFIED — say so explicitly

**UNVERIFIED/X** where X is one of `WRONG`, `PROOF_INVALID`, `INCOMPLETE`,
`MISMATCH`, `HYPOTHESIS_VIOLATION`, `CIRCULAR` (see Rule 7 for exact
definitions):
- Which building block fails and the **specific classification** (with justification — e.g., name the counterexample for WRONG, name the missing infrastructure for INCOMPLETE)
- For HYPOTHESIS_VIOLATION: name the lemma, the violated hypothesis, the offending argument, and why. Note any camouflage (e.g., the proof checks an easy condition while skipping the hard one).
- For CIRCULAR: name both blocks on the cycle and the conditioning event (or implicit assumption) that closes the loop — e.g., "Lemma 3 invokes Lemma 2 unconditionally, but Lemma 2's conclusion holds only on the event that IS Lemma 3's conclusion."
- State whether the verdict is **kernel-backed** (quote the refutation
  theorem and its closure) or **audit-only** — never present an audit-only
  verdict as machine-checked.
- Show how far the proof got (what DID verify)
- Every block must have a status — never leave a block as "not attempted"

---

## Rules — Verification Integrity

1. **Never add hypotheses.** If the proof doesn't state an assumption, you
cannot add it. If the formalization needs `(h : 0 < n)` but the submission
doesn't mention it, classify what the evidence establishes: an undefined
displayed object or omitted statement side condition is
HYPOTHESIS_VIOLATION; a refuted proof inference is PROOF_INVALID; the complete
theorem is WRONG only when it remains well-defined and an exact counterexample
satisfies every stated hypothesis.

2. **Never assume conclusions of building blocks.** Each block must be PROVEN (either from the library or from the proof's own argument).

3. **Never change the theorem statement.** The statement in the input is what gets verified. If it's wrong, it's wrong.

4. **Never fill logical gaps.** If the proof says "by standard arguments" without justification, you must still formalize it. If it's in the library → library match. If it's genuinely novel but the proof provides no argument → report as INCOMPLETE.

5. **Every building block must be CLOSED.** No block can remain as an unproven hypothesis in the final code.

6. **Report partial progress.** If 4/5 blocks verify but 1 fails, show what works and what doesn't.

7. **Distinguish failure types using EXACTLY these definitions:**

   - **WRONG**: The complete claimed mathematical statement is **false**. A
     well-defined exact instance satisfies every stated hypothesis and negates
     the theorem's conclusion. A false intermediate inference, an undefined
     term, or a missing premise is not by itself a theorem counterexample.

   - **PROOF_INVALID**: A submitted proof inference is refuted or logically
     invalid, while the theorem itself may still be true. Name the exact step
     and keep theorem truth UNKNOWN.

   - **INCOMPLETE**: The proof's mathematical argument is **correct but cannot be fully formalized**. The proof provides a valid sketch or invokes a valid result, but the formalization fails because: (a) required infrastructure is missing from Mathlib (e.g., Brouwer's theorem, spectral theory), (b) the proof says "by standard arguments" without enough detail to reconstruct, or (c) the proof skips a non-trivial step that isn't in the library. The key distinction from WRONG: the underlying math is sound.

   - **MISMATCH**: The proof cites a specific result but the actual library theorem has **different hypotheses** than what the proof assumes. The proof's reasoning would be correct if the cited result had the assumed signature, but it doesn't.

   - **HYPOTHESIS_VIOLATION**: A correct lemma is applied to an argument that **provably violates** a stated hypothesis. The lemma is right, the instantiation is wrong. Distinct from WRONG (the lemma itself is correct) and from INCOMPLETE (the proof isn't missing a step — it's applying a step to the wrong object).

   - **CIRCULAR**: A block's justification **presupposes the conclusion of a block that (directly or transitively) depends on it** — the proof's true dependency graph has a cycle. Includes cycles hidden by conditional conclusions: a lemma proved "on the event E" invoked unconditionally by the block that proves E (Hypothesis Audit item 4). Distinct from HYPOTHESIS_VIOLATION (the dropped condition is another block's conclusion, not a library lemma's hypothesis) and from INCOMPLETE (no step is missing — the steps exist but support each other). The theorem itself may still be true with an added hypothesis, but adding it violates Rule 1.

   **Decision rule**: A well-defined counterexample satisfying every theorem
   hypothesis and negating the complete conclusion → WRONG. A counterexample
   to only a submitted inference or another logical fallacy in the proof →
   PROOF_INVALID. An operation undefined under the written contract or a
   load-bearing omitted statement hypothesis → HYPOTHESIS_VIOLATION. If two
   blocks rest on each other → CIRCULAR. If the mathematical argument appears
   sound but cannot be closed → INCOMPLETE. Never collapse these axes.

8. **No `sorry` in the kernel closure.** `sorryAx` in the `#print axioms`
   closure ⇒ UNVERIFIED, no exceptions — even when the file compiles with no
   `sorry` token visible (the sorry may live in an imported module). `axiom`
   is permitted only under the four Axiom lifecycle conditions (Phase 4); the
   verdict is then VERIFIED MODULO AXIOMS, never plain VERIFIED.

9. **Warn on search limitations.** `d.grep()` is substring-only and `d.hybrid_search()` is keyword-based (BM25) — neither understands semantics. `d.library_search()` is type-directed but matches only up to unification (misses shape variants). If a block is marked "novel" but could plausibly exist under a different shape, say so.

## Known Limitations

- **Search**: `d.grep()` is substring matching (id matches rank first); `d.hybrid_search()` is BM25 keyword ranking over id + tags + docstring + statement. Try both, with multiple phrasings, plus `d.library_search()` once a statement elaborates.
- **Falsification scope**: the numeric gate only covers concretely sampleable claims; a PASS is never evidence, and constant/log-factor errors may need astronomically large parameters to manifest.
- **Schematic proofs**: "by induction on X" without naming the specific lemma may not decompose cleanly.
- **Non-compiling modules**: 3 library modules have broken builds (Hellinger, ChiSquared, TriangularDiscrimination). Search marks their theorems `[NOT BUILT — cannot import]` — do not import them; treat such a block as needing its own proof (or the Axiom lifecycle if it qualifies).
- **Corpus freshness**: the corpus is regenerated from the Lean source tree by `python scripts/export_retrieval_corpus.py` (use `--check` to detect drift). If search results look stale, rebuild it.
