# RLVerify

A proof verification pipeline for reinforcement learning theory. Given a theorem and its proof, RLVerify determines whether the proof is correct by formalizing it in Lean 4 against a 1700+ theorem library.

## How It Works

```
Input: theorem + proof sketch
  ↓
Sealed adversarial triage (a subagent that sees ONLY the proof text
  ranks suspect steps — prioritizes scrutiny order, never decides,
  never skips a check; an all-clear carries zero weight)
  ↓
Decompose into building blocks (+ hypothesis audit)
  ↓
Resolve each block: library / instantiation / novel
  (type-directed dedup: `exact?` over Mathlib + library before "novel")
  (near-match log-arg scan: a kernel-checked neighbor lemma with a
   DIFFERENT log argument is flagged — every `differs:` line must be
   adjudicated in the report)
  ↓
Falsification gate: numeric counterexample search on novel blocks
  (a re-verified counterexample = instant UNVERIFIED/WRONG)
  ↓
Sketch: full skeleton with blocks sorried — compiling skeleton
  machine-checks the decomposition before any proof effort
  ↓
Discharge each block (must compile; anti-vacuity + back-translation audits)
  ↓
Final compile + kernel audit (#print axioms: sorryAx ⇒ UNVERIFIED,
  custom axioms ⇒ VERIFIED MODULO AXIOMS — transitive through imports)
  ↓
Output: VERIFIED (with reproducible certificate) or UNVERIFIED (with failure point)
```

RLVerify does **not** fix proofs. If a step is wrong, it reports the failure.

## Commands

These are Claude Code skills, run from the project root:

| Command | What it does |
|---------|-------------|
| `/verify-full-process "theorem" "proof"` | Full pipeline: verify a single proof end-to-end |
| `/verifyRL-paper paper.tex [Section N]` | Verify a multi-lemma paper proof in dependency order |
| `/formalize "statement"` | Formalize one theorem with compilation loop and anti-vacuity checks |
| `/expand-library` | Autonomous library growth from RL theory sources |
| `/audit-papers` / `/extract-proofs` | Paper auditing and proof-fixture extraction |

Output of a verification is either:
- Complete, compiling Lean 4 code (VERIFIED), or
- The specific step that fails and why (UNVERIFIED), with a JSON run record in `runs/`.

## How Verification Works

### Building Block Classification

Each step in the proof is classified as:

- **Library**: an exact match exists in the formalization library. Applied with `exact theorem_name args`.
- **Instantiation**: a more general library theorem can be specialized to this case.
- **Novel**: not in library. Must be proven from the proof's own argument.
- **Prior** (paper mode only): proven by a component already verified in this session.

### Axiom Lifecycle

A block may be temporarily axiomatized ONLY if it is a well-known named result (citable to a textbook/paper — e.g., von Neumann's minimax theorem), correctly invoked, registered in `rlverify/results/axiom_backlog.md`, AND its statement passes the back-translation audit — every variable must be bound by hypotheses to what its name suggests (an axiom `(E : ℕ) : (E : ℝ) ≤ bound` over an arbitrary `E` is inconsistent regardless of the name):

```
Paper hits missing named result → temporarily use `axiom` in Lean
  ↓
Register in axiom_backlog.md (statement + reference + missing infrastructure)
  ↓
Verdict: VERIFIED MODULO AXIOMS (explicitly weaker than VERIFIED)
  ↓
Afterwards: attempt to formalize the axiom
  If proved → replace axiom with theorem, add to library, move backlog entry to "Formalized"
  If blocked → stays Pending in axiom_backlog.md
```

Axioms are NOT foundational assumptions — they are theorems not yet proved. Axioms never enter the library: `d.add_novel` rejects code containing `axiom` declarations, and `d.assemble` flags any axiom it finds.

### Verification Integrity

The pipeline **never**:
- Adds hypotheses not in the original proof
- Assumes conclusions of building blocks as hypotheses
- Inserts `sorry` to make things compile
- Changes the theorem statement

If any building block cannot be closed, the verdict is **UNVERIFIED** with the specific failure.

**The verdict source is the kernel, not the source code.** `d.assemble` runs
`#print axioms <main_theorem>` and reads the exact axiom closure, transitively
through all imports: `sorryAx` anywhere in the closure ⇒ UNVERIFIED (this
catches a sorry hiding in an imported module, which compiles with exit 0 and
no `sorry` token in the file); custom axioms ⇒ VERIFIED MODULO AXIOMS;
closure ⊆ {propext, Classical.choice, Quot.sound} ⇒ VERIFIED. Saved run
artifacts in `runs/` end with the `#print axioms` line, so any verdict is
independently reproducible with `lake env lean runs/<file>.lean`.

**Failure verdicts can be kernel-backed too.** For the verdict-deciding
block of an UNVERIFIED run, `d.refute` compiles a small Lean counterexample
to the invalid *inference* (premises-hold ∧ ¬conclusion on a concrete
instance). The run record's `verdict_evidence` becomes `"kernel"` only when
that refutation compiled with a clean standard-axiom closure — derived,
fail-closed, never asserted. Otherwise the verdict is audit-only, and the
report must say which it is. A kernel-backed refutation certifies "this
inference step is invalid", never "the theorem is false".

**Statement faithfulness is audited, not assumed.** The main theorem, every
axiom, and every library candidate gets an independent back-translation: a
subagent that never sees the paper renders the Lean statement back into
English (variable names treated as opaque), and the result is diffed against
the original claim (quantifier binding, relation, constants, hypothesis set,
object types). A mismatch blocks the verdict.

### Failure Types

| Type | Meaning |
|------|---------|
| WRONG | The claimed step is mathematically false |
| INCOMPLETE | The argument is sound but a step can't be formalized (missing infrastructure or detail) |
| MISMATCH | A cited result doesn't match the library's version |
| HYPOTHESIS_VIOLATION | A correct lemma is applied to an argument that violates its hypotheses |
| CIRCULAR | (paper mode) the dependency graph has a cycle |

## The Library

The corpus (`rlverify/corpus.jsonl`) contains 1700+ theorems from `RLGeneralization/`, covering MDP theory, concentration inequalities, bandits, policy optimization, imitation learning, linear MDPs, offline RL, and exploration.

**The Lean source tree is the single source of truth; the corpus is a derived cache.** Rebuild it with:

```bash
python scripts/export_retrieval_corpus.py          # regenerate corpus.jsonl
python scripts/export_retrieval_corpus.py --check  # report drift (duplicates, stale/missing entries, unbuilt modules)
```

Run the rebuild after library-expansion sessions. Novel-lemma metadata (tags, docstrings) is merged from the existing corpus by id.

When a novel lemma is verified and is fundamental (reusable), `d.add_novel` adds it to the corpus AND the source tree, registers it in `RLGeneralization.lean`, and builds it (rolling back on failure). It refuses duplicates, axioms, files that import the root module (cycle), and — via a kernel `#print axioms` check — any lemma whose closure contains `sorryAx` or custom axioms (which catches a sorry hiding in an *imported* module, invisible to source-level checks).

### Reuse Tracking

The retriever tracks two levels of corpus usage, persisted across sessions in `rlverify/corpus_retrieval_stats.json`:

- **Retrieved**: a premise appeared in search results (`d.grep` / `d.hybrid_search`)
- **Matched**: a premise was used to resolve a proof step (`d.resolve(library=...)` / `d.resolve(instantiation=...)` record this automatically)

This data answers: which theorems are actually used? Which are dead weight? Inspect with `d.reuse_stats()`, or run the aggregate report:

```bash
python3 scripts/corpus_reuse_report.py   # joins library_expansion.tsv with the
                                         # stats: per added lemma, matched
                                         # (real signal) vs retrieved (weak)
```

Only **matched** counts are evidence of value — `retrieved` is polluted by the expansion loop's own redundancy searches. Matches come exclusively from verification runs (`d.resolve(library=...)` / `instantiation=...`), so the way to grow ground truth is to run `/verify-full-process` on real proofs.

**Design rationale** (informed by [DreamProver, April 2026](https://arxiv.org/abs/2604.11547)):
LEGO-Prover's growing skill library had 0% verbatim reuse — raw lemmas were too proof-specific. DreamProver fixed this with abstraction + dedup + LRU forgetting, reaching 58% reuse. Our library differs (retrieval corpus, not generation context), but the feedback loop is the same: without tracking which entries get used, you can't distinguish a useful library from one padded with ballast.

**Future work** (gated on accumulating enough stats):
- Deprioritize entries with 0 retrievals after N runs in search ranking
- Semantic dedup if reuse data reveals high redundancy
- Per-module coverage reports (which modules have high match rates?)

## Reading the Output

Every pipeline event is one line in a fixed grammar — `[phase] block status`:

```
[resolve   ] regret_decomposition         ✓ library — Bandits.Pseudoregret….pseudoRegret_eq_sum_gap_mul_pullCount
[gate      ] ✗ DUPLICATE (12s) — exact? found RLGeneralization.pseudoRegret_eq_sum_gap_mul_pullCount
[falsify   ] count_bound                  · SKIPPED — contains an unspecified O(1) constant
[sketch    ] ✓ skeleton compiles (4s) — decomposition machine-checked (blocks still sorried)
[discharge ] step2                        ✓ formalized (4s)
[assemble  ] ✓ VERIFIED — kernel closure ⊆ {propext, Classical.choice, Quot.sound}
```

Glyphs: `✓` success · `✗` failure/refuted · `~` instantiation · `?` novel ·
`·` info/skipped · `⚠` warning.

- `d.status()` — live per-block table (kind, falsify verdict, compiled, match)
  at any point in a session.
- `d.finish()` — fixed-format summary block; grep its `Verdict :` line for
  the one-line result. The JSON run record in `runs/` carries the same data
  for aggregation.

## Using the Driver Directly

```python
from rlverify.driver import VerifyDriver
d = VerifyDriver()

# Search the library
d.grep("bellman")                  # substring search (id matches first; unbuilt modules marked)
d.hybrid_search("variance of bounded random variable")   # BM25 keyword search
d.show("RLGeneralization.MDP.BellmanContraction.bellmanOptOp_contraction")
d.reuse_stats()                    # corpus reuse summary

# Type-directed search: the statement IS the query (`by exact?` over
# Mathlib + RLGeneralization + deps, ~15s). found=True ⇒ duplicate.
d.library_search("theorem t (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : Real.sqrt (a+b) ≤ Real.sqrt a + Real.sqrt b")

# Compile Lean code (prefer narrow imports — ~6x faster than `import RLGeneralization`)
d.compile("""
import RLGeneralization.MDP.BellmanContraction
variable (M : FiniteMDP)
theorem foo (Q₁ Q₂ : M.ActionValueFn) :
    M.supDistQ (M.bellmanOptOp Q₁) (M.bellmanOptOp Q₂) ≤ M.γ * M.supDistQ Q₁ Q₂ := by
  exact M.bellmanOptOp_contraction Q₁ Q₂
""")

# Fast iteration: persistent REPL with Mathlib + RLGeneralization pre-imported.
# One-time warmup (~10-60s), then sub-second per check. No import lines in code.
# Iteration only — gates/kernel audits stay on d.compile (fresh process).
d.repl_verify("example : 1 + 1 = 2 := by norm_num")

# Validate a statement before proving it (proof stubbed with sorry)
d.compile_statement("theorem foo (x : ℝ) (hx : 0 < x) : 0 < x * x",
                    imports=["Mathlib.Tactic"])

# Full session (sketch-first)
d.begin("my_theorem")

# Sealed triage output is recorded, not just narrated (fail toward scrutiny:
# malformed triage ⇒ all_clear=False, suspects=[])
d.record_triage(suspects=[{"step": 3, "suspicion": "union bound scope",
                           "severity": "high"}], all_clear=False)

# statement_nl is mandatory: it feeds the near-match log-arg scan, which
# flags kernel-checked neighbor lemmas whose log arguments differ
d.resolve("step1", library="Some.Library.Theorem",
          statement_nl="radius sqrt(ln(2K/delta)/(2t))")   # records reuse match
d.resolve("step2", novel=True, statement_nl="...")

# Early exits are persisted, not just narrated: a hypothesis-violating block
# is its own resolution kind, and the verdict lands in the runs/ JSON.
d.resolve("bad_step", violation="Lib.correct_lemma",
          reason="applied at a sample-dependent count; lemma requires fixed n")
d.set_verdict("UNVERIFIED/HYPOTHESIS_VIOLATION",
              reason="bad_step applies Lib.correct_lemma at a random count",
              block="bad_step")

# Optional upgrade from audit-only to kernel-backed (time-boxed, ≤5 compiles):
# a Lean counterexample asserting premises-hold ∧ ¬conclusion for a concrete
# instance. Failure to build one never changes the verdict.
d.refute("bad_step", counterexample_code,
         description="the refuted claim, verbatim")

from rlverify.falsify import FalsifyReport             # numeric gate on novel blocks
d.record_falsification(FalsifyReport(block="step2", verdict="PASSED",
                                     instances=200_000, hyp_satisfied=180_000))

d.sketch(skeleton_code, expected_blocks=["step2"])     # blocks sorried; compiling
                                                       # skeleton = decomposition checked
d.formalize("step2", statement="theorem ...", proof="...", imports=["..."])
d.assemble(statement="theorem main ...", proof="...", imports=["..."])
                 # runs the kernel audit (#print axioms) and prints the verdict
d.finish()       # writes .lean output (+ #print axioms) + JSON run record to runs/

# Library growth (code mode; statement auto-extracted, docstring indexed for search)
d.add_novel(
    name="weighted_sum_le_sup",
    code=full_lean_file,
    target_dir="Optimization",
    docstring="A probability-weighted sum is at most the supremum of the summands.",
    reusable=True,
    reuse_reason="General weighted inequality useful beyond the source proof.",
)
```

## Requirements

- Lean 4 toolchain (for compilation checks)
- The `RLGeneralization` project built (`lake build`)
- Python 3.10+

No API keys needed. The reasoning is done by Claude Code; the Python layer provides search, compilation, and corpus management.

## Known Limitations

- **Search**: `d.grep()` is substring-based and `d.hybrid_search()` is BM25 — neither is semantic. `d.library_search()` is type-directed but matches only up to unification: it misses an existing lemma that is stronger but differently shaped (n-ary vs binary, `Finset.range` vs `Fintype`, `<` vs `≤`). Use all three before declaring a block "novel".
- **Falsification scope**: the numeric gate covers concretely sampleable claims only; a PASS carries zero verification weight, and constant/log-factor errors may need astronomically large parameters to manifest (growing parameters are sampled on log-scale grids for this reason).
- **Schematic proofs**: "by induction" or "by linearity" without naming the specific lemma may not decompose cleanly. Works best with proofs that name their building blocks explicitly.

Resolved 2026-06-11 (formerly listed here):

- ~~3 non-compiling modules~~: Hellinger, ChiSquared, TriangularDiscrimination repaired and re-imported in `RLGeneralization.lean`; all kernel-checked, no more `[NOT BUILT]` markers.
- ~~Compile latency~~: `d.repl_verify(code)` runs checks against a persistent REPL (vendored at `tools/repl`, leanprover-community/repl v4.28.0; build once with `cd tools/repl && lake build`). One warmup (~10–60s) imports Mathlib + RLGeneralization, then each check is sub-second. Iteration fast path only — `library_search`, pre-`add_novel` re-runs, and kernel audits still use fresh `lake env lean` compiles so certified results never depend on REPL session state. `d.compile` with narrow imports (~4s) remains available.
