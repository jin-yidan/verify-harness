---
name: verifyRL-paper
description: Verify a multi-lemma mathematical paper with dependency extraction, circularity checks, trusted harness execution, and Lean evidence
user_invocable: true
---

# /verifyRL-paper — RLVerify: Verify a Multi-Lemma Paper Proof

Verify a full proof from a paper (LaTeX or natural language) that contains multiple interdependent lemmas/theorems. Automatically extracts the dependency structure, detects circularity, and verifies each lemma in topological order.

**CRITICAL PRINCIPLE: This tool VERIFIES — it does not REPAIR.** If the proof is wrong, incomplete, has logical gaps, or contains circular reasoning, report the failure. Never add assumptions, hypotheses, or proof steps that aren't in the input to make it compile.

## Execution Entry Point — Harness Only

This command is a skill wrapper around the RLVerify BYO-agent harness. Do **not**
hand-run `python -m rlverify.ingest`, instantiate `VerifyDriver`, or manually
drive `PaperSession` from this skill. Those are internal implementation details
owned by the harness path.

Start every run from the repository root using the harness:

```bash
python3 -m harness verify <paper-or-fixture> --backend claude --report
```

For an arXiv URL, PDF, `.tex`, or pasted paper, use the paper front-end.
Always run the extraction/estimate step first:

```bash
python3 -m harness verify <paper-or-url> --theorem "<label>" --backend claude --dry-run
python3 -m harness verify <paper-or-url> --all-theorems --backend claude --dry-run
```

Report the extracted fixture path(s) and the formal-proof cost estimate to the
user. Do not launch the formal proof attempt until the user approves that
estimate. After approval, rerun without `--dry-run` and add `--report`:

```bash
python3 -m harness verify <paper-or-url> --theorem "<label>" --backend claude --report
python3 -m harness verify <paper-or-url> --all-theorems --backend claude --report
```

Use `--theorem` when the user names a theorem/lemma/proposition. Use
`--all-theorems` only when the user explicitly asks for a whole-paper run or
approves the larger spend. If the user gives only a paper link and no theorem
label, run a dry extraction to list candidates:

```bash
python3 -m harness verify <paper-or-url> --backend claude --dry-run
```

If multiple candidates are reported, ask for the theorem label unless the user
has already requested `--all-theorems`.

Network access for arXiv is parent-side harness work. If the environment blocks
network, rerun/approve the **harness verify** command with network permission;
do not bypass the harness by downloading or ingesting the paper manually.

**This skill wraps `/verify-full-process`.** Phase 0 (parse and order) and Phase 6 (report) below are paper-specific. The per-component verification in between is the `/verify-full-process` procedure — read `.claude/commands/verify-full-process.md` and apply its Phases 1–5 to each component, with the paper-specific modifications listed in "Per-Component Verification". Do not re-derive that machinery from memory; the single-proof skill is the source of truth for decomposition, hypothesis audit, formalization, anti-vacuity checks, the axiom lifecycle, and library growth.

## Input

$ARGUMENTS

The input can be:
1. **A `.tex` file path** — optionally followed by a section filter (e.g., `paper.tex Section 3`)
2. **A `.pdf` file path** — a paper PDF on disk
3. **An arXiv id or URL** — e.g. `2407.13743`, `arXiv:2407.13743`, or `https://arxiv.org/abs/2407.13743`
4. **Inline text** — LaTeX or natural language with theorem/lemma/proof content pasted directly

Forms 2 and 3 are normalized by the harness paper front-end before verification.
The harness materializes reviewable fixtures under `rlverify-out/` and then runs
the same verifier used for fixture folders.

The input should contain:
- A main theorem statement
- Multiple lemmas/propositions/claims with their proofs
- Cross-references between them (e.g., "by Lemma 3", "from Proposition 2")

## Harness Workflow

The executable workflow is:

1. Run `python3 -m harness verify ... --dry-run` with `--backend claude`.
2. Let `harness.ingest` fetch/normalize arXiv/PDF/TeX input and materialize the
   theorem fixture.
3. Show the harness formal-proof cost estimate and wait for user approval.
4. Rerun without `--dry-run`; let `harness.runner` launch the authenticated Claude Code driving agent and
   sealed grader calls.
5. Report the harness verdict line and artifact/report paths. Do not report a
   verdict that contradicts the harness output.

## Internal Paper Semantics

Per-component verification is the **frozen `/verify-full-process` pipeline** — do not
reimplement it. The *cross-component* concerns (dependency graph, cycle
detection, topological order, the paper-level sketch, prior-component reuse,
and the paper record) are owned by `rlverify.paper.PaperSession`, which
*composes* `VerifyDriver` (it never modifies it):

```python
from rlverify.driver import VerifyDriver
from rlverify.paper import PaperSession

d = VerifyDriver()
p = PaperSession("<paper_name>", driver=d)   # one paper-level session
```

`PaperSession` is the code backing for Phase 0 and Phase 6 below. Register every
extracted component on it (`p.add_component(label, statement, proof, deps=[...],
kind=..., external=..., is_main=...)` and `p.add_standing_assumption(...)`),
then use its graph/order/sketch/record methods instead of tracking that state by
hand. Each component's actual Lean verification still runs the full `/verify-full-process`
procedure via `d`.

---

### Phase 0: Parse and Order

Extract the logical structure of the proof and determine verification order.

#### Step 0.0: Normalize Input (harness front-end)

If the argument is a **`.pdf` path**, an **arXiv id**, or an **arXiv URL**, normalize
it through the harness paper front-end:

```bash
python3 -m harness verify "<arg>" --theorem "<label>" --backend claude --dry-run
```

This writes a fixture under `rlverify-out/<paper>/<label>/` and records source
metadata (`kind=` is `arxiv-source` / `arxiv-pdf` / `pdf` / `tex`). It:
- for arXiv, downloads the **LaTeX source** (preferred — exact, no glyph loss) and
  inlines `\input`/`\include`; falls back to the PDF text layer only if no source
  is published;
- for a PDF, extracts the text layer (pymupdf → pdftotext → pypdf);
- for a `.tex`, inlines `\input`/`\include`.

Then show the cost estimate and wait for user approval before running formal
verification on the materialized fixture through the harness. Record the `kind=`
value — when it is `arxiv-pdf` or `pdf`, the source is a lossy text layer, so the
back-translation audit (Step "Per-Component Verification" item 6) is doubly
important and the report must note the extraction mode.

If ingest fails (no source, network blocked, scanned PDF with no text layer),
report the failure and stop — do not hand-transcribe from a rendered PDF.

#### Step 0.1: Read Input

**If the argument is a `.tex` file path** (or the normalized path from Step 0.0):
1. Read the file using the Read tool
2. `\input{...}` / `\include{...}` are already inlined by ingest; if any remain (a hand-supplied `.tex` you read directly), read those files too (resolve relative to the .tex file's directory)
3. If a section filter is provided (e.g., "Section 3", "Chapter 2", "Appendix B"), extract only that section — from its `\section{...}` heading to the next same-level heading
4. If no filter, process the entire file

**If the argument is inline text**: use it directly.

**Macro expansion**: If the preamble defines `\newcommand` or `\DeclareMathOperator` macros used in theorem bodies, mentally expand them when interpreting the math. Note the expansion in the report for clarity.

#### Step 0.2: Extract LaTeX Environments

Parse the input for mathematical environments. Recognize these patterns:

**Numbered environments** (with optional labels):
```latex
\begin{theorem}[Optional Name]\label{thm:key} ... \end{theorem}
\begin{lemma}[Optional Name]\label{lem:key} ... \end{lemma}
\begin{proposition}[Optional Name]\label{prop:key} ... \end{proposition}
\begin{corollary}[Optional Name]\label{cor:key} ... \end{corollary}
\begin{claim}\label{clm:key} ... \end{claim}
\begin{definition}\label{def:key} ... \end{definition}
```

**Proof environments** (associate with the immediately preceding theorem-like environment):
```latex
\begin{proof} ... \end{proof}
\begin{proof}[Proof of Lemma X] ... \end{proof}
```

**Also recognize**:
- `\newtheorem`-style custom environments (e.g., `\begin{thm}`, `\begin{lem}`)
- Inline definitions: `\textbf{Lemma 1.}` or `\noindent\textbf{Theorem (Name).}`
- Numbered by hand: "**Lemma 1.**", "**Theorem 2.**"

For each component, record:
- **Label**: the `\label{...}` key or the display name (e.g., "Lemma 1", "Theorem 3.2")
- **Statement**: the mathematical content inside the environment
- **Proof**: the content of the associated `\begin{proof}...\end{proof}` block
- **Type**: theorem / lemma / proposition / corollary / claim / definition

**Commented-out environments**: ingest (Step 0.0) already removes `%`-commented
LaTeX, so `%\begin{theorem}...` blocks are gone. If you are reading a hand-supplied
`.tex` you did NOT run through ingest, ignore any environment whose `\begin{...}`
line is commented — drafts routinely leave dead theorems in the source.

**Main-theorem prose fallback (Step 0.2b)**: a paper's headline result is sometimes
NOT in an uncommented `theorem` environment — it may be commented out and only
restated in running text ("we show that ... using $T$ samples where
$\epsilon = ...$"). If no uncommented `\begin{theorem}` carries the main bound,
recover it from prose:

```python
from rlverify.extract import find_main_claims
for c in find_main_claims(open("/tmp/<paper>.tex").read(), "<id>"):
    print(c.label, c.theorem)
```

Treat the recovered claim as the main theorem (proof assembled from the lemmas it
cites). Flag in the report that the main statement was recovered from prose, and
give it the back-translation audit with extra care — prose statements are the most
drift-prone input of all.

**Standing assumptions**: Look for section-level or paper-level assumptions that apply to multiple components (e.g., "Throughout this section, let M = (S,A,P,r,γ) be a finite MDP with γ ∈ [0,1)"). Record these separately — they become shared hypotheses in the Lean formalization for every component in their scope.

Definitions are not verified but are tracked as available context for other components.

#### Step 0.3: Identify Dependencies via References

Scan each proof block for references to other components. Detect:

**LaTeX cross-references**:
- `\ref{lem:key}`, `\cref{lem:key}`, `\eqref{eq:key}`
- `\autoref{thm:key}`, `\hyperref[prop:key]{...}`
- `Theorem~\ref{thm:main}`

**Natural-language references**:
- "by Lemma 1", "from Lemma 2", "using Proposition 3"
- "by the previous lemma", "by Theorem A above"
- "it follows from (3.2)", "applying Corollary 1"

**Resolving ambiguous references**: "the previous lemma" or "the above result" — resolve by document order. If truly ambiguous (multiple candidates), list all possibilities and pick the most recent matching type. Note the ambiguity in the report.

**External references**: If a proof cites a result NOT defined in this paper (e.g., "by Banach's fixed point theorem", "by [12, Theorem 3]"), these are NOT edges in the dependency graph. They are handled during block resolution as library/novel blocks (or via the Axiom lifecycle in `/verify-full-process` Phase 4 if they qualify).

**Auto-routing cited environments (Step 0.3b)**: a theorem-like environment whose
title *restates* an external result — `\begin{lemma}[Lemma 4.1 in~\cite{jin2018q}]`,
`[Martingale Concentration, Corollary 2.20 in~\cite{...}]`, `[Restatement of Lemma 3
of~\cite{...}]`, `[... (Jin et al., 2018)]` — is NOT a verifiable component of this
paper. It carries no proof; do not try to verify it and do not put it on the
verification plan. Route it to the library/axiom lane: resolve via `d.grep`/
`d.hybrid_search`, and if absent, treat as a library gap (candidate for
`/verify-full-process` Phase 5 growth) or, if it qualifies, an axiom per the Axiom lifecycle.
`extract.py` flags these with `external=True`:

```python
from rlverify.extract import extract_from_latex
comps = extract_from_latex(open("/tmp/<paper>.tex").read(), "<id>")
verifiable = [c for c in comps if not c.external]
cited      = [c for c in comps if c.external]   # -> library/axiom lane, not the plan
```

**Build the dependency graph**: register each component on the `PaperSession`
with its `deps=[...]` (labels of OTHER components its proof uses). A directed
edge A → B means "A's proof uses B". Edges point only at *verifiable*
components — `p.dependency_graph()` automatically drops edges to `external=True`
(cited) and `kind="definition"` nodes. Check `p.unknown_deps()` for any cited
label that is not a component (dangling reference — investigate before
proceeding).

#### Step 0.4: Check for Circularity

```python
cyc = p.detect_cycle()   # DFS; returns the cycle path or None
```

If `cyc` is not None, **STOP immediately**:
- Report the exact cycle path (`" → ".join(cyc)`)
- Explain which references create the cycle
- Verdict: **UNVERIFIED / CIRCULAR — circular reasoning**
- No formalization needed

#### Step 0.5: Topological Sort and Verification Plan

```python
order = p.topo_order()   # deps before dependents; raises if a cycle exists
print(p.plan())          # graph + order + external/definition routing
```

The tie-breaking (definitions are context-only and excluded; lemmas before
theorems at equal depth; document order breaks remaining ties) is built in. Show
`p.plan()` as the verification plan.

#### Step 0.6: Paper-level sketch (machine-check the dependency graph)

Before verifying any component, machine-check that the **main theorem actually
follows from its claimed lemma dependencies** — the paper-level analogue of the
`/verify-full-process` sketch. Once you have a Lean statement for the main theorem and its
dependency lemmas, stub the dependencies and confirm the main proof compiles
against them:

```python
r = p.paper_sketch(main_label, lean_main_statement, lean_main_proof, imports=[...])
```

This delegates to `d.sketch`: it allows the intentional stub `sorry`s but
**FAILS if the main proof does not actually use every stubbed dependency**
(a missing edge / spurious dependency / vacuous glue). Success ⇒ the graph
really entails the main result. Failure ⇒ a missing edge or a genuine gap —
diagnose, do not auto-verdict. (You can sketch intermediate dependent components
the same way once their Lean statements exist.)

**Accumulation rule**: when verifying component N, its already-verified
dependencies are available — `p.prior_context(N)` returns the library
`imports` for deps added via `add_novel` and the `stub_statements` for deps not
yet in the library. Reference a prior lemma with `exact`/`apply`; never re-prove
it (record it as kind `prior`, below).

---

### Per-Component Verification (delegates to /verify-full-process)

Process components in topological order. For each component, apply the FULL `/verify-full-process` procedure (Phases 0–5 of `.claude/commands/verify-full-process.md`): prose triage → decompose → hypothesis audit → resolve → formalize (with anti-vacuity checks) → assemble → library growth. All of its rules apply per component, including the Salvage rule, the early exits, and the recursive-decomposition strategy. The `/verify-full-process` Phase 0 triage runs ONCE per component (sealed subagent, component text only — never the whole paper), under the same hard constraints: prioritizes, never decides, never skips; the report's reconciliation table covers all components.

Paper-specific modifications:

1. **Extra block kind — `prior`**: a block may be resolved by a component already verified in this session. Record it as kind `prior` (the resolution table gains this kind), and prove it with `exact prior_lemma args`. Prior components' compiled Lean code is available in the Lean context (include their declarations in the component's file, or import them if already added to the library).

2. **Standing assumptions** from Phase 0 become shared hypotheses of every component in their scope. They are input hypotheses, not additions — adding any OTHER hypothesis is still forbidden.

3. **Iteration cap**: process at most 15 components. If the paper has more, verify the main theorem's dependency chain first, then independent lemmas in document order until the cap. Report which components were not attempted because of the cap.

4. **On component failure**:
   - Classify per `/verify-full-process` Rule 7 (WRONG / INCOMPLETE / MISMATCH / HYPOTHESIS_VIOLATION).
   - Call `p.mark_failed(label, verdict=...)` — it marks all downstream components SKIPPED (blocked by: ...) automatically; a failed dependency is a hard block regardless of failure type.
   - **Continue** verifying all independent branches. "Not attempted" is never an acceptable status for a component that is not blocked.
   - For the verdict-deciding component, attempt a **kernel-backed refutation**
     (`d.refute` + `d.set_verdict(..., block=...)`, per `/verify-full-process`
     "Kernel-backed refutation") — time-boxed; failure leaves the verdict
     audit-only. The report must state kernel-backed vs audit-only for each
     failure verdict; refutation statements get the back-translation audit.

5. **Parallel verification (optional)**: components with no dependency path between them may be verified concurrently by subagents, each running the `/verify-full-process` procedure for its component with: the component statement + proof, the standing assumptions, and the statements of already-verified prior components. Use this when there are ≥3 mutually independent components. Constraints:
   - Subagents must NOT call `d.add_novel` or edit `RLGeneralization.lean` (concurrent corpus appends and lake builds race). They return their compiled blocks; the parent performs all Phase 5 library additions serially after merging.
   - Merge results back in topological order before verifying dependent components.

6. **Back-translation audit is mandatory in paper mode** — papers are where
   statement drift between the LaTeX and the formalization has actually
   occurred. It applies to each component's MAIN statement (compared against
   the paper's LaTeX statement, macros expanded) and to every `axiom`, per
   `/verify-full-process` Phase 3. The back-translator subagent may run alongside the
   parallel-verification subagents, but it must NEVER receive the paper text —
   only the Lean statement(s) and the definitions they reference.

---

### Phase 4: Assemble

Combine all verified components into one Lean 4 file:
1. Imports at the top
2. Independent verified lemmas (leaves)
3. Dependent lemmas, each referencing previously defined ones
4. Main theorem last (included if all dependencies are verified)

Failed and skipped components are excluded. Compile with `d.assemble(...)` so the **kernel audit** runs: the verdict source is the `#print axioms` closure of the main theorem (transitive through imports), not the source regex. `sorryAx` in the closure ⇒ UNVERIFIED, no exceptions. Any custom axiom in the closure must satisfy all FOUR Axiom lifecycle conditions (`/verify-full-process` Phase 4 — including the back-translation audit) and be registered in `rlverify/results/axiom_backlog.md`; they downgrade the verdict to VERIFIED MODULO AXIOMS.

---

### Phase 5: Library Growth

Apply `/verify-full-process` Phase 5 to every verified novel block across all components — it is mandatory, including for blocks salvaged from failed components. Use code mode with `target_dir` and `docstring`:

```python
d.add_novel(
    name="lemma_name",
    code=full_lean_code,           # statement extracted automatically
    target_dir="Concentration",    # topic directory
    docstring="One-line NL description (indexed for search)",
    reusable=True,
    reuse_reason="Atomic general fact with plausible use in other proofs",
    generalized_from="<paper/lemma/block provenance>",
)
```

The generality gate, dedup/axiom/root-import enforcement, and build registration are as documented in `/verify-full-process` Phase 5. After all additions, run `lake build RLGeneralization` once so the root module picks them up.

---

### Phase 6: Verdict and Report

#### Structured paper record (machine-readable, written first)

As each component resolves, record its outcome on the session so the verdict is
computed, not hand-tallied:

```python
p.mark_verified(label, lean_name=..., lean_statement=...,
                library_module=...,           # if added via add_novel
                kernel_axioms=[...])           # from #print axioms
p.mark_failed(label, verdict="INCOMPLETE", note="...")  # auto-marks downstream SKIPPED
```

Then emit the aggregate record:

```python
p.paper_verdict()   # VERIFIED | VERIFIED MODULO AXIOMS | PARTIALLY VERIFIED | UNVERIFIED | UNVERIFIED/CIRCULAR
p.save()            # runs/papers/<paper_name>.json — the source of truth for the verdict
```

The paper verdict is derived from the per-component statuses and their kernel
axiom closures (custom axioms ⇒ VERIFIED MODULO AXIOMS; any unverified
verifiable component ⇒ PARTIALLY VERIFIED; a cycle ⇒ UNVERIFIED/CIRCULAR). The
markdown report below is a human-readable rendering of `p.record()` — never a
hand-tallied verdict that could contradict it.

#### Terminal Output

Summarize the result briefly in the conversation.

#### Write Report File

Write a structured markdown report to `rlverify/results/<paper_name>_report.md` (derive `<paper_name>` from the input filename or use `proof_report` for inline input).

The report must contain:

```markdown
# Verification Report: <Paper/Theorem Name>

**Date**: YYYY-MM-DD
**Input**: <filename or "inline">
**Overall Verdict**: VERIFIED / VERIFIED MODULO AXIOMS / PARTIALLY VERIFIED / UNVERIFIED

## Axioms

(list each axiom with reference and backlog entry, or "none")

## Dependency Graph

```
Lemma 1 → (none)
Lemma 2 → Lemma 1
...
```

## Verification Order

| # | Component | Dependencies | Status |
|---|-----------|-------------|--------|
| 1 | Lemma 1   | (none)      | VERIFIED |
| 2 | Lemma 2   | Lemma 1     | VERIFIED |
| 3 | Lemma 3   | Lemma 2     | FAILED — wrong claim |
| 4 | Lemma 4   | (none)      | VERIFIED |
| 5 | Theorem   | Lemma 2, 3, 4 | SKIPPED — blocked by Lemma 3 |

## Summary

- Total components: N
- Verified: X
- Failed: Z (list with one-line reason each)
- Skipped: W (list with which failure blocked them)

## Detailed Results

### Lemma 1 — VERIFIED

**Statement**: ...
**Building blocks**: (resolution table, including `prior` resolutions)
**Lean proof**: (code block)

### Lemma 3 — FAILED

**Statement**: ...
**Failure**: (which block, why, failure type per /verify-full-process Rule 7)
**Partial progress**: (what compiled before the failure)

### Lemma 5 — SKIPPED

**Blocked by**: Lemma 3
**Would depend on**: ...

...

## Assembled Lean Code

```lean
-- Verified components
theorem lemma_1 ...
...
```
```

#### Verdict categories:

- **VERIFIED** — every component compiled with full proofs AND the kernel axiom closure of each main theorem is ⊆ {propext, Classical.choice, Quot.sound}
- **VERIFIED MODULO AXIOMS** — every component compiled, but the kernel closure contains custom axioms, each satisfying all four Axiom lifecycle conditions
- **PARTIALLY VERIFIED** — some components verified, others failed or skipped
- **UNVERIFIED** — no components verified (circularity, or root lemmas all fail)

Every component and every block must have a status — never "not attempted" (except components beyond the 15-component cap, reported as such). Use the exact classifications from `/verify-full-process` Rule 7, plus:

- **CIRCULAR**: the paper's dependency graph has a cycle — a component depends (directly or transitively) on itself. Detected in Phase 0; reported with the exact cycle path.

---

## Rules — Verification Integrity

All nine `/verify-full-process` Verification Integrity rules apply verbatim to every component. In addition:

1. **Never break a dependency cycle by assuming one of its components.** A cycle is UNVERIFIED/CIRCULAR, full stop.
2. **Prior components are the only free facts.** A component may use a previously verified component's statement without re-proving it; everything else must be library, instantiation, or freshly formalized.
3. **The 15-component cap must be reported.** Components skipped due to the cap are listed in the report as "not attempted (cap)".

## Known Limitations

- **Search**: `d.grep()` is substring matching (id matches rank first); `d.hybrid_search()` is BM25 keyword ranking over id + tags + docstring + statement. Try both, with multiple phrasings.
- **Schematic proofs**: "by induction on X" without naming the specific lemma may not decompose cleanly.
- **Non-compiling modules**: 3 library modules have broken builds (Hellinger, ChiSquared, TriangularDiscrimination). Search marks their theorems `[NOT BUILT — cannot import]` — do not import them.
- **Corpus freshness**: regenerate with `python scripts/export_retrieval_corpus.py` (use `--check` to detect drift).
- **Ingest fidelity**: arXiv LaTeX source is exact; PDF text layers (`kind=pdf`/`arxiv-pdf`) can merge columns, mangle math glyphs, or be empty for scanned papers. Prefer the arXiv id over a downloaded PDF when both are available, and lean on the back-translation audit when the source is a PDF.
