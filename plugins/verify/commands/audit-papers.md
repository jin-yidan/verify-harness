# /audit-papers — Audit RL Theory Papers from Arxiv

Search arxiv for RL theory papers, fetch them, and run `/verifyRL-paper` on each to verify ALL lemmas and theorems. Maintains a structured audit log tracking verification outcomes across papers.

## Purpose

1. **Find proof errors** in published RL theory papers
2. **Grow the library** — novel correct blocks from each paper get added
3. **Stress-test the pipeline** — patterns in failures reveal what to improve next

## Input

$ARGUMENTS

Optional arguments:
- **Topic focus**: e.g., "sample complexity", "regret bounds", "policy optimization", "exploration"
- **Number of papers**: e.g., "5 papers" (default: 3)
- **Specific arxiv IDs**: e.g., "2306.12345, 2401.67890"

If no arguments, pick 3 recent papers from areas where the library has coverage (MDP theory, concentration inequalities, policy optimization, regret analysis).

## Workflow

### Step 1: Source Papers

Search arxiv for RL theory papers containing provable theorems.

```
WebSearch("arxiv RL theory sample complexity regret bound 2024 2025")
```

**Selection criteria** — pick papers that:
- State formal theorems with proofs (not just empirical results)
- Cover topics where our library has some coverage (check with `d.grep()`)
- Have proofs that decompose into verifiable building blocks
- Are from reputable venues (NeurIPS, ICML, COLT, ALT, JMLR, or arxiv with multiple citations)

**Skip papers that:**
- Are purely empirical (no formal theorems)
- Require measure-theoretic probability infrastructure we completely lack
- Are survey/overview papers with no original proofs
- Have already been audited (check `rlverify/results/paper_audit_log.tsv`)

For each selected paper, record:
- Arxiv ID
- Title
- Authors
- Year
- Domain tags (e.g., sample-complexity, regret-bound, policy-optimization)

### Step 2: Fetch and Verify Each Paper

For each paper:

#### 2a: Fetch the Paper

Do **not** hand-fetch with WebFetch or call `python -m rlverify.ingest` directly.
`/verifyRL-paper` runs the RLVerify harness, whose paper front-end downloads and
normalizes papers — pass it the arXiv id directly in Step 2b. (Use
WebSearch/WebFetch in Step 1 only to *discover and select* papers, not to extract
their proof content.)

#### 2b: Run `/verifyRL-paper` on the Full Paper

Invoke `/verifyRL-paper <arxiv_id>` — it must first run
`python3 -m harness verify ... --dry-run` through the slash command. The harness
paper front-end downloads the LaTeX source (preferred) or PDF, extracts
theorems/lemmas/proofs, and prints the formal-proof cost estimate. Wait for
approval before launching the full `--all-theorems --report` verification. This
handles:
- Extracting ALL theorem/lemma/proposition environments (Phase 0)
- Building the dependency graph and checking for cycles (Phase 0.3-0.5)
- Verifying each component in topological order (Phases 1-3)
- Hypothesis audit across all inter-lemma invocations
- Formalizing every independent correct block (salvage rule)
- Library growth for generalized novel blocks (Phase 5)
- Writing a per-paper report to `rlverify/results/` (Phase 6)

The report file should be named `rlverify/results/audit_<arxiv_id>_report.md`.

#### 2c: Record Results

After `/verifyRL-paper` completes, extract the paper-level verdict from the report:

- **VERIFIED**: All components verified — complete Lean code compiles
- **WRONG**: At least one component is mathematically false (counterexample found)
- **INCOMPLETE**: All math is sound but formalization couldn't close (missing Mathlib infrastructure)
- **MIXED**: Some components verified, others failed with different classifications
- **NEEDS_HUMAN_REVIEW**: Ambiguous cases — e.g., a claim that MIGHT be false but no definitive counterexample, or a hypothesis violation that could be a notation issue

### Step 3: Update Audit Log

Append results to `rlverify/results/paper_audit_log.tsv`.

**Columns:**
```
arxiv_id	title	authors	year	domain	theorems_checked	verdict	wrong_count	incomplete_count	compiled_count	library_additions	failure_reasons	date_audited
```

- `arxiv_id`: e.g., 2306.12345
- `title`: paper title (truncate to 80 chars)
- `authors`: first author et al.
- `year`: publication year
- `domain`: comma-separated tags
- `theorems_checked`: total number of theorem/lemma components verified
- `verdict`: VERIFIED / WRONG / INCOMPLETE / MIXED / NEEDS_HUMAN_REVIEW
- `wrong_count`: number of WRONG blocks across all components
- `incomplete_count`: number of INCOMPLETE blocks
- `compiled_count`: number of blocks that compiled successfully
- `library_additions`: number of novel blocks added to the library
- `failure_reasons`: semicolon-separated one-line reasons for each failure (empty if VERIFIED)
- `date_audited`: YYYY-MM-DD

### Step 4: Pipeline Feedback Summary

After all papers are processed, output a summary analyzing patterns:

```markdown
## Audit Summary

**Papers audited**: N
**Verdicts**: X verified, Y wrong, Z incomplete, W mixed

### Failure Patterns
- Most common failure type: [WRONG/INCOMPLETE/...]
- Most common WRONG pattern: [e.g., "missing communicating assumption", "independence violation"]
- Most common INCOMPLETE cause: [e.g., "Brouwer not in Mathlib", "spectral theory"]

### Library Impact
- Novel blocks added: N
- Most productive paper: [title] (added M blocks)

### Pipeline Improvement Suggestions
Based on the audit results:
1. [e.g., "Add Brouwer's fixed-point theorem — blocked 3/5 papers"]
2. [e.g., "Hypothesis audit caught 2 independence violations — this check is valuable"]
3. [e.g., "BM25 search missed Mathlib lemmas in 4 cases — consider expanding the corpus"]
```

## Rules

1. **Never fabricate results.** If you can't access a paper or can't extract theorems, skip it and note why.
2. **Use exact classifications.** WRONG/INCOMPLETE/MISMATCH/HYPOTHESIS_VIOLATION per Rule 7 of `/verify-full-process`. NEEDS_HUMAN_REVIEW only when genuinely uncertain.
3. **Salvage rule applies.** Even in a WRONG paper, formalize and add independent correct blocks.
4. **Library additions must be generalized.** Never add paper-specific assembled proofs. Decompose to atomic reusable form.
5. **Verify ALL lemmas.** Don't cherry-pick — the whole point is to run `/verifyRL-paper` on the full proof structure, not just the "easy" theorems.
6. **Track everything.** Every paper gets a TSV row and a report file. No silent skips.
7. **Be honest about limitations.** If a theorem is beyond our current capability (e.g., requires continuous-state MDPs and we only have finite), say INCOMPLETE with the specific blocker — don't force a WRONG classification.
