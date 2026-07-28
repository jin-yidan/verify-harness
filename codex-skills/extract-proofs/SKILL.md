---
name: extract-proofs
description: "Duplicate of Claude /extract-proofs. Use when the user invokes /extract-proofs, $extract-proofs, or asks to run this RLVerify command. Extract theorems from recent RL theory papers, download PDFs, create proof fixtures, and verify quotes"
---

# /extract-proofs — Codex Duplicate

This is a Codex skill duplicate of `.claude/commands/extract-proofs.md`. The Claude slash command name is `/extract-proofs`; in Codex, invoke it as `$extract-proofs` or write `/extract-proofs` in the prompt. Interpret Claude-specific Task/Bash references as workflow instructions and use Codex-native tools or the local RLVerify CLI.

Preserve the verification discipline from the original command: verify, do not repair; do not add hypotheses or proof steps; treat sealed gates and kernel evidence according to the RLVerify output contract.

When this skill calls `python3 -m harness` directly or through RLVerify CLI examples, pass `--backend codex` unless the user explicitly asks for another backend. Pass `--model <codex-model>` when a specific Codex model is under test; otherwise let the Codex CLI use its configured default.

---

<command-name>extract-proofs</command-name>

# Extract Proofs from Recent RL Papers

You are the RLVerify proof extraction pipeline. Your job is to find recent RL theory papers from top venues, extract their main theorems and proof sketches verbatim, download the source PDFs, create proof fixture files, and independently verify every quote against the PDF.

## Input

The user may optionally specify:
- A topic focus (e.g., "offline RL", "linear MDPs", "RLHF")
- A venue filter (e.g., "NeurIPS 2024", "ICML 2025")
- A number of papers to extract (default: 5-7)
- A specific arXiv ID or paper title

If no input is given, find papers across RL theory from recent top venues (ICML, NeurIPS, ICLR, COLT, ALT, Operations Research — 2024-2025).

## Pipeline

Execute these steps in order. Do NOT skip any step.

### Step 1: Research — Find candidate papers

Use WebSearch to find recent RL theory papers from top ML venues. Look for papers with:
- Novel regret bounds, sample complexity results, or minimax-optimal guarantees
- Clear theorem statements with explicit rates (not just "we improve over prior work")
- Published at ICML, NeurIPS, ICLR, COLT, ALT, OR, JMLR (2024-2025 preferred)

For each candidate, record: title, authors, venue, arXiv ID, and the main theorem you plan to extract.

**Validation**: Drop any paper where:
- The arXiv ID date is in the future or suspiciously recent
- The venue attribution can't be confirmed
- The paper is primarily empirical with no formal theorem
- **DUPLICATE CHECK (MANDATORY)**: The paper or theorem already has a fixture. Run:
  ```
  grep -rn "arXiv:<candidate_id>" tests/proofs/ --include="*.py"
  grep -rn "<candidate_theorem_name>" tests/proofs/ --include="*.py"
  ```
  If either returns a match, skip that paper — do NOT create a duplicate fixture.

### Step 2: Download PDFs

For each paper, download the PDF from arXiv:
```
curl -L -o papers/<Authors>_<Year>_<short_topic>.pdf https://arxiv.org/pdf/<arxiv_id>
```

Naming convention: `<FirstAuthor>_et_al_<Year>_<snake_case_topic>.pdf`
Save to the `papers/` directory at the project root.

### Step 3: Extract theorems verbatim

Read each PDF and extract the main theorem statement **word for word**. Rules:
- Copy the EXACT text from the PDF — do not paraphrase, reorder, or "improve"
- Use ASCII transliteration for math symbols. The full table:
  - Greek letters: `delta` δ, `pi` π, `epsilon` ε, `varepsilon` ε (use whichever the paper's LaTeX uses — check the source), `eta` η, `lambda` λ, `gamma` γ, `rho` ρ, `alpha` α, `beta` β, `sigma` σ, `omega` ω, `mu` μ, `nu` ν, `kappa` κ, `tau` τ, `phi` φ, `psi` ψ, `theta` θ
  - Inequalities: `<=` for ≤, `>=` for ≥, `lesssim` for ≲ (NOT `<=` — these are different relations), `gtrsim` for ≳
  - Decorations — EVERY decoration MUST be preserved: `hat{x}` for x̂, `tilde{x}` for x̃, `bar{x}` or `overline{x}` for x̄, `widetilde{x}` for wide-tilde, `underline{x}` for x̲, `dot{x}` for ẋ, `star` or `*` for ⋆, `mathbb{V}` for blackboard-bold V (𝕍), `mathbb{E}` for blackboard-bold E (𝔼), `mathcal{F}` for calligraphic F (ℱ), `mathcal{N}` for calligraphic N (𝒩), `mathcal{D}` for calligraphic D (𝒟). Blackboard-bold, calligraphic, and plain letters are DIFFERENT objects — `mathbb{V}_h` is a variance operator, `V_h` is a value function.
  - Superscripts — ALWAYS use `^` for superscripts: `V^*` not `V*`, `pi^*` not `pi*`, `V^{hat{pi}}` not `V^hat{pi}`. If you write `V*(rho)` without the caret, it looks like function application, not optimal value.
  - Other: `sqrt` for √, `O_tilde` or `~O` for Õ, `sum` for ∑, `prod` for ∏, `infty` for ∞, `in` for ∈, `subset` for ⊂, `forall` for ∀, `exists` for ∃
  - **CRITICAL**: If two symbols look similar but have different decorations (e.g., `overline{Sigma}` vs `widetilde{Sigma}`), they are DIFFERENT mathematical objects. Collapsing them to the same name silently changes the theorem's meaning.
- Include theorem number, any parenthetical name, all conditions, the bound, and any trailing remarks that are part of the formal statement
- Stop at the period that ends the theorem statement — do not include proof text in the theorem field
- **Multi-term bounds**: For theorems with sums of O(...) terms, count the terms in the PDF and verify the count matches your extraction. Copy each term individually — do NOT reconstruct the bound from memory or paraphrase. Missing or extra terms is the #1 source of fixture errors.
- **Verbatim means verbatim**: Do not "normalize" punctuation, pluralization, or parentheticals. If the PDF says "iteration" (singular), write "iteration", not "iterations". If the PDF includes "(with the probability)", include it. If the PDF has no period after a theorem name like "Theorem 1 (Name)", do not add one.
- **Inequality symbol check**: Before writing, re-read the PDF's inequality symbol at every `<=` you write. Is it `≤` (leq, standard) or `≲` (lesssim, up to constants/logs)? These are the two most commonly confused symbols. Zoom in on the PDF if needed — `≲` has a small tilde under it.
- **Log/sqrt argument check**: For every `log(...)` and `sqrt(...)`, verify each factor inside the parentheses matches the PDF exactly. Missing a factor like H inside `log(SAH/delta)` vs `log(SA/delta)` is a substantive mathematical error.

Also extract a **proof sketch** (your summary of the proof structure, NOT verbatim):
- Identify the main decomposition steps
- Name the key lemmas invoked
- Note the concentration inequalities used
- Keep it to 5-10 sentences

### Step 4: Create proof fixture files

For each paper, create a Python file in `tests/proofs/` following this exact format:

```python
"""<One-line description of the result>.

Source: <Full author list>, "<Paper title>,"
arXiv:<id>. <Venue> <Year>. <Theorem number>.

Verbatim from the source (<Theorem number>, p. <page>):

    <Exact theorem text, indented 4 spaces, with line breaks
    matching the logical structure>

Proof sketch (from <Section>, pp. <pages>):

    <Your proof summary, 5-10 sentences>
"""

PROOF = {
    "id": "<snake_case_id>_<year>",
    "theorem": (
        "<Verbatim theorem text, using Python string concatenation "
        "for multi-line. One sentence per string literal.>"
    ),
    "proof": (
        "<Proof sketch text, also using string concatenation.>"
    ),
    "reference": (
        "<Author1>, <Initial>., <Author2>, <Initial>., ... (<Year>). "
        "<Title>. <Venue>. arXiv:<id>. <Theorem number>."
    ),
    "library_match": None,
}
```

File naming: `tests/proofs/<snake_case_topic>.py`

**Pre-write dedup guard (MANDATORY)**: Before writing each fixture file, run:
```python
python3 -c "
import ast, os, re
target_id = '<new_fixture_id>'
target_arxiv = '<new_arxiv_id>'  # e.g. '2406.06856'
for f in sorted(os.listdir('tests/proofs')):
    if not f.endswith('.py') or f == '__init__.py': continue
    with open(os.path.join('tests/proofs', f)) as fh:
        content = fh.read()
    try:
        tree = ast.parse(content)
        for node in ast.walk(tree):
            if isinstance(node, ast.Assign):
                for t in node.targets:
                    if isinstance(t, ast.Name) and t.id == 'PROOF':
                        d = ast.literal_eval(node.value)
                        if d.get('id') == target_id:
                            print(f'DUPLICATE ID: {target_id} already in {f}')
                        if target_arxiv and target_arxiv in d.get('reference',''):
                            print(f'DUPLICATE PAPER: arXiv:{target_arxiv} already in {f}')
    except: pass
print('Dedup check passed' if True else '')
"
```
If the check prints DUPLICATE, do NOT write the file. Investigate whether the existing fixture already covers the same theorem. If it covers a DIFFERENT theorem from the same paper, use a distinct `id` with a suffix (e.g. `paper_name_2024_thm2`).

### Step 5: Self-check before verification — MANDATORY

Before launching subagent verification, re-read each PDF theorem one more time and check your own fixture against this 30-second checklist:

1. **Inequality symbols**: For every `<=` or `>=` in your fixture, look at the PDF symbol. Is it `≤` or `≲`? Mark each one.
2. **Term count**: For multi-term bounds, count the `+` signs in your fixture and in the PDF. Do they match?
3. **Decorations**: Scan the PDF for any hat, tilde, overline, widetilde, bar, mathbb, mathcal on variables. Does your fixture preserve each one?
4. **Superscripts**: Check every `*` in your fixture has a `^` before it where appropriate (V^*, pi^*).
5. **Log/sqrt arguments**: For each `log(...)` and `sqrt(...)`, verify every factor inside matches the PDF.
6. **Punctuation**: Does the theorem name in the PDF end with a period? Does your fixture match?

Fix any issues found BEFORE launching verification agents. This step catches ~60% of errors at near-zero cost and prevents wasted verification cycles.

### Step 6: Verify quotes — MANDATORY

This step is NOT optional. Launch **one independent subagent per paper** to verify quotes. Each subagent must:

1. Read the fixture file and extract the `"theorem"` field value
2. Read the corresponding PDF at the specified page
3. Compare WORD BY WORD — report ANY discrepancy using this checklist:
   - **Term count**: For multi-term bounds (sums of O(...) terms), count terms in PDF vs fixture. Missing or extra terms is the most common error.
   - **Inequality symbols**: `≤` vs `≲` (lesssim) vs `≦` — these are different relations. `≲` hides polylog factors; `≤` does not.
   - **Symbol decorations**: `overline{X}` vs `widetilde{X}` vs `hat{X}` vs plain `X` — different decorations mean different objects.
   - **Greek letter variants**: `epsilon` vs `varepsilon` — use whichever the paper uses.
   - **Operator placement**: Is a factor inside or outside a sqrt/log? E.g., `gamma*sqrt(log T)` ≠ `sqrt(gamma*log T)`.
   - **Exponents**: `log^3 T` vs `sqrt(log^3 T)` (= `(log T)^{3/2}`) — these are different.
   - **Parenthesization**: Check that grouping in ASCII matches the PDF's typeset fractions and radicals.
   - **Blackboard bold / calligraphic**: `mathbb{V}` ≠ `V`, `mathcal{F}` ≠ `F`, `mathcal{N}` ≠ `N`. These are different objects in the paper.
   - **Superscript consistency**: `V^*` ≠ `V*`. Every optimal-value superscript needs the `^` caret.
   - **Verbatim text**: Check punctuation (extra/missing periods), parentheticals (e.g., "(with the probability)"), and singular vs plural ("iteration" vs "iterations"). The theorem field must match the PDF word for word, not just mathematically.
   - **Log/sqrt arguments**: Count factors inside each `log(...)` and `sqrt(...)` — a missing `H` or `d` inside a log is a mathematical error, not a formatting issue.
4. Report either "VERIFIED: verbatim match" or list every discrepancy in a table with columns: Location | PDF | Fixture

Use the Agent tool with `run_in_background: true` for all verification agents so they run in parallel.

**If any discrepancy is found**: fix the fixture file immediately. Then re-verify.

### Step 7: Full dedup scan — MANDATORY

After all fixtures are written and verified, run a full dedup scan across ALL fixtures:
```bash
python3 -c "
import ast, os, re, collections
ids, arxivs = [], []
for f in sorted(os.listdir('tests/proofs')):
    if not f.endswith('.py') or f == '__init__.py': continue
    with open(os.path.join('tests/proofs', f)) as fh:
        content = fh.read()
    try:
        tree = ast.parse(content)
        for node in ast.walk(tree):
            if isinstance(node, ast.Assign):
                for t in node.targets:
                    if isinstance(t, ast.Name) and t.id == 'PROOF':
                        d = ast.literal_eval(node.value)
                        ids.append((f, d.get('id','')))
                        m = re.search(r'arXiv:(\d+\.\d+)', d.get('reference',''))
                        if m: arxivs.append((f, m.group(1)))
    except: pass
dup_ids = [k for k,v in collections.Counter(i for _,i in ids).items() if v > 1]
dup_ax = [k for k,v in collections.Counter(a for _,a in arxivs).items() if v > 1]
if dup_ids: print(f'DUPLICATE IDs: {dup_ids}')
if dup_ax: print(f'DUPLICATE papers: {dup_ax}')
if not dup_ids and not dup_ax: print(f'All {len(ids)} fixtures are unique.')
"
```

If any duplicates are found, resolve them before reporting (merge, rename, or delete the duplicate).

### Step 8: Lemma cross-reference — MANDATORY

After all fixtures are written and verified, cross-reference the key lemmas from each proof sketch against the actual Lean library (`RLGeneralization/`). For each lemma, grep for it:

```bash
# For each lemma name, search the Lean source:
grep -rn "<keyword>" RLGeneralization/ --include="*.lean" | head -5
```

Report a table with columns: Lemma | Status | Lean location

Status values:
- **HAVE**: A theorem/lemma exists in Lean source that covers this
- **PARTIAL**: Related results exist but the specific form needed is absent (explain what's missing)
- **MISSING**: Not formalized and requires genuine new mathematical content (new definitions, non-trivial proofs, new algebraic structure)

**Instantiation filter (MANDATORY)**: Before adding a lemma to the MISSING list, check whether it is just an instantiation of an existing general result. A lemma is an instantiation — NOT a library gap — if it:
- Follows by plugging specific constants into an existing theorem (e.g., FTRL = OMD with D₀=log(K))
- Is a trivial summation or union bound over an existing per-item result (e.g., RUCB = sum Hoeffding over K arms)
- Is a 1-3 line consequence of existing lemmas via `linarith`/`positivity`/`exact` (e.g., weak duality = `inf'_le` + `le_sup'`)

Instantiations belong as inline `have` steps in the proofs that use them, not as standalone library theorems. Do NOT add them to the checklist.

Then update `docs/LEMMA_CHECKLIST.md` — merge new findings into the existing checklist. Add new MISSING/PARTIAL entries, and move any that are now HAVE. Do not overwrite existing entries that are still accurate.

### Step 9: Report results

After all verification and lemma cross-referencing passes, report:
- Number of papers extracted
- Table: fixture name | paper | venue | theorem | status
- Any papers that were dropped and why
- Lemma cross-reference table from Step 8 (HAVE/PARTIAL/MISSING for each)

## Quality rules

- NEVER fabricate a theorem statement. If you can't read the PDF clearly, say so.
- NEVER add "Theorem X states that..." wrapper text — the fixture should contain the theorem's own words.
- NEVER create a fixture with a duplicate `id` or duplicate arXiv ID — always run the dedup checks in Steps 1, 5, and 7.
- ALWAYS include the theorem number as it appears in the paper.
- ALWAYS download the PDF before creating the fixture — don't work from memory or search snippets.
- ALWAYS verify with independent subagents — a single-pass check is not sufficient.
- ALWAYS run the full dedup scan (Step 7) after writing all fixtures.
- The `"proof"` field is YOUR summary, not verbatim. The `"theorem"` field is VERBATIM.

## Existing fixtures

Check `tests/proofs/` for existing fixtures before starting — don't duplicate papers already extracted. Run the dedup check from Step 1 before doing any work.

## Known failure modes (from past audits)

These are the actual errors found in prior fixture runs. The verification checklist in Step 6 exists because of them:

**Tier 1 — Substantive mathematical errors** (change meaning of the theorem):

1. **Hallucinated terms in multi-term bounds**: A 15-term regret bound was extracted as 11 terms — 5 missing, 1 fabricated. Root cause: reconstructing the bound from understanding instead of copying term-by-term. *Found in: single_loop_actor_critic.py*
2. **Missing factor inside log/sqrt**: `log(SA / (delta * epsilon))` was written instead of `log(SAH / (delta * epsilon))` — the H was dropped. This changes the sample complexity. *Found in: span_avg_reward.py*
3. **Operator misplacement**: `gamma * sqrt(log T)` (gamma outside) was written as `sqrt(gamma * log T)` (gamma inside). Similarly, `sqrt(log^3 T)` was written as `log^3 T`. Both change the rate. *Found in: single_loop_actor_critic.py*

**Tier 2 — Semantic precision errors** (lose information but don't change the bound):

4. **`≲` silently downgraded to `<=`**: The symbol `≲` (lesssim) means "up to constant/polylog factors" and is semantically different from `≤`. The ASCII rendering must be `lesssim`, not `<=`. This was the MOST COMMON error — 4 fixtures had it. *Found in: thompson_sampling_variance, chi_squared_po, settling_online_rl, exploratory_po (docstring)*
5. **Symbol decorations collapsed**: `overline{Sigma}_{t,a}` and `widetilde{Sigma}_{t,a}` (two different covariance matrices) were both rendered as plain `Sigma_{t,a}`, losing the distinction. Also: `mathbb{V}_h` (blackboard-bold variance operator) collapsed to plain `V_h` (value function). *Found in: best_of_both_worlds_linear, pnlsvi_offline_rl*
6. **LaTeX glyph variant ignored**: Paper used `\varepsilon` consistently but fixture used `epsilon`. Use whichever name the paper's LaTeX uses. *Found in: distributional_rl_minimax, npg_convergence*
7. **Missing superscript caret**: `V*(rho)` instead of `V^*(rho)`. Without the `^`, it reads as function application instead of optimal value. *Found in: reward_free_exploration*

**Tier 3 — Verbatim fidelity errors** (text doesn't match PDF word-for-word):

8. **Added/removed punctuation**: Extra period added after theorem name "Theorem 1 (Name)." where PDF has no period. *Found in: greedy_rlhf*
9. **Dropped parenthetical text**: PDF says "w.p. (with the probability) at least" but fixture dropped the parenthetical. *Found in: generative_model_pac*
10. **Singular/plural change**: PDF says "iteration" (singular) but fixture says "iterations" (plural). *Found in: generative_model_pac*
11. **Changed connector word**: PDF says "where H := ..." but fixture says "Here H := ...". *Found in: span_avg_reward*
