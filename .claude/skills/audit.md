---
name: audit
description: Comprehensive audit of the Lean 4 RL formalization — proof integrity, naming honesty, corpus quality, and structural health
user_invocable: true
---

<command-name>audit</command-name>

# Audit the Lean 4 RL Formalization

You are the RLVerify audit pipeline. Your job is to examine the entire codebase for integrity issues that matter in a formal mathematics project: dishonest names, vacuous proofs, orphaned files, and corpus drift. This is NOT a style or coverage review — it checks things that affect whether the formalization can be trusted.

## Input

The user may optionally specify:
- A scope: `full` (default), `quick` (automated checks only, no subagents), or a specific module (e.g., `Concentration/`)
- A focus: `integrity`, `naming`, `corpus`, or `structure`

If no input is given, run the full audit.

## What matters and why

This project is a formal Lean 4 library that also serves as a retrieval corpus for an auto-formalization pipeline. The key invariants:

1. **Zero sorry** — A sorry anywhere means an incomplete proof is claimed as done. Hard failure.
2. **Clean build** — Type-checked code is the foundation of everything. Hard failure.
3. **Honest names** — A theorem named `X_convergence` that proves `0 <= expr` misleads both humans and the retrieval pipeline. This is the single most recurring problem in the codebase.
4. **Tagged wrappers** — If a proof just returns a hypothesis (`exact h_foo`), it must carry a `[WRAPPER]`, `[TAUTOLOGICAL]`, or `[CONDITIONAL]` tag. Untagged wrappers inflate the apparent proof depth.
5. **No orphan files** — Every `.lean` file must be reachable from `RLGeneralization.lean`. Orphan files compile but are invisible to downstream tooling.
6. **Corpus freshness** — The retrieval corpus (`benchmark/retrieval_corpus.jsonl`) must reflect the current codebase.
7. **No fixture duplicates** — Proof fixtures in `tests/proofs/` must have unique IDs and unique arXiv references.

What we do NOT check (confirmed non-issues by prior evaluation):
- Test coverage percentage (Lean's type checker IS the test suite)
- MDP structure duplication (intentional — different type params)
- Import cleanliness (too many false positives from transitive imports)
- Cross-layer dependencies (mathematically motivated)

## Pipeline

Execute ALL checks. The automated checks (Steps 1-3) run first. If any hard failure is found, report immediately. Then run the subagent checks (Steps 4-6) in parallel.

---

### Step 1: Hard checks (automated, must pass)

Run these sequentially — if any fails, stop and report:

```bash
# 1a. Zero sorry
echo "=== Sorry check ==="
sorry_count=$(grep -rn "sorry" RLGeneralization/ --include="*.lean" | grep -v "^.*:.*--\|^.*:/\*\|^.*:\*\|zero.sorry\|zero sorry\|0 sorry" | wc -l | tr -d ' ')
echo "Sorry in proof bodies: $sorry_count"

# 1b. Clean build
echo "=== Build check ==="
lake build 2>&1 | grep -E "^(error:|✖)" | head -10

# 1c. Build warnings
echo "=== Warnings ==="
lake build 2>&1 | grep "^warning:" | grep -v "SLT.*local changes" | head -10

# 1d. Double doc comments (Lean syntax error waiting to happen)
echo "=== Double doc comments ==="
grep -rn "\-\/ /\-\-" RLGeneralization/ --include="*.lean" | head -10
```

**Pass criteria**: sorry=0, errors=0, warnings=0, double-docs=0. Any nonzero is a hard failure requiring immediate fix.

---

### Step 2: Orphan file check (automated)

```bash
echo "=== Orphan files ==="
for f in $(find RLGeneralization -name "*.lean" | sort); do
  module=$(echo "$f" | sed 's|/|.|g; s|\.lean$||')
  count=$(grep -rl "import ${module}$\|import ${module} " RLGeneralization.lean RLGeneralization/ --include="*.lean" 2>/dev/null | wc -l | tr -d ' ')
  if [ "$count" -eq "0" ]; then
    echo "  ORPHAN: $module"
  fi
done
```

**Pass criteria**: zero orphan files. Any orphan should be added to `RLGeneralization.lean`.

---

### Step 3: Corpus and fixture checks (automated)

```bash
# 3a. Regenerate corpus and compare
python3 scripts/export_retrieval_corpus.py 2>/dev/null
corpus_count=$(wc -l < benchmark/retrieval_corpus.jsonl | tr -d ' ')
echo "Corpus entries: $corpus_count"

# 3b. Fixture dedup
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
if not dup_ids and not dup_ax: print(f'All {len(ids)} fixtures unique.')
"
```

**Pass criteria**: corpus regenerates without error, fixture IDs and arXiv IDs are unique.

---

### Step 4: Vacuous theorem detection (subagent)

This is the most important judgment check. Launch **one subagent** with this prompt:

```
Search all .lean files in RLGeneralization/ for theorems that claim a substantive
result in their name but prove something trivial. Specifically:

1. VACUOUS BOUNDS: theorems named "*_bound" or "*_lower_bound" whose conclusion
   is `0 <= expr` (nonnegativity, not a bound on a quantity of interest).
   Run: grep -rn "theorem.*_bound\b" RLGeneralization/ --include="*.lean"
   Then for each, check if the conclusion is nonnegativity.

2. VACUOUS CONVERGENCE: theorems named "*_convergence*" or "*_rate*" whose proof
   is a single tactic (linarith, norm_num, exact h_*).
   Run: grep -rn "theorem.*convergence\|theorem.*_rate" RLGeneralization/ --include="*.lean"

3. ALGEBRAIC IDENTITIES WITH SUBSTANTIVE NAMES: theorems whose proof is `by ring`
   or `by field_simp` or `by norm_num` but whose name suggests a bound or inequality.

4. NEW TAUTOLOGICAL PROOFS: theorems whose entire proof is `exact h_something`
   (returning a hypothesis) but lack [WRAPPER]/[TAUTOLOGICAL]/[CONDITIONAL] tags.
   Run: grep -B3 ":= h_\|exact h_" RLGeneralization/ --include="*.lean" -r
   Filter out those that already have tags in their docstring.

For each finding, report: file:line, theorem name, what it actually proves,
what the name implies, and whether it has a tag. Group by severity:
- CRITICAL: substantive name, trivial proof, no tag
- WARNING: substantive name, trivial proof, has tag (tag may be wrong)
- INFO: trivial proof, honest name (no action needed)
```

---

### Step 5: Name-conclusion alignment (subagent)

Launch **one subagent** to spot-check name-conclusion alignment across modules:

```
Sample 30 theorems across different modules in RLGeneralization/.
For each, read the theorem name and the conclusion (type signature),
and check whether the name accurately describes what is proved.

Sampling strategy: pick 2-3 theorems from each of these modules:
MDP/, Concentration/, Bandits/, Exploration/, PolicyOptimization/,
LinearMDP/, Generalization/, LowerBounds/, OfflineRL/, Algorithms/,
Complexity/, ImitationLearning/

Check for:
- "bound" in name → conclusion should be an inequality X <= Y or Y <= X
- "convergence" in name → conclusion should involve a limit or rate
- "decomposition" in name → conclusion should be an equality
- "nonneg" in name → conclusion should be 0 <= X (this is honest)
- "optimal" in name → conclusion should prove optimality

Also check for docstrings that describe something different from the conclusion.

Report mismatches only. If all 30 pass, say "All 30 sampled theorems
have honest names."
```

---

### Step 6: Unused definition scan (subagent)

Launch **one subagent**:

```
Find definitions in RLGeneralization/ that have no references anywhere
(excluding their own definition line and comments).

Run:
grep -rn "^def \|^noncomputable def " RLGeneralization/ --include="*.lean"

For each definition found, check:
grep -rn "definition_name" RLGeneralization/ --include="*.lean" | grep -v "def definition_name" | grep -v "-- "

Report definitions with zero external references that are NOT already
marked with [UNUSED]. Only report the count and the top 10 by
importance (prefer defs in non-Draft modules).
```

---

### Step 7: Synthesize and report

After all checks complete, produce a single report:

```
## Audit Report — [date]

### Hard checks
| Check           | Status | Details |
|-----------------|--------|---------|
| Zero sorry      | PASS/FAIL | count |
| Clean build     | PASS/FAIL | error count |
| Warnings        | PASS/FAIL | count |
| Double docs     | PASS/FAIL | count |
| Orphan files    | PASS/FAIL | count |
| Corpus fresh    | PASS/FAIL | entry count |
| Fixture dedup   | PASS/FAIL | fixture count |

### Judgment checks
| Check                    | Findings |
|--------------------------|----------|
| Vacuous theorems         | count new / count total |
| Name-conclusion mismatch | count / 30 sampled |
| Unmarked unused defs     | count new |

### Action items
[Prioritized list of things to fix, grouped by:
 - CRITICAL (fix now): sorry, build errors, new vacuous theorems
 - WARNING (fix soon): untagged wrappers, misleading names
 - INFO (defer): unused defs, style nits]

### Summary
[One sentence: "N hard checks passed, M judgment issues found, K action items."]
```

---

## Quick mode

If the user specifies `quick` or the scope is narrow, skip Steps 4-6 (subagent checks) and only run the automated checks (Steps 1-3). Report the hard check table and stop.

## Module-scoped audit

If the user specifies a module (e.g., `audit Concentration/`), restrict all grep/find commands to that subdirectory. Still run the full pipeline but only on the specified module.

## Quality rules

- NEVER skip the hard checks (Steps 1-3). These are the foundation.
- NEVER report a theorem as vacuous without reading its actual proof body. The name alone is not sufficient — a theorem named `_nonneg` that proves nonnegativity is honest.
- ALWAYS run subagent checks in parallel (Steps 4-6) to minimize wall time.
- ALWAYS compare against the PREVIOUS audit's numbers if available. If vacuous count went UP, that's a regression.
- The goal is a clean bill of health, not a long list of findings. Findings should be actionable, not exhaustive.
