---
name: verify-library
description: Standalone library growth — evaluate a verified novel lemma for addition to RLGeneralization, generalize it to its atomic reusable form, re-run the redundancy and back-translation gates, then add_novel
user_invocable: true
---

<command-name>verify-library</command-name>

# /verify-library — should this verified lemma join the library?

> A standalone component of **/verify-full-process** (Phase 5). Run it to evaluate a
> compiled novel lemma for the shared library — WITHOUT running the rest of the
> pipeline. For the full flow, use `/verify-full-process`. Additive — calls
> `VerifyDriver.add_novel`.

## Input

$ARGUMENTS

A novel lemma that **compiled** (its full Lean code) plus its NL meaning.

## Decide: add or skip

The library holds only **generalized, reusable** building blocks — never
paper-specific or proof-specific results. Every addition must be decomposed to
its most general form.

**Add** if the lemma is:
- A self-contained fact in **general terms** (not tied to this proof's
  variables, notation, or context).
- Decomposed to its atomic level — if it combines two independent facts, add
  them separately.
- Something another proof could plausibly need.
- Named for what it IS, not where it came from (`weighted_sum_le_sup`, not
  `cfpo_step3_bound`).

**Skip** if the lemma is: a paper-specific assembled proof; proof-specific glue;
a trivial restatement of an existing theorem; an intermediate step that only
makes sense in this proof; tied to specific paper constants/notation. Also skip
**instantiations** — already covered by the general theorem.

**Generalization check:** "Would I need to rename variables or strip context to
make this useful elsewhere?" If yes, do that first. If it can't be stated
without this proof's setup, skip it.

## Re-run the two gates (statements drift during proof iteration)

1. `d.library_search(statement)` must still return **not-found** — if it finds a
   proof now, the lemma is redundant; skip it.
2. The **back-translation audit** (`/verify-backtranslate`) on the candidate
   must return no MISMATCH between the statement and its docstring/claimed
   content.

## Add it (code mode — preferred)

```python
from rlverify.driver import VerifyDriver
d = VerifyDriver()
d.add_novel(
    name="lemma_name",
    code=full_lean_code,           # statement extracted automatically
    target_dir="Optimization",     # ALWAYS set — pick the topic dir (Concentration, MDP, …)
    docstring="One-line NL description (indexed for search)",
    reusable=True,
    reuse_reason="General atomic fact plausibly useful in other proofs",
)
```

`add_novel` enforces automatically: an explicit reusable-only assessment and
reason; no duplicate id/name; **no `axiom`s**; no
bare `import RLGeneralization` (would create an import cycle); build
registration in `RLGeneralization.lean` + `lake build`, rolling back on
failure. Always pass a `docstring` (or a `/-- … -/` comment) — without one the
lemma is nearly invisible to natural-language search. After adding, run
`lake build RLGeneralization` once so future `import RLGeneralization` sees it.

This phase is mandatory in a full run **even when the overall verdict is
UNVERIFIED** — independent correct blocks salvaged during an early exit still
get evaluated here. A broken proof can still contain reusable lemmas.

**Both gates are BLOCKING.** A drifted-redundant candidate → `SKIPPED-REDUNDANT`;
a back-translation MISMATCH → `REJECTED-BY-GATE`. Note that `add_novel` enforces
only dup/axiom/import/build — it does **not** check generality, so the
"never paper-specific" rule must be applied by you (the add/skip + generalization
check) *before* the call.

## Output (standard result card)

End with the standard result card (`verify-output-contract.md`). The two gates
are the skill-specific table. Distinguish a deliberate **`WITHHELD-NO-WRITE`**
(gates passed, `add_novel` not run) from a `REJECTED-BY-GATE` — they look the
same otherwise.

Real example (Basel block ∑t⁻²=π²/6, audit run):
```
/verify-library · basel_sum
OUTCOME   WITHHELD-NO-WRITE   (gates passed; corpus not mutated during audit)
EVIDENCE  search-hit + audit-only
WEIGHT    zero-weight   (load-bearing only when add_novel actually writes)
DETAIL    general/atomic/reusable; target_dir=Analysis; add_novel withheld
NEXT      —   (run add_novel to write; OUTCOME would become ADDED)
```

| gate | result |
|------|--------|
| library_search not-found | PASS (grep tsum=0, zeta=0) |
| back-translation MATCH | PASS |

## Optional: link a lemma to its origin block

```python
d.add_novel(name="...", code=..., target_dir="...", docstring="...",
            block="origin_block_name", reusable=True,
            reuse_reason="...")   # records the generalized lemma's source block
```
