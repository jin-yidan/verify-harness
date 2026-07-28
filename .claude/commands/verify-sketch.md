---
name: verify-sketch
description: Standalone sketch check — write the proof as a Lean skeleton with sorried block-lemmas and machine-check that the conclusion actually follows from the stated blocks before proving any of them
user_invocable: true
---

<command-name>verify-sketch</command-name>

# /verify-sketch — does the conclusion follow from the stated blocks?

> A standalone component of **/verify-full-process** (the sketch gate). Run it to
> machine-check a *decomposition* — that the main theorem really follows from
> its building blocks, even with every block `sorry`ed — WITHOUT discharging or
> assembling them. For the full flow, use `/verify-full-process`. Additive — calls
> `VerifyDriver.sketch`.

## Input

$ARGUMENTS

The main theorem statement plus the list of building blocks (name + Lean
statement each) and the intended glue.

## Write the skeleton

- Each non-library block is a **lemma-style** stub above the main theorem:
  `private lemma block_i (...) : ... := sorry`. (`have`-style only for
  proof-local glue facts — lemma-style handles induction, variable binding,
  attributes, reuse, and matches the final assembly byte-for-byte.)
- A block used "inside an induction" is stated as the fully-quantified step
  `∀ m, P m → P (m+1)`.
- Library blocks are imported and used directly.
- The main theorem is proven from the blocks with **explicit glue**: `exact`,
  a `calc` naming each block, or `linarith [block1, block2, ...]`. Bare
  `nlinarith` / `simp_all` / `aesop` / `omega` without explicit block
  arguments are **FORBIDDEN** at sketch time — a skeleton they close certifies
  nothing.

## Run it

```python
from rlverify.driver import VerifyDriver
d = VerifyDriver()                 # no begin() needed
result = d.sketch(skeleton_code, expected_blocks=["block1", "block2", ...])
```

Use **narrow imports** — the skeleton compile costs ~4s, same as one block.

## Read the result

- **Success** ⇒ the decomposition is machine-checked: the conclusion really
  follows from the stated blocks (Lean checks this even with the blocks
  sorried). `sketch` additionally fails any skeleton whose glue does not
  actually use every `expected_blocks` entry. **Caveat: skeleton-OK ≠
  blocks-OK** — the sorried statements can still be false; discharging them
  (`/verify-discharge`) is what proves them.
- **Failure is diagnostic, never an auto-verdict.** Distinguish a genuine
  decomposition gap (the blocks don't imply the conclusion — `result.goals`
  shows the missing implication) from a fixable glue/coercion bug. Fix glue
  bugs; report decomposition gaps honestly. **NEVER repair the decomposition
  just to make the skeleton compile** — adding a block or a hypothesis the
  proof never claimed defeats the purpose.

If discharging a block later forces its signature to change (extra binder, sum
reindexing, coercion), re-run `sketch` before continuing.

## Output (standard result card)

End with the standard result card (`verify-output-contract.md`). The blocks
table is the skill-specific table. **A pass certifies the GLUE, never the
blocks** — the card's `DETAIL` must restate "blocks still sorried" so the
caveat travels with the verdict (a vacuous or self-contradictory block set also
makes the skeleton compile while proving nothing).

Real example (UCB1 Step 7 skeleton):
```
/verify-sketch · ucb_step7_combine
OUTCOME   DECOMPOSITION-OK
EVIDENCE  kernel(skeleton)   (glue checked; blocks still sorried)
WEIGHT    load-bearing (decomposition) · zero-weight (proof)
DETAIL    conclusion follows from 1 sorried block; blocks NOT yet proven
NEXT      /verify-discharge (1 block: combine_count_bound)
```

| block | sorried | used in glue |
|-------|---------|--------------|
| combine_count_bound | yes | yes |
`DECOMPOSITION-GAP` (`result.goals` shows a missing implication) → `NEXT —`,
report honestly, never repair. `GLUE-BUG` (coercion/binder mismatch) → fix and
re-run.

## Optional: attach to a live /verify-full-process session

`d.sketch(...)` automatically stores the skeleton on the active session if one
exists (`d.resume("fixture_name")` first) — no separate record call needed.
