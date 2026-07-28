---
name: verify-discharge
description: "Duplicate of Claude /verify-discharge. Use when the user invokes /verify-discharge, $verify-discharge, or asks to run this RLVerify command. Standalone discharge phase — formalize one building block into a compiling Lean 4 proof that follows the given argument, then run the anti-vacuity checks; or build a kernel-backed refutation of an invalid inference"
---

# /verify-discharge — Codex Duplicate

This is a Codex skill duplicate of `.claude/commands/verify-discharge.md`. The Claude slash command name is `/verify-discharge`; in Codex, invoke it as `$verify-discharge` or write `/verify-discharge` in the prompt. Interpret Claude-specific Task/Bash references as workflow instructions and use Codex-native tools or the local RLVerify CLI.

Preserve the verification discipline from the original command: verify, do not repair; do not add hypotheses or proof steps; treat sealed gates and kernel evidence according to the RLVerify output contract.

When this skill calls `python3 -m harness` directly or through RLVerify CLI examples, pass `--backend codex` unless the user explicitly asks for another backend. Pass `--model <codex-model>` when a specific Codex model is under test; otherwise let the Codex CLI use its configured default.

---

<command-name>verify-discharge</command-name>

# /verify-discharge — formalize one block (and prove it isn't vacuous)

> A standalone component of **/verify-full-process** (Phase 3). Run it to formalize a
> single block in Lean — or to build a small counterexample refuting an invalid
> inference — WITHOUT running the rest of the pipeline. For the full flow, use
> `/verify-full-process`. Additive — calls `VerifyDriver.compile` / `.formalize` /
> `.refute`.

## Input

$ARGUMENTS

The block's NL statement + the proof's argument for it (or, for a refutation,
the invalid inference and a concrete instance that breaks it).

## Formalize the block

Formalize **EXACTLY** what the proof argues. If the proof's argument is
incomplete or wrong, the formalization will fail — that is the signal, not a
problem to engineer around.

```python
from rlverify.driver import VerifyDriver
d = VerifyDriver()                                  # no begin() needed
d.compile_statement(stmt, imports=[...])            # validate signature first
result = d.compile(full_code)                       # then the full proof
```

- **Narrow imports** — `import RLGeneralization` pulls all of Mathlib and is
  ~6x slower. Use the specific `RLGeneralization.X.Y` / `Mathlib.*` modules. If
  narrow imports lack `Finset`/`BigOperators`, pass `opens=` (possibly
  `opens=""`).
- Strategy priority: `exact library_thm args` → `apply` + fill → `calc` chain →
  `have ...; linarith` → tactic combinators.
- **≤ 5 iterations** per block. On unsolved goals, `result.goals` holds the
  full goal states — keep the working prefix and retry only the listed goals;
  do NOT regenerate the whole proof.
- If 5 iterations fail, decompose the block into 2–3 sub-lemmas targeting the
  listed goals (depth limit 2) before marking it a gap.

**Rules (verification integrity):** never add a hypothesis not in the input;
never assume what should be proven; no `sorry` in the final output; prefer
library theorems; keep proofs short.

## Anti-vacuity checks (mandatory for novel blocks)

A block that compiles can still prove something weaker or trivial. Before
counting it verified:

1. **Hypothesis minimality** — comment out each hypothesis and recompile. Still
   compiles ⇒ the hypothesis is unused; often the statement is weaker than the
   claim. Investigate. Never suppress linters to hide this.
2. **Independence test** — can `positivity`/`simp`/`norm_num` alone close it
   without the hypotheses? If yes, the formalization doesn't capture the claim.
3. **Statement–claim contract** — quantifiers, inequality directions, and which
   variables are universally quantified all match the NL claim.
4. **Contradictory-hypothesis probe** — if the hypotheses look strong, exhibit
   a trivial instance (`example : ∃ ...`). Unsatisfiable hypotheses verify
   nothing.

For the main theorem statement, any `axiom`, an `add_novel` candidate, or a
`refute` statement, the **back-translation audit** is also mandatory — use
`/verify-backtranslate`.

## Kernel-backed refutation (upgrade an audit verdict to kernel evidence)

When a flaw is an *invalid inference* refutable on a tiny finite instance:

```python
d.refute("block_name", counterexample_code,
         description="<the refuted claim, verbatim>")
d.set_verdict("UNVERIFIED/WRONG", reason="...", block="block_name")
```

The counterexample theorem asserts *premises-hold ∧ ¬conclusion* for a concrete
instance. `verdict_evidence` becomes `"kernel"` only when the refutation
compiled with a clean standard-axiom closure. Attempt it for the
verdict-deciding block only, ≤5 compile iterations; failure never changes the
verdict (it stays audit-only, which is honest). Semantics: it certifies "this
inference step is invalid", never "the theorem is false". Never `add_novel` a
refutation — it's a paper-specific negative fact.

## Salvage rule

Any block **independent** of a failed block and **mathematically correct** MUST
still be formalized here and evaluated for the library (`/verify-library`).
"Not attempted" is never acceptable for an independent correct block.

## Output (standard result card)

End with the standard result card (`verify-output-contract.md`). A plain
discharged block is **`EVIDENCE compile-only`** — Lean accepted it but no kernel
closure has been read, so it can still be vacuous or import a sorry;
`/verify-assemble` is what yields `kernel`. If any anti-vacuity check fails, the
OUTCOME is `COMPILED-VACUOUS-RISK` (`WEIGHT zero-weight`), not `COMPILED`. The
four anti-vacuity results are the skill-specific table.

Real example (UCB1 `combine_count_bound`):
```
/verify-discharge · combine_count_bound
OUTCOME   COMPILED
EVIDENCE  compile-only   (kernel closure comes from /verify-assemble)
WEIGHT    load-bearing
DETAIL    proved via mul_le_mul_of_nonneg_left h hd (4s, 1/5 iterations)
NEXT      /verify-assemble
```

| anti-vacuity check | result |
|--------------------|--------|
| hypothesis minimality | PASS (hd used) |
| independence (simp alone) | PASS (fails without hd) |
| statement-claim contract | PASS |
| contradictory-hyp probe | PASS |
A kernel-backed refutation prints `OUTCOME REFUTED-KERNEL · EVIDENCE kernel`
only on a clean standard-axiom closure; a failed attempt is
`REFUTED-AUDIT-ONLY · EVIDENCE audit-only` (the verdict stays audit-only — honest).

## Optional: attach to a live /verify-full-process session

```python
d.resume("fixture_name")
d.formalize("block_name",
            statement="theorem block_name (...) : ...",   # signature, no := by
            proof="<tactic body, no leading by>",
            imports=[...])                                  # records the block on the session
```
