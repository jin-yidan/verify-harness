---
name: verify-assemble
description: "Duplicate of Claude /verify-assemble. Use when the user invokes /verify-assemble, $verify-assemble, or asks to run this RLVerify command. Standalone assemble + kernel audit — compile the fully-discharged file and read its #print axioms closure, the verdict source of truth that catches sorries and axioms hidden in imports"
---

# /verify-assemble — Codex Duplicate

This is a Codex skill duplicate of `.claude/commands/verify-assemble.md`. The Claude slash command name is `/verify-assemble`; in Codex, invoke it as `$verify-assemble` or write `/verify-assemble` in the prompt. Interpret Claude-specific Task/Bash references as workflow instructions and use Codex-native tools or the local RLVerify CLI.

Preserve the verification discipline from the original command: verify, do not repair; do not add hypotheses or proof steps; treat sealed gates and kernel evidence according to the RLVerify output contract.

When this skill calls `python3 -m harness` directly or through RLVerify CLI examples, pass `--backend codex` unless the user explicitly asks for another backend. Pass `--model <codex-model>` when a specific Codex model is under test; otherwise let the Codex CLI use its configured default.

---

<command-name>verify-assemble</command-name>

# /verify-assemble — compile the final file and read the kernel closure

> A standalone component of **/verify-full-process** (Phase 4). Run it to assemble a
> discharged proof and get its kernel axiom closure — the real verdict source —
> WITHOUT re-running earlier phases. For the full flow, use `/verify-full-process`.
> Additive — calls `VerifyDriver.assemble`.

## Input

$ARGUMENTS

The discharged pieces (no sorries left): the helper lemmas (novel blocks, each
proven from the proof's own argument) and the main theorem — its signature, its
tactic proof, and the imports.

## Run it

`assemble` builds the final file itself: imports → `open` line → `novel_code`
(helper lemmas) → `{statement} := by {proof}`. The main theorem name is parsed
from `statement` — there is no `main=` argument.

```python
from rlverify.driver import VerifyDriver
d = VerifyDriver()                       # no begin() needed; sets fixture="unknown"
result = d.assemble(
    statement="theorem main_thm (...) : ...",   # signature, no := by; name parsed from here
    proof="<tactic body of the main theorem>",
    novel_code="<all helper lemmas as one Lean string>",   # standalone: pass them here
    imports=[...],                                          # narrow imports
    opens="Finset BigOperators",                            # SAME opens used in formalize
)
# result.kernel_axioms · result.has_sorry_ax · result.compiled
```

(Inside a live session, `novel_code` may be omitted — `assemble` collects the
code of every compiled non-library lemma already formalized on the session.) On
success the driver automatically runs `#print axioms <main_theorem>`, reporting
the exact axiom closure transitively through all imports.

## Read the closure — this is the verdict, not the source text

- closure ⊆ `{propext, Classical.choice, Quot.sound}` → **VERIFIED**
- custom `axiom`s in the closure → **VERIFIED MODULO AXIOMS** (each must meet
  all four Axiom-lifecycle conditions: a well-known named result, correctly
  invoked, registered in `rlverify/results/axiom_backlog.md`, and passing the
  back-translation audit). Weaker than VERIFIED — say so.
- `sorryAx` in the closure → **UNVERIFIED, no exceptions** — this catches a
  sorry hiding in an imported module, which compiles cleanly with no warning
  and no `sorry` token in your source.
- no file to compile because the main statement is **not formalizable**
  (`d.main_unformalizable(...)` recorded) → **MAIN-UNFORMALIZABLE**, verdict
  INCOMPLETE — structurally impossible, not a failed check; never report it as
  CLOSURE-FAILED.

If the kernel check itself fails (`closure.ok == False`), do **not** report
VERIFIED — fix the check first (usually a wrong/unqualified theorem name). A
compile success alone is NOT VERIFIED; the closure is the source of truth.

VERIFIED verdicts can never be set manually — they come only from this audit.

## When the main statement can't even be STATED in Lean

If the conclusion needs infrastructure missing from Mathlib (a.s. convergence
of stochastic iterates, weak convergence, Itô calculus), assemble/kernel-closure
are structurally impossible, not negligently skipped. Record it:

```python
d.main_unformalizable("a.s. convergence of SA iterates needs measure-theoretic "
                      "stochastic-approximation infrastructure absent from Mathlib")
```

This never weakens the verdict (typically INCOMPLETE) — it makes the record
honest about WHY there's no closure. A later successful `assemble()` clears it.

## Output (standard result card)

End with the standard result card (`verify-output-contract.md`). The verdict is
READ from two fields: scan `kernel_axioms` for any name outside {propext,
Classical.choice, Quot.sound} or any `sorryAx`, and `has_sorry_ax` must be
False. Any *other* non-standard kernel axiom (e.g. `Lean.ofReduceBool`,
`Lean.trustCompiler`) → `CLOSURE-FAILED`, not VERIFIED. The axiom list is the
skill-specific table.

Real example (UCB1 Step 7 assembled):
```
/verify-assemble · ucb_step7_combine
OUTCOME   VERIFIED
EVIDENCE  kernel
WEIGHT    load-bearing
DETAIL    kernel closure ⊆ {propext, Classical.choice, Quot.sound}; has_sorry_ax=False
NEXT      —   (no novel blocks to evaluate; else /verify-library)
```

| axiom | standard? |
|-------|-----------|
| propext | yes |
| Classical.choice | yes |
| Quot.sound | yes |

`VERIFIED-MODULO-AXIOMS` lists each custom axiom (standard? = no) and requires
all four lifecycle conditions; `UNVERIFIED-SORRYAX` prints when `sorryAx` is in
the closure (no exceptions, even with no `sorry` token in source).

`MAIN-UNFORMALIZABLE` example (SA a.s.-convergence — no closure to read):
```
/verify-assemble · sa_ode_gas_circular
OUTCOME   MAIN-UNFORMALIZABLE
EVIDENCE  none
WEIGHT    zero-weight
DETAIL    a.s. convergence of SA iterates needs measure-theoretic infra absent
          from Mathlib; sketch n/a, kernel n/a (no closure) -> verdict INCOMPLETE
NEXT      —   (here also dominated by upstream CIRCULAR early exit)
```
(MAIN-UNFORMALIZABLE has no axiom table — there is no closure.)

## Optional: attach to a live /verify-full-process session

If a session is active (`d.resume("fixture_name")`), `assemble()` stores the
file and closure on it automatically; `d.finish()` then writes the run record
with the kernel axioms and a reproducible `#print axioms` appended to the saved
`.lean` file.
