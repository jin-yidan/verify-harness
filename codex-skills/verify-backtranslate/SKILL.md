---
name: verify-backtranslate
description: "Duplicate of Claude /verify-backtranslate. Use when the user invokes /verify-backtranslate, $verify-backtranslate, or asks to run this RLVerify command. Standalone back-translation audit — a sealed subagent renders a Lean statement to precise English with no other context, then a match rubric flags any quantifier/relation/constant/hypothesis/type mismatch against the claimed meaning"
---

# /verify-backtranslate — Codex Duplicate

This is a Codex skill duplicate of `.claude/commands/verify-backtranslate.md`. The Claude slash command name is `/verify-backtranslate`; in Codex, invoke it as `$verify-backtranslate` or write `/verify-backtranslate` in the prompt. Interpret Claude-specific Task/Bash references as workflow instructions and use Codex-native tools or the local RLVerify CLI.

Preserve the verification discipline from the original command: verify, do not repair; do not add hypotheses or proof steps; treat sealed gates and kernel evidence according to the RLVerify output contract.

When this skill calls `python3 -m harness` directly or through RLVerify CLI examples, pass `--backend codex` unless the user explicitly asks for another backend. Pass `--model <codex-model>` when a specific Codex model is under test; otherwise let the Codex CLI use its configured default.

---

<command-name>verify-backtranslate</command-name>

# /verify-backtranslate — does this Lean statement say what it claims?

> A standalone component of **/verify-full-process** (the back-translation audit). Run it
> to check whether a Lean statement faithfully encodes a claimed mathematical
> meaning — for ANY statement, not just inside the pipeline. For the full flow,
> use `/verify-full-process`. The audit is **sealed**: a self-check by the same context
> window that wrote the formalization is circular, so this MUST be an
> independent subagent.

## Input

$ARGUMENTS

The Lean statement(s) to audit — **plus the `def`s for any non-Mathlib symbols
in the signature** (without them the rendering is impossible) — and the claimed
NL meaning you'll compare against. Audit-worthy statements: a main theorem, any
`axiom` declaration, any `add_novel` candidate, any `refute` counterexample.

## Step 1 — sealed render (subagent, no other context)

Spawn a subagent (Task tool) whose ENTIRE prompt is **only** this plus the Lean
declarations + their definitions. No paper text, no NL claim, no conversation
context.

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

## Step 2 — match rubric (you, with the claim + the rendering, NOT the Lean)

For each category output **MATCH**, **NOTE** (benign formalization choice), or
**MISMATCH** (blocking):

1. **QUANTIFIER ORDER & BINDING** — same variables, same ∀/∃, same nesting?
   Any paper-universal made existential/fixed, or vice versa? Any variable the
   paper binds to a SPECIFIC object (an algorithm's epoch count, a maximizer, a
   fixed point) that the Lean leaves arbitrary? **Arbitrary-where-specific is
   always MISMATCH.**
2. **RELATION** — ≤ vs <, = vs ≤, direction, sup vs inf, max vs min.
3. **CONSTANTS** — every constant, exponent, log base, √ verbatim (2 vs 4,
   2logK/β vs logK/β).
4. **HYPOTHESIS SET** — every paper hypothesis present; NO extra or silently
   strengthened hypotheses (e.g. K ≥ 1 became log K ≥ 1 — extras violate "never
   add hypotheses"); none weakened.
5. **OBJECT TYPES** — finite vs compact vs arbitrary; matrix vs scalar stand-in;
   distribution vs weight function; the actual MDP/process vs an abstract
   sequence of reals. A scalar standing in for a structured object is MISMATCH
   unless the relation between scalars IS the cited lemma and this is disclosed.

**Benign (NOTE, never MISMATCH):** `Fin n → ℝ` for ℝⁿ; `Finset` ∑/sup' for
finite ∑/max; `(0 ≤ x : ℝ)` for `x : ℝ≥0`; currying; `[Fintype]`/`[Nonempty]`
instances when the setting is finite/nonempty; a named hypothesis restating a
standing assumption.

**Any MISMATCH ⇒ the formalization is unfaithful.** Fix the Lean and redo the
back-translation, or carry the discrepancy into the verdict (the statement
cannot count as verifying the claim). **Never downgrade MISMATCH to NOTE to
preserve a verdict.**

**Decorative-binder check (drives OBJECT TYPES).** In Step 1, require the
subagent to list every binder/hypothesis that appears in NO other hypothesis and
NOT in the conclusion (e.g. underscore-prefixed `_B, _T, _hT`). If structural
binders meant to encode the object (an MDP, an algorithm, a count) are unused,
the object is **DECORATIVE → forces an OBJECT TYPES MISMATCH**. Also require the
claimed meaning to name the concrete object under test ("the expected regret of
the UCB1 *algorithm*", not "a regret bound") — otherwise the check passes
spuriously against a scalar stand-in.

## Output (standard result card)

End with the standard result card (`verify-output-contract.md`). The five rubric
categories are the skill-specific table; **OUTCOME is the worst category**;
`DETAIL` is the subagent's "In plain terms" sentence.

Real example (corpus `ucb_expected_regret_bound`):
```
/verify-backtranslate · ucb_expected_regret_bound
OUTCOME   MISMATCH   (worst of the 5 categories)
EVIDENCE  audit-only
WEIGHT    load-bearing
DETAIL    "if a real x ≤ (1−δ)·g + δ·T with δ>0, g≥0 then x ≤ g + δ·T" — bandit binders unused
NEXT      —   (MISMATCH blocks the verdict: fix the Lean statement, redo)
```

| category | verdict | note |
|----------|---------|------|
| quantifier order/binding | MATCH | |
| relation | MATCH | |
| constants | MATCH | |
| hypothesis set | NOTE | _hT, _hd_le, _hL present but unused |
| object types | MISMATCH | _B, _T, _L decorative → an arbitrary real, not UCB1 regret |

## Optional: attach to a live /verify-full-process session

```python
from rlverify.driver import VerifyDriver
d = VerifyDriver(); d.resume("fixture_name")
d.record_backtranslation("main",                 # or block name / "refutation"
                         verdict="MATCH",         # MATCH | NOTE | MISMATCH
                         notes="...",
                         categories={"quantifiers": "MATCH", "relation": "MATCH", ...})
```

A MISMATCH on a main theorem or axiom blocks the verdict; on an `add_novel`
candidate it blocks the addition until statement and docstring agree.
