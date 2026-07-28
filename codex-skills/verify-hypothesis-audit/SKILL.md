---
name: verify-hypothesis-audit
description: "Duplicate of Claude /verify-hypothesis-audit. Use when the user invokes /verify-hypothesis-audit, $verify-hypothesis-audit, or asks to run this RLVerify command. Standalone hypothesis audit — at every point one block invokes another, list ALL hypotheses of the invoked result and check each against the actual argument; catch missed/substituted hypotheses and cycles hidden by conditional conclusions"
---

# /verify-hypothesis-audit — Codex Duplicate

This is a Codex skill duplicate of `.claude/commands/verify-hypothesis-audit.md`. The Claude slash command name is `/verify-hypothesis-audit`; in Codex, invoke it as `$verify-hypothesis-audit` or write `/verify-hypothesis-audit` in the prompt. Interpret Claude-specific Task/Bash references as workflow instructions and use Codex-native tools or the local RLVerify CLI.

Preserve the verification discipline from the original command: verify, do not repair; do not add hypotheses or proof steps; treat sealed gates and kernel evidence according to the RLVerify output contract.

When this skill calls `python3 -m harness` directly or through RLVerify CLI examples, pass `--backend codex` unless the user explicitly asks for another backend. Pass `--model <codex-model>` when a specific Codex model is under test; otherwise let the Codex CLI use its configured default.

---

<command-name>verify-hypothesis-audit</command-name>

# /verify-hypothesis-audit — does each step satisfy what it invokes?

> A standalone component of **/verify-full-process** (the inter-block Hypothesis Audit).
> Run it to check the *connections* in a proof — where one step applies
> another result or a library lemma — WITHOUT formalizing anything. For the
> full flow, use `/verify-full-process`. This phase is the load-bearing detector for the
> failure modes prose review and the textual dependency graph both miss.

## Input

$ARGUMENTS

A proof (or the specific step + the lemma it invokes). If a corpus/Mathlib
lemma is cited, you may pull its exact hypotheses with `VerifyDriver().show(id)`
or `d.grep(...)`.

## The audit

For **every** point where one block invokes another (or a library lemma):

1. **List ALL hypotheses** of the invoked result — not just the ones the proof
   bothers to check.
2. **Check each** against the actual argument supplied. A proof that verifies
   one hypothesis (e.g. boundedness) while silently skipping another (e.g.
   independence) is a red flag, not a reassurance.
3. **Hypothesis-substitution camouflage**: when the proof explicitly verifies
   condition A but the critical condition is B, flag it. A parenthetical like
   "which satisfies [easy condition]" after an application often masks an
   unchecked [hard condition].
4. **Conditional-conclusion camouflage (cycle detector)**: when a block's
   conclusion holds only "on the event E" / "given X" / "whenever Y is
   bounded", record E as a hypothesis of **every** downstream invocation of
   that block. An invocation that drops the conditioning is unjustified. If E
   is (or implies) the conclusion of a block that in turn invokes this one,
   the proof is **CIRCULAR** even though the textual `depends_on` graph is
   acyclic — citation arrows point one way; the conditioning closes the loop.
   Canonical instance: a stochastic-approximation proof establishes noise
   convergence "on the event {supₙ‖θₙ‖ < ∞}", then invokes it unconditionally
   to prove that very boundedness (the Borkar–Meyn stability gap).

## Hypotheses commonly missed

**Probabilistic proofs**
- **Independence** — Hoeffding / Azuma / Bernstein require the concentrated
  quantity to be independent of the averaged randomness. Fixed points of
  empirical operators (V̂*, Q̂*) depend on ALL samples and violate this.
- **Measurability** — functions of random variables must be measurable w.r.t.
  the correct σ-algebra.
- **Uniform vs. pointwise** — a bound for a fixed quantity does not hold
  uniformly over a data-dependent quantity without a union bound / covering.

**Optimization proofs**
- **Maximizer identity** — "for the maximizing action a*", verify WHICH problem
  a* solves. If T̂ and T have different maximizers, writing (T̂−T)f(s) as a
  single-action expression is wrong — use |max f − max g| ≤ max|f − g|.
- **Convexity / compactness** — minimax, duality, sup/inf exchange need
  specific structural conditions.

## Outcomes (early exits this audit can decide)

- **HYPOTHESIS_VIOLATION** — a correct lemma is applied to an argument that
  **provably violates** a stated hypothesis. Name the lemma, the hypothesis,
  the offending argument, and why. The lemma is right; the instantiation is
  wrong.
- **CIRCULAR** — block A's justification presupposes the conclusion of a block
  that (directly or transitively) depends on it, via a conditioning event.
  Name both ends of the cycle and the event that closes it.
- **Clear** — every invocation's full hypothesis set is met. This is **not**
  evidence the proof is correct; it only clears the connections.

A flag here is a *prioritization signal*, never a verdict on its own — a
verdict still needs a named violated hypothesis (testimony) or, better, a
kernel-backed refutation.

**Inventory first.** Before judging any site, list EVERY invocation (one row
per site) so cleared sites are recorded, not just the flagged one. A
`HYPOTHESIS_VIOLATION` is emitted as four labelled fields — **LEMMA /
HYPOTHESIS / OFFENDING-ARG / WHY** — never a sentence. Decision rule:
HYPOTHESIS_VIOLATION = the invoked result is right but the instantiation
violates a hypothesis at THIS site; CIRCULAR = that violated hypothesis is a
conditioning event E which a downstream block proves *using* this block.

## Output (standard result card)

End with the standard result card (`verify-output-contract.md`). The invocation
inventory is the skill-specific table; record whether the verdict is still
testimony or was upgraded to a kernel refutation via `/verify-discharge`.

Real example (`ucb1_hoeffding_at_random_count`, Step 3):
```
/verify-hypothesis-audit · ucb1_hoeffding_at_random_count
OUTCOME       HYPOTHESIS_VIOLATION
EVIDENCE      audit-only   (UPGRADE: testimony — /verify-discharge not yet run)
WEIGHT        prioritization-only
DETAIL        Step 3 applies Hoeffding at the random count N_{t-1}(a)
LEMMA         Hoeffding's inequality
HYPOTHESIS    sample size n fixed & independent of the data
OFFENDING-ARG n := N_{t-1}(a)  (a stopping-time count of the same rewards)
WHY           the 1/t^4 bound needs a deterministic n; the clean proof fixes (t,s) then unions
NEXT          /verify-discharge (attempt a kernel refutation of the 1/t^4 step)
```

| invoked | hypotheses | argument | met? | why / camouflage |
|---------|-----------|----------|------|------------------|
| Hoeffding ineq. | $n$ fixed, indep. of data | $n = N_{t-1}(a)$ | no | random count, measurable in the rewards' σ-algebra |

A `CLEAR` card lists the inventory with all rows `met? = yes` and `DETAIL N
invocations, all hypotheses satisfied — clears connections only, not the proof`.

`CIRCULAR` example (SA-ODE method — name BOTH ends + the conditioning event E):
```
/verify-hypothesis-audit · sa_ode_gas_circular
OUTCOME   CIRCULAR
EVIDENCE  audit-only   (UPGRADE: testimony — downstream discharge gated)
WEIGHT    prioritization-only
DETAIL    Lemma 3 invokes Lemma 2 but drops Lemma 2's conditioning event E
EVENT     E = { sup_k ||θ_k|| < ∞ }  (the conditioning that closes the loop; Borkar-Meyn gap)
NEXT      —   (verdict-deciding cycle; sketch/discharge/library GATED)
```

| end | proves | only under |
|-----|--------|------------|
| Lemma 2 | noise negligible | E (= bounded iterates) |
| Lemma 3 | E (boundedness) | Lemma 2, used unconditioned → E presupposes E |

(The textual `depends_on` graph is acyclic, Lemma 3 → Lemma 2; the dropped
conditioning is what closes the cycle.)

## Optional: attach to a live /verify-full-process session

```python
from rlverify.driver import VerifyDriver
d = VerifyDriver(); d.resume("fixture_name")
d.resolve("block_a", violation="Library.Lemma.id",
          reason="applied at the random count N_t(a); the lemma needs a fixed n")
d.set_verdict("UNVERIFIED/HYPOTHESIS_VIOLATION",
              reason="block_a applies Library.Lemma.id at a sample-dependent count",
              block="block_a")
# or for a cycle:
d.resolve("block_a", circular="block_b", reason="...the conditioning event E...")
d.set_verdict("UNVERIFIED/CIRCULAR", reason="...", block="block_a")
```

To upgrade testimony to kernel evidence, see `/verify-discharge` (a small
Lean counterexample to the invalid inference via `d.refute`).
