---
name: verify-triage
description: "Duplicate of Claude /verify-triage. Use when the user invokes /verify-triage, $verify-triage, or asks to run this RLVerify command. Standalone adversarial prose triage — a sealed subagent with no tools and no context rates each proof step SOUND or SUSPECT and ranks likely fatal flaws, to prioritize (never decide) scrutiny"
---

# /verify-triage — Codex Duplicate

This is a Codex skill duplicate of `.claude/commands/verify-triage.md`. The Claude slash command name is `/verify-triage`; in Codex, invoke it as `$verify-triage` or write `/verify-triage` in the prompt. Interpret Claude-specific Task/Bash references as workflow instructions and use Codex-native tools or the local RLVerify CLI.

Preserve the verification discipline from the original command: verify, do not repair; do not add hypotheses or proof steps; treat sealed gates and kernel evidence according to the RLVerify output contract.

When this skill calls `python3 -m harness` directly or through RLVerify CLI examples, pass `--backend codex` unless the user explicitly asks for another backend. Pass `--model <codex-model>` when a specific Codex model is under test; otherwise let the Codex CLI use its configured default.

---

<command-name>verify-triage</command-name>

# /verify-triage — sealed adversarial read of a proof's steps

> A standalone component of **/verify-full-process** (Phase 0). Run it for a fast,
> independent first read of where a proof is most likely broken — WITHOUT
> decomposing or formalizing. For the full flow, use `/verify-full-process`. The triage is
> **sealed** for a reason: an inline review by the orchestrating context is the
> same window later "confirming" its own guess — circular. Independence is what
> makes triage and a later audit two signals instead of one.

## Input

$ARGUMENTS

The theorem + proof text to triage.

## Run it

Spawn a SEALED subagent (Task tool) whose ENTIRE prompt is the verbatim
theorem+proof text plus exactly this instruction — **no library access, no
driver, no conversation context**:

```
You are an adversarial reviewer. You have no other context and no tools.
Assess each proof step: SOUND or SUSPECT, with a one-line reason each, then
list the most likely fatal flaws ranked by severity. Output JSON only:
{"suspects": [{"step": <n>, "suspicion": "<reason>",
               "severity": "high|medium|low"}], "all_clear": <bool>}
```

If the subagent returns malformed JSON, re-prompt once; if still malformed,
treat it as `all_clear=False, suspects=[]` (fail toward MORE scrutiny, never
less).

## How to read the output (hard constraints — do not weaken)

- **Triage PRIORITIZES; it never decides and never skips.** It sets the
  ORDER in which you'd scrutinize steps — flagged steps first — so early exits
  are reached sooner. It does not shorten any later phase.
- **An `all_clear` triage carries ZERO weight.** Documented shipped failures
  (inconsistent axioms, a compact→finite downgrade, an imported sorry) all
  passed prose review. Finding nothing is a signature to scrutinize, not a
  clearance.
- **A triage flag is never evidence.** A verdict still requires a certificate,
  a named violated hypothesis, or a kernel result.

## Output (standard result card)

End with the standard result card (grammar + vocabulary:
`verify-output-contract.md`). Sort suspects by severity (high→low) — the schema
does not guarantee order. Calibrate severity in the sealed prompt: **high** = if
this step is wrong the theorem breaks; **medium** = weakens but recoverable;
**low** = cosmetic. On `ALL-CLEAR` the card MUST still carry the zero-weight
warning, so an empty suspects list is never read as a clearance.

Real example (clean UCB1 proof):
```
/verify-triage · ucb_regret_clean
OUTCOME   SUSPECTS-FOUND   (all_clear=false)
EVIDENCE  audit-only
WEIGHT    prioritization-only   (triage is ALWAYS this; it never decides)
DETAIL    4 suspects; top = Step 5 Hoeffding at fixed-s vs random count
NEXT      /verify-hypothesis-audit (Step 5 first), then /verify-resolve
```

| step | severity | suspicion |
|------|----------|-----------|
| 5 | high | Hoeffding legitimacy hinges on fixed s, not random T_i(t-1) |
| 4 | low | threshold 8 ln n vs needed 8 ln t (relies on t ≤ n) |
| 6 | low | per-pair 2/t^4 summed over (s,s*) over-counts ~t |
| 3 | low | max-over-s ≥ min-over-s* is an over-approximation |

An `ALL-CLEAR` card prints `DETAIL nothing flagged — a signature to scrutinize,
not a clearance` and no table.

## Optional: attach to a live /verify-full-process session

```python
from rlverify.driver import VerifyDriver
d = VerifyDriver(); d.resume("fixture_name")
d.record_triage(suspects=[{"step": 3, "suspicion": "...", "severity": "high"}],
                all_clear=False)
```

Standalone, just keep the JSON — feed its ranking to `/verify-resolve` and
`/verify-hypothesis-audit` to order their work.
