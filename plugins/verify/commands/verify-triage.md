---
name: verify-triage
description: Adversarial prose triage via the RLVerify harness — a sealed grader with no tools and no context rates each proof step SOUND or SUSPECT and ranks likely fatal flaws, to prioritize (never decide) scrutiny. Accepts a folder, a paper/link, pasted text, or -s/-p.
user_invocable: true
---

<command-name>verify-triage</command-name>

# /verify-triage — sealed adversarial read of a proof's steps

> A fast, cheap, independent first read of where a proof is most likely broken —
> WITHOUT decomposing or formalizing. Seconds to a minute, cents. For the full
> gated verdict, use `/verify-full-process`.
>
> The triage is **sealed** for a reason: an inline review by the orchestrating
> context is the same window later "confirming" its own guess — circular.
> Independence is what makes triage and a later audit two signals instead of one.
> **You do not perform the triage yourself.** The harness makes the sealed call
> parent-side; your job is to run it and relay the card.

## Input

$ARGUMENTS

A theorem + proof: pasted text, a fixture folder, a paper file, or an arXiv link.

## Run it

Read `harness/AGENT_CONVENTIONS.md` and follow it — especially input routing and
the verbatim-relay rule. Then run the harness from the repo root. This is short;
foreground is fine.

The trusted harness sends the sealed grader exactly this frozen instruction
before the theorem/proof text; keeping it here verbatim preserves the drift
guard between the compatibility command and the executed gate:

```
You are an adversarial reviewer. You have no other context and no tools.
Assess each proof step: SOUND or SUSPECT, with a one-line reason each, then
list the most likely fatal flaws ranked by severity. Output JSON only:
{"suspects": [{"step": <n>, "suspicion": "<reason>",
               "severity": "high|medium|low"}], "all_clear": <bool>}
```

```bash
# pasted theorem + proof → write to files first, then:
python3 -m harness triage -s <statement-file> -p <proof-file>

# an existing fixture folder:
python3 -m harness triage path/to/fixture/

# a paper (costs one extra sealed extraction call):
python3 -m harness triage paper.pdf --theorem "3.1"
```

Add `--json` only if the user wants machine-readable output; otherwise the
harness prints the card for you. It always exits 0 for a valid advisory result —
findings do NOT set a failure code, because triage is not a check. Exit 2 means
the tool or the grader itself failed; that is not a statement about the math.

If the harness reports a malformed grader reply it already fails toward MORE
scrutiny (`all_clear=false`); do not re-interpret that as a clean result.

## How to read the output (hard constraints — do not weaken)

- **Triage PRIORITIZES; it never decides and never skips.** It sets the ORDER in
  which you'd scrutinize steps — flagged steps first — so early exits are
  reached sooner. It does not shorten or replace any later phase.
- **An `ALL-CLEAR` triage carries ZERO weight.** Documented shipped failures
  (inconsistent axioms, a compact→finite downgrade, an imported sorry) all passed
  prose review. Finding nothing is a signature to scrutinize, not a clearance.
  Never report `ALL-CLEAR` as "the proof looks correct".
- **A triage flag is never evidence.** A verdict still requires a certificate, a
  named violated hypothesis, or a kernel result — none of which this command
  produces.

## Output

Relay the harness's card verbatim. It follows the standard grammar
(`verify-output-contract.md`): `OUTCOME` in
`ALL-CLEAR | SUSPECTS-FOUND | TRIAGE_ERROR | UNCERTAIN`, `EVIDENCE audit-only`,
`WEIGHT prioritization-only`, suspects sorted high→low severity.

Severity calibration used by the sealed grader: **high** = if this step is wrong
the theorem breaks; **medium** = weakens but recoverable; **low** = cosmetic.

Real example (clean UCB1 proof):
```
/verify-triage · ucb_regret_clean
OUTCOME   SUSPECTS-FOUND   (all_clear=false)
EVIDENCE  audit-only
WEIGHT    prioritization-only   (triage is ALWAYS this; it never decides)
DETAIL    4 suspects; top = Step 5 Hoeffding at fixed-s vs random count
NEXT      /verify-hypothesis-audit (Step 5 first), then /verify-full-process
```

| step | severity | suspicion |
|------|----------|-----------|
| 5 | high | Hoeffding legitimacy hinges on fixed s, not random T_i(t-1) |
| 4 | low | threshold 8 ln n vs needed 8 ln t (relies on t ≤ n) |
| 6 | low | per-pair 2/t^4 summed over (s,s*) over-counts ~t |
| 3 | low | max-over-s ≥ min-over-s* is an over-approximation |

An `ALL-CLEAR` card prints `DETAIL nothing flagged — a signature to scrutinize,
not a clearance` and no table.

## Where this fits

Triage is the cheap drafting-loop signal. Point the user onward:
`/verify-hypothesis-audit` on the flagged steps, `/verify-falsify` to hunt a
numeric counterexample, `/verify-full-process` when the proof is finished and
they want a real verdict. The full flow runs its own sealed triage parent-side
and stamps it into the run record automatically — running this first is for
*your* prioritization, and is never a substitute.
