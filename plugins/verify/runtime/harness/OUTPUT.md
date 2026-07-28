# Harness output structure

The contract for what the BYO-agent harness emits. It mirrors the `/verify-full-process`
skill's output (see `PIPELINE.md §5`) and adds the two things an *untrusted*
driver requires — **enforcement** and **provenance**. Unlike the skill, whose
output grammar is *instructed in prose* and produced by the agent, the harness
output is produced by **code** (`rlverify/verdict.py`, `rlverify/mcp_server.py`,
`harness/runner.py`); this file documents that code contract so it is as
specified as the skill's.

There are three layers.

---

## Layer 1 — driver event lines + summary block (shared with the skill)

The harness drives the **same** `VerifyDriver`, so its phase events and final
summary block are byte-for-byte the skill's. One line per event:

```
[PHASE     ] BLOCK                        GLYPH STATUS — detail
```

Phases: `begin | resolve | gate | falsify | sketch | discharge | compile |
assemble | library | verdict`. Glyphs: `✓` ok · `✗` fail/refuted · `~`
instantiation · `?` novel · `·` info/skip · `⚠` warning. The
`=== RLVerify: <fixture> ===` summary block (Verdict / Blocks / Falsify /
Sketch / Kernel / Novel added / Artifacts) is emitted by `driver.finish()`.

(The demo scripts in `harness/examples/` hide these lines by default for a clean
panel; set `DEMO_VERBOSE=1` to show them.)

---

## Layer 2 — the harness `verdict_line` (string contract)

Built by `HarnessSession._enforced_line()` — the **only** place a verdict is
emitted, so no raw VERIFIED can leak before enforcement. Fixed grammar; **line 1
is the machine-readable result** (the analog of the skill's `Verdict :` line):

```
VERDICT: <class>                                       (always — see classes below)
  (downgraded from <base_verdict>)                     iff strict enforcement downgraded
  gate gaps: <reason>; <reason>; …                     iff required gates missing
  ⚠ UNSANDBOXED (RLVERIFY_SANDBOX=0): …                iff the run was unconfined (execution-safety provenance, a LABEL not a gate)
  evidence: <tier>                                     (always — the contract EVIDENCE tier ESTABLISHED, ≠ the verdict)
  falsify: R refuted / P passed / V vacuous / S skipped iff any falsification recorded
    PASSED depth (hyp-satisfied instances): <blk>=<n>, …
  ⚠ SHALLOW falsification (zero verification weight; thin flaw-hunt): <blk>(<n>), …
    falsify provenance: <x> harness-executed / <y> agent-attested
  ⚠ AGENT-ATTESTED falsification (numbers not verified by the harness): <blk>, …
```

Parsing rule: take everything after `VERDICT: ` on the first line as the
verdict class; all subsequent lines are indented qualifiers.

---

## Layer 3 — structured contracts (the machine-readable shapes)

### Ingested fixture folder  (`rlverify-out/<paper>/<label>/`)
Paper/link/stdin inputs are normalized into an ordinary fixture folder before
verification:
```
statement.md     # extracted theorem statement, copied from source anchors
proof.txt        # extracted proof text, copied from source anchors
claim.txt        # natural-language claim passed to back-translation
source.txt       # normalized paper/source text
metadata.json    # source kind, source URL/path, extraction notes, uses[]
```
`--dry-run` stops after writing this folder. A PDF fixture's metadata notes
`source: PDF text layer`, because downstream mismatches may be extraction noise.

### `run_verification(...) -> dict`  (`harness/runner.py`)
```python
{
  "fixture":          str,   # session name
  "verdict_line":     str,   # the Layer-2 string above
  "paused":           bool,  # legacy resumable state; current authorized runs continue automatically
                             #   requires an explicit continuation choice
  "decision_required": bool,
  "preflight":        dict,  # findings, targeted confirmation, and next action
  "triage_suspects":  int,   # number of sealed-triage suspects flagged
  "corpus":           str,   # path to the run's frozen corpus snapshot;
                             #   its sibling runs/ dir holds the artifacts
  "sandbox":          str,   # "on" | "off" — execution-safety provenance:
                             #   "off" (RLVERIFY_SANDBOX=0, the only non-macOS
                             #   path) means the untrusted-code guarantee was not
                             #   in effect. A LABEL; never an input to the verdict.
  "state_dir":        str | None,  # resumable CLI state when enabled
  "structural":       dict,  # trusted conditional-source recheck; when
                             #   compiled, status is COMPILES MODULO PLACEHOLDERS
  "phase_telemetry":  dict,  # per-phase calls/cost/time and incremental findings
}
```

### Resumable state  (`rlverify-out/.state/<name>/`)
CLI verification stores resumable state under `rlverify-out/.state/<name>/`
while a run is incomplete:
`corpus.jsonl`, `runs/<name>.inprogress.json`, sealed-gate sidecars,
`preflight.json`, `confirmation.json`, `verification_mode.json`,
`phase_telemetry.json`, `cost.json`, and `input.json` with the
statement/proof/claim fingerprint. Runner-owned triage, hypothesis,
confirmation, and preflight sidecars are SHA-256-bound in
`input.json.trusted_sidecars`; mutation causes cache rejection and recomputation.
`python3 -m harness verify --resume <name>` loads that state and re-launches the
agent with `RLVERIFY_RESUME=1`; the MCP `begin(name)` call resumes the journal
instead of overwriting it. A fresh same-name run refuses while the state
directory exists. After a terminal verdict the CLI copies the durable evidence
bundle to `rlverify-out/` and removes completed state automatically.
`--keep-intermediates` preserves it for debugging.

### Fetched-paper cache  (`rlverify-out/.papers/<id>/`)
Ingesting a URL or arXiv id caches the fetched source under
`rlverify-out/.papers/<id>/`, keyed by id **including the version** (`2406.01234v2`
caches separately from `2406.01234`), so a rerun does not refetch. The cache is
pure input — nothing downstream reads it after the fixture is materialized —
so delete `rlverify-out/.papers/` freely; the next run refetches. Materialized
fixtures under `rlverify-out/<paper>/<label>/` are NOT cache and are the
reviewable record of what was actually verified.

### `enforce(run, strict=True) -> dict`  (`rlverify/verdict.py`)
The verdict authority. **Every** harness verdict passes through this.
```python
{
  "verdict":       str,        # the enforced class (UNVERIFIED/UNGATED if downgraded)
  "base_verdict":  str,        # the class before enforcement
  "downgraded":    bool,       # True iff a VERIFIED-class base had gate failures
  "gate_failures": list[str],  # human-readable missing/failed gates
}
```

### `falsify_summary(run) -> dict`  (`rlverify/verdict.py`)
```python
{
  "counts":           {"REFUTED": int, "PASSED": int, "VACUOUS": int, "SKIPPED": int},
  "passed_depths":    list[tuple[str, int]],  # (block, hyp_satisfied) per PASSED
  "shallow":          list[str],              # "block(n)" with n < 10_000
  "attested":         list[str],              # blocks whose falsify was agent-attested
  "harness_executed": int,                    # count run by trusted harness code
  "total":            int,
}
```

### `build_report(out, rec) -> dict`  (`harness/report.py`)
Structured renderer input for terminal and Markdown output. It delegates verdict
class/evidence/gate decisions to `rlverify.verdict` and adds artifact/provenance
metadata:
```python
{
  "name": str,
  "verdict": {"class": str, "reason": str, "evidence": str,
              "gate_failures": list[str], "line": str},
  "formal": {"statement": str, "proof": str, "compiled": bool,
             "kernel_axioms": list[str], ...},
  "preflight": dict,
  "structural": {"status": str, "compiled": bool,
                 "placeholders": list[str],
                 "independent_discharged": list[str], ...},
  "phase_telemetry": {
      "schema_version": 1,
      "phases": list[dict],  # phase/status/calls/wall/cost/discoveries
  },
  "gates": {"triage": dict, "backtranslations": list[dict],
            "falsifications": list[dict], "falsification_summary": dict},
  "refutations": list[dict],
  "artifacts": list[dict],  # main certificate and refutation Lean files, labeled
  "cost": {"agent_usd": float | None, "wall_s": float | None,
           "sealed_gate_calls_metered": False},
  "provenance": {"sandbox": "on" | "off", "corpus": str, "record_path": str},
}
```

### `verdict_class(run) -> str`  — the possible verdict classes
Kernel-derived or agent-set, then enforcement-adjusted:

| Class | Source | Meaning |
|---|---|---|
| `VERIFIED` | kernel | compiled; closure ⊆ {propext, Classical.choice, Quot.sound} |
| `VERIFIED/ALTERNATIVE-PROOF` | trusted parent | theorem kernel-verified, submitted proof-step mapping not established |
| `VERIFIED MODULO AXIOMS` | kernel | compiled; closure has custom axioms |
| `UNVERIFIED` | kernel | `sorryAx` in the closure |
| `UNVERIFIED/WRONG` | scoped kernel-backed main-theorem refutation | a well-defined witness satisfies every hypothesis and negates the theorem |
| `UNVERIFIED/PROOF_INVALID` | scoped kernel-backed proof-step refutation | the submitted proof is invalid; theorem truth remains unknown |
| `UNVERIFIED/HYPOTHESIS_VIOLATION` | deterministic contract check or scoped finding | the statement/proof omits a load-bearing hypothesis; no theorem counterexample established |
| `UNVERIFIED/MISMATCH` | sealed statement audit | the formal and submitted statements do not match |
| `UNVERIFIED/SUSPECTED` | audit | a serious finding lacks independent mathematical certification |
| `UNVERIFIED/INCOMPLETE` | agent `set_verdict` | recorded inability to complete |
| `UNVERIFIED/UNGATED` | **enforcement** | VERIFIED-class base but a required gate didn't run |
| `COMPILED` / `HAS GAPS` | driver | compiled-without-kernel / unfinished |

### Run-record JSON  (`<runs>/<fixture>_<ts>.json`)
Same schema as the skill's runs/ record. Key fields:
`fixture, workflow_contract_version, verdict, verdict_reason, verdict_evidence,
kernel_axioms, has_sorry_ax, compiled, gate_downgrade, lemmas[],
sketch_verified, sketch_expected_blocks[], discharge_order[],
falsifications[], refutations[], step_certificates[], triage{}, hypothesis_audit{},
backtranslations[], novel_added[]`. Each v3 lemma also records the immutable
proof mapping: `source_excerpt`, `source_excerpt_sha256`,
`source_excerpt_verified`, `hypotheses[]`, `depends_on[]`,
`discharge_certificate_sha256`, and `trusted_rechecked`. The run-level
`proof_faithfulness` distinguishes `submitted-proof` from `alternative-proof`.

Preflight state also has `confirmation.json`, keyed by the stable hash of the
exact finding set. Confirmed negative states preserve the certificate scope,
finding kind, premise-satisfaction, definedness, conclusion-negation, and
statement-faithfulness stamps; `NOT_CONFIRMED` includes a trusted positive step
certificate and match evidence; `UNRESOLVED` records rejected or conflicting
candidates and any bounded confirmation error without upgrading the audit.

Structural-continuation records additionally carry `preflight`,
`structural_mode`, `structural_code`, `structural_placeholders`,
`structural_independent_discharged`, `structural_trusted_recheck`, and
`structural_artifact`. These fields describe conditional compilation and never
upgrade the theorem verdict.

### Reproducible certificate  (`<runs>/<fixture>_<ts>.lean`)
Written when a main theorem was assembled; ends with `#print axioms <main>`.
Re-checkable with `lake env lean <file>` — no agent, no harness, kernel only.
The CLI copies artifacts from the run record, not from a broad filename glob:
the main certificate is labeled separately from any
`<fixture>_<ts>_refute_<block>.lean` counterexample files.

### Signed integrity manifest (`<state>/integrity.json`)

The trusted parent hashes the exact saved `input.json`, canonical run record,
and content-addressed main Lean certificate, then signs those hashes with
Ed25519. The CLI copies the manifest and input beside the user-facing artifacts.
Verify the signature and artifact hashes without an agent:

```bash
python3 -m harness.integrity rlverify-out/<name>-integrity.json \
  --input rlverify-out/<name>-input.json \
  --record rlverify-out/<timestamped-record>.json \
  --certificate rlverify-out/<certificate>.lean
```

The manifest includes the public-key fingerprint so a stable installation key
can be pinned across runs. Set `RLVERIFY_SIGNING_KEY` to a protected Ed25519 PEM
path when an organization-managed identity is required.

### Markdown report  (`python3 -m harness verify ... --report [path]`)
`--report` writes a durable Markdown report. Bare `--report` defaults to
`rlverify-out/<name>-report.md`; passing a path overrides it. The report includes
the source, the original claim, formal Lean statement/proof, verdict/evidence,
gate table, flaw/refutation section, labeled artifacts with `lake env lean ...`
reproduction commands, cost/wall-time when available, and sandbox/run-record
provenance.

**Source provenance.** The `**Source:**` line names where the claim came from —
the arXiv URL or file for an ingested paper, `CLI input: <name>` otherwise —
followed by `**Source note:**` lines carrying the ingestion stamps, notably
`source: PDF text layer`. Without that stamp a downstream MISMATCH cannot be
told apart from PDF extraction noise. Provenance is recovered from the fixture's
`metadata.json` when you rerun on a materialized fixture folder, so the
`verify <fixture path>` rerun keeps it.

With `--all-theorems`, the `--report` path receives the one final,
self-contained aggregate report: dependency graph, verification order, summary,
one detailed section per component, aggregate kernel-audited Lean source,
artifact links, and golden-workflow hashes. Separate per-theorem Markdown files
are intermediate renderings and are not written.

### Standalone component cards  (`triage`, `audit`, `falsify`)
These are drafting-loop surfaces, not full verifier verdicts.

`python3 -m harness triage ...` runs sealed adversarial triage and emits a card
with `OUTCOME` in `ALL-CLEAR | SUSPECTS-FOUND | TRIAGE_ERROR | UNCERTAIN`,
`EVIDENCE audit-only`, and `WEIGHT prioritization-only - not a verdict`.
Valid advisory outcomes exit 0. Tool/backend/malformed-output errors exit 2.

`python3 -m harness audit ...` runs the sealed hypothesis audit and emits
`OVERALL CLEAR | HYPOTHESIS_VIOLATION | CIRCULAR | UNCERTAIN | ERROR`,
`EVIDENCE audit-only`, and `WEIGHT prioritization-only - not a verdict`.
Findings exit 0 because they are prioritization-only; `ERROR` exits 2.

`python3 -m harness falsify ...` runs a seeded Python sampler through
`rlverify.falsify_run.run_sampler`. `REFUTED` exits 1 and carries a witness,
seed, and rerun command. `PASSED` and `VACUOUS` exit 0 and carry zero
verification weight: no counterexample found is evidence, not proof; vacuous
means the hypotheses were not exercised enough. Generated samplers are arbitrary
Python and require explicit trusted-local consent (`--trust-samplers`,
`RLVERIFY_TRUST_SAMPLERS=1`, or an interactive yes). Tool/sampler errors exit 2.

---

## What the harness adds over the skill output (by design)

Both surface the same verdict and the same summary block. The harness output
*additionally* foregrounds, because its driving agent is **untrusted**:

1. **Enforcement** — the headline can be `UNVERIFIED/UNGATED` (`downgraded from
   VERIFIED`). A clean kernel closure is necessary but **not sufficient**: the
   flaw-hunting gates must have run. `enforce()` is the gate; `_enforced_line`
   guarantees the verdict never bypasses it.
2. **Provenance** — `falsify provenance: x harness-executed / y agent-attested`
   and the `⚠ AGENT-ATTESTED` line. The skill needs neither (the human is the
   trusted runner); the harness must report **who** checked each claim, because
   an agent-attested number rests only on the agent's word.

So the contract is: *the skill's structure, plus enforcement and provenance,
with the verdict forced through `enforce()`.*

---

## Crosswalk to the `/verify-*` output contract (A1a)

The skill emits a **per-phase result card** with a closed OUTCOME vocabulary, an
EVIDENCE ladder, and a WEIGHT (`.claude/commands/verify-output-contract.md`). The
harness emits ONE **composite** verdict (Layer 2), not a card stack — different
shapes, so this is a **one-way crosswalk, not an identity**. The harness has one
**deliberate verdict-class extension the contract lacks** (it is *why the
untrusted harness exists*): `UNVERIFIED/UNGATED` (enforcement). A second
harness-only token, `GATE_ERROR`, is **not a verdict class** — it is a
back-translation *gate-record* outcome (a grader timeout/crash) that surfaces as
the downgrade *reason* behind a `UNVERIFIED/UNGATED`. The harness does **not**
flatten its composite verdict into a single per-phase OUTCOME token.

### Verdict-class → contract concept
| Harness `verdict_class` | Nearest contract OUTCOME | EVIDENCE | Note |
|---|---|---|---|
| `VERIFIED` | `VERIFIED` (assemble) | `kernel` | aligned |
| `VERIFIED/ALTERNATIVE-PROOF` | `VERIFIED` (assemble) | `kernel` | theorem established, but the submitted proof-step mapping did not pass |
| `VERIFIED MODULO AXIOMS` | `VERIFIED-MODULO-AXIOMS` | `kernel` | spelling (space vs hyphen) reconciled **in docs only**; the live driver string keeps the space (frozen) |
| `UNVERIFIED` (sorryAx) | `UNVERIFIED-SORRYAX` | `kernel` | spelling reconciled here only |
| `UNVERIFIED/WRONG` | `REFUTED` (falsify) / refute | `kernel` (kernel-backed refute) · `certificate` (deterministically, independently validated witness) | detection axis |
| `UNVERIFIED/SUSPECTED` | `REFUTED` / hypothesis-audit finding | `audit-only` | agent testimony or confined witness awaiting independent validation |
| `UNVERIFIED/MISMATCH` | `MISMATCH` (back-translate) | `audit-only` | blocks the verdict |
| `UNVERIFIED/HYPOTHESIS_VIOLATION` · `…/CIRCULAR` | `HYPOTHESIS_VIOLATION` · `CIRCULAR` (hyp-audit) | `audit-only` | |
| `UNVERIFIED/INCOMPLETE` | `MAIN-UNFORMALIZABLE` (assemble) — nearest | `audit-only`/`none` | composite: sound but a step is unformalizable |
| `COMPILED` | `COMPILED` (discharge) | `compile-only` | not a pass |
| `HAS GAPS` | — | `none` | unfinished run |
| `UNVERIFIED/UNGATED` | **HARNESS-ONLY** | n/a | enforcement — no contract analog (by design) |

`GATE_ERROR` is **not** in this table because it is not a `verdict_class`: it is a
back-translation gate-record outcome (`harness/backtranslate.py`) — a grader
timeout/crash, not a proof defect — that `gate_failures` turns into the downgrade
reason behind `UNVERIFIED/UNGATED`. Harness-only, like the enforcement it triggers.

### EVIDENCE ladder — what the harness can honestly emit
`kernel` (VERIFIED or a kernel-backed refute) · `compile-only` (COMPILED) ·
`search-hit` (a resolve library match) · `audit-only` (report_failure /
back-translation / hypothesis-audit / generated-sampler REFUTED) · `none`
(HAS GAPS, a clean falsify PASS, VACUOUS). The contract's **`certificate`** tier
requires a trusted deterministic checker to validate the serialized witness and
stamp `certificate_validated=true` plus
`independent_checker="deterministic"`. Harness execution alone, including an
agent-authored second `recheck` formula, does not establish independence. The MCP
`falsify_run` route executes generated Python only through the confined runner
and records its result as `audit-only`; the trusted parent also clears forged
certificate stamps before deriving the final verdict. A kernel-backed Lean
refutation remains the strongest negative evidence.

**A1b (DONE 2026-06-28):** `rlverify.verdict.evidence_tier(run)` derives the
strongest tier the run established and it is surfaced on the verdict line
(`evidence: <tier>`) and the result panel. It is **not the verdict** — a
`UNVERIFIED/UNGATED` run reads `evidence: kernel` (a clean closure was read, the
gates just didn't run). Tiers the harness emits: `kernel` (clean/sorryAx closure
or a kernel-backed refute), `compile-only`, `audit-only` (a testimony verdict or
an agent-attested or `dep|` REFUTED falsify), `none` (HAS GAPS / clean PASS), and
`certificate` (a trusted deterministic checker independently validated the
serialized REFUTED witness). `search-hit`
is a per-phase tier, not a final-verdict tier.

### WEIGHT
The composite verdict is **load-bearing**. The hypothesis audit's findings and
resolve/search hits remain prioritization-only. Discharge's heuristic
independence smell remains a warning, while its deterministic id-shaped finding
(`hypothesis == conclusion`) is a workflow-v2 gate failure. Workflow v2 also
gates explicit dependency declarations, graph validity, successful sketch
coverage, and dependency-ordered per-block discharge. A falsify PASS is
**zero-weight** (surfaced, never verifying).

**Triage is a deliberate split, not a clean prioritization-only:** the triage
*suspect rankings* are prioritization-only (they order which steps to scrutinise,
never decide which is flawed), but the sealed-triage *gate record* IS
load-bearing — its absence or a missing `executed_by="harness"` stamp downgrades a
VERIFIED-class base to `UNVERIFIED/UNGATED` (`rlverify/verdict.py` `gate_failures`,
the first check). So triage's rankings match the contract's `prioritization-only`
WEIGHT, while its gate *presence* is part of enforcement (a harness addition over
the skill, which trusts the human runner).

---

## Scope — verification plus trusted reusable-only curation

The harness exposes **no library-growth tool**: `add_novel` / the skill's
`/verify-library` Phase 5 are intentionally **absent** from the MCP surface, so a
BYO agent cannot grow the corpus.

**Why (not an oversight — a consequence of the trust model):** library growth
*mutates the corpus*, but the harness deliberately drives a **private corpus
snapshot** so an untrusted agent can never write the real library (W0/W2). A
persisted novel lemma would either be written to the throwaway snapshot
(pointless) or to the live corpus (the exact mutation the snapshot exists to
prevent). So the harness **verifies** proofs; it does not **grow the library**.

A verified novel lemma is still reported in the run record; the **owner** may add
it through the trusted `/verify-library` path outside the untrusted harness.
`add_novel` now fails closed unless the curator supplies `reusable=True`, a
concrete `reuse_reason`, and searchable documentation. It records the decision
and provenance, while paper-specific glue and rejected candidates remain only in
the immutable run artifacts. Thus the system saves every verification artifact
for reproducibility but promotes only plausibly reusable atomic lemmas to the
shared corpus.

---

## Proposed (NOT built): advisory repair hint

> **Status: design sketch, unimplemented.** This section specifies *how* a
> "here's the likely fix" feature could be added **without touching the trust
> model** — so the proposal can be judged before any code. It deliberately
> conflicts with nothing in Layers 1–3: the verdict contract above is unchanged.

The skill's load-bearing rule is **"this tool VERIFIES — it does not REPAIR"**
(`.claude/commands/verify-full-process.md`): never add steps to make a proof
compile. A repair feature must not weaken that. The only safe form is a hint
that is **strictly advisory and walled off from the verdict** — it describes a
plausible fix, but the harness never certifies the fixed proof and the hint
never changes what `enforce()` returns.

### Shape — a separate field on the run record / `run_verification` dict
```python
"repair_hint": {                  # advisory ONLY — never an input to the verdict
  "applicable":  bool,            # true only for a FAILING verdict with a LOCAL flaw
  "block":       str,             # the failing block (already known: the failure point)
  "diagnosis":   str,             # why this step fails (already produced today)
  "suggestion":  str | None,      # plausible repair, or None if not "easy to spot"
  "confidence":  "high" | "low",  # only "high" ever fills `suggestion`; low → None
  "verified":    False,           # ALWAYS False — the suggested fix is NOT certified
}
```

### Invariants (what keeps it from leaking into trust)
1. **Verdict-independent.** `repair_hint` is computed *after* `enforce()` and is
   never read by `verdict_class` / `enforce` / `gate_failures`. Removing the
   field cannot change any verdict. (Mechanically: it is not in the `run` dict
   `gate_failures` inspects.)
2. **Only on a failure.** Emitted only when the verdict is `UNVERIFIED/WRONG`
   (or `…/INCOMPLETE` with a localized cause). Never on a VERIFIED — there is
   nothing to repair, and we never "improve" a passing proof.
3. **`verified` is always `False`.** The harness does **not** re-run the patched
   proof to a VERIFIED. Certifying the suggested fix would mean certifying a
   proof the author did not submit — exactly the honesty failure
   back-translation guards against. To verify a repaired proof, the user
   re-submits it as a fresh run; then it goes through the full gated pipeline
   like any other input.
4. **"Easy to spot" gate.** `suggestion` is non-null only when the flaw is local
   *and* the fix is high-confidence (e.g. a missing hypothesis the counterexample
   already exposes, a one-step lemma substitution). Otherwise `suggestion=None`
   and the output is just the diagnosis — matching the user intent: *advise only
   when easy, otherwise no need.*

### Why this is cheap to build
The raw material already exists: the harness produces the precise failure block
(Layer 1 events) and, for `WRONG`, a counterexample. `repair_hint` is a thin,
clearly-labeled rendering of that — not new verification machinery. The hard
part is **discipline, not code**: the field must stay out of every verdict path.
A test asserting `enforce(run) == enforce(run without repair_hint)` pins it.

---

## Provenance / trust note

`gate_failures()` checks the **presence** of gate records with an
`executed_by="harness"` stamp. Sealed triage and back-translation are
trusted-executed (the runner runs them); the **falsification** gate is still
agent-attested today (surfaced via the provenance line, not yet harness-run) —
a documented remaining gap (`harness/README.md`, `HARNESS_IMPLEMENTATION.md`).
The `verdict_line` does not hide this: it labels attested falsifications so a
BYO user can weigh them.
