# RLVerify Harness — Pipeline (as built)

The normative mathematical procedures are
`.claude/commands/verify-full-process.md` and
`.claude/commands/verifyRL-paper.md`. Their exact text and SHA-256 provenance
are loaded at runtime. This document describes the executable harness/MCP
binding for those golden instructions; it does not supersede them.

How a verification actually flows through the **bring-your-own-agent (BYO)
harness** — the path where a *third-party* agent (its own Claude/Codex account)
drives RLVerify over MCP, as opposed to the trusted-local `/verify-full-process` skill
(documented in the repo-root `PIPELINE.md`).

This doc traces the **real code**. When it names a function, that function
exists and does what's described. Keep it in sync; see the Changelog.

> Status (2026-06-27): end-to-end **live-verified on both axes** — a real Opus
> agent reached a kernel-closed VERIFIED on a novel proof (`ucb_radius_antitone`)
> and correct failure verdicts on flawed fixtures (CIRCULAR / HYPOTHESIS_VIOLATION
> / WRONG, incl. a kernel-backed refutation). See `harness/README.md`.

---

## 0. Three run types

The harness does two jobs; the agent chooses which the proof deserves:

- **Verification run** — the proof is (hopefully) correct. The agent *builds* it
  to a kernel-closed VERIFIED: search → resolve with dependencies → sketch →
  discharge in topological order → assemble. Verdict source: the Lean kernel.
- **Detection run** — the proof is flawed. The agent *finds the flaw* and reports
  the right failure (`report_failure`, optionally `refute` for a kernel-backed
  counterexample). It does not build a proof — there is nothing valid to build.
- **Structural continuation** — preflight found a likely fatal block and the
  user explicitly chose to continue. The failed block becomes a visible named
  placeholder, every independent correct block is discharged, and the
  downstream conditional proof is compiled. The only success label is
  `COMPILES MODULO PLACEHOLDERS`; this path can never yield `VERIFIED`.

Both run through the same orchestration below; they differ only in which MCP
tools the agent ends on (`assemble` vs `report_failure`/`refute`).

---

## 1. The three processes

```
   RUNNER (harness/runner.py)                 — trusted, you control it
     │  owns a corpus SNAPSHOT (→ shared runs_dir for the journal handoff)
     │  runs sealed triage, hypothesis audit, and back-translation
     ▼
   AGENT  (claude/codex, headless)            — UNtrusted, the user's account
     │  drives the MCP tools; writes Lean; cannot author a gate record
     ▼
   MCP SERVER (rlverify/mcp_server.py)        — one HarnessSession per process
     │  every Lean compile routed through the W0 SANDBOX (fail-closed)
     ▼
   DRIVER + Lean kernel (rlverify/driver.py, lean.py)  — the verdict source
```

The agent runs in its own OS process (`launch_agent` spawns `claude -p` → which
spawns `python -m rlverify.mcp_server`). Runner and agent share **one record**
not via shared memory but via the **session journal** under the shared corpus's
`runs_dir` — the runner `resume()`s what the agent journaled.

---

## 2. End-to-end flow (`runner.run_verification`)

The exact step order in `harness/runner.py`:

```
1. SEALED TRIAGE (trusted, FIRST)        harness/triage.py : sealed_triage
     an isolated model call sees ONLY the theorem+proof text, ranks suspect
     steps. Written to a sidecar (run_dir/triage_suspects.json) that launch_agent
     injects into the agent's prompt — so the agent scrutinizes flagged steps
     first. NOT yet a gate record (that's step 5).
2. TARGETED CONFIRMATION (bounded)        profile/verify-confirmation.md
     serious triage findings receive a narrow certificate-seeking pass before
     the main proof. Model agreement has no weight. Negative results are split
     into theorem refutation, proof-step failure, and well-definedness gap;
     only the first supports theorem-level REFUTED. Each certificate is matched
     to an exact submitted excerpt;
     NOT_CONFIRMED requires a trusted positive Lean proof matched to that exact
     disputed inference; otherwise the result is UNRESOLVED.
3. SEALED HYPOTHESIS AUDIT (trusted)      harness/hypothesis_audit.py
     audits every cited invocation and conditional conclusion. New serious
     findings receive the same targeted-confirmation pass.
4. PREFLIGHT ROUTING GATE                 runner._preflight_summary
     One prior full-run confirmation covers this gate. Any confirmed negative
     state automatically selects structural salvage; UNRESOLVED automatically
     continues full verification. Clear and NOT_CONFIRMED proofs continue to
     the full proof agent. No additional user confirmation is requested.
5. AGENT DRIVES                           agent_drive(fixture, statement, proof, corpus)
     the untrusted agent runs its own HarnessSession via the MCP tools (§3),
     journaling its work to the shared runs_dir.
6. JOURNAL HANDOFF                       s.d.resume(fixture)  (→ amend → begin)
     the runner loads the AGENT'S record. resume = in-progress journal; amend =
     the agent already called finalize; begin = agent never ran (empty → HAS GAPS).
7. RECORD SEALED REVIEWS (trusted)
     s.record_triage(...) + s.record_hypothesis_audit(...)
     the step-1 result is now stamped onto the agent's record. Provenance the
     agent cannot forge — gate_failures REQUIRES this stamp.
8. TRUSTED SOURCE RECHECK
     recompile the main certificate, discharged blocks, and—when structural
     continuation was selected—the exact conditional source. Structural source
     is accepted only when every `sorry` is in a named placeholder, no custom
     axiom is declared, every placeholder is used, and every independent block
     has a trusted discharge recheck.
9. SEALED BACK-TRANSLATION (trusted)     harness/backtranslate.py : back_translate
     if the agent assembled a main theorem, an isolated call renders the Lean
     back to English (opaque identifiers) and a judge diffs it against the NL
     claim → MATCH/NOTE/MISMATCH, recorded stamped executed_by="harness".
10. ENFORCE + VERDICT                    s.finalize() → verdict.enforce(...)
     kernel result, DOWNGRADED to UNVERIFIED/UNGATED if a required gate is
     missing. Returns the one verdict line the user reads.
11. PHASE TELEMETRY                      phase_telemetry.json
     append execution status, model-call count, wall time, provider cost when
     available, and stable discovery keys. Repeated findings are retained but
     marked non-incremental, so later benchmark analysis can measure what each
     phase uniquely discovered per unit cost.
```

**Why triage is split (compute at 1, record at 4):** the agent needs the suspect
hints *before* it works (a detection-axis fix — it used to drive blind), but the
gate *record* must land on the agent's real post-resume record. Same single
trusted result; the agent never authors it.

---

## 3. The agent-facing MCP tools (`HarnessSession`)

Coarse, pipeline-ordered (not a 1:1 mirror of the ~25 driver methods). The
agent has NO tool to write triage or back-translation — those are trusted-only.

| Tool | Purpose | Axis |
|---|---|---|
| `begin(fixture)` | start the session (first call) | both |
| `status()` | inspect dependencies, sketch/discharge provenance, and remaining workflow gaps | both |
| `search(query)` | substring + BM25 over the 1,800-lemma corpus | both |
| `resolve_block(name, nl, kind, …, depends_on)` | classify a step and declare its dependency list (`[]` for a root) | both |
| `falsify_block(block, verdict, …)` | record a numeric counterexample-search outcome | both |
| `compile(code)` | sandboxed iteration compile (not verdict-bearing) | verify |
| `sketch(skeleton, blocks)` | compile the sorried skeleton — machine-checks the decomposition | verify |
| `discharge(block, stmt, proof, imports)` | prove one block (writes Lean) | verify |
| `assemble(stmt, proof, imports)` | assemble + **kernel audit** → the VERIFIED path | verify |
| `structural_assemble(code, placeholders)` | compile the full conditional proof with `sorry` only in named failed blocks | structural |
| `report_failure(kind, reason, block)` | record a candidate flaw label (WRONG / PROOF_INVALID / HYPOTHESIS_VIOLATION / CIRCULAR / INCOMPLETE); trusted scoping determines the final verdict | detect |
| `refute(block, code, description)` | compile a negative certificate; kernel closure proves only that Lean proposition, while trusted scope matching decides whether it bears on the theorem or one proof step | detect |
| `certify_step(block, code, description)` | compile a positive certificate for one disputed inference; never verifies the full theorem | confirm |
| `finalize()` | (the agent is told NOT to call this — the runner finalizes) | — |

`HarnessSession._norm_proof` normalizes proof indentation before handing to the
driver: the driver wraps `:= by\n  {proof}` (indents only line 1), so multi-line
proofs need their continuation lines re-indented or Lean rejects them. (A real
bug found live — see Changelog.)

---

## 4. Why a verdict is trustworthy (the four controls)

1. **Kernel is the floor.** VERIFIED comes from `#print axioms` (closure ⊆
   {propext, Classical.choice, Quot.sound}), not the agent's say-so. The agent
   over-claiming "it compiled" cannot produce VERIFIED — the record decides
   (`verdict.verdict_class`). Observed live: the agent claimed success on a proof
   the harness hadn't compiled; the verdict was correctly HAS GAPS.
2. **Sandbox.** Every agent-authored Lean compiles under `sandbox-exec` (no
   network, no host writes outside scratch, secrets unreadable, only the `lean`
   toolchain may exec) — `rlverify/sandbox.py`, fail-closed. macOS today;
   `RLVERIFY_SANDBOX=0` opts out for trusted-local. When off, the posture is
   **stamped on every durable surface** — the verdict line (`⚠ UNSANDBOXED`), the
   `run_verification` dict (`sandbox: "off"`), the result panel, and a leading
   comment on the saved certificate — so an unconfined run is never byte-
   indistinguishable from a confined one. The posture is also propagated to the
   agent's MCP server (`launch_agent`'s `server_env`) so the stamp reflects the
   process that actually compiled. It is a **label, not a gate**: it never enters
   `gate_failures`/`verdict_class`, so it records the run without downgrading it.
3. **Trusted reviews/gates.** Triage + hypothesis audit + back-translation run
   in runner code. Triage and back-translation carry the
   `executed_by="harness"` provenance stamp that `verdict.gate_failures`
   requires; hypothesis audit is persisted but remains prioritization-only. An
   agent-written gate record is rejected. Why the agent can't forge that stamp:
   §4.1.
4. **Enforcement.** `verdict.enforce` downgrades a kernel-clean VERIFIED to
   UNVERIFIED/UNGATED if any required gate or workflow-v2 phase is missing.
   New runs require explicit dependency declarations, an acyclic known-block
   graph, a successful sketch covering every novel/instantiation block,
   per-block discharge in dependency order, and no deterministic id-shaped
   anti-vacuity failure. One verdict authority (`rlverify/verdict.py`) is shared
   by driver, scorer, and harness.

### 4.1 Why the `executed_by="harness"` stamp can't be faked

Control 3 hangs on one claim: a gate counts only if its record is stamped
`executed_by="harness"`, and the agent can't produce that stamp. Here is the
whole argument in one place — three layers, each of which the agent would have
to defeat.

- **The stamp is a side-effect of trusted code, not a value anyone passes in.**
  `executed_by="harness"` is written by `mcp_server.py:record_triage` /
  `record_backtranslation`, whose first line of business is to *run the real
  gate* and then set the field. The string's presence therefore *is* the
  evidence the gate executed — there is no code path that writes `"harness"`
  without the work having happened.
- **The agent has no path to call that code.** `record_triage` is a plain
  `HarnessSession` method, deliberately **not** registered as an MCP tool (its
  docstring: *"runner-only… an agent has no path to call this"*). The agent's
  entire surface is the coarse tool list in §3; the stamping methods are not on
  it. Re-exposing `record_triage` as a tool is exactly the "attestation hole"
  the W1/W3 work closed (`HARNESS_IMPLEMENTATION.md`).
- **Even a hand-scribbled journal entry is overwritten.** Suppose the agent
  writes `triage={..., executed_by:"harness"}` into its own session journal
  directly. It doesn't survive: the runner runs `sealed_triage` itself
  (`run_verification` step 1), then **after** `resume()`ing the agent's journal
  calls `record_triage` (step 5), which overwrites that slot with its own
  freshly-executed, stamped result. The verdict (step 6) is computed over the
  runner's record, not the agent's. The agent's forgery is clobbered before it
  is ever read.

So "stamped" ⟺ "the trusted runner re-ran the gate." The guarantee comes from
trusted code having *executed and overwritten*, never from the string itself.

**The boundary of this argument: it holds only for reviews the runner
re-derives.** Triage, hypothesis audit, and back-translation are re-run and
overwritten, so their provenance is unforgeable. The hypothesis audit remains
zero-weight by design. Falsification is **not** re-derived — `falsify_block` records
the agent's own numbers stamped `executed_by="agent"` — so there the stamp is
just a label and is trusted accordingly (surfaced, not counted as a trusted
gate; see §5). The trustworthy failure-side analog is `refute`, whose outcome is
*derived* from a real kernel compile, not asserted.

---

## 5. Honest gaps (current)

- **Falsification gate is agent-attested**, not trusted-executed: `falsify_block`
  ingests the agent's numbers (stamped `executed_by="agent"`). Depth is surfaced
  and shallow-flagged on the verdict line (`verdict.falsify_summary`) so a thin
  flaw-hunt is visible, but the numbers aren't harness-run. The kernel-backed
  `refute` path IS trusted.
- **Sandbox: macOS validated; Linux UNVALIDATED.** macOS `sandbox-exec` is the
  proven W0. A bubblewrap (`bwrap`) port now exists behind the same fail-closed
  seam (`rlverify/sandbox.py` `_confine_prefix`/`_require_confiner`), but it has
  no acceptance run on real Linux yet, so it is **gated behind an explicit opt-in
  (`RLVERIFY_LINUX_SANDBOX=1`)** and never silently claims the guarantee. Open: a
  Linux acceptance suite (the macOS one asserts macOS-specific sensitive paths)
  and confirming the read-bind set is complete + the exec-pinning assurance gap
  (bwrap can't pin exec to `lean` the way SBPL does).
- **`launch_agent`/grader** are validated for `claude`; `codex` is now
  **implemented** (driver + sealed grader, against codex-cli 0.120.0) but
  **pending live validation** — confirm end-to-end before trusting a codex run.
- **Single global MCP session** per server process — safe under stdio (each
  client spawns its own server child, so concurrent IDEs get isolated sessions);
  only a hazard for a future shared HTTP/SSE server where clients share one
  process.
- **Dependency declarations are agent-authored.** The harness validates names,
  cycles, sketch coverage, and actual discharge order, but it cannot prove that
  the agent listed every semantic dependency. The sealed hypothesis audit is the
  independent detector for omitted hypotheses and conditional cycles.

---

## 6. Evaluation

`harness/evaluate.py` runs the harness on benchmark fixtures (sealed ground
truth) and scores with `benchmarks/score.py`. Latest (3 fixtures, 2026-06-27):
verdict-match 3/3; full-PASS 1/3 — the two non-PASSes were a scorer
keyword-brittleness false-negative and `min_kernel_backed` thresholds calibrated
for the thorough skill run, not detection misses. See `harness/README.md`.

---

## Changelog
- **2026-07-23** — Added workflow contract v2: persisted sealed hypothesis audit,
  explicit block dependencies, cycle/unknown-reference checks, mandatory
  decomposition sketch, mandatory dependency-ordered discharge, and
  deterministic id-shaped anti-vacuity enforcement for VERIFIED-class runs.
- **2026-06-27** — Created. Traces `run_verification` step order, the coarse MCP
  tool surface, the four trust controls, and the honest gaps. Records the live
  novel-proof VERIFIED and the `_norm_proof` indentation bug (the driver indents
  only the first proof line; multi-line agent proofs broke until the harness
  re-indented continuation lines — found only by a real end-to-end run).
