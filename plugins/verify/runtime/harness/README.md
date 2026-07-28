# RLVerify BYO-Agent Harness

Run RLVerify proof verification driven by **your own agent account**. The main
flow is paper in, report out: give the CLI a folder, a PDF/LaTeX/Markdown file,
an arXiv link, or pasted text; it writes a reviewable fixture, runs the trusted
parent-side gates, lets your agent formalize the proof through MCP, and saves a
terminal verdict plus optional Markdown report.

> **Golden workflows:** `../.claude/commands/verify-full-process.md` and
> `../.claude/commands/verifyRL-paper.md`. The harness loads and hashes those
> files at runtime. `PIPELINE.md` documents their harness/MCP binding and is not
> an independent mathematical procedure. `../HARNESS_DESIGN.md` = vision;
> `../HARNESS_IMPLEMENTATION.md` = plan/history. Status: live-verified on both
> axes (2026-06-27); macOS-only sandbox.

## Setup
```bash
harness/setup.sh                # doctor + provision (Lean, mcp, build, sandbox, agent CLI)
python3 -m harness doctor       # same thing (--skip-build / --check-auth)
SKIP_BUILD=1 harness/setup.sh   # skip the heavy Mathlib cache/build if already done
CHECK_AUTH=1  harness/setup.sh  # also live-test that your agent CLI is logged in (spends a few tokens)
```
Requirements: a Lean 4 toolchain (elan), Python ≥3.10, the built
`RLGeneralization` project, macOS `sandbox-exec` (for untrusted BYO), and one
supported agent CLI on PATH and logged in. Claude (`claude`) is the historically
validated default. Codex (`codex`) is implemented for current expansion/testing
but remains live-unvalidated until a full local run confirms it; select it with
`--backend codex` or `HARNESS_BACKEND=codex`. Setup checks the selected CLI for
free; `CHECK_AUTH=1` makes a tiny live call to confirm login. At run time, an
auth/launch failure is raised loudly (not a silent `HAS GAPS`) — auth can lapse
after setup.

Platform truth: macOS is the validated sandbox path. Linux has an unvalidated
bubblewrap path behind `RLVERIFY_LINUX_SANDBOX=1`; otherwise use `--no-sandbox`
only for trusted-local runs. Native Windows shells are unsupported; use WSL2,
then the Linux caveats apply.

## Codex workflow

Codex users should treat skills as the instruction layer and this CLI as the
execution layer. The repo ships Codex skill duplicates in
[`../codex-skills/`](../codex-skills/), including:

- `$rlverify-researcher` — practical wrapper over this harness CLI.
- `$verify-full-process` — duplicate of the original Claude full-proof command.
- `$verify-rl-paper` — paper/multi-lemma workflow.
- `$verify-triage`, `$verify-hypothesis-audit`, `$verify-falsify` — single-phase
  drafting checks.

Install or refresh them in the user-scoped Codex skill directory. Restart Codex
after installing or refreshing skills:

```bash
mkdir -p ~/.codex/skills
rsync -a codex-skills/ ~/.codex/skills/
```

Use them from Codex as `$skill-name`, not as real shell commands:

```text
Use $rlverify-researcher to verify this paper:
https://arxiv.org/abs/1703.05449
Theorem: Theorem 1
```

```text
Use $rlverify-researcher to verify this local PDF:
/Users/me/papers/ucbvi.pdf
Theorem: Main theorem
```

```text
Use $rlverify-researcher to verify this theorem and proof:
Theorem: ...
Proof: ...
```

Codex may understand `/verify-full-process` textually because the duplicate
skill preserves the slash-command name, but `$verify-full-process` is the
reliable invocation form. Do not ask researchers to run `python3 -m harness`
commands in a terminal. The skill runs those commands internally after the user
pastes a link, theorem/proof, or PDF path into the chatbox.

Important backend distinction: using Codex as the outer assistant is supported
by the skill docs; using the harness's internal `--backend codex` subprocess path
is how to verify with Codex models. That path is implemented and test-covered at
the CLI/adapter level, but it still needs your own full live validation run
before treating it as production-equivalent to the historically validated Claude
path.

Use `--model` to choose the Codex model under test. If omitted, the Codex CLI
uses its own configured default. Use `--reasoning-effort` to choose the Codex
effort for both the driving agent and sealed grader; this overrides
`model_reasoning_effort` from your Codex config for the run.

For a Codex-testing session, you can also set `HARNESS_BACKEND=codex` once and
omit `--backend codex` from individual harness commands.

The command-line flags in this document are implementation details for agents,
maintainers, and automated tests. The supported researcher interface is the
Codex or Claude Code chatbox.

## Run a verification

Your input is **informal math (prose/LaTeX)** — you do NOT write Lean; your agent
formalizes it. Put a theorem + proof in a folder and run the CLI:

```bash
# folder convention: statement.md + proof.txt  (+ optional claim.txt)
python3 -m harness verify path/to/mytheorem/

# …or pass files / inline text directly:
python3 -m harness verify -s statement.md -p proof.txt -c "the plain-English claim"
python3 -m harness verify -s "Theorem: a+b = b+a for reals." -p "By commutativity. ∎"

# paper/link/paste front-end: writes a fixture, then runs the same verifier
python3 -m harness verify https://arxiv.org/abs/2406.01234 --theorem "3.1"
python3 -m harness verify paper.pdf --theorem "Main theorem"
python3 -m harness verify paper.tex --all-theorems
python3 -m harness verify - --theorem "Theorem 1"        # paste or pipe text
python3 -m harness verify paper.tex --theorem "3.1" --dry-run

python3 -m harness verify path/to/mytheorem/ --budget 2400  # longer hard proofs
python3 -m harness verify --resume mytheorem                 # continue saved state
python3 -m harness verify --resume mytheorem --continue-structural
python3 -m harness verify path/to/mytheorem/ --report        # write rlverify-out/<name>-report.md
```
`-c/--claim` feeds the back-translation gate (defaults to the statement). The
certificate, record, exact input, and signed integrity manifest land in
`./rlverify-out/`; a VERIFIED one is re-checkable independently with
`lake env lean <cert>`, and the complete bundle with
`python3 -m harness.integrity <manifest> --input ... --record ... --certificate
...`. Off macOS you must add
`--no-sandbox` (drops the untrusted guarantee — see Known limitations).
PDF input uses the text layer and requires `pip install pypdf` (or
`pip install .[pdf]`). While a run is incomplete, resumable state lives in
`rlverify-out/.state/<name>/`. After a terminal verdict the CLI removes that
state and any generated theorem fixture, retaining the final report/evidence
bundle. Pass `--keep-intermediates` only for debugging. Fetched papers are
cached under `rlverify-out/.papers/<id>/`.

Before launching the expensive full-proof agent, `verify` runs sealed triage
and a bounded targeted-confirmation pass for every serious finding. Another
model opinion is still audit-only. Negative certificates are scoped as
main-theorem refutations, proof-step failures, or well-definedness gaps. Only a
well-defined witness satisfying every submitted hypothesis and negating the
complete theorem supports `UNVERIFIED/WRONG`. One full-run confirmation covers
the entire Lean attempt: every confirmed negative state automatically selects
structural salvage, while `UNRESOLVED` automatically continues the
full Lean path. A clean, faithfully matched positive proof of the disputed
inference yields `NOT_CONFIRMED` and continues automatically; merely finding
no counterexample does not. Structural continuation permits `sorry` only in
named failed blocks, discharges independent correct blocks, and compiles the
remaining conditional proof. Its strongest result is
`COMPILES MODULO PLACEHOLDERS`, never `VERIFIED`. The trusted parent replaces
each placeholder with a distinct probe axiom and checks that every one appears
in the final theorem's kernel closure, rejects any additional custom/imported
axiom, and back-translates the final structural statement against the original
claim. Merely mentioning a placeholder in an unused local fact is rejected.

Every executed phase appends `phase_telemetry.json` with status, wall time,
sealed model-call count, provider cost when available, and stable discovery
keys. A repeated finding remains visible but is marked non-incremental.

With `--all-theorems`, theorems are verified in dependency-first order over the
model-asserted `uses[]` graph. Exact compiled declarations from verified
dependencies become runner-owned MCP `prior` blocks and are rechecked in the
dependent certificate; unrelated earlier results remain context-only. The
paper's final phase builds and kernel-audits one aggregate Lean file.
`--report` writes one self-contained aggregate with per-component sections;
intermediate theorem reports and completed state directories are not retained.

For paper/link inputs, use `--dry-run` as the explicit extraction and cost
checkpoint before formal proof search:

```bash
python3 -m harness verify https://arxiv.org/abs/2406.01234 \
  --theorem "3.1" --dry-run
```

The dry run materializes the fixture under `rlverify-out/` and prints a
heuristic formal-proof estimate based on the extracted statement/proof size,
backend/model, and configured timeouts. After reviewing it, launch the same
fixture or rerun the paper command without `--dry-run`. Exact spend is only known
after the backend returns its metering envelope, so the estimate is advisory.

Worked local example source:
```bash
python3 -m harness verify benchmarks/successive_elimination_hp_regret/statement.md \
  --theorem "Theorem" --report
```
That benchmark is deliberately useful for a first serious run because it is an
RL-style proof with planted flaws; do not copy its sealed `expected.json` into a
new example.

## Drafting Loop

Before spending on a full formalization, run the cheap parent-side components:
```bash
python3 -m harness triage -s statement.md -p proof.txt
python3 -m harness audit  -s statement.md -p proof.txt
python3 -m harness falsify "for all x > 0, sqrt(x) <= x" --trust-samplers
```
`triage` and `audit` are prioritization-only and never verdicts. `falsify`
executes a seeded numeric sampler: `REFUTED` exits 1 with a witness and rerun
command, while `PASSED`/`VACUOUS` exit 0 and mean only that no counterexample
was found at that depth. Generated samplers are arbitrary Python, so non-TTY
runs require `--trust-samplers` or `RLVERIFY_TRUST_SAMPLERS=1`.

## Domain Fit

Today RLVerify is strongest on concentration, bandit, and discrete-optimization
arguments shaped like the bundled corpus; adequate on Mathlib-covered analysis
and algebra; and weakest on heavy measure theory or continuous counterexamples.
For those harder cases the system may still detect the flaw, but evidence can
fall back to audit-only rather than a kernel-backed refutation.

## What makes a verdict trustworthy (the design in four pieces)
- **W0 — sandbox.** Untrusted agent-authored Lean is compiled under
  `sandbox-exec` (no network, no host writes outside a scratch dir, reads of the
  user's home/secrets denied, only the `lean` binary may exec). `rlverify/
  sandbox.py`; acceptance test `harness/sandbox/run_w0_acceptance.py` (14 checks).
- **W1 — enforcement.** The verdict comes from the Lean kernel (`rlverify/
  verdict.py`); a VERIFIED with missing flaw-hunting gates is downgraded to
  `UNVERIFIED/UNGATED`.
- **W2 — MCP server.** Coarse, pipeline-ordered tools over the driver
  (`rlverify/mcp_server.py`); every compile routed through the sandbox
  (fail-closed); the server owns the corpus snapshot so the agent can't mutate
  the real library.
- **W3/W4 — trusted gates + runner.** Sealed triage, hypothesis audit, and
  back-translation run in trusted harness code (`harness/triage.py`,
  `hypothesis_audit.py`, `backtranslate.py`), stamped with unforgeable
  provenance the gate requires; the runner (`harness/runner.py`) brackets the
  untrusted agent with them and resumes the agent's session journal to enforce
  on its real work.

### Two roles of your account, and what a run costs
A run uses your selected backend account in **two deliberately separated roles**,
so the agent that writes a proof never also grades it:
1. the **driving agent** (`launch_agent`) — formalizes the prose and drives the
   MCP tools to build the proof or find the flaw;
2. a **sealed grader** (`get_backend`) — runs triage, hypothesis audit, and
   back-translation in isolation. Claude disables MCP/tools; Codex ignores user
   config/rules, clears MCP, uses a clean cwd, and runs read-only.

So one run spends tokens on the driving agent **plus ~3-4 sealed gate calls**. The
CLI wires both for you; you only pick `--backend`/`--model`.

For Codex testing, omit `--model` to use the Codex CLI default, or pass
`--model <codex-model>` explicitly. Pass `--reasoning-effort medium` when a
medium-effort comparison should not inherit a stronger global Codex config.

> **Claude plan tiers:** `--model opus` (the Claude-oriented default, and what
> the framework was tuned for historically) needs a **Max-tier** Claude
> subscription; `--model sonnet` runs on Pro but expect more `INCOMPLETE`s on
> hard proofs. A `403 request not allowed` at launch is a plan/quota limit, not
> a login bug.

### Reading the verdict
| Verdict line | Meaning |
|---|---|
| `VERIFIED (kernel closure standard)` | a genuine kernel proof; closure ⊆ {propext, Classical.choice, Quot.sound} |
| `UNVERIFIED/WRONG` | a scoped, faithfully matched counterexample refutes the complete theorem |
| `UNVERIFIED/PROOF_INVALID` | a submitted inference is refuted; theorem truth remains unknown |
| `UNVERIFIED/HYPOTHESIS_VIOLATION` | an omitted hypothesis or undefined term requires restatement |
| `UNVERIFIED/MISMATCH` | the formal statement does not match the submission |
| `UNVERIFIED/UNGATED` | compiled, but a required flaw-hunting gate didn't run/pass |
| `… HAS GAPS` | the agent didn't finish (e.g. stalled on a bad import) — transient, retryable |

A `VACUOUS`/`⚠ SHALLOW` note on the line is a *falsification annotation* (the
counterexample search never satisfied the hypotheses, or was thin), not a
standalone verdict.

### Advanced: the Python API
- **Python API** (what the CLI calls; use for batching/embedding):
  ```python
  from harness.runner import run_verification, launch_agent
  from harness.backends import get_backend
  out = run_verification("my_fixture", statement, proof,
                         call_model=get_backend("claude", model="opus"),
                         agent_drive=launch_agent("claude", model="opus"),
                         nl_claim="the original natural-language claim")
  print(out["verdict_line"])
  ```
  For offline testing, pass a fake `agent_drive` and `call_model` (see
  `tests/test_runner.py`). Runnable demos: `harness/examples/`.
- **No IDE-facing MCP registration.** The CLI/runner is the only supported
  entry point (CLI-only v1 — `../HARNESS_DESIGN.md` §10.2). The MCP server
  (`rlverify/mcp_server.py`) is internal plumbing: the runner spawns it per-run
  as the driving agent's tool surface. The former advisory IDE loop (repo-root
  `.mcp.json`) was retired — a server launched by *your* agent can't self-attest
  the sealed flaw-hunt gates (§8.0), so it could never produce a gated verdict.

## Output structure
The verdict line, the structured return dicts (`run_verification`, `enforce`,
`falsify_summary`), the verdict classes, and the run-record / certificate
artifacts are specified in [`OUTPUT.md`](OUTPUT.md) — the harness's documented
output contract, mirroring the skill's (`PIPELINE.md §5`) and adding the
enforcement + provenance fields an untrusted driver requires.

## Status: end-to-end VERIFIED achieved (2026-06-27)
A **real Opus agent**, driving its own MCP session through the harness, produced
a genuine **kernel-closed VERIFIED** on `add_comm_real (a b : ℝ) : a + b = b + a`:
`assemble` compiled (`compiled=True`), the kernel closure was clean (`propext,
Classical.choice, Quot.sound`), the journal handoff worked, both trusted gates
ran (sealed triage + back-translation MATCH; the hypothesis audit was also
executed as a prioritization-only review), the falsification gate passed, and
enforcement held the verdict at VERIFIED (no downgrade). This closes the
agent↔MCP↔runner↔gates↔kernel loop end-to-end on a live model.

## Real RL fixture — flaw DETECTED live (2026-06-27)
Pointed the harness at `expectation_sum_exchange_erratum` (a real regret-
decomposition workhorse with a planted flaw: E[Σ Xᵢ]=Σ E[Xᵢ] claimed from "the
sum exists" alone, invalid without domination). A live Opus agent, through the
harness, reached **UNVERIFIED/WRONG** — matching the sealed ground truth — and
constructed an exact telescoping counterexample (`Xₙ = n·1_(0,1/n) −
(n−1)·1_(0,1/(n−1))` ⇒ E[X]=0 ≠ 1=Σ E[Xᵢ]). The trusted sealed triage
independently flagged the interchange step as the #1 suspect. Scorer: verdict
✅, flaw-detection ✅, false-positives ✅; **only `min_kernel_backed` failed** —
the agent's counterexample was audit-only, not compiled in Lean, because the MCP
surface has no `refute` tool yet (the failure-side analog of `assemble`). So:
detection works end-to-end; kernel-BACKED refutation is the next additive tool.

This + the earlier VERIFIED on `add_comm_real` exercise **both axes** of the tool
through the live harness: a sound proof → kernel VERIFIED, a flawed proof →
correct UNVERIFIED/WRONG with the precise flaw.

## Forward-proving path — VERIFIED live by an agent (2026-06-27)
A live Opus agent drove a **novel** proof (`ucb_radius_antitone`, UCB
confidence-radius monotonicity) to a **kernel-closed VERIFIED** — the agent
authored real multi-step Lean (not a library one-liner):
```lean
apply Real.sqrt_le_sqrt
have hs0 : (0:ℝ) < s := lt_of_lt_of_le one_pos hs
have hnum : (0:ℝ) ≤ 2 * Real.log t := by
  have := Real.log_nonneg ht
  linarith
gcongr
```
`compiled=True`, closure `{propext, Classical.choice, Quot.sound}`, back-translation
MATCH → VERDICT: VERIFIED. The certificate `.lean` ends with `#print axioms` and
is independently reproducible.

**Getting here took fixing a real harness bug** the test surfaced: the driver
wraps a proof as `:= by\n  {proof}`, indenting only the FIRST line, so multi-line
proofs broke ("unexpected token 'have'"). Two earlier live runs produced *correct*
proofs that the harness mangled → HAS GAPS, with the agent over-claiming success
(the kernel record correctly overruled it). Fix: `HarnessSession._norm_proof`
normalizes indentation (textwrap dedent + uniform re-indent, preserving relative
nesting) — robust to flat AND pre-indented proofs (both seen live), additive,
frozen driver untouched. **Lesson: the agent CAN author correct novel-proof Lean;
the blocker was harness proof-wrapping, not agent capability.**

## Known limitations (honest)
- **`refute` MCP tool — BUILT (2026-06-27).** The agent can compile a
  counterexample (`refute(block, code, description)`); a clean closure makes the
  local negative proposition kernel-backed. The trusted parent must still scope
  it: only a complete, well-defined main-theorem counterexample produces WRONG;
  proof-step and well-definedness findings receive their own statuses. The
  scorer credits scoped kernel-backed refutations toward `min_kernel_backed`.
  Verified with a real compilable counterexample (`sqrt(a+b)≤sqrt a` falsity →
  kernel-backed, fixture scores PASS in simulation). **Caveat:** `refute` removes
  the tooling gap, not the formalization difficulty — for a flaw whose
  counterexample is hard to state in Lean (e.g. a measure-theoretic construction),
  a live agent may still fall back to audit-only WRONG (correct verdict, not
  certified). Live confirmation on a hard counterexample pending.
- **Sandbox: macOS validated, Linux UNVALIDATED.** macOS `sandbox-exec` is the
  proven path. A bubblewrap port now exists behind the same fail-closed seam but
  has no Linux acceptance run yet, so it is gated behind `RLVERIFY_LINUX_SANDBOX=1`
  (opt-in, at your own risk) and never silently claims the guarantee. Local
  trusted users on any OS can set `RLVERIFY_SANDBOX=0` to skip confinement (same
  trust posture as `/verify-full-process`): use only when you trust the agent AND
  the proof source.
- **Agent-subprocess Lean resolution — FIXED (2026-06-27).** The runner
  pre-resolves `LEAN_PATH` + augmented PATH into the MCP-server config; the
  sandbox resolves the real toolchain binary from the elan dir (never the shim)
  and realpaths its scratch. Live-confirmed (compile succeeds in-subprocess).
- **Single-block reconciliation cosmetic.** When a one-block proof is closed
  inline by `assemble`, the block table still shows the block as `GAP` even
  though the MAIN verdict is correctly VERIFIED (the kernel closure is the
  source of truth). Harmless; the verdict is right.
- **Proven on a trivial identity, not yet a hard RL fixture.** The live VERIFIED
  was a single-step algebra identity. A multi-lemma RL proof driven all the way
  to VERIFIED by a live agent is the next milestone.
- **Falsification trust split.** The full `verify` pipeline can still contain
  agent-attested falsification records unless the agent uses the trusted-local
  `falsify_run` tool. The standalone `harness falsify` command is
  harness-executed, seeded, and reproducible, but generated samplers are still
  trusted-local Python and require explicit consent. **Codex backend** is
  implemented (driver + sealed grader, against codex-cli 0.120.0) but pending
  live validation.
- **`launch_agent` — plumbing validated (claude), full completion not yet.** A
  real `claude -p` run drove the MCP tools end-to-end (begin→resolve→assemble),
  journaled, the runner resumed the agent's record, both trusted gates stamped,
  and finalize emitted a verdict (2026-06-27, trivial `n+0=n` fixture, 92s).
  Still unproven: an agent driving a real RL fixture all the way to a
  kernel-backed VERIFIED (the trivial case short-circuited to a library
  citation before assembly). The codex backend is implemented but not yet
  live-validated end-to-end.
- **Falsification gate is still agent-attested** — only triage and
  back-translation are trusted-executed; making falsification trusted is the
  next hardening step.
- **Single global MCP session** per server process — **safe under stdio**, which
  is how the server runs: the runner spawns a fresh server child process per
  run, so concurrent runs get independent sessions and never share records.
  Only a hazard if a future *shared* server (one long-lived HTTP/SSE process
  multiple clients dial into) lets callers share one process; then
  per-connection isolation is required.
- **Model allowlist (W6) deferred** — Opus-only until the framework stabilizes.
