# Verification UX Experiment Results

## Material Passport

- Origin Skill: `academic-research-suite` → `experiment-agent`
- Workflow: run + validate
- Date: 2026-07-26
- Environment: macOS, Lean 4.28.0, Mathlib/RLGeneralization workspace,
  Codex backend
- Verification Status: `ANALYZED`
- Reproducibility: repository suite `646 passed`; final artifacts replayed
  through the production confined closure checker

## Goal

Evaluate the verifier as a user-facing product on two representative inputs:

1. a short valid inequality that should reach a positive kernel certificate;
2. a plausible-looking but false constant-step Q-learning convergence proof
   that should stop early with decisive negative evidence.

The target is not merely mathematical accuracy. The workflow should expose
phase progress, fail before model spend if its backend is unusable, stop early
on decisive flaws, survive reconnects, and never call a parseable but erroneous
Lean run `VERIFIED`.

## Inputs

| Case | Expected outcome | Fixture |
|---|---|---|
| Scalar discount inequality | Kernel-clean positive certificate | `scalar_discount_contraction.md` |
| Constant-step Q-learning | Early fatal proof-step certificate | `constant_alpha_q_learning.md` |

## Observed User Journeys

### 1. False Q-learning theorem

The sealed triage found four high-severity issues. Targeted confirmation then
constructed a concrete rational-valued sampled-operator counterexample to Step
2:

```lean
theorem sampled_target_need_not_fix_expected_fixed_point :
    (let T : ℚ → ℚ := fun _ => 1
     let T_hat : ℚ → ℚ := fun _ => 0
     let T_hat_other : ℚ → ℚ := fun _ => 2
     T 1 = 1 ∧
       (T_hat 1 + T_hat_other 1) / 2 = T 1 ∧
       T_hat 1 ≠ 1) := by
  norm_num
```

Final observed outcome: `PAUSED: CONFIRMED FATAL PROOF STEP`, with
`LEAN_KERNEL` evidence. Full hypothesis audit and proof discharge were
deferred. On the final successful confirmation attempt:

| Phase | Wall time |
|---|---:|
| Backend capability | 19.85 s |
| Targeted confirmation + sealed semantic match | 108.13 s |
| Total final attempt | about 128 s |

The artifact
`rlverify-out/refutation-step-2-bd9b1da51862a170.lean` replayed successfully
through the production confined checker with the standard closure
`{propext, Classical.choice, Quot.sound}`.

This is the desired early-exit behavior. The workflow did not spend time
formalizing the entire false stochastic-convergence theorem.

### 2. Valid scalar inequality

The full live path exercised decomposition, source-span capture, falsification,
sorried-skeleton compilation, discharge, assembly, trusted recheck, and sealed
back-translation.

The experiment was especially valuable because it exposed a real fail-open:
Lean could print a valid `#print axioms` line after an earlier
`unknown namespace Finset` error. The ordinary closure checker had been fixed,
but the production sandbox wrapper still accepted that output. The resumed run
then exposed a second problem: the parent accepted legacy closure objects that
did not carry the exact subprocess result.

After both fixes, production replay distinguishes the files correctly:

| Artifact | Exact compile | Confined closure result |
|---|---:|---|
| Historical file with earlier namespace error | nonzero | rejected |
| Corrected scalar certificate | zero | accepted, standard axioms |
| Q-learning refutation | zero | accepted, standard axioms |

The repaired parent gate failed closed during the resumed run:
`VERDICT: HAS GAPS`, because the block certificate did not yet carry the newly
required exact compile result. This is the correct trust behavior. Direct
production replay of the corrected scalar artifact subsequently returned
`ok=True`, `compile=True`, with only the three standard axioms.

The live path remains slower than desired:

| Phase group | Representative wall time |
|---|---:|
| Capability | 28–34 s |
| Triage + hypothesis audit | 53 s |
| Proof agent, including retries | 263–370 s |
| Trusted recheck | 2–4 s |
| Back-translation | 36–51 s |

The main source of latency is model-driven phase sequencing and failed
discharge/terminal-action retries, not the final kernel check.

## Implemented Changes

### Faster, observable workflow

- Durable per-phase telemetry for resolve, falsify, sketch, discharge,
  assemble, trusted recheck, back-translation, finalization, and deferred
  library growth.
- Cross-process locking, monotonic sequences, atomic replacement, and atomic
  `append_phase_once`.
- Durable `start / events / result / cancel` product API with opaque run IDs,
  persisted inputs, reconnect-safe polling, and contained resume paths.
- Semantic discovery IDs and resumable/idempotent block resolution.
- Library growth moved after the terminal verdict.
- Bounded proof-agent retry and cleanup of timed-out MCP/model processes.

### Stronger trust boundary

- Actual Codex/Claude-to-MCP capability smoke before mathematical work.
- Versioned block records with input hash, exact raw Unicode character and byte
  spans, excerpt hash, formal signature, hypotheses, and dependencies.
- Trusted parent revalidates those hashes and spans instead of replacing them
  with substring membership.
- Novel/instantiation blocks must have dependencies and falsification records
  before sketch, a successful sketch before discharge, and discharge before
  assembly. Standalone discharge remains usable without a full DAG.
- Heuristic hypothesis-edge/name correlation is explicitly non-decisive
  `AUDIT` evidence and can no longer promote an audit to kernel evidence.
- Refutation back-translation has counterexample-aware polarity and premise
  checks.
- Cancellation signals the worker, which terminates independently sessioned
  model processes before `CANCELLED` is persisted.

### Lean/kernel improvements

- Both ordinary and confined closure checkers reject every nonzero Lean exit,
  even if a later closure line is parseable.
- Verdict-bearing closure objects must include a successful exact
  `compile_result`; parsed legacy output is insufficient.
- Assembly reuses its closure compile rather than compiling the same file
  twice.
- Multi-declaration `check_axiom_closures` compiles several closure queries in
  one process.
- Warm confined REPL is used only for iteration; it cannot independently
  establish `VERIFIED`.
- Optional `leanchecker --fresh` replay and Lean capability detection are
  available. The pinned Lean 4.28 toolchain does not expose Lean 4.32
  incremental-header support, so the implementation detects and falls back
  rather than pretending snapshots are available.
- Empty but successfully checked axiom closures now count as kernel evidence.

## Validation

```text
Focused post-fix suite: 94 passed
Complete repository suite: 646 passed in 29.24 s
Python syntax compilation: passed
```

The independent post-fix subagent identified the sandbox closure gap,
hypothesis-edge overclaim, cancellation boundary, exact-span weakening,
resume-path issue, and telemetry race. The first five trust/correctness issues
and the telemetry race were fixed in this pass.

## Remaining Efficiency Work

The current system is safer, but the live scalar run shows that it is not yet
as fast or simple as the target product:

1. Replace model-driven phase ordering with a deterministic orchestrator. The
   model should supply block content, not decide whether to call the next
   required tool or remember to finalize.
2. Cache the actual backend smoke more aggressively by backend/config/toolchain
   fingerprint. A 20–35 second capability cost on every resume is too high.
3. Run main-statement back-translation immediately after skeleton elaboration,
   before discharge. The current trusted audit still occurs after proof work.
4. Generate one typed final bundle from BlockIR and batch all block/main axiom
   closures in one fresh compile. The batch primitive exists, but trusted
   recheck still performs separate checks for proposed block files.
5. Make falsification parameter negotiation deterministic. One live agent asked
   for one million samples, exceeded the 200,000 harness limit, then recorded an
   agent-attested pass. Such a pass has zero verification weight, but the UX is
   noisy and wasteful.
6. Add structured Lean diagnostics to phase events and show the first useful
   failure line. Several live discharge events exposed only `FAILED`, forcing
   the model to rediscover the cause.

## Product Conclusion

The workflow now has a credible trust boundary and a useful early-refutation
path. It is not yet at the desired “fast and effortless” level for positive
full verification. The next release should focus on deterministic orchestration
and early semantic checking; weakening the kernel or evidence gates would make
the UI faster but would undo the main value of the tool.
