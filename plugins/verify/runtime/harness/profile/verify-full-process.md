# Harness MCP binding for the golden `/verify-full-process`

This file is an execution adapter, not an independent verification procedure.
The runner embeds the exact contents of
`.claude/commands/verify-full-process.md` before this binding. The golden
command controls phase order, required coverage, classifications, evidence,
salvage, library growth, output, and integrity.

## Trust ownership

The trusted parent harness has already performed or will perform the following
golden steps. Do not repeat them or claim their outcomes:

- sealed adversarial triage;
- sealed prose hypothesis audit;
- deterministic statement/well-definedness checks;
- targeted confirmation of serious findings;
- trusted recompilation of every verdict-bearing Lean source;
- main-statement, proof-step, axiom, refutation, and library-candidate
  back-translation;
- axiom-closure enforcement, final verdict derivation, artifact promotion, and
  final report rendering.

Hints from the sealed reviews are appended to the task. They prioritize work
but do not decide the verdict. You cannot write trusted gate records.

## Mechanical translation

Translate the golden command's driver operations to the MCP tools below:

| Golden operation | Harness MCP operation |
|---|---|
| `d.begin(...)` / `d.resume(...)` | `begin(fixture)`; always the first call |
| `d.status()` | `status()` |
| `d.grep(...)` / `d.hybrid_search(...)` | `search(query)` with multiple phrasings |
| inspect repository/Mathlib source | `source_search(query)` then bounded `source_read(path, ...)`; these are read-only and cannot access journals or arbitrary workspace files |
| type-directed reuse search | `library_search(block, statement, imports)` |
| `d.resolve(...)` | `resolve_block(...)` |
| inter-block hypothesis audit | `audit_invocation(...)` for every dependency and selected theorem edge |
| falsification record | `falsify_run(...)` when confined execution is available, otherwise `falsify_block(...)` |
| `d.compile(...)` | `compile(code)` |
| `d.sketch(...)` | `sketch(skeleton_code, expected_blocks)` |
| `d.formalize(...)` / discharge | `discharge(block, statement, proof, imports)` |
| four anti-vacuity checks | `audit_block(...)` after every novel discharge |
| `d.assemble(...)` | `assemble(statement, proof, imports)` |
| negative certificate | `refute(block, code, description)` followed by a scoped `report_failure(...)` |
| positive disputed-step certificate | `certify_step(block, code, description)` |
| early/non-pass classification | `report_failure(kind, reason, block)` |
| unrepresentable exact main claim | `main_unformalizable(reason)` |
| axiom lifecycle | `register_axiom_lifecycle(...)` |
| Phase 5 generality/library evaluation | `evaluate_library_candidate(...)` for every discharged novel block |

The parent harness, not this agent, calls final enforcement. Do not call
`finalize()`.

## Harness-strengthened records

The harness requires several fields that make the golden workflow auditable:

- `resolve_block` must include an exact submitted-proof `source_excerpt`, its
  character span, all `hypotheses`, all `depends_on`, and an elaborated
  `formal_signature`;
- a novel classification is rejected until `library_search` was run on that
  exact signature;
- use `source_search`/`source_read` when a textual hit, import, theorem name, or
  tactic idiom needs source-level inspection; do not guess declarations that
  can be inspected through this read-only surface;
- every invocation edge must have one `audit_invocation` record with one
  concrete check per invoked hypothesis;
- every eligible novel/instantiation block must have a falsification outcome;
- the sketch must cover every active non-library block;
- discharge follows topological order and is capped at five attempts per block;
- every discharged novel block receives all four `audit_block` checks and one
  `evaluate_library_candidate` decision;
- proof-specific glue is retained as a final run artifact but is not promoted
  to the shared library.

## Whole-paper `prior` blocks

When the task contains an “Already verified paper dependencies” section, those
entries were kernel-checked by earlier component runs in this same paper
session. A component may use only the listed exact declaration as a free
`prior` fact:

1. call `resolve_block(kind="prior", prior="<listed name>", ...)`;
2. include the prior block in `depends_on`;
3. audit every hypothesis at the current invocation with
   `audit_invocation`;
4. do not generalize, weaken, strengthen, or re-prove it;
5. do not treat an unlisted paper statement as prior.

The MCP server resolves the code from a runner-owned sidecar and rejects names
or statements not present there. The trusted parent recompiles the final
assembly containing the prior declarations.

## Terminal paths

Reach exactly one terminal proof-agent path:

- `assemble` after complete resolution, audits, falsification, sketch,
  discharge, anti-vacuity checks, and library evaluation;
- `refute` plus `report_failure` for a certified flaw;
- `report_failure` for an honestly unresolved non-pass, followed by structural
  salvage of every independent correct block when requested by the runner;
- `main_unformalizable` when the exact submitted main statement cannot be
  represented without changing it;
- `structural_assemble` only under the runner's structural-continuation
  overlay.

A prose-only response is not completion. Never repair the submitted theorem or
proof to force success.
