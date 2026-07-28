# Full verification workflow

Use when the user asks to verify a mathematical proof or theorem, requests
verification in Lean, or asks whether a theorem/proof is correct. Selecting
this workflow starts preparation only, never Lean execution.

## Golden workflow contract

The mathematical procedure is defined exclusively by:

- `.claude/commands/verify-full-process.md` for each theorem/proof; and
- `.claude/commands/verifyRL-paper.md` for paper dependency orchestration.

This product workflow is a routing/authorization adapter. It must not replace,
abridge, or reinterpret the golden phase order, coverage, classifications,
evidence rules, salvage rule, library-growth rule, paper dependency semantics,
or final report contract. The trusted harness embeds the exact golden
single-proof workflow in the MCP proof-agent task and records both golden file
hashes in final paper outputs.

## Trusted execution rule

Complete verification must go through the trusted parent harness. Do not use a
raw MCP `assemble` result as the final source of truth because the agent-facing
MCP session cannot author the sealed triage and back-translation gates.

## Procedure

1. Preserve the theorem, proof, and natural-language claim exactly.
2. Resolve file, folder, paper, URL, or pasted input.
3. For papers or unfamiliar sources, run a dry run first:

   ```text
   <verify-python> -m harness verify <target> --backend <current-host> --dry-run
   ```

4. Resolve a **Lean contract** before quoting an estimate: list the exact formal
   objects, domains, policy class, every nonemptiness or attainment assumption
   required by `max` or `argmax`, and all side conditions used by the proof.
   Distinguish assumptions stated by the input from conventions that would
   otherwise be implicit. Never silently add a convention to make a theorem
   formalizable: if an essential choice is unsettled, report the ambiguity and
   ask the user to choose the precise statement. This contract is the statement
   later passed to Lean and must be preserved by statement back-translation.
5. Show the extracted theorem/proof, Lean contract, scope, and estimate.
   Typeset mathematical content with `\(...\)` and `\[...\]`. State that Lean
   has not started, then ask for confirmation.
6. Require one separate user response approving the displayed
   full-verification attempt. The initial request that selected this workflow
   is not confirmation, even if it said "fully verify" or "run it now." Once
   given, this single confirmation authorizes the complete uninterrupted Lean
   4 attempt: translation, targeted checks, proof retries, block discharge,
   assembly, trusted recompilation, axiom-closure audit, and final reporting.
   If generated local sampler execution may be used, include it in this upfront
   authorization or skip that optional phase. Do not ask for another
   confirmation during the run.
7. Only after that confirmation, run
   `verify_run(scope="full", confirmed=true, ...)`.
   Pasted theorem/proof text can be supplied directly. If the product tool is
   unavailable, run:

   ```text
   <verify-python> -m harness verify <target> --backend <current-host> --report
   ```

   For the fallback, use temporary workspace files for pasted theorem/proof
   content. Do not place long or sensitive proof text into shell arguments. Run
   the module from the runtime source directory returned by the root preflight.
   Preserve the foreground host's solving capability: pass its model,
   reasoning effort, service tier, and an adequate agent budget explicitly when
   available. Also pass concise `agent_context` with useful notation, prior
   library discoveries, and failed Lean attempts from the active conversation.
   Do not put new assumptions or proposed repairs in that context. The harness
   treats it as non-authoritative guidance, never as mathematical evidence.
8. Let the harness run sealed triage before launching the expensive full-proof
   agent. For each serious triage or hypothesis-audit finding, run the bounded
   targeted-confirmation profile. It may seek a concrete witness and compile a
   narrow Lean refutation, or prove the exact disputed inference positively,
   but it must not formalize the whole theorem. Never promote model agreement,
   an unchecked witness, or a missing certificate.
9. Follow the derived preflight state without pausing for another user choice:
   - `CONFIRMED_THEOREM_REFUTATION` requires a clean trusted certificate for a
     well-defined instance satisfying every submitted hypothesis and negating
     the complete theorem.
   - `CONFIRMED_PROOF_STEP_FAILURE` requires a clean trusted certificate for an
     exact submitted inference; it invalidates the proof, not necessarily the
     theorem.
   - `CONFIRMED_WELL_DEFINEDNESS_GAP` records that a displayed object is
     undefined without an omitted hypothesis. It requires restatement and is
     not a counterexample.
     Each confirmed negative state continues with structural salvage of every
     independent block.
   - `UNRESOLVED` means targeted checking settled neither direction.
     Automatically continue on the already-authorized full Lean path.
   - `NOT_CONFIRMED` requires a clean positive kernel certificate plus a
     faithful exact-excerpt match. Continue the already-authorized full path.
   - `CLEAR_TO_PROCEED` continues the already-authorized full verification.
10. Structural continuation must record the failed block, decompose the full
   dependency graph, discharge every correct block independent of the failure,
   and compile one conditional Lean source through `structural_assemble`.
   The source may contain `sorry` only in explicitly named failed blocks. It
   must reject custom axioms, unnamed sorries, unused placeholders, a sorried
   main theorem, and undischarged independent blocks. The trusted parent must
   additionally verify that every named placeholder occurs in the final
   theorem's kernel dependency closure and that the final structural statement
   back-translates to the original claim. Report success only as
   `COMPILES MODULO PLACEHOLDERS`; it can never become `VERIFIED`.
11. If preflight permits full continuation, continue with statement back-translation,
   falsification gates, proof construction, assembly, and kernel audit. For
   every decomposed block, require an explicit dependency list (`[]` for a
   root), exact source-proof excerpt, and complete hypothesis list; for every
   novel or instantiation block, require a successful decomposition sketch and
   successful discharge in dependency order before assembly. Treat a
   deterministic id-shaped anti-vacuity finding as a blocking workflow gap.
   Keep working through ordinary compile errors and proof-search failures within
   the configured retry and time budgets. Do not return merely because the first
   Lean translation or compile attempt failed.
12. Report the harness result without upgrading it. Format mathematical
   explanations in Markdown-compatible LaTeX while keeping Lean source in code
   fences.
13. Keep the default user-facing answer diagnostic:
   - list only problems supported by the returned evidence, or say that no
     problem was established at the completed verification depth;
   - when problems exist, present `Location`, `Problem`, `Evidence`, and
     `Weight`, following the legacy output-contract distinction between
     load-bearing, zero-weight, and prioritization-only results;
   - give a short plain-language conclusion explaining whether the submitted
     theorem/proof verified and what remains unknown;
   - print the decomposition chart with every block's statement, dependencies,
     `library` / `instantiation` / `novel` classification, selected repository
     theorem and source location, and formal status;
   - link every saved `.lean` artifact and give its exact
     `lake env lean <path>` reproduction command.
   Do **not** supply a corrected proof, replacement derivation, new hypotheses,
   or newly authored Lean code unless the user explicitly asks for repair or
   proof construction in a separate request. A request to check, review, audit,
   or verify a submission is not by itself a request to rewrite it.

## Verdict rule

`VERIFIED` requires a trusted-parent recompile of the saved Lean certificate,
acceptable axiom closure, required trusted gates, and workflow-contract
coverage for proof-step mappings, hypotheses, dependencies, sketch, ordered
discharge, and deterministic anti-vacuity. `VERIFIED/ALTERNATIVE-PROOF` means
the theorem was kernel-proven but the submitted proof steps were not faithfully
discharged. The sealed hypothesis audit remains prioritization-only: its
findings must be independently confirmed before reporting a mathematical
failure. Audit-only failures are `SUSPECTED`; only a kernel-backed refutation
or independently checked deterministic certificate is `REFUTED`. A timeout,
provider failure, or unresolved block is `UNKNOWN` or `INCOMPLETE`.

A prose proof, a statement audit, or a run that stops before `assemble` is
never full Lean verification. It must not be labeled `VERIFIED`, even if every
informal step appears sound.

For a sound submission, `assemble` plus trusted kernel recheck is the mandatory
terminal path. For a false theorem or invalid submitted inference, a faithful
kernel-backed refutation is the preferred terminal path; for an exact statement
that cannot be represented or completed within the available formal
infrastructure, report `INCOMPLETE` or `UNKNOWN`. These non-verified terminal
paths are outcomes of the same authorized run, not reasons to request another
confirmation.

The confirmed-negative states and `UNRESOLVED` are routing states, not
interchangeable theorem verdicts. Only `CONFIRMED_THEOREM_REFUTATION` supports
the theorem-level `REFUTED` status. A proof-step failure means the submitted
proof is invalid; a well-definedness gap means the statement requires
restatement.
`COMPILES MODULO PLACEHOLDERS` certifies only the conditional proof structure:
the main conclusion follows if the named placeholder blocks are assumed. The
overall theorem remains unverified or refuted according to the actual failure
evidence.

Retain the final report and its referenced evidence/certificates. Once the run
has a terminal result, remove resumable journals, worker logs, generated
fixtures, and intermediate report versions; preserve them only when the user
explicitly requests `--keep-intermediates` for debugging. Promote only
generalized, atomic lemmas with an explicit reusable assessment into the shared
library; never promote paper-specific glue or mere instantiations.
