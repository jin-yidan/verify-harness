# RLVerify — targeted confirmation procedure

Your only task is to settle the serious preflight finding shown at the end of
the prompt. This is a bounded confirmation pass, not full verification.

1. Call `begin(fixture)` first. Under resume, inspect `status()`.
2. Isolate the exact disputed inference \(H_1,\ldots,H_m \Rightarrow C\).
3. Look first for a concrete exact witness satisfying every \(H_i\) and
   falsifying \(C\). Every object and operation in \(C\) must be defined on the
   witness. Prefer finite, integer, or rational witnesses.
4. When a concrete witness exists, call `refute` with a sorry-free Lean theorem
   explicitly asserting premises-hold and a negated conclusion (`¬`, `Not`, or
   `≠`). A theorem that merely proves some unrelated true proposition is
   quarantined even if it compiles.
   Choosing an empty domain so that `max`, `argmax`, an inverse, division, or
   another displayed object is undefined is not a counterexample. Leave it as
   a well-definedness/hypothesis finding.
5. Set `description` to an exact, contiguous excerpt from the submitted
   statement or proof. The trusted parent rejects paraphrases.
6. After a successful `refute`, call
   `report_failure("PROOF_INVALID", reason, block=<same block>)` when the
   excerpt is a submitted proof inference. Use `WRONG` only when the exact
   target is the complete submitted theorem and the witness satisfies every
   theorem hypothesis. The trusted parent, not this label, decides final scope.
7. If the suspicion is instead a clear false positive, call `certify_step` with
   a sorry-free Lean theorem proving the exact disputed inference from its
   actual premises. Set `description` to the same kind of exact contiguous
   excerpt. This may produce `NOT_CONFIRMED`; it does not verify the full
   theorem.
8. If you can produce neither certificate, stop. Do not report a model
   judgment as confirmation. Do not assemble the theorem, build its full
   dependency graph, use placeholders, or call `finalize`.

The MCP server enforces this scope: full resolve, falsify, sketch, discharge,
assemble, structural-assemble, and finalize tools are unavailable in
confirmation mode.

Only a trusted parent recompile plus a sealed, structured scope audit can
produce `CONFIRMED_THEOREM_REFUTATION`,
`CONFIRMED_PROOF_STEP_FAILURE`, or `NOT_CONFIRMED`. Deterministic undefined-term
checks may produce `CONFIRMED_WELL_DEFINEDNESS_GAP` without claiming a
counterexample. A missing or conflicting certificate leaves the finding
`UNRESOLVED`; that is an acceptable result of this bounded pass.
