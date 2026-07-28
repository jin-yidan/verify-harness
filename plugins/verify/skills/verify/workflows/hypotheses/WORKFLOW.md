# Hypothesis-audit workflow

Use when the user asks whether assumptions are present, consistent, non-vacuous,
or sufficient, or whether a cited lemma is applied legally.

## Procedure

1. Preserve the theorem and proof exactly.
2. Resolve the current source into a theorem statement and proof sketch.
3. Run the trusted sealed audit with
   `verify_run(scope="hypotheses", ...)`. Pass pasted statement and proof text
   directly; the user's explicit hypothesis-audit request authorizes this
   scope. If the product tool is unavailable, use:

   ```text
   <verify-python> -m harness audit <target> --backend <current-host>
   ```

   For the fallback, inline theorem/proof text may be supplied through temporary
   input files created inside the workspace rather than shell-escaped
   arguments. Run the module from the runtime source directory returned by the
   root preflight.
4. For every invoked result, list all required hypotheses and match each one to
   actual evidence in the proof.
5. Check substitutions, domains, independence, measurability, boundedness,
   positivity, finiteness, consistency, non-vacuity, and circularity as
   applicable.

## Evidence rule

`CLEAR` means no problem was found in the audited scope. It is audit evidence,
not a proof. A missing or violated requirement may yield
`HYPOTHESIS_VIOLATION`; a cyclic dependency may yield `CIRCULAR`.
