# Verify use-case examples

This directory contains small, reviewable theorem-and-proof inputs that
demonstrate different Verify situations. They are user examples, not benchmark
grading keys and not precomputed claims about a particular model run.

Each case uses the harness folder convention:

- `statement.md` — the theorem as submitted;
- `proof.txt` — the submitted proof or proof sketch;
- `claim.txt` — the intended natural-language meaning;
- `scenario.json` — recommended public workflow, honest outcome boundary, and
  shared-library policy.

Users can reference a case folder in Codex or Claude Code and ask the request
shown in `scenario.json`. The harness reads only the three theorem/proof/claim
files; maintainers may pass the folder directly. Full verification still
requires the normal separate confirmation before Lean or provider spend.

## Scenario matrix

| Case | Situation | Primary workflow | Main lesson |
|---|---|---|---|
| `01-valid-direct-proof` | Correct theorem and proof | Full verification | A faithful kernel proof can become `VERIFIED`. |
| `02-false-claim` | False theorem with a concrete counterexample | Falsification / full verification | Audit finds are `SUSPECTED`; only an independent certificate or kernel refutation is `REFUTED`. |
| `03-true-theorem-bad-proof` | True theorem, invalid submitted argument | Full verification | Proving the theorem another way is not the same as verifying the submitted proof. |
| `04-missing-hypothesis` | A standard lemma is used without its positivity condition | Hypothesis audit | Model audit is prioritization-only; the missing condition can guide a later certificate. |
| `05-circular-proof` | True statement argued from its own conclusion | Hypothesis audit / full verification | Circularity must be recorded without silently repairing the proof. |
| `06-statement-mismatch` | Formal target is only a finite special case of the intended claim | Statement audit | A compiling weaker statement does not verify the intended theorem. |
| `07-incomplete-proof` | Plausible theorem with “standard” steps omitted | Full verification | Unresolved obligations are `INCOMPLETE` or `UNKNOWN`, never verified. |
| `08-reusable-lemma-candidate` | General atomic inequality useful across proofs | Full verification + trusted library review | It may be promoted only after the reusable-only gates pass. |
| `09-proof-specific-glue` | Correct but paper-specific bookkeeping | Full verification | Save the run artifact; do not promote the lemma to the shared corpus. |
| `10-falsification-pass` | True claim checked only by bounded sampling | Falsification | `NO_COUNTEREXAMPLE` has zero proof weight. |
| `11-kernel-only-hidden-sorry` | Clean top-level certificate imports a theorem proved with hidden `sorry` | Certificate recheck / full verification | Compilation alone passes; only transitive kernel-closure inspection exposes `sorryAx` and rejects the certificate. |

## Kernel-only control

Case `11-kernel-only-hidden-sorry` is the controlled demonstration for why the
kernel audit is necessary. Its sealed triage input consists only of
`statement.md`, `proof.txt`, and `claim.txt`; those describe a correct
elementary theorem and a sound mathematical argument. The submitted top-level
Lean file also contains no `sorry` token and compiles without a local
placeholder warning.

The imported `HiddenDependency` module, however, proves the lemma used by the
top-level certificate with `sorry`. Lean permits this placeholder during
compilation. Reading `#print axioms submittedCertificate` is the decisive step:
the transitive closure contains `sorryAx`, so this certificate is
`UNVERIFIED`.

This example establishes a precise claim: under the sealed triage information
boundary and a clean top-level source scan, only the trusted transitive
kernel-closure audit detects the hidden dependency. It does not claim that the
mathematical theorem is false.

## Outcome vocabulary

`scenario.json` distinguishes:

- `likely` — the outcome the case is designed to exercise;
- `allowed` — honest alternatives when execution depth varies;
- `must_not_report` — conclusions that would cross the evidence boundary.

The expected interpretation is intentionally visible because these are teaching
examples. It is not a sealed grading key. For an unbiased evaluation, submit
only `statement.md`, `proof.txt`, and `claim.txt`; use `benchmarks/` for
controlled regression scoring.
