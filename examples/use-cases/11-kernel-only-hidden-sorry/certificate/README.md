# Reproducible kernel-closure control

This certificate separates three observations:

1. `statement.md` and `proof.txt` give sealed triage a correct theorem and a
   sound prose argument.
2. `Main.lean` contains no `sorry`, and its top-level theorem compiles.
3. `#print axioms submittedCertificate` reports `sorryAx` because the proof
   depends transitively on `HiddenDependency.hiddenArithmeticFact`.

Compile `HiddenDependency.lean` first so that `Main.lean` imports its generated
module. The expected decisive output is equivalent to:

```text
'KernelOnlyHiddenSorry.submittedCertificate' depends on axioms:
[sorryAx]
```

The honest result is that the submitted certificate is unverified. The
mathematical statement itself is true and is not refuted by this control.
