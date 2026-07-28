# Certificate-recheck workflow

Use when the user supplies a saved `.lean` certificate and asks to recheck,
recompile, or audit it.

1. Confirm the target is an existing `.lean` file.
2. Run it in the pinned project environment:

   ```text
   lake env lean <certificate>
   ```

   Use the runtime source directory returned by the root preflight as the
   pinned project working directory.
3. Inspect output for `sorryAx`, unexpected axioms, compilation failures, or
   import drift.
4. Report the current kernel evidence and the exact artifact path.

Rechecking needs no model API. A compilation failure means the certificate no
longer establishes the result in the current environment; it does not by itself
show the mathematical theorem is false.
