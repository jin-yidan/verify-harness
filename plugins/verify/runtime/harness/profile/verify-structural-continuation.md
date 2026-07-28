# STRUCTURAL CONTINUATION MODE — authorized full-process salvage

Preflight or the proof agent found a likely fatal block. The original complete
verification authorization includes the command's mandatory salvage rule, so
this mode checks the rest of the proof without pretending the failed block is
true.

This section supersedes the base profile only where that profile says to stop
immediately after `report_failure` or forbids every use of `sorry`.

1. Call `begin` and inspect `status`.
2. Decompose the entire proof with `resolve_block`, including the failed block,
   and declare every dependency.
3. Independently confirm the fatal finding. Record it with `report_failure`;
   use `refute` first when a concrete Lean counterexample is practical.
4. Name each failed block that will become a placeholder. Do not use a
   placeholder for mere inconvenience or for any independent correct block.
5. Run `sketch` to check the dependency glue.
6. Discharge every mathematically correct block that is independent of all
   placeholders, run its required anti-vacuity audit, and evaluate every
   verified novel block for library reuse. Blocks depending on a placeholder may be proved conditionally
   inside the final structural source.
7. Build one full Lean source file whose main theorem follows from the blocks.
   Use `sorry` only in the declarations whose names exactly match the failed
   placeholder blocks. Do not declare `axiom`s, do not leave the main theorem
   sorried, and do not leave any unnamed gap.
8. Call `structural_assemble(code, placeholder_blocks)` as the final tool.
   Fix structural errors until it returns `COMPILES MODULO PLACEHOLDERS`, then
   stop. Do not call ordinary `assemble` and do not call `finalize`.

The result means only that the remaining proof is structurally valid
conditional on the named failed blocks. It can never be reported as VERIFIED.
