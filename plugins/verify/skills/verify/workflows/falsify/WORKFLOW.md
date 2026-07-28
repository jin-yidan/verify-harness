# Falsification workflow

Use this workflow when the user asks to falsify, disprove, find a
counterexample, test a claim for violations, or "try to break" a proof step.

## Scope

Run falsification only. Do not begin Lean proof discharge, assembly, or complete
verification unless the user later asks for it.

## Procedure

1. Identify the exact claim and all hypotheses.
2. If the target is a trusted sampler `.py` file, run:

   ```text
   <verify-python> -m rlverify falsify <sampler-path>
   ```

3. For a paper, proof file, folder, or prose claim, use the trusted harness
   falsification entry point through `verify_run(scope="falsify", ...)`, passing
   pasted claim/proof text directly. Do not set `confirmed=true` or execute a
   generated sampler unless it passes the confined runner or the user
   explicitly authorizes the legacy trusted-local sampler path after a warning
   that generated Python will execute locally.
   If the product tool is unavailable, use the equivalent trusted harness
   command.
   Run engine modules from the runtime source directory returned by the root
   preflight.
4. Record the seed, number of instances, hypotheses satisfied, violations, and
   witness.
5. Independently recheck a proposed witness when possible.

## Outcomes

- `REFUTED` requires a reproducible witness satisfying the tested hypotheses.
- No found witness maps to `NO_COUNTEREXAMPLE`, never `VERIFIED`.
- Unsatisfied sampling hypotheses map to `UNKNOWN` with a vacuity explanation.
- Unsafe or unsupported sampling maps to `UNKNOWN`.

Do not repair the claim. You may explain which assumption or expression caused
the failure after presenting the result.
