---
description: >
  Directly select Verify's complete theorem-and-proof verification workflow,
  including Lean contract resolution, trusted harness execution, and kernel
  evidence. Use only when invoked explicitly by the user.
disable-model-invocation: true
argument-hint: "<theorem, proof, file, folder, paper, or URL>"
---

# Verify full process

This is a direct entry point into the Verify plugin; it is not a standalone
copy of the verification machinery.

1. Read `../verify/SKILL.md` and follow all of its runtime, trust, reporting,
   and authorization rules.
2. Select `../verify/workflows/full-check/WORKFLOW.md` directly. Do not reroute
   to a smaller workflow.
3. Treat this invocation as the initial full-verification request, not as the
   separate confirmation required before Lean execution.
4. Use the bundled plugin runtime and product tools. Never assume the user's
   current project is a clone of Verify Harness.

The user's target is:

$ARGUMENTS
