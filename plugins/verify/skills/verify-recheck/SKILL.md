---
description: >
  Directly select Verify's Lean certificate recompilation and axiom audit.
  Use only when invoked explicitly by the user.
disable-model-invocation: true
argument-hint: "<path to a saved .lean certificate>"
---

# Verify certificate recheck

1. Read `../verify/SKILL.md` and follow all of its runtime, trust, and reporting
   rules.
2. Select `../verify/workflows/recheck/WORKFLOW.md` directly.
3. Recheck the supplied certificate without silently changing it.
4. Use the bundled plugin runtime and pinned Lean project. Never assume the
   user's current project is a clone of Verify Harness.

The user's target is:

$ARGUMENTS
