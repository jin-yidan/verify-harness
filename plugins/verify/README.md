# Verify plugin

Verify is a dual Codex and Claude Code plugin for automatically routing
mathematical proof-checking requests to the local Lean-backed Verify engine.

Users speak naturally; they do not invoke Verify skills or internal commands.

The cached plugin includes the complete engine source, a portable launcher,
and a permissioned first-use runtime manager. On the first relevant request,
the Verify skill checks runtime status. If the versioned Python environment is
missing, the agent explains the copy/build and asks permission before installing
the bundled engine in user data.

```text
scripts/verify_runtime.py --status --json
```

Lightweight falsification and retrieval can run after the Python engine is
ready even when Lean is unavailable. Before complete verification, the agent
offers a separate permissioned installation of pinned elan 4.2.1, verifies the
official release digest, avoids shell-profile edits, and builds the pinned Lean
project. This official fallback can be a large first-time download; lightweight
workflows remain usable while it is unavailable.

The MCP launcher resolves only the bundled, versioned engine from user data.
It exposes product-level routing, formal-library search, and guarded
triage/hypothesis/falsification/full workflows. Pasted theorem and proof text
is accepted directly. Users never configure MCP or run the runtime scripts
themselves.

Complete verification uses the trusted `python -m harness verify` path so
sealed gates remain outside the agent-facing MCP session.
