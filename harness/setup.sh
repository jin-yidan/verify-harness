#!/usr/bin/env bash
# W5 — one-command provisioning + doctor for the RLVerify BYO-agent harness.
# Idempotent: safe to re-run. Exits non-zero with a clear message on the first
# unmet requirement. Heavy steps (Mathlib cache, lake build) are skippable once
# satisfied.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

say() { printf '\033[1m[setup]\033[0m %s\n' "$*"; }
die() { printf '\033[31m[setup] ERROR:\033[0m %s\n' "$*" >&2; exit 1; }

# 1. Lean toolchain ---------------------------------------------------------
say "checking Lean toolchain (elan/lake/lean)…"
command -v lake >/dev/null 2>&1 || die "lake not found. Install elan: \
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh"
command -v lean >/dev/null 2>&1 || die "lean not found (broken elan install?)"
say "  ok: $(lean --version 2>/dev/null | head -1)"

# 2. Python + MCP SDK -------------------------------------------------------
say "checking Python ≥3.10 and the MCP SDK…"
python3 -c 'import sys; assert sys.version_info[:2] >= (3,10)' \
  || die "Python ≥3.10 required (have $(python3 --version))"
if ! python3 -c 'import mcp' >/dev/null 2>&1; then
  say "  installing mcp…"; python3 -m pip install -q mcp || die "pip install mcp failed"
fi
say "  ok: python $(python3 --version | awk '{print $2}'), mcp present"

# 3. Mathlib cache + build --------------------------------------------------
if [ "${SKIP_BUILD:-0}" != "1" ]; then
  say "fetching Mathlib cache (lake exe cache get — gigabytes, one-time)…"
  lake exe cache get >/dev/null 2>&1 || say "  (cache get skipped/failed — continuing)"
  say "building RLGeneralization (lake build)…"
  lake build >/dev/null 2>&1 || die "lake build failed — fix the Lean project first"
  say "  ok: project builds"
else
  say "SKIP_BUILD=1 — skipping cache/build"
fi

# 4. Security sandbox doctor (W0) — REQUIRED for untrusted BYO --------------
say "checking the untrusted-Lean sandbox (W0)…"
case "$(uname -s)" in
  Darwin) [ -x /usr/bin/sandbox-exec ] || die "sandbox-exec missing — required on macOS" ;;
  Linux)  say "  NOTE: Linux bubblewrap sandbox is present but UNVALIDATED. \
Set RLVERIFY_LINUX_SANDBOX=1 to opt in at your own risk, or pass --no-sandbox \
at verify time for trusted-local runs." ;;
  MINGW*|MSYS*) die "Windows is unsupported natively — use WSL2, then the Linux \
sandbox caveats apply (RLVERIFY_LINUX_SANDBOX=1 opt-in or --no-sandbox)." ;;
  *) die "unsupported platform $(uname -s)" ;;
esac
python3 -c 'from rlverify.sandbox import safe_verify' || die "sandbox import failed"
say "  ok: sandbox importable"

# 5. Smoke: a benign proof compiles under the sandbox -----------------------
if [ "${SKIP_BUILD:-0}" != "1" ]; then
  if [ "$(uname -s)" = "Linux" ] && [ "${RLVERIFY_LINUX_SANDBOX:-0}" != "1" ]; then
    say "skipping sandboxed compile smoke on Linux (set RLVERIFY_LINUX_SANDBOX=1 to opt in)"
  else
    say "smoke-testing a sandboxed compile…"
    python3 -m rlverify.sandbox || die "sandboxed compile smoke test failed"
  fi
fi

# 6. BYO agent CLI — the harness drives YOUR agent; it must be installed + ---
#    logged in. Presence is checked free; a live auth smoke test is opt-in
#    (CHECK_AUTH=1) because it spends a few tokens and needs network.
AGENT_BACKEND="${HARNESS_BACKEND:-claude}"
case "$AGENT_BACKEND" in
  claude) AGENT_CLI="claude" ;;
  codex)  AGENT_CLI="codex" ;;
  *) die "unknown HARNESS_BACKEND='$AGENT_BACKEND' (expected claude or codex)" ;;
esac
say "checking BYO agent CLI for backend '$AGENT_BACKEND' ('$AGENT_CLI')…"
if ! command -v "$AGENT_CLI" >/dev/null 2>&1; then
  if [ "$AGENT_BACKEND" = "codex" ]; then
    die "'codex' not on PATH. Install/log in to Codex, then rerun with HARNESS_BACKEND=codex."
  else
    die "'claude' not on PATH. Install Claude Code and log in, or rerun with HARNESS_BACKEND=codex for Codex testing."
  fi
fi
say "  ok: $AGENT_CLI found at $(command -v "$AGENT_CLI")"
if [ "$AGENT_BACKEND" = "codex" ]; then
  say "  note: Codex backend is implemented and intended for Codex expansion/testing; validate a full run before treating it as production-equivalent."
fi
if [ "${CHECK_AUTH:-0}" = "1" ]; then
  say "  live auth smoke test (CHECK_AUTH=1; spends a few tokens)…"
  if [ "$AGENT_BACKEND" = "codex" ]; then
    tmp_msg="$(mktemp)"
    if printf 'reply with exactly: OK\n' | "$AGENT_CLI" exec - \
        --skip-git-repo-check -C "$ROOT" --ephemeral \
        --sandbox read-only --output-last-message "$tmp_msg" >/dev/null 2>&1 \
        && grep -q "OK" "$tmp_msg"; then
      rm -f "$tmp_msg"
      say "  ok: codex is authenticated"
    else
      rm -f "$tmp_msg"
      die "codex is installed but the test call failed — are you logged in?"
    fi
  elif echo | "$AGENT_CLI" -p "reply with exactly: OK" >/dev/null 2>&1; then
    say "  ok: claude is authenticated"
  else
    die "claude is installed but the test call failed — are you logged in? \
Run 'claude' once interactively to authenticate."
  fi
else
  say "  (auth not live-tested — run CHECK_AUTH=1 HARNESS_BACKEND=$AGENT_BACKEND harness/setup.sh to verify login)"
fi

BACKEND_FLAG=""
if [ "$AGENT_BACKEND" != "claude" ]; then
  BACKEND_FLAG=" --backend $AGENT_BACKEND"
fi

say "READY. Verify a proof with:"
say "    python3 -m harness verify <folder-or-paper>${BACKEND_FLAG} --report"
say "Draft cheaply with:"
say "    python3 -m harness triage -s statement.md -p proof.txt${BACKEND_FLAG}"
say "    python3 -m harness audit  -s statement.md -p proof.txt${BACKEND_FLAG}"
say "  See harness/README.md."
