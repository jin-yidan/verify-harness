"""W3 — backend adapters: turn a BYO agent account into a `call_model`.

A `call_model` is `Callable[[str], str]`: prompt in, completion text out. The
sealed gates (triage, back-translation) use it so they run under whatever agent
the user brought, while staying backend-agnostic.

Sealing note: the trusted gate calls must NOT inherit the project's CLAUDE.md /
skills / MCP servers, or the "sees only the proof text" guarantee breaks. Each
adapter runs the model in a CLEAN temp cwd so no project context bleeds in.
"""
from __future__ import annotations

import json
import os
import subprocess
import tempfile
from typing import Callable

CallModel = Callable[[str], str]


# Tools/servers the sealed call must NOT have. cwd-isolation alone drops only
# project .claude/; these flags also kill globally-configured MCP servers and
# built-in tools so "you have no tools" is actually true at runtime.
_SEALED_DISALLOWED = "Bash,Read,Write,Edit,Glob,Grep,WebFetch,WebSearch,Task,NotebookEdit"
CLAUDE_PROVIDER_ENV_KEYS = frozenset({
    "ANTHROPIC_BASE_URL",
    "ANTHROPIC_AUTH_TOKEN",
    "ANTHROPIC_API_KEY",
    "ANTHROPIC_MODEL",
    "ANTHROPIC_DEFAULT_OPUS_MODEL",
    "ANTHROPIC_DEFAULT_SONNET_MODEL",
    "ANTHROPIC_DEFAULT_HAIKU_MODEL",
    "CLAUDE_CODE_SUBAGENT_MODEL",
    "CLAUDE_CODE_EFFORT_LEVEL",
})


def claude_backend(model: str = "opus", timeout: int = 600,
                   reasoning_effort: str | None = None,
                   service_tier: str | None = None,
                   provider_env: dict[str, str] | None = None) -> CallModel:
    """Headless `claude -p` in a clean cwd with MCP + built-in tools disabled,
    so the sealed reviewer truly has no context and no tools."""
    def call(prompt: str) -> str:
        cwd = tempfile.mkdtemp(prefix="rlverify_sealed_")
        # Prompt on STDIN (T21 — `-p` takes no prompt arg then), so a long paper /
        # proof can't blow Linux's 128KB single-argv cap (E2BIG). Sealing flags
        # (clean cwd, no MCP, no tools) are unchanged.
        env = dict(os.environ)
        if provider_env is not None:
            for key in CLAUDE_PROVIDER_ENV_KEYS:
                env.pop(key, None)
            env.update(provider_env)
        p = subprocess.run(
            ["claude", "-p", "--model", model, "--output-format", "json",
             "--strict-mcp-config", "--mcp-config", '{"mcpServers":{}}',
             "--disallowedTools", _SEALED_DISALLOWED],
            input=prompt, capture_output=True, text=True, timeout=timeout, cwd=cwd,
            env=env,
        )
        try:
            return json.loads(p.stdout).get("result", "") or p.stdout
        except (json.JSONDecodeError, AttributeError):
            return p.stdout
    return call


def codex_backend(model: str | None = None, timeout: int = 600,
                  reasoning_effort: str | None = None,
                  service_tier: str | None = None,
                  provider_env: dict[str, str] | None = None) -> CallModel:
    """Headless `codex exec` as a SEALED reviewer — clean temp cwd, MCP servers
    cleared, user config/rules ignored, and read-only sandbox. Codex does not
    expose a Claude-style `--disallowedTools` flag here, so this is the Codex
    sealing posture rather than a literal no-tools mirror. The final agent
    message is captured via
    `--output-last-message` so the grader's answer is clean of codex's UI chrome
    (the old `p.stdout.strip()` swallowed banners/token-counts).

    Built against codex-cli 0.120.0's surface (`codex exec --help`); UNVALIDATED
    against a live account — confirm with a real run before trusting the verdict
    (the codex grader sealing is the W3 portability experiment). The sealed call
    ignores user config/rules, runs from a clean cwd, clears MCP, and uses a
    read-only sandbox.

    `model=None` lets codex use its own config default rather than a guessed id."""
    def call(prompt: str) -> str:
        cwd = tempfile.mkdtemp(prefix="rlverify_sealed_")
        last = tempfile.mktemp(prefix="rlverify_codex_msg_", suffix=".txt")
        # Prompt on STDIN (T21 — `codex exec -`), avoiding the 128KB argv cap.
        argv = ["codex", "exec", "-",
                "--skip-git-repo-check", "-C", cwd, "--ephemeral",
                "--ignore-user-config", "--ignore-rules",
                "--color", "never",
                "--sandbox", "read-only",          # grader needs no writes/tools
                "-c", "mcp_servers={}",            # kill globally-configured MCP servers
                "--output-last-message", last]
        if model:
            argv += ["-m", model]
        if reasoning_effort:
            argv += ["-c", f"model_reasoning_effort={json.dumps(reasoning_effort)}"]
        if service_tier:
            argv += ["-c", f"service_tier={json.dumps(service_tier)}"]
        p = subprocess.run(argv, input=prompt, capture_output=True, text=True,
                           timeout=timeout, cwd=cwd)
        try:
            msg = open(last).read().strip()
        except OSError:
            msg = ""
        return msg or p.stdout.strip()
    return call


_BACKENDS = {"claude": claude_backend, "codex": codex_backend}


def get_backend(name: str, **kw) -> CallModel:
    if name not in _BACKENDS:
        raise ValueError(f"unknown backend {name!r}; have {list(_BACKENDS)}")
    return _BACKENDS[name](**kw)
