from __future__ import annotations

import json
import time
from pathlib import Path

from rlverify.mcp_server import HarnessSession

from ..tools import ToolRegistry
from .protocol import BackendBundle, ToolCallingBackend


class APIAgentDrive:
    """Bounded function-calling agent over the protocol-independent session."""

    def __init__(
        self,
        backend: ToolCallingBackend,
        *,
        max_turns: int = 40,
        timeout_s: int = 900,
        sandbox: bool | None = None,
    ):
        self.backend = backend
        self.max_turns = max_turns
        self.timeout_s = timeout_s
        self.sandbox = sandbox
        self.last_usage: dict = {}

    def __call__(self, fixture: str, statement: str, proof: str,
                 corpus_path: str) -> None:
        session = HarnessSession(corpus_path=corpus_path, sandbox=self.sandbox)
        registry = ToolRegistry(session)
        profile = (
            Path(__file__).resolve().parents[2]
            / "harness" / "profile" / "verify-full-process.md"
        ).read_text()
        messages: list[dict] = [
            {
                "role": "system",
                "content": (
                    profile
                    + "\n\nYou are running through a bounded API tool loop. "
                      "Call begin first. Use only the supplied verification tools. "
                      "For a proof, assemble and then evaluate every discharged "
                      "novel block for library reuse before returning. Finish "
                      "with report_failure for a detected flaw/incomplete result. "
                      "Never claim VERIFIED in text."
                ),
            },
            {
                "role": "user",
                "content": (
                    f"Session name: {fixture}\n\n"
                    f"Statement:\n{statement}\n\nProof:\n{proof}"
                ),
            },
        ]
        start = time.monotonic()
        idle_turns = 0

        for _turn_no in range(self.max_turns):
            elapsed = time.monotonic() - start
            if elapsed >= self.timeout_s:
                _record_incomplete(
                    registry,
                    f"API agent time budget exhausted after {self.timeout_s}s",
                    fixture,
                )
                return
            turn = self.backend.complete(
                messages,
                registry.openai_tools(),
                timeout_s=max(1, int(self.timeout_s - elapsed)),
            )
            self.last_usage = _merge_usage(self.last_usage, turn.usage)
            assistant = {"role": "assistant", "content": turn.content or None}
            if turn.tool_calls:
                assistant["tool_calls"] = [
                    call.as_openai_dict() for call in turn.tool_calls
                ]
            messages.append(assistant)

            if not turn.tool_calls:
                idle_turns += 1
                if idle_turns >= 2:
                    _record_incomplete(
                        registry,
                        "API agent stopped without a terminal verification action",
                        fixture,
                    )
                    return
                messages.append({
                    "role": "user",
                    "content": (
                        "Continue by calling an available verification tool. "
                        "Finish by assembling and evaluating all discharged "
                        "novel blocks, or by calling report_failure."
                    ),
                })
                continue

            idle_turns = 0
            for call in turn.tool_calls:
                result = registry.execute(call.name, call.arguments)
                messages.append({
                    "role": "tool",
                    "tool_call_id": call.id,
                    "content": result.content,
                })
                if result.terminal:
                    return

        _record_incomplete(
            registry,
            f"API agent turn budget exhausted after {self.max_turns} turns",
            fixture,
        )


def api_bundle(backend: ToolCallingBackend, *, name: str,
               timeout_s: int = 900, max_turns: int = 40,
               sandbox: bool | None = None) -> BackendBundle:
    drive = APIAgentDrive(
        backend,
        timeout_s=timeout_s,
        max_turns=max_turns,
        sandbox=sandbox,
    )
    return BackendBundle(
        name=name,
        model=backend.capabilities.model,
        call_model=lambda prompt: backend.call_sealed(prompt),
        agent_drive=drive,
        health_check=backend.health_check,
        close=backend.close,
    )


def _record_incomplete(registry: ToolRegistry, reason: str, fixture: str) -> None:
    if not registry.begun:
        registry.execute("begin", json.dumps({"fixture": fixture}))
    if not registry.terminal:
        registry.execute(
            "report_failure",
            json.dumps({"kind": "INCOMPLETE", "reason": reason, "block": ""}),
        )


def _merge_usage(previous: dict, current: dict) -> dict:
    merged = dict(previous)
    for key, value in current.items():
        if isinstance(value, (int, float)) and isinstance(merged.get(key, 0), (int, float)):
            merged[key] = merged.get(key, 0) + value
        else:
            merged[key] = value
    return merged
