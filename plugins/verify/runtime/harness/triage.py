"""W3 — sealed adversarial triage, executed by TRUSTED harness code.

In the Claude Code skill, triage is a Task subagent; in the BYO-agent harness it
must be a backend-agnostic isolated model call the *runner* makes — NOT a record
the driving agent supplies (W1/W2 headline: gates must be trusted-executed, not
attested). The call sees ONLY the verbatim theorem+proof text: no library, no
tools, no conversation. The result is then recorded into the session by the
runner, so the agent under test cannot fabricate it.

`call_model` is injected (a `Callable[[str], str]`) so this works under any
backend (claude CLI, codex, an API) — see harness/backends.py.
"""
from __future__ import annotations

import json
from typing import Callable

CallModel = Callable[[str], str]

# Verbatim from .claude/commands/verify-full-process.md Phase 0 — the ONLY instruction the
# sealed reviewer receives, prepended to the proof text and nothing else.
TRIAGE_INSTRUCTION = (
    "You are an adversarial reviewer. You have no other context and no tools.\n"
    "Assess each proof step: SOUND or SUSPECT, with a one-line reason each, then\n"
    "list the most likely fatal flaws ranked by severity. Output JSON only:\n"
    '{"suspects": [{"step": <n>, "suspicion": "<reason>",\n'
    '               "severity": "high|medium|low"}], "all_clear": <bool>}'
)


def build_prompt(theorem_proof_text: str) -> str:
    """The sealed prompt = instruction + ONLY the proof text. Kept as a function
    so isolation is testable (no library/context may appear here)."""
    return f"{TRIAGE_INSTRUCTION}\n\n{theorem_proof_text}"


def _parse(raw: str) -> dict | None:
    """Extract the JSON object; tolerate code fences / surrounding prose."""
    raw = raw.strip()
    start, end = raw.find("{"), raw.rfind("}")
    if start == -1 or end <= start:
        return None
    try:
        obj = json.loads(raw[start:end + 1])
    except json.JSONDecodeError:
        return None
    if not isinstance(obj, dict) or "suspects" not in obj or "all_clear" not in obj:
        return None
    if not isinstance(obj["suspects"], list):
        return None
    if not isinstance(obj["all_clear"], bool):
        return None
    # Normalize to EXACTLY what driver.record_triage accepts. A malformed
    # suspect row invalidates the reply instead of being dropped: otherwise a
    # bad row plus a truthy all_clear string could silently become ALL-CLEAR.
    suspects = []
    for s in obj["suspects"]:
        if not isinstance(s, dict) or "step" not in s or "suspicion" not in s:
            return None
        suspects.append(s)
    # If any suspect survives, the proof is NOT all-clear regardless of the flag;
    # driver.record_triage rejects all_clear=True alongside suspects.
    all_clear = obj["all_clear"] and not suspects
    return {"suspects": suspects, "all_clear": all_clear}


def sealed_triage(theorem_proof_text: str, call_model: CallModel) -> dict:
    """Run trusted sealed triage. Fail toward MORE scrutiny: a malformed result
    OR a backend failure (after one retry) becomes
    ``{"suspects": [], "all_clear": False}`` — never a silent all-clear.

    The result carries ``executed_by="harness"``: provenance the agent cannot
    forge. The W4 gate must REQUIRE this stamp so an agent-written ``triage``
    dict (the old attestation hole) no longer satisfies the gate."""
    prompt = build_prompt(theorem_proof_text)
    last_error = "malformed triage response"
    for _ in range(2):
        try:
            parsed = _parse(call_model(prompt))
            if parsed is None:
                last_error = "malformed triage response"
        except Exception as e:
            parsed = None  # backend failure → fail closed, not crash
            last_error = f"backend failure: {e}"
        if parsed is not None:
            parsed["executed_by"] = "harness"
            return parsed
    return {"suspects": [], "all_clear": False, "executed_by": "harness",
            "error": last_error, "partial": True}
