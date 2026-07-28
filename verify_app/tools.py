from __future__ import annotations

import json
from dataclasses import dataclass
from typing import Any, Callable

from rlverify.mcp_server import HarnessSession


def _object(properties: dict, required: list[str] | None = None) -> dict:
    return {
        "type": "object",
        "properties": properties,
        "required": required or [],
        "additionalProperties": False,
    }


_S = {"type": "string"}
_I = {"type": "integer"}
_B = {"type": "boolean"}
_SA = {"type": "array", "items": {"type": "string"}}


TOOL_SCHEMAS: dict[str, dict] = {
    "begin": _object({"fixture": _S}, ["fixture"]),
    "search": _object({"query": _S, "limit": _I}, ["query"]),
    "library_search": _object(
        {"block": _S, "statement": _S, "imports": _SA},
        ["block", "statement"],
    ),
    "refute": _object(
        {"block": _S, "code": _S, "description": _S},
        ["block", "code", "description"],
    ),
    "certify_step": _object(
        {"block": _S, "code": _S, "description": _S},
        ["block", "code", "description"],
    ),
    "report_failure": _object(
        {"kind": _S, "reason": _S, "block": _S},
        ["kind", "reason"],
    ),
    "main_unformalizable": _object({"reason": _S}, ["reason"]),
    "resolve_block": _object(
        {
            "name": _S,
            "statement_nl": _S,
            "kind": {"type": "string",
                     "enum": ["library", "instantiation", "novel"]},
            "library": _S,
            "instantiation": _S,
            "depends_on": _SA,
            "source_excerpt": _S,
            "source_char_start": _I,
            "source_char_end": _I,
            "formal_signature": _S,
            "hypotheses": _SA,
        },
        [
            "name", "statement_nl", "depends_on", "source_excerpt",
            "formal_signature", "hypotheses",
        ],
    ),
    "audit_invocation": _object(
        {
            "caller": _S,
            "invoked": _S,
            "hypotheses": _SA,
            "checks": _SA,
            "outcome": {
                "type": "string",
                "enum": [
                    "CLEAR", "HYPOTHESIS_VIOLATION", "CIRCULAR",
                    "UNCERTAIN",
                ],
            },
            "reason": _S,
            "conditioning": _S,
        },
        [
            "caller", "invoked", "hypotheses", "checks", "outcome",
            "reason",
        ],
    ),
    "adjudicate_near_match": _object(
        {"block": _S, "reason": _S},
        ["block", "reason"],
    ),
    "falsify_block": _object(
        {
            "block": _S,
            "verdict": {
                "type": "string",
                "enum": ["REFUTED", "PASSED", "VACUOUS", "SKIPPED"],
            },
            "instances": _I,
            "hyp_satisfied": _I,
            "claim": _S,
        },
        ["block", "verdict"],
    ),
    "falsify_run": _object(
        {"block": _S, "sampler_code": _S, "n": _I, "seed": _I},
        ["block", "sampler_code"],
    ),
    "status": _object({}),
    "compile": _object({"code": _S}, ["code"]),
    "sketch": _object(
        {"skeleton_code": _S, "expected_blocks": _SA},
        ["skeleton_code", "expected_blocks"],
    ),
    "discharge": _object(
        {"block": _S, "statement": _S, "proof": _S, "imports": _SA},
        ["block", "statement", "proof", "imports"],
    ),
    "audit_block": _object(
        {
            "block": _S,
            "hypothesis_minimality": _S,
            "independence": _S,
            "statement_claim": _S,
            "satisfiability": _S,
            "notes": _S,
        },
        [
            "block", "hypothesis_minimality", "independence",
            "statement_claim", "satisfiability",
        ],
    ),
    "assemble": _object(
        {"statement": _S, "proof": _S, "imports": _SA},
        ["statement", "proof", "imports"],
    ),
    "evaluate_library_candidate": _object(
        {
            "block": _S,
            "reusable": _B,
            "reason": _S,
            "generalized_name": _S,
            "target_dir": _S,
            "docstring": _S,
            "generalized_code": _S,
        },
        ["block", "reusable", "reason"],
    ),
    "register_axiom_lifecycle": _object(
        {
            "name": _S,
            "statement": _S,
            "claimed_meaning": _S,
            "reference": _S,
            "backlog_entry": _S,
            "hypotheses_checked": _B,
        },
        [
            "name", "statement", "claimed_meaning", "reference",
            "backlog_entry", "hypotheses_checked",
        ],
    ),
    "structural_assemble": _object(
        {"code": _S, "placeholder_blocks": _SA},
        ["code", "placeholder_blocks"],
    ),
}


TOOL_DESCRIPTIONS = {
    "begin": "Start the verification session. This must be the first tool call.",
    "search": "Search the trusted Lean premise library.",
    "library_search": "Run and persist the exact type-directed reuse gate.",
    "refute": "Compile a Lean counterexample to an invalid inference.",
    "certify_step": "Compile a positive certificate for a disputed inference.",
    "report_failure": (
        "Report a candidate WRONG, PROOF_INVALID, INCOMPLETE, MISMATCH, "
        "HYPOTHESIS_VIOLATION, or CIRCULAR finding; trusted scope matching "
        "determines the final verdict."
    ),
    "main_unformalizable": "Record a terminal infrastructure-level formalization gap.",
    "resolve_block": "Classify one proof block as library, instantiation, or novel.",
    "audit_invocation": "Audit every hypothesis at one actual dependency invocation.",
    "adjudicate_near_match": "Adjudicate a logged constant or logarithm near-match.",
    "falsify_block": "Record an agent-attested numeric falsification outcome.",
    "falsify_run": "Run generated sampler code through the harness falsification path.",
    "status": "Inspect dependency, sketch, discharge, and gate state.",
    "compile": "Sandbox-compile candidate Lean code for iteration.",
    "sketch": "Compile a sorried skeleton to check proof decomposition.",
    "discharge": "Prove and compile one atomic proof block.",
    "audit_block": "Record all four anti-vacuity checks for a novel block.",
    "assemble": "Assemble the final theorem and run the kernel axiom audit.",
    "evaluate_library_candidate": "Evaluate one discharged novel block for reuse.",
    "register_axiom_lifecycle": "Register reference, backlog, and meaning for a custom axiom.",
    "structural_assemble": "Compile all salvageable structure modulo explicit failed blocks.",
}


@dataclass
class ToolResult:
    content: str
    terminal: bool = False


class ToolRegistry:
    """Validated API-facing view of the existing HarnessSession."""

    def __init__(self, session: HarnessSession):
        self.session = session
        self.begun = False
        self.terminal = False

    def openai_tools(self) -> list[dict]:
        return [
            {
                "type": "function",
                "function": {
                    "name": name,
                    "description": TOOL_DESCRIPTIONS[name],
                    "parameters": schema,
                },
            }
            for name, schema in TOOL_SCHEMAS.items()
        ]

    def execute(self, name: str, raw_arguments: str) -> ToolResult:
        if name not in TOOL_SCHEMAS:
            return ToolResult(f"TOOL_ERROR: unknown tool {name!r}")
        if self.terminal:
            return ToolResult("TOOL_ORDER_ERROR: session already reached a terminal action",
                              terminal=True)
        if not self.begun and name != "begin":
            return ToolResult("TOOL_ORDER_ERROR: call begin before any other tool")
        if self.begun and name == "begin":
            return ToolResult("TOOL_ORDER_ERROR: begin was already called")
        try:
            args = json.loads(raw_arguments or "{}")
        except ValueError:
            return ToolResult("TOOL_ARGUMENT_ERROR: arguments are not valid JSON")
        if not isinstance(args, dict):
            return ToolResult("TOOL_ARGUMENT_ERROR: arguments must be an object")
        error = _validate_args(name, args)
        if error:
            return ToolResult(f"TOOL_ARGUMENT_ERROR: {error}")

        method: Callable[..., Any] = getattr(self.session, name)
        try:
            content = str(method(**args))
        except Exception as exc:
            return ToolResult(
                f"TOOL_EXECUTION_ERROR: {type(exc).__name__}: {str(exc)[:500]}"
            )

        if name == "begin":
            self.begun = True
        terminal = name in {
            "report_failure", "main_unformalizable", "structural_assemble",
        }
        if name in {"assemble", "evaluate_library_candidate"}:
            terminal = self._assembled_with_library_evaluations_complete()
        if terminal:
            self.terminal = True
        return ToolResult(content=content, terminal=terminal)

    def _assembled_with_library_evaluations_complete(self) -> bool:
        rec = self.session.d._result
        if rec is None or not (rec.compiled and rec.main_code):
            return False
        evaluated = {
            str(row.get("generalized_from") or row.get("name") or "")
            for row in rec.library_evaluations
        }
        return all(
            lemma.name in evaluated
            for lemma in rec.lemmas
            if lemma.kind == "novel" and lemma.discharged
        )


def _validate_args(name: str, args: dict) -> str | None:
    schema = TOOL_SCHEMAS[name]
    allowed = set(schema["properties"])
    unexpected = set(args) - allowed
    if unexpected:
        return f"unexpected fields: {sorted(unexpected)}"
    for key in schema.get("required", []):
        if key not in args:
            return f"missing required field {key!r}"
    for key, value in args.items():
        expected = schema["properties"][key].get("type")
        if expected == "string" and not isinstance(value, str):
            return f"{key!r} must be a string"
        if expected == "integer" and not isinstance(value, int):
            return f"{key!r} must be an integer"
        if expected == "boolean" and not isinstance(value, bool):
            return f"{key!r} must be a boolean"
        if expected == "array" and (
            not isinstance(value, list) or
            not all(isinstance(item, str) for item in value)
        ):
            return f"{key!r} must be a list of strings"
        enum = schema["properties"][key].get("enum")
        if enum and value not in enum:
            return f"{key!r} must be one of {enum}"
    return None
