"""W3 — sealed back-translation audit, executed by TRUSTED harness code.

Two isolated steps, both backend-agnostic:
1. RENDER: a context-free call that sees ONLY the Lean statement (variable names
   treated as opaque) and renders it back into plain English. It must NOT see
   the paper / original claim — that isolation is the whole point.
2. JUDGE: a second call that diffs the rendering against the original NL claim
   across the 5-category rubric (quantifier binding, relation, constants,
   hypothesis set, object types) and returns MATCH / NOTE / MISMATCH.

The runner performs both and records the verdict into the session, so the agent
under test cannot pass off an unfaithful formalization as MATCH.
"""
from __future__ import annotations

import json
from typing import Callable

CallModel = Callable[[str], str]

# Ported from .claude/commands/verify-full-process.md back-translation audit (the
# discriminating rules, not just the category names — those rules are what
# catch the documented shipped failures, e.g. minimax compact→finite).
RENDER_INSTRUCTION = (
    "You are a Lean 4 reader with no other context and no tools. Render the\n"
    "following Lean statement into plain English. Rules:\n"
    "- Treat every identifier as an OPAQUE symbol. NAMES ARE NOT EVIDENCE: a\n"
    "  variable called `entropy` is just a real number unless a hypothesis\n"
    "  constrains it; say 'an arbitrary real number, unconstrained'.\n"
    "- State every quantifier and its binding, every hypothesis, the relation\n"
    "  and its DIRECTION, and all constants EXACTLY as written (2 ≠ 4;\n"
    "  2·log K/β ≠ log K/β).\n"
    "- A bare ℝ/ℕ/type with no hypothesis is 'arbitrary/unconstrained'.\n"
    "- If the statement is trivially true or false, SAY SO and give the\n"
    "  instantiation that shows it.\n"
    "Output ONLY the English rendering."
)

JUDGE_INSTRUCTION = (
    "Compare a CLAIM with an independent English rendering of a Lean statement\n"
    "across 5 categories: quantifier binding, relation/direction, constants,\n"
    "hypothesis set, object types. MISMATCH triggers (any one ⇒ MISMATCH):\n"
    "- arbitrary-where-the-claim-is-specific (or vice versa);\n"
    "- a strengthened/weakened hypothesis (e.g. claim 'K ≥ 1' became 'log K ≥ 1');\n"
    "- a scalar standing in for a structured object (a number where the claim\n"
    "  needs a function/measure/policy);\n"
    "- any constant or relation-direction differing from the claim.\n"
    "NOTE = harmless wording/notation only. Output JSON only:\n"
    '{"verdict": "MATCH|NOTE|MISMATCH", "reason": "<one line>"}'
)

REFUTATION_JUDGE_INSTRUCTION = (
    "Compare a CLAIM with an independently rendered Lean theorem and decide "
    "whether it is a valid concrete COUNTEREXAMPLE. MATCH only if the rendering "
    "(1) instantiates "
    "objects allowed by the claim, (2) establishes the relevant premises or "
    "context, and (3) explicitly negates the claim's conclusion on that same "
    "instance. Every term in the claimed theorem must be DEFINED on the witness. "
    "Choosing an empty domain so that max, argmax, division, an inverse, or "
    "another required object is undefined is NOT a counterexample; classify it "
    "as UNDEFINED_TERM or MISSING_HYPOTHESIS. A concrete scalar/finite/rational "
    "instance of a universal claim is expected and is not a type mismatch. "
    "MISMATCH if it changes the disputed relation, omits a required premise, "
    "uses an object outside the claim's domain, or merely proves an unrelated "
    "fact. target_scope is MAIN_THEOREM only when the complete submitted theorem "
    "is instantiated and negated; otherwise use PROOF_STEP or WELL_DEFINEDNESS. "
    "Output JSON only:\n"
    '{"verdict":"MATCH|NOTE|MISMATCH","reason":"<one line>",'
    '"target_scope":"MAIN_THEOREM|PROOF_STEP|WELL_DEFINEDNESS",'
    '"finding_kind":"COUNTEREXAMPLE|INVALID_INFERENCE|MISSING_HYPOTHESIS|'
    'UNDEFINED_TERM|STATEMENT_MISMATCH",'
    '"premises_satisfied":true|false,"objects_well_defined":true|false,'
    '"conclusion_negated":true|false}'
)


def render_prompt(lean_statement: str, definitions: str = "") -> str:
    """Sealed render prompt = instruction + the Lean statement (+ any custom
    definitions it references; without them a non-Mathlib statement renders
    blind). NOTHING about the original claim appears here."""
    defs = f"\n\nDefinitions it references:\n{definitions}" if definitions.strip() else ""
    return f"{RENDER_INSTRUCTION}\n\n{lean_statement}{defs}"


def judge_prompt(
    original_claim: str, rendering: str, comparison: str = "match",
) -> str:
    instruction = (
        REFUTATION_JUDGE_INSTRUCTION
        if comparison == "refutation" else JUDGE_INSTRUCTION
    )
    return (f"{instruction}\n\nCLAIM:\n{original_claim}\n\n"
            f"RENDERING:\n{rendering}")


def _parse_verdict(raw: str, *, comparison: str = "match") -> dict | None:
    raw = raw.strip()
    s, e = raw.find("{"), raw.rfind("}")
    if s == -1 or e <= s:
        return None
    try:
        obj = json.loads(raw[s:e + 1])
    except json.JSONDecodeError:
        return None
    v = obj.get("verdict")
    if v not in ("MATCH", "NOTE", "MISMATCH"):
        return None
    parsed = {"verdict": v, "reason": obj.get("reason", "")}
    if comparison != "refutation":
        return parsed
    scopes = {"MAIN_THEOREM", "PROOF_STEP", "WELL_DEFINEDNESS"}
    kinds = {
        "COUNTEREXAMPLE",
        "INVALID_INFERENCE",
        "MISSING_HYPOTHESIS",
        "UNDEFINED_TERM",
        "STATEMENT_MISMATCH",
    }
    scope = str(obj.get("target_scope") or "").upper()
    kind = str(obj.get("finding_kind") or "").upper()
    flags = {
        key: obj.get(key)
        for key in (
            "premises_satisfied",
            "objects_well_defined",
            "conclusion_negated",
        )
    }
    if (
        scope not in scopes
        or kind not in kinds
        or any(not isinstance(value, bool) for value in flags.values())
    ):
        return None
    return {
        **parsed,
        "target_scope": scope,
        "finding_kind": kind,
        **flags,
    }


def _safe_call(call_model: CallModel, prompt: str) -> tuple[str, bool]:
    """Returns (text, errored). A backend FAILURE (timeout, missing binary,
    non-zero exit) sets errored=True so the caller can distinguish "the grader
    crashed" from "the model genuinely returned nothing" — the two must not read
    the same on the verdict line (a grader timeout is not a proof defect)."""
    try:
        return (call_model(prompt) or "").strip(), False
    except Exception:
        return "", True


def back_translate(lean_statement: str, original_claim: str,
                   call_model: CallModel, target: str = "main",
                   definitions: str = "",
                   comparison: str = "match") -> dict:
    """Run the trusted sealed back-translation. Returns a record ready for the
    run JSON, stamped ``executed_by="harness"`` (provenance the agent cannot
    forge). Fail-closed, but with two DISTINCT failure verdicts:
      • ``GATE_ERROR`` — the grader itself failed (timeout/crash). Still
        downgrades a VERIFIED (fail-safe), but renders as "gate failed to
        execute, not a proof defect — re-run", so a correct proof isn't
        mislabeled as an unfaithful formalization.
      • ``MISMATCH``  — the grader RAN and judged the formalization unfaithful
        (or returned empty/unparseable content, which is itself suspicious)."""
    base = {"target": target, "executed_by": "harness"}
    rendering, errored = _safe_call(call_model, render_prompt(lean_statement, definitions))
    if errored:
        return {**base, "verdict": "GATE_ERROR",
                "reason": "render call failed (grader timeout/crash)", "rendering": ""}
    if not rendering:
        return {**base, "verdict": "MISMATCH",
                "reason": "render empty — failing closed", "rendering": ""}
    for _ in range(2):
        raw, errored = _safe_call(
            call_model, judge_prompt(original_claim, rendering, comparison)
        )
        if errored:
            return {**base, "verdict": "GATE_ERROR",
                    "reason": "judge call failed (grader timeout/crash)", "rendering": rendering}
        parsed = _parse_verdict(raw, comparison=comparison)
        if parsed is not None:
            return {**base, **parsed, "rendering": rendering}
    return {**base, "verdict": "MISMATCH",
            "reason": "judge output unparseable — failing closed", "rendering": rendering}
