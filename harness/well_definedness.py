"""Deterministic, fail-closed checks for common statement definedness gaps.

This is deliberately narrow.  It does not try to prove that arbitrary prose is
well-defined; it recognizes operations whose displayed meaning requires a
nonempty finite domain and records an explicit hypothesis violation when that
side condition is absent.
"""
from __future__ import annotations

import re


def _compact(value: str) -> str:
    return " ".join(value.replace("\u2260", " != ").split())


def _states_nonempty(text: str, symbol: str, noun: str) -> bool:
    escaped = re.escape(symbol)
    patterns = (
        rf"\bNonempty\s+{escaped}\b",
        rf"\[\s*Nonempty\s+{escaped}\s*\]",
        rf"\b{re.escape(noun)}s?\b[^.;:]{{0,50}}\bnon[- ]?empty\b",
        rf"\bnon[- ]?empty\b[^.;:]{{0,50}}\b{re.escape(noun)}s?\b",
        rf"\b{escaped}\s*(?:!=|\\ne|is not)\s*(?:\u2205|emptyset|empty set)\b",
    )
    return any(re.search(pattern, text, flags=re.IGNORECASE) for pattern in patterns)


def audit_well_definedness(statement: str) -> dict:
    """Return deterministic hypothesis-audit-shaped findings.

    The checks are intentionally source-level and therefore support a
    ``HYPOTHESIS_VIOLATION``/restatement conclusion, never theorem falsity.
    """
    text = _compact(statement)
    lower = text.lower()
    findings: list[dict] = []

    finite_mdp = "finite markov decision process" in lower or "finite mdp" in lower
    action_domain = bool(
        re.search(r"\bfinite\s+action\s+(?:space|set)\s+A\b", text)
        or finite_mdp
    )
    action_max = bool(
        re.search(r"\barg\s*max\b|\bargmax\b", text, flags=re.IGNORECASE)
        or re.search(
            r"\bmax[^\n]{0,16}(?:a\s*∈|a\s*\\in|a\b)",
            text,
            flags=re.IGNORECASE,
        )
        or "max_a" in lower
    )
    if action_domain and action_max and not _states_nonempty(text, "A", "action"):
        findings.append({
            "site": "statement contract: action maximum",
            "invoked": "max/argmax over A",
            "outcome": "HYPOTHESIS_VIOLATION",
            "missed_hypothesis": "A is nonempty",
            "why": (
                "The displayed real-valued max/argmax over the action space is "
                "undefined when A is empty. This requires restatement; it is "
                "not a counterexample to the theorem."
            ),
            "finding_kind": "UNDEFINED_TERM",
            "target_scope": "WELL_DEFINEDNESS",
            "validator": "deterministic-well-definedness-v1",
        })

    state_domain = bool(
        re.search(r"\bfinite\s+state\s+(?:space|set)\s+S\b", text)
        or finite_mdp
    )
    max_norm = bool(
        ("sup norm" in lower or "\u2016" in text or "||" in text)
        and (
            re.search(
                r"\bmax[^\n]{0,16}(?:s\s*∈|s\s*\\in|s\b)",
                text,
                flags=re.IGNORECASE,
            )
            or "max_s" in lower
        )
    )
    if state_domain and max_norm and not _states_nonempty(text, "S", "state"):
        findings.append({
            "site": "statement contract: max-based sup norm",
            "invoked": "max over S",
            "outcome": "HYPOTHESIS_VIOLATION",
            "missed_hypothesis": "S is nonempty",
            "why": (
                "The displayed norm uses a real-valued maximum over S, which "
                "requires S to be nonempty as written."
            ),
            "finding_kind": "UNDEFINED_TERM",
            "target_scope": "WELL_DEFINEDNESS",
            "validator": "deterministic-well-definedness-v1",
        })

    return {
        "findings": findings,
        "overall": "HYPOTHESIS_VIOLATION" if findings else "CLEAR",
        "resolved": [],
        "partial": False,
        "executed_by": "harness",
        "validator": "deterministic-well-definedness-v1",
    }


def merge_with_hypothesis_audit(model_audit: dict, contract_audit: dict) -> dict:
    """Merge deterministic contract findings into the sealed model audit."""
    merged = dict(model_audit or {})
    rows = list(merged.get("findings") or [])
    seen = {
        (
            str(row.get("site") or ""),
            str(row.get("missed_hypothesis") or ""),
        )
        for row in rows if isinstance(row, dict)
    }
    for row in contract_audit.get("findings") or []:
        key = (
            str(row.get("site") or ""),
            str(row.get("missed_hypothesis") or ""),
        )
        if key not in seen:
            rows.append(row)
            seen.add(key)
    merged["findings"] = rows
    if contract_audit.get("findings"):
        merged["overall"] = "HYPOTHESIS_VIOLATION"
    merged["well_definedness"] = contract_audit
    merged["executed_by"] = "harness"
    return merged
