from __future__ import annotations

import re

from .types import Intent, RoutingDecision


_SLASH = {
    "/falsify": Intent.FALSIFY,
    "/hypotheses": Intent.HYPOTHESES,
    "/check": Intent.CHECK,
    "/verify": Intent.CHECK,
    "/statement": Intent.STATEMENT,
    "/retrieve": Intent.RETRIEVE,
    "/recheck": Intent.RECHECK,
    "/runs": Intent.RUNS,
    "/resume": Intent.RESUME,
    "/settings": Intent.SETTINGS,
    "/model": Intent.SETTINGS,
    "/help": Intent.HELP,
    "/quit": Intent.QUIT,
    "/exit": Intent.QUIT,
}

_NO_FULL = re.compile(
    r"\b(?:do not|don't|dont|without|not)\s+(?:run\s+)?(?:a\s+)?"
    r"(?:full|complete|fully)\s+(?:verification|verify|checking)\b"
    r"|\b(?:falsif(?:y|ication)|hypotheses?|hypothesis)\s+only\b",
    re.I,
)

_MATH_CONTEXT = re.compile(
    r"\b(?:theorem|lemma|proof|claim|inequalit(?:y|ies)|bound|derivation|"
    r"hypothes(?:is|es)|assumptions?|concentration|expectation|probability|"
    r"regret|bandit|mdp|martingale|lean|mathlib|certificate|axioms?)\b"
    r"|\.lean\b",
    re.I,
)


def _has_any(text: str, phrases: tuple[str, ...]) -> bool:
    return any(phrase in text for phrase in phrases)


def route(text: str) -> RoutingDecision:
    """Route a conversational request to the smallest matching workflow.

    This router is intentionally deterministic for explicit requests.  A model
    fallback can be added by the controller for genuinely ambiguous text.
    """
    raw = text.strip()
    if not raw:
        return RoutingDecision(Intent.UNKNOWN, 0.0, "empty request")

    first = raw.split(maxsplit=1)[0].lower()
    if first in _SLASH:
        intent = _SLASH[first]
        return RoutingDecision(intent, 1.0, "explicit interactive action",
                               forbids_full_check=(intent in {
                                   Intent.FALSIFY, Intent.HYPOTHESES,
                                   Intent.STATEMENT, Intent.RETRIEVE,
                               }))

    lower = raw.lower()
    forbids = bool(_NO_FULL.search(lower))

    if _has_any(lower, (
        "falsify", "counterexample", "disprove", "find a violation",
        "search for a flaw numerically", "try to break this",
        "try to break it", "test this claim for failures", "look for a witness",
        "find a failing example",
    )):
        return RoutingDecision(Intent.FALSIFY, 0.98,
                               "request asks for falsification", True)

    if _has_any(lower, (
        "check the hypotheses", "check hypotheses", "audit the hypotheses",
        "audit hypotheses", "missing assumption", "missing hypothesis",
        "assumptions satisfied", "hypotheses satisfied",
        "hypothesis violation", "check whether all hypotheses",
        "check whether the hypotheses", "are the hypotheses",
        "side conditions", "lemma applies", "apply this lemma",
        "circular reasoning", "circular dependency",
    )) or re.search(
        r"\b(?:check|audit)\b.*\b(?:every|all|the)?\s*hypothes(?:is|es)\b",
        lower,
    ):
        return RoutingDecision(Intent.HYPOTHESES, 0.98,
                               "request asks for a hypothesis audit", True)

    if _has_any(lower, (
        "back-translate", "backtranslate", "formal statement",
        "statement match", "formalize the statement", "statement faithful",
        "lean statement mean", "same theorem",
    )):
        return RoutingDecision(Intent.STATEMENT, 0.95,
                               "request asks to inspect the statement", True)

    if _has_any(lower, (
        "search the library", "search formalized", "find a theorem",
        "retrieve", "already formalized", "in mathlib",
        "existing lean lemma", "reuse a lemma",
    )):
        return RoutingDecision(Intent.RETRIEVE, 0.94,
                               "request asks for premise search", True)

    if _has_any(lower, (
        "recheck", "check the certificate", "audit the certificate",
        "recompile the certificate", "kernel-check this file",
    )) or (".lean" in lower and _has_any(lower, ("compile", "recompile", "axiom"))):
        return RoutingDecision(Intent.RECHECK, 0.96,
                               "request asks to recheck an artifact")

    if _has_any(lower, (
        "looks suspicious", "look suspicious", "identify suspicious",
        "find suspicious", "which steps are suspicious",
        "what looks wrong", "spot likely flaws",
    )):
        return RoutingDecision(
            Intent.TRIAGE,
            0.96,
            "request explicitly asks only for suspicious-step triage",
            forbids,
        )

    if _has_any(lower, (
        "fully verify", "full verification", "complete verification",
        "verify in lean", "prove this in lean", "formalize the proof",
        "kernel-verified proof", "kernel verified proof",
        "verify this proof", "verify my proof",
        "verify this theorem", "verify my theorem",
        "is this proof correct", "is my proof correct",
        "determine whether this proof is correct",
        "check this proof", "check my proof",
        "check this theorem", "check my theorem",
    )) or re.search(
        r"\bverify\b.*\b(?:proof|theorem|mathematical claim|derivation)\b",
        lower,
    ):
        if forbids:
            return RoutingDecision(Intent.TRIAGE, 0.85,
                                   "full verification is explicitly forbidden",
                                   True)
        return RoutingDecision(
            Intent.CHECK,
            0.95,
            "request selects full-verification preparation",
        )

    if _MATH_CONTEXT.search(lower) and (
        _has_any(lower, (
        "look at this proof", "review this proof",
        "check this argument", "look at this argument",
        "review this argument", "does this proof work", "what do you think",
        "check this derivation", "review this derivation",
        ))
        or re.search(
            r"\b(?:check|review|inspect|look at)\b.*"
            r"\b(?:proof|argument|derivation|theorem|claim)\b",
            lower,
        )
    ):
        return RoutingDecision(
            Intent.TRIAGE,
            0.88,
            "vague mathematical review starts with triage",
            forbids,
        )

    if lower in {"help", "what can you do", "commands"}:
        return RoutingDecision(Intent.HELP, 0.95, "help request")
    if lower in {"quit", "exit", "bye"}:
        return RoutingDecision(Intent.QUIT, 0.95, "quit request")

    return RoutingDecision(Intent.UNKNOWN, 0.25,
                           "no explicit verification scope detected", forbids)


def slash_actions() -> list[str]:
    return sorted(_SLASH)
