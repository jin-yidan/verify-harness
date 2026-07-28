"""A2 — sealed hypothesis audit, executed by TRUSTED harness code.

The harness counterpart to the `/verify-hypothesis-audit` component: at every
point one block invokes another (or a library lemma), list ALL hypotheses of the
invoked result and check each against the actual argument — the load-bearing
detector for HYPOTHESIS_VIOLATION and conditional-conclusion CIRCULARITY.

Unlike sealed triage (which is sound tool-free, because it needs only the proof
text), this audit needs the invoked results' FULL hypothesis sets, which for a
library citation live in the corpus, not the proof. So it is **sealed-from-the-
claim but corpus-READING**: a two-call design mirroring back-translation —
  1. EXTRACT: a context-free call lists every invoked result (block or library
     lemma) named in the proof.
  2. (harness) ENRICH: for each name, `lookup(name)` returns the corpus signature
     (the `statement` field carries the hypotheses). Mathlib `#check` enrichment
     is a future tier — until then, a citation whose signature can't be resolved
     is flagged UNCERTAIN, never CLEAR (honest partialness, not false comfort).
  3. AUDIT: a second call does the 4-point audit over the proof + the resolved
     signatures.

WEIGHT = **prioritization-only** (`verify-output-contract.md`): the result is a
scrutiny hint stamped ``executed_by="harness"``, NOT a verdict and NOT a
downgrade gate. It never enters `gate_failures` — a kernel-clean proof is never
turned UNGATED on a prose suspicion. It joins the agent's suspect hint so the
flagged sites are scrutinised first.
"""
from __future__ import annotations

import json
from typing import Callable

CallModel = Callable[[str], str]
Lookup = Callable[[str], "str | None"]

# Port of the verify-hypothesis-audit checklist (the discriminating rules, not
# just the category names — those rules catch the documented failures: a skipped
# independence hypothesis, a conditional-conclusion cycle).
EXTRACT_INSTRUCTION = (
    "You are a proof reader with no other context and no tools. List EVERY point\n"
    "where this proof invokes a named prior result — a block it proved earlier OR\n"
    "a named library/Mathlib lemma (concentration inequality, fixed-point theorem,\n"
    "etc.). Do not judge correctness yet; just inventory the invocations. Output\n"
    'JSON only: {"invocations": [{"site": "<step/where>", "invoked": "<name>"}]}'
)

AUDIT_INSTRUCTION = (
    "You are an adversarial hypothesis auditor with no tools. For EACH invocation\n"
    "below, of the invoked result list ALL its hypotheses and check each against\n"
    "the argument the proof actually supplies. Rules:\n"
    "- A proof that verifies one hypothesis (boundedness) while silently skipping\n"
    "  another (independence, measurability) is a RED FLAG, not a reassurance.\n"
    "- Hypothesis-substitution camouflage: 'which satisfies [easy condition]' often\n"
    "  masks an unchecked [hard condition]. Flag it.\n"
    "- Conditional-conclusion / cycle: if a block's conclusion holds only 'on the\n"
    "  event E' / 'given X', E is a hypothesis of EVERY downstream use. If E is (or\n"
    "  implies) the conclusion of a block that depends on this one, it is CIRCULAR\n"
    "  even when the citation graph is acyclic (the Borkar-Meyn stability gap).\n"
    "- For an invoked result whose signature is NOT in the SIGNATURES block, you do\n"
    "  NOT know its full hypotheses — mark that site UNCERTAIN, never CLEAR.\n"
    "Per site outcome ∈ {CLEAR, HYPOTHESIS_VIOLATION, CIRCULAR, UNCERTAIN}. This is\n"
    "a PRIORITIZATION signal, not a verdict. Output JSON only:\n"
    '{"findings": [{"site": "<where>", "invoked": "<name>",\n'
    '  "outcome": "CLEAR|HYPOTHESIS_VIOLATION|CIRCULAR|UNCERTAIN",\n'
    '  "missed_hypothesis": "<which, or empty>", "why": "<one line>"}],\n'
    ' "overall": "CLEAR|HYPOTHESIS_VIOLATION|CIRCULAR|UNCERTAIN"}'
)

_OUTCOMES = {"CLEAR", "HYPOTHESIS_VIOLATION", "CIRCULAR", "UNCERTAIN"}
_RANK = {"CLEAR": 0, "UNCERTAIN": 1,
         "HYPOTHESIS_VIOLATION": 2, "CIRCULAR": 3}


def extract_prompt(proof_text: str) -> str:
    """Sealed invocation-inventory prompt = instruction + ONLY the proof text."""
    return f"{EXTRACT_INSTRUCTION}\n\n{proof_text}"


def audit_prompt(proof_text: str, signatures: str, inventory: str = "") -> str:
    sigs = signatures.strip() or "(none resolved — treat all citations as UNCERTAIN)"
    inv = inventory.strip() or "(none extracted)"
    return (f"{AUDIT_INSTRUCTION}\n\nINVOCATIONS to audit:\n{inv}\n\n"
            f"SIGNATURES (best-effort corpus matches; verify each is really the "
            f"cited result):\n{sigs}\n\nPROOF:\n{proof_text}")


def _json(raw: str) -> dict | None:
    raw = raw.strip()
    s, e = raw.find("{"), raw.rfind("}")
    if s == -1 or e <= s:
        return None
    try:
        obj = json.loads(raw[s:e + 1])
    except json.JSONDecodeError:
        return None
    return obj if isinstance(obj, dict) else None


def _safe(call_model: CallModel, prompt: str) -> tuple[str, bool]:
    """(text, errored). Backend failure → errored=True so we fail closed, never
    silently CLEAR."""
    try:
        return (call_model(prompt) or "").strip(), False
    except Exception:
        return "", True


def _enrich(invocations: list, lookup: Lookup | None) -> tuple[str, list]:
    """Resolve each invoked name to a signature via the corpus lookup. Returns
    (signatures_block, resolved_names)."""
    if lookup is None:
        return "", []
    lines, resolved = [], []
    seen = set()
    for inv in invocations:
        name = (inv or {}).get("invoked") if isinstance(inv, dict) else None
        if not name or name in seen:
            continue
        seen.add(name)
        try:
            sig = lookup(name)
        except Exception:
            sig = None
        if sig:
            lines.append(f"{name}: {sig}")
            resolved.append(name)
    return "\n".join(lines), resolved


def _fail(reason: str) -> dict:
    # Fail CLOSED toward scrutiny: never report CLEAR when the audit didn't run.
    return {"findings": [], "overall": "ERROR", "reason": reason,
            "resolved": [], "partial": True, "executed_by": "harness"}


def _text(value) -> str:
    """One-line user text that cannot masquerade as verifier authority."""
    s = "" if value is None else str(value)
    s = " ".join(s.split())
    return s.replace("VERIFIED", "verified").replace("UNVERIFIED", "unverified")


def _normalise_findings(rows: list) -> tuple[list[dict], bool]:
    findings: list[dict] = []
    malformed = False
    for row in rows:
        if not isinstance(row, dict):
            malformed = True
            findings.append({
                "site": "?",
                "invoked": "?",
                "outcome": "UNCERTAIN",
                "missed_hypothesis": "",
                "why": "malformed audit row; check by hand",
            })
            continue
        outcome = row.get("outcome")
        outcome = outcome if isinstance(outcome, str) else "UNCERTAIN"
        outcome = outcome.strip().upper()
        if outcome not in _OUTCOMES:
            outcome = "UNCERTAIN"
            malformed = True
        findings.append({
            "site": _text(row.get("site") or "?"),
            "invoked": _text(row.get("invoked") or "?"),
            "outcome": outcome,
            "missed_hypothesis": _text(row.get("missed_hypothesis") or ""),
            "why": _text(row.get("why") or ""),
        })
    return findings, malformed


def _derive_overall(findings: list[dict], *, partial: bool) -> str:
    if not findings:
        return "UNCERTAIN" if partial else "CLEAR"
    worst = max((_RANK.get(f.get("outcome", "UNCERTAIN"), 1) for f in findings),
                default=0)
    if worst >= _RANK["CIRCULAR"]:
        return "CIRCULAR"
    if worst >= _RANK["HYPOTHESIS_VIOLATION"]:
        return "HYPOTHESIS_VIOLATION"
    if partial or worst >= _RANK["UNCERTAIN"]:
        return "UNCERTAIN"
    return "CLEAR"


def sealed_hypothesis_audit(statement: str, proof: str, call_model: CallModel,
                            lookup: Lookup | None = None) -> dict:
    """Run the trusted sealed hypothesis audit (corpus-reading, two calls).

    Returns a record stamped ``executed_by="harness"``:
      {findings: [...], overall: <outcome>, resolved: [names], partial: bool}
    `partial=True` whenever some citation could not be resolved to a signature
    (so a CLEAR is "clear among what we could check", not a guarantee). Fail
    closed: a backend failure or unparseable reply (after one retry) yields
    overall="ERROR" with empty findings — NEVER a silent CLEAR.

    PRIORITIZATION-ONLY: the caller uses this to order scrutiny; it must not feed
    `gate_failures` or downgrade a verdict.
    """
    text = f"{statement}\n\n{proof}"
    # 1. EXTRACT invocations (sealed, proof-only) — retry + fail-closed, like the
    #    audit call. extract_ok tracks whether we actually got an inventory: if
    #    not, we do NOT know what the proof cites, so the result can't be CLEAR.
    invocations, extract_ok = [], False
    for _ in range(2):
        raw, err = _safe(call_model, extract_prompt(text))
        if err:
            return _fail("extract call failed (grader timeout/crash)")
        parsed = _json(raw)
        if parsed is not None and isinstance(parsed.get("invocations"), list):
            invocations, extract_ok = parsed["invocations"], True
            break

    # 2. ENRICH via the corpus lookup.
    signatures, resolved = _enrich(invocations, lookup)
    invoked_names = {i.get("invoked") for i in invocations
                     if isinstance(i, dict) and i.get("invoked")}
    # partial unless the inventory parsed AND every cited result was resolved to a
    # signature — so a CLEAR can never rest on an unknown inventory or an
    # unresolved citation (the airtight backstop the review asked for).
    partial = (not extract_ok) or (len(resolved) < len(invoked_names))
    inventory = "\n".join(f"- {i.get('site', '?')}: {i.get('invoked', '?')}"
                          for i in invocations if isinstance(i, dict))

    # 3. AUDIT (sealed, proof + inventory + resolved signatures), retry on parse.
    for _ in range(2):
        raw, err = _safe(call_model, audit_prompt(text, signatures, inventory))
        if err:
            return _fail("audit call failed (grader timeout/crash)")
        parsed = _json(raw)
        if parsed is not None and isinstance(parsed.get("findings"), list):
            findings, malformed = _normalise_findings(parsed["findings"])
            partial = partial or malformed
            overall = _derive_overall(findings, partial=partial)
            return {"findings": findings, "overall": overall,
                    "resolved": resolved, "partial": partial, "executed_by": "harness"}
    return _fail("audit output unparseable")
