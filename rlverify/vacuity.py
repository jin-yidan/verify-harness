"""Detection of id-shaped (vacuous) theorem statements.

A theorem is *id-shaped* when its conclusion appears verbatim as the type of
one of its hypotheses — the proof is literally ``exact h``. Such scalar
stand-in lemmas verify nothing: a block resolved against one (e.g. an
``azuma_hoeffding_trajectory`` whose statement assumes the Azuma bound it
claims) is camouflage, not library coverage.

Used by ``scripts/audit_corpus_vacuity.py`` (corpus-wide report) and by the
driver (search-result markers + a resolve-time warning).
"""

from __future__ import annotations

import re


def split_top_level(sig: str) -> tuple[list[str], str] | None:
    """Split a theorem signature into (hypothesis types, conclusion).

    Scans bracket-aware for binder groups ``(... : TYPE)`` / ``{... : TYPE}``
    / ``[...]`` and the final top-level ``:`` that introduces the conclusion.
    Returns None when the signature can't be parsed.
    """
    m = re.match(r"\s*(?:private\s+|protected\s+|noncomputable\s+)*"
                 r"(?:theorem|lemma)\s+\S+", sig)
    if not m:
        return None
    rest = sig[m.end():]

    hyps: list[str] = []
    depth = 0
    i = 0
    start = -1
    conclusion_at = -1
    while i < len(rest):
        c = rest[i]
        if c in "({[":
            if depth == 0:
                start = i
            depth += 1
        elif c in ")}]":
            depth -= 1
            if depth == 0 and start >= 0:
                group = rest[start + 1:i]
                gd = 0
                for j, gc in enumerate(group):
                    if gc in "({[":
                        gd += 1
                    elif gc in ")}]":
                        gd -= 1
                    elif gc == ":" and gd == 0:
                        hyps.append(group[j + 1:].strip())
                        break
                start = -1
        elif c == ":" and depth == 0:
            conclusion_at = i
            break
        i += 1
    if conclusion_at < 0:
        return None
    return hyps, rest[conclusion_at + 1:].strip()


def _norm(s: str) -> str:
    return re.sub(r"\s+", " ", s).strip()


def is_id_shaped(statement: str) -> bool:
    """True iff the statement's conclusion equals one of its hypothesis types."""
    parsed = split_top_level(statement)
    if parsed is None:
        return False
    hyps, concl = parsed
    n_concl = _norm(concl)
    if not n_concl:
        return False
    return any(_norm(h) == n_concl for h in hyps)
