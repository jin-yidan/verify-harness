"""Extract theorem/proof pairs from LaTeX or plain text files."""

from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path


@dataclass
class ExtractedTheorem:
    label: str
    theorem: str
    proof: str
    kind: str  # theorem, lemma, proposition, corollary
    source_file: str = ""
    line_number: int = 0
    external: bool = False  # an environment that merely restates a cited result

    def to_fixture(self) -> dict:
        return {
            "id": self.label,
            "theorem": self.theorem.strip(),
            "proof": self.proof.strip(),
            "reference": f"Extracted from {self.source_file}",
            "library_match": None,
            "external": self.external,
        }


# A theorem-env title that signals the body is a restatement of an external,
# already-published result — these route to the library/axiom lane in Phase 0,
# not the per-component verification lane.
_EXTERNAL_TITLE = re.compile(
    r"\\cite\b"                       # [... in \cite{foo}]
    r"|\bin\s*~?\s*\[\d"              # "in [12]"
    r"|\brestatement\b"              # "Restatement of Lemma 3 of ..."
    r"|\bdue to\b"                    # "due to [Foo]"
    r"|\([^)]*\d{4}[a-z]?\)",        # parenthetical year cite, e.g. "(Jin et al., 2018)"
    re.IGNORECASE,
)


_THEOREM_ENVS = ["theorem", "lemma", "proposition", "corollary"]
_ENV_PATTERN = re.compile(
    r"\\begin\{(" + "|".join(_THEOREM_ENVS) + r")\}"
    r"(?:\[([^\]]*)\])?"
    r"(?:\{([^}]*)\})?"
    r"\s*(?:\\label\{([^}]*)\})?"
    r"(.*?)"
    r"\\end\{\1\}",
    re.DOTALL,
)
_PROOF_PATTERN = re.compile(
    r"\\begin\{proof\}(.*?)\\end\{proof\}",
    re.DOTALL,
)


def _clean_latex(text: str) -> str:
    text = re.sub(r"\\textbf\{([^}]*)\}", r"\1", text)
    text = re.sub(r"\\emph\{([^}]*)\}", r"\1", text)
    text = re.sub(r"\\textit\{([^}]*)\}", r"\1", text)
    text = re.sub(r"\\cite\{[^}]*\}", "", text)
    text = re.sub(r"\\ref\{[^}]*\}", "REF", text)
    text = re.sub(r"\\eqref\{[^}]*\}", "EQ", text)
    text = re.sub(r"%.*$", "", text, flags=re.MULTILINE)
    text = re.sub(r"\s+", " ", text)
    return text.strip()


def extract_from_latex(text: str, source_file: str = "") -> list[ExtractedTheorem]:
    # Defensively strip LaTeX comments so commented-out environments (a common
    # draft-paper artifact) are never matched, even if the caller passed raw
    # source that did not go through ingest.normalize_latex.
    from rlverify.ingest import strip_latex_comments
    text = strip_latex_comments(text)

    theorems = list(_ENV_PATTERN.finditer(text))
    proofs = list(_PROOF_PATTERN.finditer(text))

    results: list[ExtractedTheorem] = []
    used_proofs: set[int] = set()

    for i, m in enumerate(theorems):
        kind = m.group(1)
        bracket_title = m.group(2) or ""  # the [...] header — carries any \cite
        title = bracket_title or m.group(3) or ""
        label = m.group(4) or ""
        is_external = bool(_EXTERNAL_TITLE.search(bracket_title))
        body = _clean_latex(m.group(5))

        thm_end = m.end()
        proof_text = ""
        for j, p in enumerate(proofs):
            if j in used_proofs:
                continue
            if p.start() >= thm_end:
                gap = text[thm_end:p.start()].strip()
                gap_no_ws = re.sub(r"\s+", "", gap)
                if not gap_no_ws or not re.search(
                    r"\\begin\{(" + "|".join(_THEOREM_ENVS) + r")\}", gap
                ):
                    proof_text = _clean_latex(p.group(1))
                    used_proofs.add(j)
                    break

        # External (cited) results carry no proof in the paper — keep them so
        # Phase 0 can route them to the library/axiom lane. Everything else must
        # have an associated proof block to count as a verifiable component.
        if not proof_text and not is_external:
            continue

        if not label:
            slug = re.sub(r"[^a-z0-9]+", "_", (title or kind).lower()).strip("_")
            label = f"{slug}_{i+1}" if slug else f"{kind}_{i+1}"

        line_number = text[:m.start()].count("\n") + 1

        header = f"{kind.capitalize()}"
        if title:
            header += f" ({title})"
        theorem_text = f"{header}. {body}"

        results.append(ExtractedTheorem(
            label=label,
            theorem=theorem_text,
            proof=proof_text,
            kind=kind,
            source_file=source_file,
            line_number=line_number,
            external=is_external,
        ))

    return results


# Prose patterns that introduce a paper's headline result when it is NOT wrapped
# in a theorem environment (commented out, or only stated inline in the text).
_MAIN_PROSE = re.compile(
    r"(?:^|[.\s])"
    r"(?:we\s+(?:show|prove|establish|obtain)\s+that\b"
    r"|our\s+main\s+(?:result|theorem|contribution)\b"
    r"|the\s+main\s+(?:result|theorem)\b"
    r"|we\s+(?:show|prove)\s+the\s+following)"
    r"(.{0,600}?[.])",
    re.IGNORECASE | re.DOTALL,
)


def find_main_claims(text: str, source_file: str = "") -> list[ExtractedTheorem]:
    """Surface candidate main-result statements stated only in prose.

    Used as a Phase-0 fallback when no (uncommented) ``theorem`` environment
    carries the paper's headline bound — e.g. drafts where the main theorem is
    commented out and restated in running text. Returns unproved claim stubs
    (empty proof) for the agent to reconcile; never a substitute for an actual
    theorem environment when one exists.
    """
    from rlverify.ingest import strip_latex_comments
    text = strip_latex_comments(text)
    if _ENV_PATTERN.search(text) and "\\begin{theorem}" in text:
        return []  # a real theorem environment exists; no fallback needed
    out: list[ExtractedTheorem] = []
    for i, m in enumerate(_MAIN_PROSE.finditer(text)):
        claim = _clean_latex(m.group(0))
        if len(claim) < 40:
            continue
        out.append(ExtractedTheorem(
            label=f"main_claim_prose_{i+1}",
            theorem=claim,
            proof="",
            kind="theorem",
            source_file=source_file,
        ))
    return out


def extract_from_text(text: str, source_file: str = "") -> list[ExtractedTheorem]:
    """Extract theorem/proof from plain text using section headers.

    Expected format:
        Theorem: <statement>
        Proof: <proof text>
    or:
        THEOREM 1. <statement>
        PROOF. <proof text>
    """
    pattern = re.compile(
        r"(?:^|\n)\s*"
        r"(?:theorem|lemma|proposition|corollary)\s*"
        r"(?:(\d+(?:\.\d+)*)\.?\s*)?"
        r"(?:\(([^)]*)\)\s*)?"
        r"[.:]?\s*"
        r"(.*?)"
        r"(?=\n\s*(?:proof|theorem|lemma|proposition|corollary)\b|\Z)",
        re.IGNORECASE | re.DOTALL,
    )
    proof_pattern = re.compile(
        r"(?:^|\n)\s*proof[.:]?\s*(.*?)(?=\n\s*(?:theorem|lemma|proposition|corollary|\\qed|□)\b|\Z)",
        re.IGNORECASE | re.DOTALL,
    )

    thm_matches = list(pattern.finditer(text))
    proof_matches = list(proof_pattern.finditer(text))

    results: list[ExtractedTheorem] = []
    used_proofs: set[int] = set()

    for i, m in enumerate(thm_matches):
        number = m.group(1) or ""
        title = m.group(2) or ""
        body = re.sub(r"\s+", " ", m.group(3)).strip()

        if not body:
            continue

        proof_text = ""
        for j, p in enumerate(proof_matches):
            if j in used_proofs:
                continue
            if p.start() >= m.start():
                proof_text = re.sub(r"\s+", " ", p.group(1)).strip()
                used_proofs.add(j)
                break

        if not proof_text:
            continue

        label = ""
        if number:
            label = f"thm_{number.replace('.', '_')}"
        elif title:
            label = re.sub(r"[^a-z0-9]+", "_", title.lower()).strip("_")
        else:
            label = f"theorem_{i+1}"

        results.append(ExtractedTheorem(
            label=label,
            theorem=body,
            proof=proof_text,
            kind="theorem",
            source_file=source_file,
        ))

    return results


def extract_file(path: str | Path) -> list[ExtractedTheorem]:
    p = Path(path)
    text = p.read_text(errors="replace")
    source = p.name

    if p.suffix == ".tex":
        results = extract_from_latex(text, source)
    else:
        results = extract_from_text(text, source)

    if not results:
        results = extract_from_text(text, source)

    return results
