from __future__ import annotations

import re
from pathlib import Path

from .types import ResolvedInput


_AT_PATH = re.compile(r'@(?:"([^"]+)"|\'([^\']+)\'|(\S+))')
_URL = re.compile(r"https?://\S+")
_THEOREM_SELECTOR = re.compile(
    r"\b(?:theorem|theroem|thm)\s*(?:number|no\.?)?\s*"
    r"([A-Za-z]?\d+(?:\.\d+)*|[A-Za-z][A-Za-z0-9_.-]*)",
    re.IGNORECASE,
)


def referenced_target(text: str) -> str | None:
    match = _AT_PATH.search(text)
    if match:
        return next(group for group in match.groups() if group is not None)
    match = _URL.search(text)
    return match.group(0).rstrip(".,)") if match else None


def _read_first(folder: Path, names: tuple[str, ...]) -> str:
    for name in names:
        path = folder / name
        if path.exists() and path.is_file():
            return path.read_text(errors="replace")
    return ""


def resolve_local_target(target: str) -> ResolvedInput:
    path = Path(target).expanduser()
    if not path.exists():
        raise FileNotFoundError(f"input not found: {path}")

    if path.is_dir():
        statement = _read_first(path, ("statement.md", "statement.txt", "theorem.md"))
        proof = _read_first(path, ("proof.md", "proof.txt", "sketch.md"))
        claim = _read_first(path, ("claim.md", "claim.txt")) or statement
        if not (statement or proof):
            raise ValueError(
                f"{path} does not contain statement.md/statement.txt and "
                "proof.md/proof.txt"
            )
        return ResolvedInput(
            statement=statement,
            proof=proof,
            claim=claim,
            source=str(path),
            target=str(path),
            name=path.name,
        )

    if path.suffix.lower() in {".md", ".txt"}:
        text = path.read_text(errors="replace")
        return parse_pasted_math(text, source=str(path), name=path.stem)

    # PDF/TeX and other supported paper files are resolved later through
    # harness.ingest, after a backend is available for theorem extraction.
    return ResolvedInput(source=str(path), target=str(path), name=path.stem)


def parse_pasted_math(text: str, source: str = "pasted text",
                      name: str = "interactive") -> ResolvedInput:
    theorem = re.search(
        r"(?is)\b(?:theorem|claim|statement)\s*:\s*(.*?)(?=\n\s*proof\s*:|\Z)",
        text,
    )
    proof = re.search(r"(?is)\bproof\s*:\s*(.*)\Z", text)
    statement_text = theorem.group(1).strip() if theorem else ""
    proof_text = proof.group(1).strip() if proof else ""
    if not statement_text and not proof_text:
        # A single pasted fragment is still useful for falsification, retrieval,
        # or follow-up prompting. Treat it as the claim.
        return ResolvedInput(
            claim=text.strip(), source=source, name=name,
        )
    return ResolvedInput(
        statement=statement_text,
        proof=proof_text,
        claim=statement_text,
        source=source,
        name=name,
    )


def resolve_from_message(message: str) -> ResolvedInput | None:
    # Explicit pasted theorem/proof text wins over any citations it contains.
    # Otherwise a Markdown link inside a submitted proof (for example a link to
    # Banach's theorem) is mistaken for the document the user wants verified.
    if re.search(r"(?i)\b(theorem|claim|statement|proof)\s*:", message):
        return parse_pasted_math(message)

    target = referenced_target(message)
    if target and not re.match(r"https?://", target):
        return resolve_local_target(target)
    if target:
        if _is_embedded_citation(message, target):
            return parse_pasted_math(message)
        selector = _requested_theorem(message)
        return ResolvedInput(
            source=target,
            target=target,
            theorem_selector=selector,
            selection_request=message,
            name="paper",
        )
    return None


def _requested_theorem(message: str) -> str:
    match = _THEOREM_SELECTOR.search(message)
    return match.group(1).strip() if match else ""


def _is_embedded_citation(message: str, target: str) -> bool:
    without_url = message.replace(target, " ")
    math_markers = (
        "$$",
        "\\begin{",
        "\\end{",
        "\\max",
        "\\sum",
        "\\mathbb",
        "\\E",
        "\\P",
    )
    return (
        len(without_url.strip()) > 500
        or sum(marker in message for marker in math_markers) >= 2
    )
