"""Researcher CLI ingestion: paper/link/paste -> reviewable fixture folder."""
from __future__ import annotations

import gzip
import io
import json
import re
import sys
import tarfile
import tempfile
import urllib.error
import urllib.request
from dataclasses import dataclass, field
from pathlib import Path, PurePosixPath
from typing import Callable

ROOT = Path(__file__).resolve().parent.parent
OUT_ROOT = ROOT / "rlverify-out"
USER_AGENT = "rlverify-harness/0.1 (paper ingestion; contact via repo)"

CallModel = Callable[[str], str]


class TheoremSelectionCancelled(RuntimeError):
    """The user cancelled paper theorem selection before verification."""


@dataclass
class PaperSource:
    text: str
    source: str
    kind: str
    paper_id: str
    notes: list[str] = field(default_factory=list)


@dataclass
class Candidate:
    label: str
    statement: str
    proof: str
    uses: list[str] = field(default_factory=list)
    source_kind: str = ""
    standing_context: str = ""
    kind: str = "theorem"
    external: bool = False
    is_main: bool = False


@dataclass
class Fixture:
    name: str
    path: Path
    statement: str
    proof: str
    claim: str
    source: PaperSource
    candidate: Candidate


def _slug(s: str, default: str = "paper") -> str:
    s = re.sub(r"[^A-Za-z0-9_.-]+", "_", s).strip("._-")
    return s[:80] or default


def _label_slug(s: str, default: str = "theorem") -> str:
    s = re.sub(r"[^A-Za-z0-9-]+", "_", s).strip("_-")
    return s[:80] or default


def needs_ingest(target: str | None, statement: str | None, proof: str | None) -> bool:
    if statement or proof or not target:
        return False
    if target == "-":
        return True
    if re.match(r"https?://", target):
        return True
    if parse_arxiv_id(target) and not Path(target).exists():
        return True
    p = Path(target)
    return p.is_file() and p.suffix.lower() in {".pdf", ".tex", ".md", ".txt"}


def _http_get(url: str, timeout: int = 60) -> tuple[bytes, str]:
    req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    try:
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            content_type = resp.headers.get("Content-Type", "")
            return resp.read(), content_type
    except urllib.error.HTTPError as e:
        if e.code == 403:
            raise RuntimeError("arXiv rejected the request (403): try the /pdf/ URL "
                               "or download manually and pass the file") from e
        raise


_ARXIV_NEW = re.compile(r"(\d{4}\.\d{4,5})(v\d+)?")
_ARXIV_OLD = re.compile(r"([a-z-]+(?:\.[A-Z]{2})?/\d{7})(v\d+)?", re.I)


def parse_arxiv_id(value: str) -> str | None:
    s = value.strip()
    if re.match(r"https?://", s) and "arxiv.org" not in s:
        return None
    if s.lower().startswith("arxiv:"):
        s = s.split(":", 1)[1]
    for marker in ("/abs/", "/pdf/", "/e-print/"):
        if marker in s:
            s = s.split(marker, 1)[1]
            break
    s = s.removesuffix(".pdf")
    m = _ARXIV_NEW.search(s) or _ARXIV_OLD.search(s)
    if not m:
        return None
    return m.group(1) + (m.group(2) or "")


def _safe_extract_tar(data: bytes, dest: Path) -> None:
    with tarfile.open(fileobj=io.BytesIO(data)) as tar:
        members = tar.getmembers()
        for member in members:
            path = PurePosixPath(member.name)
            if path.is_absolute() or ".." in path.parts:
                raise RuntimeError(f"unsafe tar path rejected: {member.name}")
            if member.issym() or member.islnk() or member.isdev():
                raise RuntimeError(f"unsafe tar member rejected: {member.name}")
        if hasattr(tarfile, "data_filter"):
            tar.extractall(dest, members=members, filter="data")
        else:
            tar.extractall(dest, members=members)


def _assemble_tex_dir(src: Path) -> tuple[str, list[str]]:
    from rlverify.ingest import _assemble_source_dir, normalize_latex

    text, _main, notes = _assemble_source_dir(src)
    text, norm = normalize_latex(text)
    return text, notes + norm


def _unpack_eprint(blob: bytes, workdir: Path) -> tuple[str, list[str]] | None:
    if blob.startswith(b"%PDF"):
        return None
    raw = gzip.decompress(blob) if blob[:2] == b"\x1f\x8b" else blob
    src = workdir / "src"
    try:
        _safe_extract_tar(blob if blob[:2] == b"\x1f\x8b" else raw, src)
        return _assemble_tex_dir(src)
    except Exception:
        pass
    try:
        body = raw.decode("utf-8", errors="replace")
    except Exception:
        return None
    if "\\begin{document}" in body or "\\begin{theorem}" in body:
        from rlverify.ingest import normalize_latex
        text, notes = normalize_latex(body)
        return text, ["single-file arXiv source"] + notes
    return None


def _pdf_text(data: bytes, source: str) -> tuple[str, list[str]]:
    try:
        import pypdf  # type: ignore
    except Exception as e:
        raise RuntimeError(
            "PDF input requires the optional dependency: `pip install pypdf` "
            "(or `pip install .[pdf]` from the repo root)") from e
    reader = pypdf.PdfReader(io.BytesIO(data))
    text = "\n".join(page.extract_text() or "" for page in reader.pages)
    if not text.strip():
        raise RuntimeError(f"PDF text layer was empty for {source}")
    return text, ["source: PDF text layer", "extracted PDF text via pypdf"]


def _source_from_arxiv(arxiv_id: str) -> PaperSource:
    paper_id = _slug(arxiv_id.replace("/", "_"))
    cache = OUT_ROOT / ".papers" / paper_id
    cache.mkdir(parents=True, exist_ok=True)
    notes: list[str] = []
    try:
        blob, _ = _http_get(f"https://arxiv.org/e-print/{arxiv_id}")
        (cache / "e-print").write_bytes(blob)
        unpacked = _unpack_eprint(blob, cache)
        if unpacked is not None:
            text, src_notes = unpacked
            return PaperSource(text=text, source=f"arXiv:{arxiv_id}",
                               kind="arxiv-source", paper_id=paper_id,
                               notes=notes + src_notes)
        notes.append("e-print was PDF-only")
    except Exception as e:
        notes.append(f"source fetch failed: {e}")
    blob, _ = _http_get(f"https://arxiv.org/pdf/{arxiv_id}")
    (cache / "paper.pdf").write_bytes(blob)
    text, pdf_notes = _pdf_text(blob, f"arXiv:{arxiv_id}")
    return PaperSource(text=text, source=f"arXiv:{arxiv_id}", kind="arxiv-pdf",
                       paper_id=paper_id, notes=notes + pdf_notes)


def load_source(target: str) -> PaperSource:
    workdir = Path(tempfile.mkdtemp(prefix="rlverify_paper_"))
    if target == "-":
        text = sys.stdin.read()
        return PaperSource(text=text, source="stdin", kind="stdin", paper_id="stdin")
    arxiv_id = parse_arxiv_id(target)
    if arxiv_id and (("arxiv.org" in target) or target.lower().startswith("arxiv:")
                     or not re.match(r"https?://", target)) and not Path(target).exists():
        return _source_from_arxiv(arxiv_id)
    if re.match(r"https?://", target):
        blob, content_type = _http_get(target)
        if blob.startswith(b"%PDF") or "pdf" in content_type.lower():
            text, notes = _pdf_text(blob, target)
            return PaperSource(text=text, source=target, kind="pdf",
                               paper_id=_slug(target, "url"), notes=notes)
        html = blob.decode("utf-8", errors="replace")
        text = re.sub(r"<(script|style)\b.*?</\1>", " ", html, flags=re.I | re.S)
        text = re.sub(r"<[^>]+>", " ", text)
        text = re.sub(r"\s+", " ", text)
        return PaperSource(text=text, source=target, kind="html",
                           paper_id=_slug(target, "url"))

    p = Path(target)
    suffix = p.suffix.lower()
    if suffix == ".pdf":
        text, notes = _pdf_text(p.read_bytes(), str(p))
        return PaperSource(text=text, source=str(p), kind="pdf",
                           paper_id=_slug(p.stem), notes=notes)
    if suffix == ".tex":
        from rlverify.ingest import _inline_inputs, normalize_latex
        text = _inline_inputs(p)
        text, notes = normalize_latex(text)
        return PaperSource(text=text, source=str(p), kind="tex",
                           paper_id=_slug(p.stem), notes=notes)
    return PaperSource(text=p.read_text(errors="replace"), source=str(p),
                       kind=suffix.lstrip(".") or "text", paper_id=_slug(p.stem))


def _normalize_with_map(text: str) -> tuple[str, list[int]]:
    out: list[str] = []
    idx: list[int] = []
    in_ws = False
    for i, ch in enumerate(text):
        if ch.isspace():
            if not in_ws and out:
                out.append(" ")
                idx.append(i)
            in_ws = True
        else:
            out.append(ch)
            idx.append(i)
            in_ws = False
    if out and out[-1] == " ":
        out.pop()
        idx.pop()
    return "".join(out), idx


def _anchor_words(anchor: str) -> int:
    return len([w for w in re.split(r"\s+", anchor.strip()) if w])


def slice_by_anchors(text: str, start: str, end: str) -> str | None:
    if not start or not end or _anchor_words(start) > 10 or _anchor_words(end) > 10:
        return None
    norm, mapping = _normalize_with_map(text)
    s_norm, _ = _normalize_with_map(start)
    e_norm, _ = _normalize_with_map(end)
    s = norm.find(s_norm)
    if s < 0:
        return None
    e = norm.find(e_norm, s + len(s_norm))
    if e < 0:
        return None
    start_i = mapping[s]
    end_i = mapping[e + len(e_norm) - 1] + 1
    return text[start_i:end_i].strip()


def _extract_json(raw: str) -> object:
    raw = raw.strip()
    start = raw.find("[")
    end = raw.rfind("]")
    if start >= 0 and end > start:
        return json.loads(raw[start:end + 1])
    start = raw.find("{")
    end = raw.rfind("}")
    if start >= 0 and end > start:
        return json.loads(raw[start:end + 1])
    raise ValueError("no JSON object/array found")


def _anchors(obj: dict, key: str) -> tuple[str, str]:
    val = obj.get(key) or {}
    if isinstance(val, dict):
        return str(val.get("start", "")), str(val.get("end", ""))
    if isinstance(val, list) and len(val) >= 2:
        return str(val[0]), str(val[1])
    return "", ""


def _fallback_candidates(source: PaperSource) -> list[Candidate]:
    from rlverify.extract import extract_from_latex, extract_from_text
    if source.kind in {"tex", "arxiv-source"}:
        extracted = extract_from_latex(source.text, source.source)
    else:
        extracted = extract_from_text(source.text, source.source)
    candidates = [
        Candidate(
            label=e.label,
            statement=e.theorem,
            proof=e.proof,
            source_kind="local-extractor",
            kind=e.kind,
            external=bool(e.external),
        )
        for e in extracted
    ]
    _attach_standing_context(source, candidates)
    return candidates


_LATEX_SECTION = re.compile(
    r"\\(?:sub)*section\*?\{[^}]*\}",
    re.IGNORECASE,
)
_LATEX_DISPLAY_ENV = re.compile(
    r"\\begin\{(?:figure|figure\*|table|table\*|algorithm)\}.*?"
    r"\\end\{(?:figure|figure\*|table|table\*|algorithm)\}",
    re.IGNORECASE | re.DOTALL,
)
_MARKDOWN_HEADING = re.compile(
    r"(?m)^(?P<marker>#{1,6})[ \t]+(?P<title>[^\n#]+?)[ \t]*#?[ \t]*$"
)
_PLAIN_CONTEXT_HEADING = re.compile(
    r"(?im)^(?P<title>"
    r"setup|assumptions?|standing assumptions?|setting|notation|"
    r"preliminaries|problem setup|model"
    r")[ \t]*:?[ \t]*$"
)
_CONTEXT_TITLE = re.compile(
    r"\b(setup|assumptions?|standing|setting|notation|preliminaries|"
    r"problem setup|model)\b",
    re.IGNORECASE,
)
_MAX_STANDING_CONTEXT = 16_000


def _candidate_source_position(source: PaperSource, candidate: Candidate) -> int:
    """Locate a candidate in the normalized paper source.

    Sealed extraction copies the exact statement, so the direct lookup is the
    normal path. The local extractor cleans theorem text; for that fallback,
    use its LaTeX label when available.
    """
    pos = source.text.find(candidate.statement)
    if pos >= 0:
        return pos
    label = re.escape(candidate.label)
    match = re.search(rf"\\label\{{{label}\}}", source.text)
    return match.start() if match else -1


def _standing_context(source: PaperSource, candidate: Candidate) -> str:
    """Return the candidate's preceding section context.

    Paper-level assumptions often live immediately before a theorem rather
    than inside its environment. Omitting them changes the submitted claim and
    makes a faithful statement audit impossible. Keep the context provenance
    explicit and bounded; large display-only environments are irrelevant to
    assumptions and are removed.
    """
    pos = _candidate_source_position(source, candidate)
    if pos <= 0:
        return ""

    if source.kind in {"tex", "arxiv-source"}:
        headings = list(_LATEX_SECTION.finditer(source.text, 0, pos))
        start = headings[-1].start() if headings else 0
    else:
        # Markdown/pasted proofs commonly put load-bearing assumptions under a
        # `Setup`/`Assumptions` heading immediately before a theorem heading.
        # Starting at the last heading would select `## Theorem` and reproduce
        # the exact bug that dropped gamma >= 0 from the Bellman example.
        markdown = list(_MARKDOWN_HEADING.finditer(source.text, 0, pos))
        preferred = [
            match for match in markdown
            if _CONTEXT_TITLE.search(match.group("title"))
        ]
        plain = list(_PLAIN_CONTEXT_HEADING.finditer(source.text, 0, pos))
        markers = preferred + plain
        if not markers:
            return ""
        start = max(markers, key=lambda match: match.start()).start()

    context = source.text[start:pos]
    if source.kind in {"tex", "arxiv-source"}:
        context = _LATEX_DISPLAY_ENV.sub("", context)
    context = context.strip()
    if not context:
        return ""
    if len(context) > _MAX_STANDING_CONTEXT:
        half = _MAX_STANDING_CONTEXT // 2
        context = (
            context[:half].rstrip()
            + "\n\n[... middle of section omitted by bounded ingestion ...]\n\n"
            + context[-half:].lstrip()
        )
    return context


def _attach_standing_context(
    source: PaperSource,
    candidates: list[Candidate],
) -> None:
    for candidate in candidates:
        candidate.standing_context = _standing_context(source, candidate)


def _effective_statement(candidate: Candidate) -> str:
    if not candidate.standing_context:
        return candidate.statement.strip()
    return (
        "STANDING CONTEXT FROM THE PAPER "
        "(submitted assumptions, not added hypotheses):\n"
        f"{candidate.standing_context.strip()}\n\n"
        "TARGET THEOREM:\n"
        f"{candidate.statement.strip()}"
    )


def extract_candidates(source: PaperSource, call_model: CallModel) -> list[Candidate]:
    prompt = (
        "You extract theorem/proof candidates from a math paper. Return JSON only: "
        "[{\"label\":\"Theorem 3.1\", \"kind\":\"theorem|lemma|proposition|"
        "corollary|claim|definition\", \"external\":false, \"is_main\":false, "
        "\"statement_anchors\":{\"start\":\"<=10 words\", "
        "\"end\":\"<=10 words\"}, \"proof_anchors\":{\"start\":\"<=10 words\", "
        "\"end\":\"<=10 words\"}, \"uses\":[\"Lemma 2.1\"]}]. The anchors must be "
        "verbatim substrings from the source; the parent process will copy text between them.\n\n"
        f"SOURCE:\n{source.text}"
    )
    candidates: list[Candidate] = []
    try:
        raw = call_model(prompt)
        obj = _extract_json(raw)
        rows = obj.get("candidates", []) if isinstance(obj, dict) else obj
        iter_rows = rows if isinstance(rows, list) else []
        dropped = 0
        for row in iter_rows:
            if not isinstance(row, dict):
                continue
            ss, se = _anchors(row, "statement_anchors")
            ps, pe = _anchors(row, "proof_anchors")
            statement = slice_by_anchors(source.text, ss, se)
            proof = slice_by_anchors(source.text, ps, pe)
            if not statement or not proof:
                dropped += 1
                continue
            candidates.append(Candidate(
                label=str(row.get("label") or f"theorem_{len(candidates)+1}"),
                statement=statement,
                proof=proof,
                uses=[str(u) for u in (row.get("uses") or [])],
                source_kind="sealed-anchor",
                kind=str(row.get("kind") or "theorem").lower(),
                external=bool(row.get("external")),
                is_main=bool(row.get("is_main")),
            ))
        if dropped:
            source.notes.append(f"sealed extraction dropped {dropped} candidate(s) with unverifiable anchors")
        if iter_rows and not candidates:
            source.notes.append("sealed extraction produced no verified anchors; fell back to local extractor")
    except Exception as e:
        source.notes.append(f"sealed extraction failed: {e}")
    if candidates:
        _attach_standing_context(source, candidates)
        return candidates
    return _fallback_candidates(source)


def _norm_label(s: str) -> str:
    s = s.lower().strip()
    s = re.sub(r"^(theorem|lemma|proposition|corollary)\s*", "", s)
    return re.sub(r"[^a-z0-9]+", "", s)


def select_candidate(
    candidates: list[Candidate],
    theorem: str | None,
    *,
    selection_request: str = "",
    call_model: CallModel | None = None,
) -> Candidate:
    if not candidates:
        raise RuntimeError("no theorem/proof candidates found")
    if theorem:
        try:
            return _resolve_candidate_selector(candidates, theorem)
        except ValueError as exc:
            if not sys.stdin.isatty():
                choices = "\n".join(
                    _candidate_choice(i, candidate)
                    for i, candidate in enumerate(candidates, 1)
                )
                raise RuntimeError(f"{exc}\nAvailable candidates:\n{choices}") from exc
            print(f"{exc}\nChoose from:")
    if len(candidates) == 1 and not theorem:
        return candidates[0]
    if not sys.stdin.isatty():
        choices = "\n".join(
            _candidate_choice(i, candidate)
            for i, candidate in enumerate(candidates, 1)
        )
        raise RuntimeError("multiple theorem candidates found; rerun with --theorem:\n" + choices)
    if (
        not theorem
        and call_model is not None
        and _needs_semantic_selection(selection_request)
    ):
        proposed = _propose_candidate(
            candidates,
            selection_request,
            call_model,
        )
        if proposed is not None:
            print(
                "Verify interpreted your request as:\n"
                f"{_candidate_choice(candidates.index(proposed) + 1, proposed)}"
            )
            answer = input(
                "Use this theorem? [Y/n/list/q] "
            ).strip().lower()
            if answer in {"", "y", "yes"}:
                return proposed
            if answer in {"q", "quit", "cancel"}:
                raise TheoremSelectionCancelled("theorem selection cancelled")
    for i, c in enumerate(candidates, 1):
        print(_candidate_choice(i, c))
    while True:
        resp = input(
            "select by menu number or theorem label "
            "(for example 1 or 3.1; q to cancel): "
        ).strip()
        if resp.lower() in {"q", "quit", "cancel"}:
            raise TheoremSelectionCancelled("theorem selection cancelled")
        try:
            return _resolve_candidate_selector(candidates, resp)
        except ValueError as exc:
            print(f"{exc} Please try again.")


def _resolve_candidate_selector(
    candidates: list[Candidate],
    selector: str,
) -> Candidate:
    requested = selector.strip()
    if not requested:
        raise ValueError("theorem selection cannot be empty.")

    wanted = _norm_label(requested)
    exact = [candidate for candidate in candidates
             if _norm_label(candidate.label) == wanted]
    if len(exact) == 1:
        return exact[0]

    # A bare integer is also a menu position. Exact theorem labels take
    # precedence above, so "--theorem 1" still selects an actual "Theorem 1"
    # when present and otherwise means the first displayed candidate.
    if re.fullmatch(r"\d+", requested):
        index = int(requested)
        if 1 <= index <= len(candidates):
            return candidates[index - 1]

    partial = [candidate for candidate in candidates
               if wanted and wanted in _norm_label(candidate.label)]
    if len(partial) == 1:
        return partial[0]
    if len(partial) > 1:
        labels = ", ".join(candidate.label for candidate in partial)
        raise ValueError(
            f"theorem selector {requested!r} is ambiguous: {labels}."
        )
    raise ValueError(f"theorem selector {requested!r} was not found.")


def _needs_semantic_selection(request: str) -> bool:
    without_target = re.sub(r"https?://\S+", " ", request.lower())
    tokens = re.findall(r"[a-z0-9]+", without_target)
    generic = {
        "a", "an", "the", "this", "that", "from", "in", "of", "paper",
        "article", "please", "fully", "full", "verify", "verification",
        "check", "prove", "theorem", "theroem", "thm", "lemma", "result",
    }
    return any(token not in generic for token in tokens)


def _propose_candidate(
    candidates: list[Candidate],
    request: str,
    call_model: CallModel,
) -> Candidate | None:
    rows = []
    for index, candidate in enumerate(candidates, 1):
        statement = re.sub(r"\s+", " ", candidate.statement).strip()
        rows.append(
            f"{index}. LABEL: {candidate.label}\n"
            f"STATEMENT: {statement[:1200]}"
        )
    prompt = (
        "Match a user's natural-language theorem request to one extracted "
        "candidate. Return JSON only with this schema: "
        "{\"label\":\"exact candidate label or null\","
        "\"reason\":\"short explanation\"}. Do not invent a label. Return "
        "null when the request is ambiguous.\n\n"
        f"USER REQUEST:\n{request}\n\n"
        "CANDIDATES:\n" + "\n\n".join(rows)
    )
    try:
        raw = call_model(prompt)
        value = _extract_json(raw)
        if not isinstance(value, dict):
            return None
        label = value.get("label")
        if not isinstance(label, str) or not label.strip():
            return None
        return _resolve_candidate_selector(candidates, label)
    except Exception:
        return None


def _candidate_choice(index: int, candidate: Candidate) -> str:
    statement = re.sub(r"\s+", " ", candidate.statement).strip()
    if not statement:
        statement = "(statement extraction was empty)"
    if len(statement) > 240:
        statement = statement[:237].rstrip() + "..."
    return f"  {index}. {candidate.label}\n       {statement}"


def materialize_fixture(source: PaperSource, candidate: Candidate,
                        out_root: Path = OUT_ROOT,
                        label_slug: str | None = None) -> Fixture:
    paper = _slug(source.paper_id)
    label = label_slug or _label_slug(candidate.label, "theorem")
    fixture_dir = out_root / paper / label
    fixture_dir.mkdir(parents=True, exist_ok=True)
    effective_statement = _effective_statement(candidate)
    (fixture_dir / "statement.md").write_text(effective_statement + "\n")
    (fixture_dir / "proof.txt").write_text(candidate.proof.strip() + "\n")
    (fixture_dir / "claim.txt").write_text(effective_statement + "\n")
    if candidate.standing_context:
        (fixture_dir / "context.txt").write_text(
            candidate.standing_context.strip() + "\n")
    (fixture_dir / "source.txt").write_text(source.text)
    (fixture_dir / "metadata.json").write_text(json.dumps({
        "source": source.source,
        "kind": source.kind,
        "notes": source.notes,
        "label": candidate.label,
        "uses": candidate.uses,
        "extraction": candidate.source_kind,
        "standing_context": bool(candidate.standing_context),
        "component_kind": candidate.kind,
        "external": candidate.external,
        "is_main": candidate.is_main,
        "target_statement": candidate.statement.strip(),
    }, indent=2) + "\n")
    return Fixture(name=f"{paper}_{label}", path=fixture_dir,
                   statement=effective_statement,
                   proof=candidate.proof.strip(),
                   claim=effective_statement,
                   source=source, candidate=candidate)


def order_candidates(candidates: list[Candidate]) -> tuple[list[Candidate], list[str]]:
    """Dependency-first order using model-asserted ``uses[]`` edges."""
    notes: list[str] = []
    label_to_idx: dict[str, int] = {}
    for i, c in enumerate(candidates):
        label_to_idx.setdefault(_norm_label(c.label), i)
    deps: list[list[int]] = []
    for i, c in enumerate(candidates):
        row: list[int] = []
        seen: set[int] = set()
        for use in c.uses:
            j = label_to_idx.get(_norm_label(use))
            if j is not None and j != i and j not in seen:
                row.append(j)
                seen.add(j)
        deps.append(row)

    ordered: list[int] = []
    temp: set[int] = set()
    perm: set[int] = set()
    cycle = False

    def visit(k: int) -> None:
        nonlocal cycle
        if k in perm:
            return
        if k in temp:
            cycle = True
            return
        temp.add(k)
        for d in deps[k]:
            visit(d)
        temp.remove(k)
        perm.add(k)
        ordered.append(k)

    for i in range(len(candidates)):
        visit(i)
    if cycle:
        notes.append("cycle detected in model-asserted uses[] graph; used document order")
        return candidates, notes
    return [candidates[i] for i in ordered], notes


def materialize_fixtures(source: PaperSource, candidates: list[Candidate],
                         out_root: Path = OUT_ROOT) -> list[Fixture]:
    fixtures: list[Fixture] = []
    used: set[str] = set()
    for candidate in candidates:
        label = _label_slug(candidate.label, "theorem")
        base = label
        i = 2
        while label in used:
            label = f"{base}_{i}"
            i += 1
        used.add(label)
        fixtures.append(materialize_fixture(source, candidate, out_root=out_root,
                                            label_slug=label))
    return fixtures


def build_paper_session(name: str, fixtures: list[Fixture]):
    """Build the golden verifyRL-paper graph from materialized components.

    Fixture names are the durable unique node identifiers.  Human labels are
    normalized only while resolving extracted ``uses[]`` references.
    """
    from rlverify.paper import PaperSession

    session = PaperSession(name)
    candidates = {
        fixture.name: (
            fixture.candidate
            if getattr(fixture, "candidate", None) is not None else
            Candidate(
                label=fixture.name,
                statement=fixture.statement,
                proof=fixture.proof,
                kind=(
                    "lemma" if "lemma" in fixture.name.lower()
                    else "theorem"
                ),
            )
        )
        for fixture in fixtures
    }
    by_normalized: dict[str, list[str]] = {}
    for fixture in fixtures:
        by_normalized.setdefault(
            _norm_label(candidates[fixture.name].label), []
        ).append(fixture.name)

    explicit_main = any(candidates[fixture.name].is_main for fixture in fixtures)
    for index, fixture in enumerate(fixtures):
        candidate = candidates[fixture.name]
        deps: list[str] = []
        for use in candidate.uses:
            matches = by_normalized.get(_norm_label(use), [])
            if len(matches) == 1 and matches[0] != fixture.name:
                deps.append(matches[0])
            elif not matches:
                # Keep dangling references visible in unknown_deps().
                deps.append(use)
        is_main = bool(candidate.is_main)
        if not explicit_main:
            later_theorem = any(
                candidates[other.name].kind == "theorem"
                and not candidates[other.name].external
                for other in fixtures[index + 1:]
            )
            is_main = (
                candidate.kind == "theorem"
                and not candidate.external
                and not later_theorem
            )
        session.add_component(
            fixture.name,
            statement=fixture.statement,
            proof=fixture.proof,
            deps=list(dict.fromkeys(deps)),
            kind=candidate.kind,
            external=candidate.external,
            is_main=is_main,
        )
        if candidate.standing_context:
            session.add_standing_assumption(
                candidate.standing_context.strip()
            )
    return session


def capped_paper_order(session, limit: int = 15) -> tuple[list[str], list[str]]:
    """Golden paper cap: main dependency chain first, then independent nodes."""
    order = session.topo_order()
    if len(order) <= limit:
        return order, []
    mains = [
        label for label in order
        if session.components[label].is_main
    ]
    main = mains[-1] if mains else order[-1]
    required: set[str] = set()

    def visit(label: str) -> None:
        if label in required:
            return
        for dep in session.dependency_graph().get(label, []):
            visit(dep)
        required.add(label)

    visit(main)
    selected = [label for label in order if label in required]
    for label in order:
        if len(selected) >= limit:
            break
        if label not in required:
            selected.append(label)
    omitted = [label for label in order if label not in selected]
    return selected[:limit], omitted


def ingest_to_fixture(
    target: str,
    theorem: str | None,
    call_model: CallModel,
    selection_request: str = "",
) -> Fixture:
    source = load_source(target)
    candidates = extract_candidates(source, call_model)
    candidate = select_candidate(
        candidates,
        theorem,
        selection_request=selection_request,
        call_model=call_model,
    )
    return materialize_fixture(source, candidate)


def ingest_all_to_fixtures(target: str, call_model: CallModel) -> list[Fixture]:
    source = load_source(target)
    candidates = extract_candidates(source, call_model)
    if not candidates:
        raise RuntimeError("no theorem/proof candidates found")
    ordered, notes = order_candidates(candidates)
    source.notes.extend(notes)
    return materialize_fixtures(source, ordered)
