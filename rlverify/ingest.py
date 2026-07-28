"""Paper ingestion front-end for /verifyRL-paper.

Normalizes any of these inputs into self-contained text the Phase 0 parser can
read directly:

  * a ``.tex`` file path        -> read, inline \\input/\\include
  * a ``.pdf`` file path        -> extract text layer (pymupdf -> pdftotext -> pypdf)
  * an arXiv id or URL          -> download e-print SOURCE (preferred) or PDF
  * any other text file path    -> read as-is

For arXiv the LaTeX *source* is preferred over the PDF: it is exact (no glyph
loss, no column-merge artifacts) and the Phase 0 parser keys off ``\\begin{theorem}``
environments. Only when no usable source is published do we fall back to the PDF
text layer.

CLI:

    python -m rlverify.ingest <input> [--out FILE] [--keep]

Writes the normalized text to FILE (or a temp file) and prints that path on
stdout; a one-line provenance summary goes to stderr. The skill then Reads the
path and proceeds with Phase 0 exactly as it would for a hand-supplied .tex.
"""

from __future__ import annotations

import argparse
import gzip
import io
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
from dataclasses import dataclass, field
from pathlib import Path

ARXIV_ID = re.compile(r"\b(\d{4}\.\d{4,5})(v\d+)?\b")
_INPUT_CMD = re.compile(r"\\(?:input|include)\{([^}]+)\}")
_USER_AGENT = "verifyRL-ingest/1.0 (Lean RL proof verification; contact via repo)"

# \newcommand{\name}{body}  or  \newcommand{\name}[1]{body}  (also \renewcommand)
_NEWCMD = re.compile(
    r"\\(?:re)?newcommand\s*\{\s*\\([A-Za-z]+)\s*\}\s*(?:\[(\d+)\])?\s*\{",
)


def strip_latex_comments(text: str) -> str:
    """Remove LaTeX comments (unescaped ``%`` to end of line), preserving line count.

    This is what stops commented-out ``\\begin{theorem}`` blocks — including the
    main theorem in draft papers — from being parsed as real components.
    """
    out = []
    for line in text.split("\n"):
        # cut at the first % not preceded by a backslash
        i, n = 0, len(line)
        cut = None
        while i < n:
            if line[i] == "\\":
                i += 2
                continue
            if line[i] == "%":
                cut = i
                break
            i += 1
        out.append(line if cut is None else line[:cut])
    return "\n".join(out)


def _find_brace_group(s: str, start: int) -> tuple[str, int] | None:
    """Given s[start]=='{', return (inner, index_after_close) with brace matching."""
    if start >= len(s) or s[start] != "{":
        return None
    depth, i = 0, start
    while i < len(s):
        c = s[i]
        if c == "\\":
            i += 2
            continue
        if c == "{":
            depth += 1
        elif c == "}":
            depth -= 1
            if depth == 0:
                return s[start + 1:i], i + 1
        i += 1
    return None


def expand_macros(text: str, max_passes: int = 5) -> tuple[str, int]:
    """Best-effort expansion of simple ``\\newcommand`` macros (0 or 1 argument).

    Returns (expanded_text, num_macros_defined). Conservative: leaves any macro it
    can't safely expand (≥2 args, unbalanced braces) untouched. Editorial macros
    that render to nothing (e.g. ``\\newcommand{\\red}[1]{}``) are expanded away,
    which removes draft TODO/color noise from theorem bodies.
    """
    macros: dict[str, tuple[int, str]] = {}
    for m in _NEWCMD.finditer(text):
        name = m.group(1)
        nargs = int(m.group(2) or 0)
        grp = _find_brace_group(text, m.end() - 1)
        if grp is None or nargs > 1:
            continue
        macros[name] = (nargs, grp[0])
    if not macros:
        return text, 0

    def expand_once(s: str) -> str:
        # longest names first so \Cone isn't shadowed by \C
        for name in sorted(macros, key=len, reverse=True):
            nargs, body = macros[name]
            pat = re.compile(r"\\" + re.escape(name) + r"(?![A-Za-z])")
            res, pos = [], 0
            for mm in pat.finditer(s):
                res.append(s[pos:mm.start()])
                if nargs == 0:
                    res.append(body)
                    pos = mm.end()
                else:
                    grp = _find_brace_group(s, mm.end()) if mm.end() < len(s) and s[mm.end()] == "{" else None
                    if grp is None:
                        res.append(s[mm.start():mm.end()])  # leave as-is
                        pos = mm.end()
                    else:
                        res.append(body.replace("#1", grp[0]))
                        pos = grp[1]
            res.append(s[pos:])
            s = "".join(res)
        return s

    prev = text
    for _ in range(max_passes):
        cur = expand_once(prev)
        if cur == prev:
            break
        prev = cur
    return prev, len(macros)


def normalize_latex(text: str, expand: bool = True) -> tuple[str, list[str]]:
    """Strip comments and (optionally) expand macros. Returns (text, notes)."""
    notes: list[str] = []
    before_envs = len(re.findall(r"\\begin\{(?:theorem|lemma|proposition|corollary)\}", text))
    text = strip_latex_comments(text)
    after_envs = len(re.findall(r"\\begin\{(?:theorem|lemma|proposition|corollary)\}", text))
    if after_envs < before_envs:
        notes.append(f"stripped comments: dropped {before_envs - after_envs} commented-out theorem env(s)")
    if expand:
        text, ndef = expand_macros(text)
        if ndef:
            notes.append(f"expanded {ndef} \\newcommand macro(s)")
    return text, notes


@dataclass
class IngestResult:
    text: str
    kind: str  # tex | pdf | arxiv-source | arxiv-pdf | text
    source: str  # original path / id / url
    main_file: str = ""  # for tex sources, the resolved main file
    notes: list[str] = field(default_factory=list)


# --------------------------------------------------------------------------- #
# PDF text extraction (tries the best-available backend, in order)
# --------------------------------------------------------------------------- #
def pdf_to_text(data: bytes, source: str = "") -> tuple[str, str]:
    """Return (text, backend_name). Raises RuntimeError if no backend works."""
    # 1. PyMuPDF (fitz) — best layout fidelity for math papers.
    try:
        import fitz  # type: ignore

        with fitz.open(stream=data, filetype="pdf") as doc:
            text = "\n".join(page.get_text("text") for page in doc)
        if text.strip():
            return text, "pymupdf"
    except Exception:
        pass

    # 2. pdftotext CLI (-layout keeps columns sane).
    if shutil.which("pdftotext"):
        try:
            with tempfile.NamedTemporaryFile(suffix=".pdf", delete=True) as tf:
                tf.write(data)
                tf.flush()
                out = subprocess.run(
                    ["pdftotext", "-layout", tf.name, "-"],
                    capture_output=True, text=True, timeout=120,
                )
            if out.returncode == 0 and out.stdout.strip():
                return out.stdout, "pdftotext"
        except Exception:
            pass

    # 3. pypdf — pure-python fallback.
    try:
        import pypdf  # type: ignore

        reader = pypdf.PdfReader(io.BytesIO(data))
        text = "\n".join((p.extract_text() or "") for p in reader.pages)
        if text.strip():
            return text, "pypdf"
    except Exception:
        pass

    raise RuntimeError(
        f"could not extract text from PDF ({source or 'bytes'}): no working backend "
        f"(install pymupdf, poppler/pdftotext, or pypdf)"
    )


# --------------------------------------------------------------------------- #
# LaTeX source assembly
# --------------------------------------------------------------------------- #
def _inline_inputs(main: Path, seen: set[Path] | None = None, depth: int = 0) -> str:
    """Recursively inline \\input / \\include relative to *main*'s directory."""
    seen = seen if seen is not None else set()
    main = main.resolve()
    if main in seen or depth > 20:
        return ""
    seen.add(main)
    try:
        text = main.read_text(errors="replace")
    except Exception:
        return ""
    base = main.parent

    def repl(m: re.Match) -> str:
        target = m.group(1).strip()
        cand = base / target
        for p in (cand, cand.with_suffix(".tex"), Path(str(cand) + ".tex")):
            if p.is_file():
                return "\n" + _inline_inputs(p, seen, depth + 1) + "\n"
        return m.group(0)  # leave unresolved references untouched

    return _INPUT_CMD.sub(repl, text)


def _pick_main_tex(tex_files: list[Path]) -> Path | None:
    """Choose the root .tex: prefers \\documentclass + \\begin{document}."""
    if not tex_files:
        return None
    scored: list[tuple[int, int, Path]] = []
    for p in tex_files:
        try:
            t = p.read_text(errors="replace")
        except Exception:
            continue
        score = 0
        if "\\documentclass" in t:
            score += 2
        if "\\begin{document}" in t:
            score += 2
        if "\\begin{theorem}" in t or "\\newtheorem" in t:
            score += 1
        # size as a tiebreaker — the root is usually substantial
        scored.append((score, len(t), p))
    if not scored:
        return None
    scored.sort(key=lambda x: (x[0], x[1]), reverse=True)
    return scored[0][2]


def _assemble_source_dir(src_dir: Path) -> tuple[str, str, list[str]]:
    """Return (text, main_file_name, notes) for an unpacked LaTeX source tree."""
    notes: list[str] = []
    tex_files = sorted(src_dir.rglob("*.tex"))
    if not tex_files:
        raise RuntimeError("no .tex files found in source archive")
    main = _pick_main_tex(tex_files)
    if main is not None and "\\documentclass" in main.read_text(errors="replace"):
        text = _inline_inputs(main)
        return text, main.name, notes
    # No clear root — concatenate everything in path order.
    notes.append(f"no \\documentclass found; concatenated {len(tex_files)} .tex files")
    parts = []
    for p in tex_files:
        parts.append(f"% ===== {p.name} =====\n" + p.read_text(errors="replace"))
    return "\n\n".join(parts), (main.name if main else tex_files[0].name), notes


def _unpack_eprint(data: bytes, workdir: Path) -> tuple[str, str, list[str]] | None:
    """Unpack an arXiv e-print blob. Returns (text, main, notes) or None if it's a PDF."""
    # arXiv e-print is usually gzip; could wrap a tar, or be a single .tex.
    if data[:1] == b"%" and data[:4] == b"%PDF":
        return None  # caller falls back to PDF path
    raw = data
    if data[:2] == b"\x1f\x8b":  # gzip magic
        try:
            raw = gzip.decompress(data)
        except Exception:
            raw = data
    # Try tar first.
    try:
        with tarfile.open(fileobj=io.BytesIO(data if data[:2] == b"\x1f\x8b" else raw)) as tar:
            src = workdir / "src"
            src.mkdir(parents=True, exist_ok=True)
            tar.extractall(src, filter="data")
            return _assemble_source_dir(src)
    except (tarfile.TarError, Exception):
        pass
    # Single decompressed file — assume it's the LaTeX body.
    try:
        body = raw.decode("utf-8", errors="replace")
        if "\\begin{document}" in body or "\\begin{theorem}" in body:
            return body, "main.tex", ["single-file arXiv source"]
    except Exception:
        pass
    return None


# --------------------------------------------------------------------------- #
# arXiv fetch
# --------------------------------------------------------------------------- #
def _http_get(url: str, timeout: int = 60) -> bytes:
    import requests

    resp = requests.get(url, headers={"User-Agent": _USER_AGENT}, timeout=timeout)
    resp.raise_for_status()
    return resp.content


def fetch_arxiv(arxiv_id: str, workdir: Path, expand: bool = True) -> IngestResult:
    """Fetch arXiv source (preferred) or PDF; return normalized text."""
    notes: list[str] = []
    # 1. Preferred: LaTeX source via e-print.
    try:
        blob = _http_get(f"https://arxiv.org/e-print/{arxiv_id}")
        unpacked = _unpack_eprint(blob, workdir)
        if unpacked is not None:
            text, main, src_notes = unpacked
            notes += src_notes
            text, norm_notes = normalize_latex(text, expand=expand)
            notes += norm_notes
            return IngestResult(
                text=text, kind="arxiv-source",
                source=f"arXiv:{arxiv_id}", main_file=main, notes=notes,
            )
        notes.append("e-print was a PDF, not LaTeX source")
    except Exception as e:
        notes.append(f"source fetch failed ({e}); falling back to PDF")

    # 2. Fallback: the published PDF.
    blob = _http_get(f"https://arxiv.org/pdf/{arxiv_id}")
    text, backend = pdf_to_text(blob, source=f"arXiv:{arxiv_id}")
    notes.append(f"extracted PDF text via {backend}")
    return IngestResult(
        text=text, kind="arxiv-pdf", source=f"arXiv:{arxiv_id}", notes=notes,
    )


def parse_arxiv_arg(arg: str) -> str | None:
    """Return a bare arXiv id if *arg* names one, else None."""
    s = arg.strip()
    if s.lower().startswith("arxiv:"):
        s = s.split(":", 1)[1]
    if "arxiv.org" in s:
        m = ARXIV_ID.search(s)
        return m.group(1) if m else None
    # A bare id like 2306.12345 — but NOT an existing file path.
    if not Path(arg).exists():
        m = re.fullmatch(r"(\d{4}\.\d{4,5})(v\d+)?", s)
        if m:
            return m.group(1)
    return None


# --------------------------------------------------------------------------- #
# Top-level entry point
# --------------------------------------------------------------------------- #
def ingest(arg: str, workdir: Path | None = None, expand: bool = True) -> IngestResult:
    """Normalize *arg* (path / arXiv id / URL) into text. See module docstring."""
    workdir = workdir or Path(tempfile.mkdtemp(prefix="ingest_"))

    arxiv_id = parse_arxiv_arg(arg)
    if arxiv_id:
        return fetch_arxiv(arxiv_id, workdir, expand=expand)

    p = Path(arg)
    if not p.exists():
        raise FileNotFoundError(
            f"'{arg}' is not a file, arXiv id (1234.56789), or arXiv URL"
        )

    suffix = p.suffix.lower()
    if suffix == ".pdf":
        text, backend = pdf_to_text(p.read_bytes(), source=str(p))
        return IngestResult(
            text=text, kind="pdf", source=str(p),
            notes=[f"extracted PDF text via {backend}"],
        )
    if suffix == ".tex":
        text = _inline_inputs(p)
        text, notes = normalize_latex(text, expand=expand)
        return IngestResult(text=text, kind="tex", source=str(p), main_file=p.name, notes=notes)
    if suffix in (".gz", ".tar"):  # a downloaded e-print blob on disk
        unpacked = _unpack_eprint(p.read_bytes(), workdir)
        if unpacked is not None:
            text, main, notes = unpacked
            text, norm_notes = normalize_latex(text, expand=expand)
            return IngestResult(
                text=text, kind="arxiv-source", source=str(p),
                main_file=main, notes=notes + norm_notes,
            )
    # Anything else: treat as plain text.
    return IngestResult(text=p.read_text(errors="replace"), kind="text", source=str(p))


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(
        prog="python -m rlverify.ingest",
        description="Normalize a paper (.tex/.pdf/arXiv id/URL) into text for /verifyRL-paper.",
    )
    ap.add_argument("input", help="file path, arXiv id (1234.56789), or arXiv URL")
    ap.add_argument("--out", help="write normalized text here (default: a temp file)")
    ap.add_argument("--keep", action="store_true",
                    help="keep the download/work directory (printed to stderr)")
    ap.add_argument("--raw", action="store_true",
                    help="skip macro expansion (still strips comments) for LaTeX inputs")
    args = ap.parse_args(argv)

    workdir = Path(tempfile.mkdtemp(prefix="ingest_"))
    try:
        res = ingest(args.input, workdir=workdir, expand=not args.raw)
    except Exception as e:
        print(f"ingest failed: {e}", file=sys.stderr)
        return 1

    out_path = Path(args.out) if args.out else (workdir / "normalized.tex")
    if not args.out:
        # keep temp output even without --keep so the path stays valid to Read
        pass
    out_path.write_text(res.text, encoding="utf-8")

    summary = (
        f"[ingest] kind={res.kind} source={res.source} "
        f"chars={len(res.text)} -> {out_path}"
    )
    if res.main_file:
        summary += f" (main={res.main_file})"
    if res.notes:
        summary += "\n[ingest] notes: " + "; ".join(res.notes)
    print(summary, file=sys.stderr)
    if args.keep:
        print(f"[ingest] workdir kept: {workdir}", file=sys.stderr)

    print(out_path)  # stdout = the path the skill should Read
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
