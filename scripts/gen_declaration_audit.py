#!/usr/bin/env python3
"""Generate FULL_DECLARATION_AUDIT.md from .lean source files.

Scans all .lean files under RLGeneralization/, classifies each theorem/def
by status (exact/conditional/wrapper/stub/vacuous), and writes a Markdown
table to FULL_DECLARATION_AUDIT.md.

The classification is based on:
  - Module-level status from verification_manifest.json
  - [CONDITIONAL: ...] annotations in the source (sorry + annotation → conditional)
  - [WRAPPER: ...] annotations (theorem body is hypothesis pass-through)
  - [VACUOUS: ...] annotations (conclusion is trivially true regardless of hypotheses)
  - Presence of bare `sorry` without annotation (→ stub)
  - Otherwise inherits module status

Usage:
    python scripts/gen_declaration_audit.py               # write FULL_DECLARATION_AUDIT.md
    python scripts/gen_declaration_audit.py --check       # fail if FULL_DECLARATION_AUDIT.md is stale
    python scripts/gen_declaration_audit.py --json        # emit JSON to stdout
    python scripts/gen_declaration_audit.py --stats       # emit summary statistics
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MANIFEST_PATH = ROOT / "verification_manifest.json"
AUDIT_PATH = ROOT / "FULL_DECLARATION_AUDIT.md"

# Declaration patterns — match at start of logical line (after any indent)
_DECL_RE = re.compile(
    r"^[ \t]*(?:@\[[^\]]*\]\s*)*"        # optional attributes
    r"(?:private\s+|protected\s+)?"       # optional visibility
    r"(theorem|lemma|def|noncomputable def|abbrev|instance)\s+"
    r"([A-Za-z_][A-Za-z0-9_.']*)",       # name
    re.MULTILINE,
)

_SORRY_RE = re.compile(r"\bsorry\b")
_CONDITIONAL_RE = re.compile(r"\[CONDITIONAL\b")
_WRAPPER_RE = re.compile(r"\[WRAPPER\b")
_VACUOUS_RE = re.compile(r"\[VACUOUS\b")

# Lines that are full-line comments
_COMMENT_LINE_RE = re.compile(r"^\s*--")


def _strip_block_comments_from_lines(lines: list[str]) -> list[str]:
    """Return lines with /- ... -/ block comment content removed.

    Preserves line count (one output line per input line) so indices
    remain valid for declaration boundary tracking.
    """
    result: list[str] = []
    depth = 0
    for line in lines:
        out_parts: list[str] = []
        i = 0
        while i < len(line):
            if depth == 0:
                if line[i:i + 2] == "/-":
                    depth += 1
                    i += 2
                else:
                    out_parts.append(line[i])
                    i += 1
            else:
                if line[i:i + 2] == "/-":
                    depth += 1
                    i += 2
                elif line[i:i + 2] == "-/":
                    depth -= 1
                    i += 2
                else:
                    i += 1
        result.append("".join(out_parts))
    return result


def _is_sorry_in_code(line: str) -> bool:
    """Return True if the line has a sorry outside a -- comment."""
    m = _SORRY_RE.search(line)
    if not m:
        return False
    comment_pos = line.find("--")
    return comment_pos < 0 or m.start() < comment_pos


def classify_declaration(
    name: str,
    decl_start: int,
    decl_end: int,
    lines: list[str],
    module_status: str,
    stripped_lines: list[str] | None = None,
) -> dict:
    """Classify a single declaration by scanning surrounding lines for markers.

    We look at:
      - 8 lines before the declaration (docstring / attribute annotations)
      - the declaration body itself, stopping at the next declaration

    ``stripped_lines``, if provided, should be the same file with block
    comments removed (via ``_strip_block_comments_from_lines``).  Using
    stripped lines for sorry detection avoids false positives from phrases
    like "zero sorry" inside /- ... -/ doc comments.

    Returns a dict with keys: name, status, has_sorry, note.
    """
    window_before = lines[max(0, decl_start - 8): decl_start]
    marker_window_after = lines[decl_start: min(decl_end, decl_start + 12)]

    # [WRAPPER] and [VACUOUS] markers live in the docstring BEFORE the
    # declaration keyword.  Scanning marker_window_after too causes
    # false positives when the next declaration's docstring falls
    # within 12 lines.
    before_snippet = "\n".join(window_before)
    is_wrapper = bool(_WRAPPER_RE.search(before_snippet))
    is_vacuous = bool(_VACUOUS_RE.search(before_snippet))

    # [CONDITIONAL] may appear near sorry in the body, so scan both.
    full_snippet = "\n".join(window_before + marker_window_after)
    is_conditional_annotated = bool(_CONDITIONAL_RE.search(full_snippet))

    # Check for sorry in non-comment lines in the window_after.
    # Use block-comment-stripped lines to avoid false positives.
    sorry_source = (stripped_lines if stripped_lines is not None else lines)
    window_after = sorry_source[decl_start: decl_end]
    sorry_lines = [
        l for l in window_after
        if not _COMMENT_LINE_RE.match(l) and _is_sorry_in_code(l)
    ]
    has_sorry = bool(sorry_lines)

    # Determine status
    if is_wrapper:
        status = "wrapper"
        note = "body is hypothesis pass-through"
    elif is_vacuous:
        status = "vacuous"
        note = "conclusion is trivially true"
    elif is_conditional_annotated:
        status = "conditional"
        note = "[CONDITIONAL] annotated"
    elif has_sorry and module_status in ("conditional", "unknown"):
        status = "conditional"
        note = "sorry in conditional module"
    elif has_sorry:
        status = "stub"
        note = "sorry without [CONDITIONAL] annotation"
    else:
        # Inherit module status
        if module_status in ("exact", "conditional", "weaker"):
            status = module_status
        else:
            status = "exact"
        note = ""

    return {
        "name": name,
        "status": status,
        "has_sorry": has_sorry,
        "note": note,
    }


def load_manifest() -> dict:
    try:
        return json.loads(MANIFEST_PATH.read_text())
    except (FileNotFoundError, json.JSONDecodeError):
        return {}


def scan_directory(scan_dir: Path) -> list[dict]:
    """Scan all .lean files and return a list of declaration audit entries."""
    manifest = load_manifest()
    module_statuses: dict[str, str] = {}
    for section in ("verified_target", "draft_target"):
        for entry in manifest.get(section, {}).get("modules", []):
            module_statuses[entry["module"]] = entry.get("status", "unknown")
    for entry in manifest.get("excluded_modules", []):
        module_statuses[entry["module"]] = "excluded"

    # Build theorem-level status overrides from manifest "theorems" array.
    # These capture wrapper/vacuous/weaker distinctions that source markers
    # may not express.
    theorem_overrides: dict[tuple[str, str], dict] = {}
    for thm in manifest.get("theorems", []):
        key = (thm["module"], thm["name"])
        theorem_overrides[key] = {
            "status": thm.get("status", ""),
            "gap_note": thm.get("gap_note", ""),
        }

    entries: list[dict] = []

    for lean_file in sorted(scan_dir.rglob("*.lean")):
        # Skip lake cache and worktrees
        parts = lean_file.parts
        if ".lake" in parts or "worktrees" in parts:
            continue

        rel_path = lean_file.relative_to(ROOT)
        module_name = ".".join(rel_path.with_suffix("").parts)
        module_status = module_statuses.get(module_name, "unknown")

        text = lean_file.read_text(errors="replace")
        lines = text.splitlines()
        stripped_lines = _strip_block_comments_from_lines(lines)

        matches = list(_DECL_RE.finditer(text))

        for idx, m in enumerate(matches):
            kind = m.group(1).strip()
            name = m.group(2)
            decl_line = text[: m.start()].count("\n")  # 0-indexed
            if idx + 1 < len(matches):
                next_decl_line = text[: matches[idx + 1].start()].count("\n")
            else:
                next_decl_line = len(lines)

            info = classify_declaration(name, decl_line, next_decl_line, lines, module_status, stripped_lines)

            # Apply theorem-level overrides from manifest (wrapper/vacuous/weaker)
            # These take precedence over source-marker classification when the
            # manifest provides a more specific status.
            # Try exact match first, then suffix match (manifest uses qualified names
            # like "FiniteHorizonMDP.foo" while source scanner finds bare "foo").
            override_key = (module_name, name)
            matched_key = None
            if override_key in theorem_overrides:
                matched_key = override_key
            else:
                for key in theorem_overrides:
                    if key[0] == module_name and key[1].endswith("." + name):
                        matched_key = key
                        break
            for candidate_key in ([matched_key] if matched_key else []):
                if candidate_key in theorem_overrides:
                    ovr = theorem_overrides[candidate_key]
                    ovr_status = ovr["status"]
                    if ovr_status in ("wrapper", "vacuous", "weaker", "conditional"):
                        info["status"] = ovr_status
                        info["note"] = ovr.get("gap_note", "") or info["note"]

            entries.append({
                "module": module_name,
                "module_status": module_status,
                "kind": kind,
                "name": info["name"],
                "status": info["status"],
                "has_sorry": info["has_sorry"],
                "line": decl_line + 1,
                "note": info["note"],
            })

    return entries


def render_markdown(entries: list[dict]) -> str:
    counts = Counter(e["status"] for e in entries)
    lines = [
        "# Full Declaration Audit",
        "",
        "This file is machine-generated by `scripts/gen_declaration_audit.py`.",
        "Do not edit manually — run `python scripts/gen_declaration_audit.py` to regenerate.",
        "",
        "## Summary",
        "",
        f"Total declarations: {len(entries)}",
        "",
        "| Status | Count |",
        "|--------|-------|",
    ]
    for status in ("exact", "conditional", "weaker", "wrapper", "stub", "vacuous", "unknown"):
        if counts.get(status, 0):
            lines.append(f"| `{status}` | {counts[status]} |")
    lines.extend([
        "",
        "## Declaration Table",
        "",
        "| Module | Kind | Name | Status | Sorry | Note |",
        "|--------|------|------|--------|-------|------|",
    ])
    for e in entries:
        sorry_marker = "yes" if e["has_sorry"] else ""
        note = e["note"].replace("|", "\\|")
        name = e["name"]
        lines.append(
            f"| `{e['module']}` | {e['kind']} | `{name}` "
            f"| `{e['status']}` | {sorry_marker} | {note} |"
        )
    lines.append("")
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check", action="store_true",
        help="Fail if FULL_DECLARATION_AUDIT.md is out of date.",
    )
    parser.add_argument(
        "--json", action="store_true",
        help="Emit JSON audit data to stdout instead of writing the Markdown file.",
    )
    parser.add_argument(
        "--stats", action="store_true",
        help="Print summary statistics to stdout.",
    )
    args = parser.parse_args()

    scan_dir = ROOT / "RLGeneralization"
    entries = scan_directory(scan_dir)

    if args.json:
        json.dump(entries, sys.stdout, indent=2)
        print()
        return

    if args.stats:
        counts = Counter(e["status"] for e in entries)
        print(f"Total declarations: {len(entries)}")
        for status, count in sorted(counts.items(), key=lambda x: -x[1]):
            print(f"  {status}: {count}")
        return

    content = render_markdown(entries)

    if args.check:
        current = AUDIT_PATH.read_text() if AUDIT_PATH.exists() else ""
        if current != content:
            print(
                "FULL_DECLARATION_AUDIT.md is out of date; run "
                "`python scripts/gen_declaration_audit.py` to regenerate.",
                file=sys.stderr,
            )
            sys.exit(1)
        print("FULL_DECLARATION_AUDIT.md is up to date.")
    else:
        AUDIT_PATH.write_text(content)
        counts = Counter(e["status"] for e in entries)
        print(f"Written {AUDIT_PATH.relative_to(ROOT)}")
        print(f"  {len(entries)} declarations total")
        for status, count in sorted(counts.items(), key=lambda x: -x[1]):
            print(f"  {status}: {count}")


if __name__ == "__main__":
    main()
