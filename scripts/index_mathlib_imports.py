#!/usr/bin/env python3
"""Index Mathlib declarations reachable from RLGeneralization imports.

Scans RLGeneralization/*.lean for `import Mathlib.*` lines, finds the
corresponding Mathlib source files, extracts theorem/lemma declarations,
and appends them to the retrieval corpus.

Usage:
    python scripts/index_mathlib_imports.py [--dry-run]
"""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MATHLIB_DIR = ROOT / ".lake" / "packages" / "mathlib"
CORPUS_PATH = ROOT / "rlverify" / "corpus.jsonl"

DECL_PATTERN = re.compile(
    r'^(?:@\[.*?\]\s*)?'
    r'(?:noncomputable\s+)?'
    r'(?:protected\s+)?'
    r'(theorem|lemma)\s+'
    r'(\w+)',
    re.MULTILINE,
)


def find_mathlib_imports() -> set[str]:
    """Extract all Mathlib imports from RLGeneralization/*.lean files."""
    imports: set[str] = set()
    for lean_file in ROOT.glob("RLGeneralization/**/*.lean"):
        for line in lean_file.read_text(errors="replace").splitlines():
            m = re.match(r'import\s+(Mathlib\.\S+)', line)
            if m:
                imports.add(m.group(1))
    return imports


def import_to_path(module: str) -> Path:
    """Convert 'Mathlib.X.Y.Z' to the source .lean file path."""
    rel = module.replace(".", "/") + ".lean"
    return MATHLIB_DIR / rel


def extract_declarations(lean_file: Path, module_name: str) -> list[dict]:
    """Extract theorem/lemma names and signatures from a Lean file."""
    try:
        text = lean_file.read_text(errors="replace")
    except OSError:
        return []

    entries = []
    for m in DECL_PATTERN.finditer(text):
        kind, name = m.group(1), m.group(2)
        if name.startswith("_"):
            continue

        start = m.start()
        rest = text[start:]
        sig_end = re.search(r'\n\s*:=|\n\s*where|\n\n', rest)
        sig = rest[:sig_end.start()].strip() if sig_end else rest[:300].strip()
        sig = " ".join(sig.split())
        if len(sig) > 500:
            sig = sig[:500]

        line_no = text[:start].count('\n') + 1
        entries.append({
            "id": f"{module_name}.{name}",
            "kind": kind,
            "statement": sig,
            "status": "mathlib",
            "tags": ["mathlib"],
            "source_file": str(lean_file.relative_to(ROOT)),
            "source_line": line_no,
            "docstring": "",
        })
    return entries


def existing_corpus_ids() -> set[str]:
    """Load IDs already in the corpus to avoid duplicates."""
    ids: set[str] = set()
    if CORPUS_PATH.exists():
        for line in CORPUS_PATH.read_text().splitlines():
            if line.strip():
                try:
                    ids.add(json.loads(line)["id"])
                except (json.JSONDecodeError, KeyError):
                    pass
    return ids


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dry-run", action="store_true",
                        help="Print stats without writing to corpus")
    args = parser.parse_args()

    imports = find_mathlib_imports()
    print(f"Found {len(imports)} unique Mathlib imports in RLGeneralization/")

    existing = existing_corpus_ids()
    all_entries: list[dict] = []
    skipped_modules = 0

    for imp in sorted(imports):
        lean_file = import_to_path(imp)
        if not lean_file.exists():
            skipped_modules += 1
            continue
        entries = extract_declarations(lean_file, imp)
        new_entries = [e for e in entries if e["id"] not in existing]
        all_entries.extend(new_entries)

    print(f"Extracted {len(all_entries)} new declarations "
          f"({skipped_modules} modules not found on disk)")

    if args.dry_run:
        for e in all_entries[:20]:
            print(f"  {e['id']}: {e['statement'][:80]}")
        if len(all_entries) > 20:
            print(f"  ... and {len(all_entries) - 20} more")
        return

    with open(CORPUS_PATH, "a") as f:
        for e in all_entries:
            f.write(json.dumps(e) + "\n")

    print(f"Appended {len(all_entries)} entries to {CORPUS_PATH.name}")
    print(f"Total corpus size: {len(existing) + len(all_entries)}")


if __name__ == "__main__":
    main()
