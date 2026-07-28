#!/usr/bin/env python3
"""Build a cross-project theorem registry from Lean 4 source files.

Scans .lean files for theorem/lemma declarations and produces a JSON
index suitable for querying what's been formalized across projects.

Usage:
    python scripts/build_registry.py                    # This project only
    python scripts/build_registry.py --output registry.json
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

DECL_RE = re.compile(r"^(theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_'.]*)", re.MULTILINE)


def scan_lean_file(path: Path, project: str) -> list[dict]:
    """Extract theorem/lemma names from a .lean file."""
    text = path.read_text(errors="replace")
    module = ".".join(path.with_suffix("").relative_to(ROOT).parts)
    entries = []
    for m in DECL_RE.finditer(text):
        kind = m.group(1)
        name = m.group(2)
        line = text[:m.start()].count("\n") + 1
        entries.append({
            "project": project,
            "module": module,
            "name": name,
            "kind": kind,
            "file": str(path.relative_to(ROOT)),
            "line": line,
        })
    return entries


def scan_project(base: Path, project: str) -> list[dict]:
    """Scan all .lean files under a directory."""
    entries = []
    for path in sorted(base.rglob("*.lean")):
        entries.extend(scan_lean_file(path, project))
    return entries


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=str, default=None,
                        help="Write JSON to file (default: stdout)")
    args = parser.parse_args()

    all_entries = []

    # Scan this project
    rl_dir = ROOT / "RLGeneralization"
    if rl_dir.exists():
        all_entries.extend(scan_project(rl_dir, "lean4-rl"))

    # Scan SLT if available
    slt_dir = ROOT / ".lake" / "packages" / "SLT" / "SLT"
    if slt_dir.exists():
        all_entries.extend(scan_project(slt_dir, "lean-stat-learning-theory"))

    registry = {
        "version": "1.0",
        "total_theorems": len(all_entries),
        "projects": sorted(set(e["project"] for e in all_entries)),
        "entries": all_entries,
    }

    output = json.dumps(registry, indent=2) + "\n"

    if args.output:
        Path(args.output).write_text(output)
        print(f"Registry: {len(all_entries)} theorems/lemmas written to {args.output}",
              file=sys.stderr)
    else:
        sys.stdout.write(output)

    # Summary
    by_project = {}
    for e in all_entries:
        by_project.setdefault(e["project"], 0)
        by_project[e["project"]] += 1
    for proj, count in sorted(by_project.items()):
        print(f"  {proj}: {count} theorems/lemmas", file=sys.stderr)


if __name__ == "__main__":
    main()
