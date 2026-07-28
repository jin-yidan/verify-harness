#!/usr/bin/env python3
"""Extract training data from .lean files for LLM prover fine-tuning (#50).

Parses Lean 4 source files and extracts (theorem_statement, proof_tactic)
pairs.  This is a lightweight regex-based extraction -- not a full LeanDojo
integration -- suitable for building initial training datasets.

Output format (JSON lines to stdout):
    {"name": "...", "module": "...", "statement": "...", "proof": "...", "file": "...", "line": N}

Usage:
    python scripts/extract_leandojo.py
    python scripts/extract_leandojo.py --root RLGeneralization --output data/training_pairs.jsonl
    python scripts/extract_leandojo.py --help
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

DECL_RE = re.compile(
    r"^(theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_'.]*)"
)


def find_assignment(lines: list[str], start: int) -> int | None:
    """Find the line containing the top-level `:=` for a declaration."""
    depth = 0
    for idx in range(start, min(start + 100, len(lines))):
        line = lines[idx]
        col = 0
        while col < len(line):
            if line.startswith("--", col):
                break
            ch = line[col]
            if ch in "({[":
                depth += 1
            elif ch in ")}]":
                depth = max(depth - 1, 0)
            elif (ch == ":" and col + 1 < len(line) and
                  line[col + 1] == "=" and depth == 0):
                return idx
            col += 1
    return None


def find_proof_end(lines: list[str], start: int) -> int:
    """Find the line after the last line of a proof block."""
    idx = start + 1
    while idx < len(lines):
        stripped = lines[idx].strip()
        if (DECL_RE.match(lines[idx]) or
                stripped.startswith("/-") or
                stripped.startswith("end ") or
                re.match(r"^(variable|variables|open|namespace|section|noncomputable)\b", stripped)):
            break
        idx += 1
    return idx


def extract_pairs(filepath: Path, module: str) -> list[dict]:
    """Extract (statement, proof) pairs from a single .lean file."""
    text = filepath.read_text(errors="replace")
    lines = text.splitlines()
    pairs = []

    i = 0
    while i < len(lines):
        m = DECL_RE.match(lines[i])
        if not m:
            i += 1
            continue

        name = m.group(2)
        decl_start = i

        assign_line = find_assignment(lines, i)
        if assign_line is None:
            i += 1
            continue

        # Statement: from declaration to `:=` (exclusive)
        stmt_lines = lines[decl_start:assign_line + 1]
        # Trim the `:= by` or `:=` from the last line
        last = stmt_lines[-1]
        assign_col = last.find(":=")
        if assign_col >= 0:
            stmt_lines[-1] = last[:assign_col].rstrip()
        statement = "\n".join(stmt_lines).strip()

        # Proof: everything after `:=` until next declaration
        proof_start = assign_line
        proof_end = find_proof_end(lines, proof_start)

        # Include the `:= by` line onwards
        proof_lines = lines[proof_start:proof_end]
        # Remove the statement part from the first proof line
        if assign_col >= 0:
            proof_lines[0] = proof_lines[0][assign_col:]
        proof = "\n".join(proof_lines).strip()

        if statement and proof:
            pairs.append({
                "name": name,
                "module": module,
                "statement": statement,
                "proof": proof,
                "file": str(filepath.relative_to(ROOT)),
                "line": decl_start + 1,
            })

        i = proof_end

    return pairs


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Extract (theorem_statement, proof_tactic) training pairs from Lean 4 files."
    )
    parser.add_argument(
        "--root", default="RLGeneralization",
        help="Root directory to scan for .lean files (relative to project root)."
    )
    parser.add_argument(
        "--output", default=None,
        help="Output file path (JSONL). Defaults to stdout."
    )
    parser.add_argument(
        "--min-proof-lines", type=int, default=1,
        help="Minimum proof lines to include a pair (default: 1)."
    )
    args = parser.parse_args()

    scan_root = ROOT / args.root
    if not scan_root.exists():
        print(f"error: directory {scan_root} does not exist", file=sys.stderr)
        sys.exit(1)

    all_pairs: list[dict] = []
    for lean_file in sorted(scan_root.rglob("*.lean")):
        module = ".".join(lean_file.with_suffix("").relative_to(ROOT).parts)
        pairs = extract_pairs(lean_file, module)
        for p in pairs:
            proof_line_count = len(p["proof"].splitlines())
            if proof_line_count >= args.min_proof_lines:
                all_pairs.append(p)

    out = open(args.output, "w") if args.output else sys.stdout
    try:
        for pair in all_pairs:
            out.write(json.dumps(pair, ensure_ascii=False) + "\n")
    finally:
        if args.output:
            out.close()

    print(f"Extracted {len(all_pairs)} training pairs from {scan_root}",
          file=sys.stderr)


if __name__ == "__main__":
    main()
