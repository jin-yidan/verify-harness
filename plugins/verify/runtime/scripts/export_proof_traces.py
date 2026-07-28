#!/usr/bin/env python3
"""Export proof traces from all Lean files under RLGeneralization/.

Scans every .lean file, extracts theorem/lemma blocks with their tactic
proofs, and writes structured JSON output suitable for proof-trace training
and evaluation.

Outputs:
  - benchmark/proofs/<SubModule>/<TheoremName>.json  (per-theorem)
  - benchmark/proof_traces.jsonl                      (one JSON per line)

Usage:
    python scripts/export_proof_traces.py
    python scripts/export_proof_traces.py --root /path/to/lean4-rl
    python scripts/export_proof_traces.py --out-dir benchmark/proofs
"""

import argparse
import json
import os
import re
import sys
from pathlib import Path

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

DECL_RE = re.compile(r"^(theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_'.]*)")
IMPORT_RE = re.compile(r"^import\s+(\S+)")

# ---------------------------------------------------------------------------
# Manifest loader
# ---------------------------------------------------------------------------


def load_manifest_statuses(root: Path) -> dict[str, str]:
    """Load module-level and theorem-level statuses from verification_manifest.json."""
    manifest_path = root / "verification_manifest.json"
    if not manifest_path.exists():
        print(f"warning: {manifest_path} not found, statuses will be 'unknown'",
              file=sys.stderr)
        return {}
    data = json.loads(manifest_path.read_text())
    statuses: dict[str, str] = {}
    for entry in data.get("verified_target", {}).get("modules", []):
        statuses[entry["module"]] = entry.get("status", "unknown")
    for entry in data.get("theorems", []):
        statuses[entry["name"]] = entry.get("status", "unknown")
    return statuses


# ---------------------------------------------------------------------------
# Proof extraction
# ---------------------------------------------------------------------------


def find_assignment(lines: list[str], start: int) -> tuple[int, int] | None:
    """Find the top-level `:=` that starts the proof body."""
    depth = 0
    for li in range(start, min(start + 80, len(lines))):
        line = lines[li]
        col = 0
        while col < len(line):
            if line.startswith("--", col):
                break
            ch = line[col]
            if ch in "({[":
                depth += 1
            elif ch in ")}]":
                depth = max(depth - 1, 0)
            elif ch == ":" and col + 1 < len(line) and line[col + 1] == "=" and depth == 0:
                return li, col
            col += 1
    return None


def find_proof_end(lines: list[str], body_start: int) -> int:
    """Find where the proof body ends (next top-level decl, section, or end)."""
    proof_end = body_start + 1
    while proof_end < len(lines):
        stripped = lines[proof_end].strip()
        if DECL_RE.match(lines[proof_end]):
            break
        if stripped.startswith("/-"):
            break
        if re.match(r"^end\b", stripped):
            break
        if re.match(r"^(variable|variables|open|local|scoped|attribute|namespace|section|noncomputable)\b",
                     stripped):
            break
        proof_end += 1
    return proof_end


def extract_tactics(lines: list[str], body_start: int, body_end: int) -> list[str]:
    """Extract tactic lines from a `by` proof block.

    Returns individual tactic lines with leading whitespace stripped.
    """
    tactics: list[str] = []
    # The proof body starts after `:= by` (possibly on the same line or next)
    first_line = lines[body_start] if body_start < len(lines) else ""
    by_match = re.search(r":=\s*by\b(.*)", first_line)
    start_line = body_start
    if by_match:
        remainder = by_match.group(1).strip()
        if remainder:
            tactics.append(remainder)
        start_line = body_start + 1
    else:
        # `:= by` might be on the next line
        for li in range(body_start, min(body_start + 3, body_end)):
            if re.match(r"\s*by\b", lines[li].strip()):
                remainder = re.sub(r"^\s*by\s*", "", lines[li]).strip()
                if remainder:
                    tactics.append(remainder)
                start_line = li + 1
                break

    for li in range(start_line, body_end):
        stripped = lines[li].strip()
        if stripped and not stripped.startswith("--"):
            tactics.append(stripped)
    return tactics


def extract_proofs_from_file(filepath: Path, root: Path,
                             statuses: dict[str, str]) -> list[dict]:
    """Extract all theorem/lemma proof traces from a single .lean file."""
    text = filepath.read_text()
    all_lines = text.splitlines()
    results: list[dict] = []

    # Collect imports
    imports: list[str] = []
    for line in all_lines:
        m = IMPORT_RE.match(line.strip())
        if m:
            imports.append(m.group(1))

    # Derive module name from file path
    try:
        rel = filepath.relative_to(root)
    except ValueError:
        rel = filepath
    module_name = str(rel).replace("/", ".").removesuffix(".lean")

    i = 0
    while i < len(all_lines):
        m = DECL_RE.match(all_lines[i])
        if not m:
            i += 1
            continue

        kind = m.group(1)
        name = m.group(2)
        decl_start = i

        assignment = find_assignment(all_lines, i)
        if assignment is None:
            i += 1
            continue

        body_line, assign_col = assignment
        proof_end = find_proof_end(all_lines, body_line)

        # Statement: everything up to (but not including) `:=`
        stmt_lines = all_lines[decl_start:body_line + 1]
        stmt_lines[-1] = stmt_lines[-1][:assign_col].rstrip()
        statement = "\n".join(stmt_lines).strip()

        # Full proof block (including := by ...)
        proof_block = "\n".join(all_lines[body_line:proof_end]).strip()

        # Extract individual tactic lines
        tactics = extract_tactics(all_lines, body_line, proof_end)

        # Determine status
        status = "unknown"
        qualified = f"{module_name}.{name}"
        for key in [qualified, name, module_name]:
            if key in statuses:
                status = statuses[key]
                break

        results.append({
            "module": module_name,
            "theorem_name": name,
            "kind": kind,
            "statement": statement,
            "proof_block": proof_block,
            "tactics": tactics,
            "imports": imports,
            "status": status,
            "source_file": str(rel),
            "source_line": decl_start + 1,
        })

        i = proof_end

    return results


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Export proof traces from RLGeneralization .lean files.")
    parser.add_argument("--root", type=Path,
                        default=Path(__file__).resolve().parent.parent,
                        help="Project root directory (default: auto-detect)")
    parser.add_argument("--out-dir", type=Path, default=None,
                        help="Per-module output directory (default: <root>/benchmark/proofs)")
    parser.add_argument("--jsonl", type=Path, default=None,
                        help="Combined JSONL output (default: <root>/benchmark/proof_traces.jsonl)")
    parser.add_argument("--source-dir", type=str, default="RLGeneralization",
                        help="Subdirectory to scan (default: RLGeneralization)")
    args = parser.parse_args()

    root = args.root.resolve()
    out_dir = (args.out_dir or root / "benchmark" / "proofs").resolve()
    jsonl_path = (args.jsonl or root / "benchmark" / "proof_traces.jsonl").resolve()
    source_dir = root / args.source_dir

    if not source_dir.is_dir():
        print(f"error: {source_dir} is not a directory", file=sys.stderr)
        sys.exit(1)

    statuses = load_manifest_statuses(root)

    all_traces: list[dict] = []
    lean_files = sorted(source_dir.rglob("*.lean"))
    print(f"Scanning {len(lean_files)} .lean files under {source_dir.name}/",
          file=sys.stderr)

    for filepath in lean_files:
        traces = extract_proofs_from_file(filepath, root, statuses)
        if not traces:
            continue

        # Write per-module JSON files
        rel_module = traces[0]["module"].removeprefix("RLGeneralization.")
        module_dir = out_dir / rel_module.replace(".", "/")
        module_dir.mkdir(parents=True, exist_ok=True)

        for trace in traces:
            safe_name = re.sub(r"[^A-Za-z0-9_]", "_", trace["theorem_name"])
            per_file = module_dir / f"{safe_name}.json"
            per_file.write_text(json.dumps(trace, indent=2) + "\n")

        all_traces.extend(traces)

    # Write combined JSONL
    jsonl_path.parent.mkdir(parents=True, exist_ok=True)
    with open(jsonl_path, "w") as f:
        for trace in all_traces:
            f.write(json.dumps(trace) + "\n")

    # Summary
    by_status: dict[str, int] = {}
    for t in all_traces:
        by_status[t["status"]] = by_status.get(t["status"], 0) + 1

    print(f"\nExported {len(all_traces)} proof traces", file=sys.stderr)
    print(f"  Per-module JSONs: {out_dir}", file=sys.stderr)
    print(f"  Combined JSONL:   {jsonl_path}", file=sys.stderr)
    print(f"  By status: {json.dumps(by_status, indent=4)}", file=sys.stderr)


if __name__ == "__main__":
    main()
