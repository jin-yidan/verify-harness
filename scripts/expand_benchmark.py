#!/usr/bin/env python3
"""Expand the MLStatBench benchmark by scanning all .lean modules (#62).

Scans ALL .lean files in the project (including new Phase 1-6 modules)
and re-extracts theorems to expand the benchmark.  Delegates to the
existing extract_theorems.py logic for the actual extraction.

This script:
  1. Discovers all .lean files under RLGeneralization/
  2. Compares against the current benchmark to find new theorems
  3. Extracts new theorems using extract_theorems.py routines
  4. Merges them into the existing benchmark

Usage:
    python scripts/expand_benchmark.py
    python scripts/expand_benchmark.py --dry-run
    python scripts/expand_benchmark.py --output benchmark/mlstatbench_expanded.json
    python scripts/expand_benchmark.py --help
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# Import extraction logic from the benchmark module
sys.path.insert(0, str(ROOT / "benchmark"))
try:
    from extract_theorems import (
        extract_declarations,
        classify_domain,
        classify_difficulty,
        is_bridge_problem,
        load_statuses,
        normalize_proof_arg_names,
        DOMAIN_MAP,
    )
except ImportError as e:
    print(f"error: could not import extract_theorems: {e}", file=sys.stderr)
    print("Ensure benchmark/extract_theorems.py exists.", file=sys.stderr)
    sys.exit(1)


def discover_lean_files(scan_dir: Path) -> list[tuple[Path, str]]:
    """Find all .lean files and compute their module names.

    Returns list of (filepath, module_name) pairs.
    """
    results = []
    for lean_file in sorted(scan_dir.rglob("*.lean")):
        rel = lean_file.relative_to(ROOT)
        module = ".".join(rel.with_suffix("").parts)
        results.append((lean_file, module))
    return results


def load_existing_benchmark(path: Path) -> dict:
    """Load the existing benchmark JSON."""
    if not path.exists():
        return {"problems": [], "total_problems": 0}
    try:
        return json.loads(path.read_text())
    except (json.JSONDecodeError, KeyError) as e:
        print(f"warning: could not load {path}: {e}", file=sys.stderr)
        return {"problems": [], "total_problems": 0}


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Expand MLStatBench by scanning all .lean files for new theorems."
    )
    parser.add_argument(
        "--benchmark", default="benchmark/mlstatbench.json",
        help="Path to existing benchmark JSON."
    )
    parser.add_argument(
        "--output", default=None,
        help="Output path for expanded benchmark. Defaults to overwriting --benchmark."
    )
    parser.add_argument(
        "--scan-dir", default="RLGeneralization",
        help="Directory to scan for .lean files (relative to project root)."
    )
    parser.add_argument(
        "--dry-run", action="store_true",
        help="Show what would be added without modifying files."
    )
    args = parser.parse_args()

    benchmark_path = ROOT / args.benchmark
    scan_dir = ROOT / args.scan_dir

    if not scan_dir.exists():
        print(f"error: scan directory not found: {scan_dir}", file=sys.stderr)
        sys.exit(1)

    # Load existing benchmark
    existing = load_existing_benchmark(benchmark_path)
    existing_names = {
        (p["source_module"], p["theorem_name"])
        for p in existing.get("problems", [])
    }

    print(f"Existing benchmark: {len(existing.get('problems', []))} problems",
          file=sys.stderr)

    # Discover and extract from all .lean files
    lean_files = discover_lean_files(scan_dir)
    print(f"Found {len(lean_files)} .lean files in {scan_dir}", file=sys.stderr)

    statuses = load_statuses()
    new_decls: list[dict] = []

    for filepath, module in lean_files:
        try:
            decls = extract_declarations(filepath, module)
        except Exception as e:
            print(f"warning: failed to extract from {filepath}: {e}",
                  file=sys.stderr)
            continue

        for decl in decls:
            key = (module, decl["name"])
            if key not in existing_names:
                new_decls.append(decl)
                existing_names.add(key)

    print(f"Found {len(new_decls)} new theorem(s)", file=sys.stderr)

    if args.dry_run:
        print("\nNew theorems that would be added:")
        for decl in new_decls:
            domain = classify_domain(decl["module"])
            print(f"  {decl['module']}.{decl['name']} [{domain}]")
        sys.exit(0)

    # Build new problem entries
    next_id = len(existing.get("problems", []))
    new_problems: list[dict] = []

    for decl in new_decls:
        domain = classify_domain(decl["module"])

        # Look up status
        status = "unknown"
        for key in [
            decl["qualified_name"],
            decl["name"],
            decl["module"],
        ]:
            if key in statuses:
                status = statuses[key]
                break

        difficulty = classify_difficulty(status, decl["proof_lines"], domain)
        if is_bridge_problem(decl["name"], decl["module"]):
            difficulty = "bridge"

        new_problems.append({
            "id": f"rl_{next_id:04d}",
            "source": "rl",
            "source_file": decl["file"],
            "source_line": decl["line"],
            "source_module": decl["module"],
            "theorem_name": decl["name"],
            "qualified_name": decl["qualified_name"],
            "context_prefix": decl["context_prefix"],
            "context_suffix": decl["context_suffix"],
            "proof_arg_names": decl["proof_arg_names"],
            "receiver_args": decl.get("receiver_args", []),
            "theorem_binders": decl.get("theorem_binders", []),
            "has_receiver": decl.get("has_receiver", False),
            "kind": decl["kind"],
            "statement": decl["statement"],
            "informal_description": decl["docstring"],
            "domain": domain,
            "difficulty": difficulty,
            "status": status,
            "proof_lines": decl["proof_lines"],
            "problem_type": "full_theorem_proving",
        })
        next_id += 1

    # Merge
    all_problems = existing.get("problems", []) + new_problems
    output = {
        **existing,
        "problems": all_problems,
        "total_problems": len(all_problems),
    }

    out_path = Path(args.output) if args.output else benchmark_path
    if not out_path.is_absolute():
        out_path = ROOT / out_path

    out_path.write_text(json.dumps(output, indent=2, ensure_ascii=False) + "\n")
    print(f"\nExpanded benchmark: {len(all_problems)} problems "
          f"(+{len(new_problems)} new)", file=sys.stderr)
    print(f"Written to {out_path}", file=sys.stderr)


if __name__ == "__main__":
    main()
