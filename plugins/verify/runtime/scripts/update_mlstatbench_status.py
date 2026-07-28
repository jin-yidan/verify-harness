#!/usr/bin/env python3
"""Add theorem_status field to each problem in mlstatbench.json.

Reads verification_manifest.json to determine per-theorem statuses
(exact/conditional/wrapper/stub/vacuous) and patches each problem
entry in mlstatbench.json with a `theorem_status` field.

The existing `status` field is left unchanged for backward compatibility.
The new `theorem_status` field provides the canonical classification:
  - exact:       Fully proved, zero sorry
  - conditional:  Proved modulo stated hypotheses
  - wrapper:     Thin wrapper around a deeper theorem
  - stub:        Placeholder with sorry
  - vacuous:     Vacuously true (trivial hypotheses)

Usage:
    python scripts/update_mlstatbench_status.py
    python scripts/update_mlstatbench_status.py --dry-run
"""

import argparse
import json
import sys
from pathlib import Path


def load_manifest_statuses(root: Path) -> dict[str, str]:
    """Load all status information from verification_manifest.json."""
    manifest_path = root / "verification_manifest.json"
    if not manifest_path.exists():
        print(f"error: {manifest_path} not found", file=sys.stderr)
        sys.exit(1)

    data = json.loads(manifest_path.read_text())
    statuses: dict[str, str] = {}

    # Module-level statuses
    for entry in data.get("verified_target", {}).get("modules", []):
        statuses[entry["module"]] = entry.get("status", "unknown")

    # Theorem-level statuses (more specific, override module-level)
    for entry in data.get("theorems", []):
        statuses[entry["name"]] = entry.get("status", "unknown")

    return statuses


def resolve_status(problem: dict, statuses: dict[str, str]) -> str:
    """Resolve the theorem_status for a single problem entry."""
    # Try exact theorem name lookups first
    for key in [
        problem.get("qualified_name", ""),
        problem.get("theorem_name", ""),
    ]:
        if key in statuses:
            return statuses[key]

    # Try with common namespace prefixes
    for prefix in [
        "FiniteMDP.",
        "FiniteHorizonMDP.",
        "BanditInstance.",
        "ImitationSetting.",
        "MixingChain.",
    ]:
        key = prefix + problem.get("theorem_name", "")
        if key in statuses:
            return statuses[key]

    # Fall back to module-level status
    module = problem.get("source_module", "")
    if module in statuses:
        return statuses[module]

    # Last resort: use existing status field
    return problem.get("status", "unknown")


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Add theorem_status field to mlstatbench.json problems.")
    parser.add_argument("--root", type=Path,
                        default=Path(__file__).resolve().parent.parent,
                        help="Project root directory (default: auto-detect)")
    parser.add_argument("--bench", type=Path, default=None,
                        help="Path to mlstatbench.json (default: <root>/benchmark/mlstatbench.json)")
    parser.add_argument("--dry-run", action="store_true",
                        help="Print summary without writing changes")
    args = parser.parse_args()

    root = args.root.resolve()
    bench_path = (args.bench or root / "benchmark" / "mlstatbench.json").resolve()

    if not bench_path.exists():
        print(f"error: {bench_path} not found", file=sys.stderr)
        sys.exit(1)

    statuses = load_manifest_statuses(root)
    data = json.loads(bench_path.read_text())

    changed = 0
    by_status: dict[str, int] = {}

    for problem in data["problems"]:
        ts = resolve_status(problem, statuses)
        if "theorem_status" not in problem or problem["theorem_status"] != ts:
            changed += 1
        problem["theorem_status"] = ts
        by_status[ts] = by_status.get(ts, 0) + 1

    print(f"Processed {len(data['problems'])} problems, {changed} updated",
          file=sys.stderr)
    print(f"  By theorem_status: {json.dumps(by_status, indent=4)}",
          file=sys.stderr)

    if args.dry_run:
        print("(dry run, no file written)", file=sys.stderr)
        return

    bench_path.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n")
    print(f"  Written: {bench_path}", file=sys.stderr)


if __name__ == "__main__":
    main()
