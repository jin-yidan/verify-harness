#!/usr/bin/env python3
"""Generate a verification status dashboard from the manifest.

Outputs a summary JSON and optionally a text-based progress bar suitable
for CI badges or terminal display.

Usage:
    python scripts/dashboard.py              # Print JSON summary
    python scripts/dashboard.py --badge      # Print badge-style one-liner
    python scripts/dashboard.py --json-out dashboard.json  # Write JSON file
"""

from __future__ import annotations

import argparse
import json
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "verification_manifest.json"


def load_manifest() -> dict:
    try:
        return json.loads(MANIFEST.read_text())
    except (FileNotFoundError, json.JSONDecodeError) as e:
        print(f"error: failed to load {MANIFEST}: {e}", file=sys.stderr)
        sys.exit(1)


def compute_stats(manifest: dict) -> dict:
    """Compute verification statistics from the manifest."""
    verified = manifest["verified_target"]["modules"]
    draft = manifest["draft_target"]["modules"]
    excluded = manifest.get("excluded_modules", [])
    theorems = manifest.get("theorems", [])

    module_counts = Counter(m["status"] for m in verified)
    theorem_counts = Counter(t["status"] for t in theorems)

    total_modules = len(verified) + len(draft) + len(excluded)
    verified_count = len(verified)
    exact_count = module_counts.get("exact", 0)
    weaker_count = module_counts.get("weaker", 0)
    conditional_count = module_counts.get("conditional", 0)

    return {
        "total_modules": total_modules,
        "verified_modules": verified_count,
        "draft_modules": len(draft),
        "excluded_modules": len(excluded),
        "exact_modules": exact_count,
        "weaker_modules": weaker_count,
        "conditional_modules": conditional_count,
        "total_theorems": len(theorems),
        "theorem_status": dict(theorem_counts),
        "exact_pct": round(100 * exact_count / verified_count, 1) if verified_count else 0,
        "verified_pct": round(100 * verified_count / total_modules, 1) if total_modules else 0,
    }


def format_badge(stats: dict) -> str:
    """One-line badge string: 'verified: 37/44 (27 exact, 7 weaker, 3 conditional)'"""
    return (
        f"verified: {stats['verified_modules']}/{stats['total_modules']} "
        f"({stats['exact_modules']} exact, "
        f"{stats['weaker_modules']} weaker, "
        f"{stats['conditional_modules']} conditional)"
    )


def format_progress_bar(stats: dict, width: int = 40) -> str:
    """Text-based progress bar for terminal display."""
    total = stats["total_modules"]
    if total == 0:
        return "[" + " " * width + "] 0/0"

    exact_w = int(width * stats["exact_modules"] / total)
    weaker_w = int(width * stats["weaker_modules"] / total)
    cond_w = int(width * stats["conditional_modules"] / total)
    draft_w = int(width * stats["draft_modules"] / total)
    rest_w = width - exact_w - weaker_w - cond_w - draft_w

    bar = (
        "#" * exact_w
        + "~" * weaker_w
        + "?" * cond_w
        + "." * draft_w
        + " " * rest_w
    )
    return f"[{bar}] {stats['verified_modules']}/{stats['total_modules']}"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--badge", action="store_true",
                        help="Print badge-style one-liner")
    parser.add_argument("--bar", action="store_true",
                        help="Print text progress bar")
    parser.add_argument("--json-out", type=str, default=None,
                        help="Write JSON stats to file")
    args = parser.parse_args()

    manifest = load_manifest()
    stats = compute_stats(manifest)

    if args.json_out:
        Path(args.json_out).write_text(json.dumps(stats, indent=2) + "\n")
        print(f"Stats written to {args.json_out}", file=sys.stderr)

    if args.badge:
        print(format_badge(stats))
    elif args.bar:
        print(format_progress_bar(stats))
        print(f"  # = exact  ~ = weaker  ? = conditional  . = draft")
    else:
        print(json.dumps(stats, indent=2))


if __name__ == "__main__":
    main()
