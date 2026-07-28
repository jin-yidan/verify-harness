#!/usr/bin/env python3
"""Generate or validate the machine-derived project status summary."""

from __future__ import annotations

import argparse
import json
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "verification_manifest.json"
STATUS = ROOT / "STATUS.md"


def render_status() -> str:
    try:
        manifest = json.loads(MANIFEST.read_text())
    except (FileNotFoundError, json.JSONDecodeError) as e:
        print(f"error: failed to load {MANIFEST}: {e}", file=sys.stderr)
        sys.exit(1)

    verified = manifest["verified_target"]["modules"]
    draft = manifest["draft_target"]["modules"]
    excluded = manifest.get("excluded_modules", [])

    counts = Counter(entry["status"] for entry in verified)
    exact = [entry for entry in verified if entry["status"] == "exact"]
    weaker = [entry for entry in verified if entry["status"] == "weaker"]
    conditional = [entry for entry in verified if entry["status"] == "conditional"]

    lines = [
        "# Status Summary",
        "",
        "This file is machine-derived from `verification_manifest.json`.",
        "",
        "## Trusted Root",
        "",
        f"- Modules: {len(verified)}",
        f"- Exact: {counts.get('exact', 0)}",
        f"- Weaker: {counts.get('weaker', 0)}",
        f"- Conditional: {counts.get('conditional', 0)}",
        f"- Build command: `{manifest['verified_target']['build_command']}`",
        "",
        "### Exact Modules",
        "",
    ]
    lines.extend(
        f"- `{entry['module']}` — {entry['note']}" for entry in exact
    )
    lines.extend(
        [
            "",
            "### Weaker Modules",
            "",
        ]
    )
    lines.extend(
        f"- `{entry['module']}` — {entry['note']}" for entry in weaker
    )
    lines.extend(
        [
            "",
            "### Conditional Modules",
            "",
        ]
    )
    lines.extend(
        f"- `{entry['module']}` — {entry['note']}" for entry in conditional
    )
    lines.extend(
        [
            "",
            "## Draft Root",
            "",
            f"- Modules: {len(draft)}",
            f"- Build command: `{manifest['draft_target']['build_command']}`",
            "",
        ]
    )
    lines.extend(f"- `{entry['module']}` — {entry['note']}" for entry in draft)
    lines.extend(
        [
            "",
            "## Excluded Modules",
            "",
            f"- Modules: {len(excluded)}",
            "",
        ]
    )
    lines.extend(f"- `{entry['module']}` — {entry['reason']}" for entry in excluded)
    lines.append("")
    return "\n".join(lines)


def render_stats_json() -> str:
    """Emit a JSON object with verification stats for dashboard consumption."""
    try:
        manifest = json.loads(MANIFEST.read_text())
    except (FileNotFoundError, json.JSONDecodeError) as e:
        print(f"error: failed to load {MANIFEST}: {e}", file=sys.stderr)
        sys.exit(1)

    verified = manifest["verified_target"]["modules"]
    draft = manifest["draft_target"]["modules"]
    excluded = manifest.get("excluded_modules", [])
    counts = Counter(entry["status"] for entry in verified)

    stats = {
        "verified_modules": len(verified),
        "draft_modules": len(draft),
        "excluded_modules": len(excluded),
        "exact": counts.get("exact", 0),
        "weaker": counts.get("weaker", 0),
        "conditional": counts.get("conditional", 0),
    }
    return json.dumps(stats, indent=2)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="Write STATUS.md")
    parser.add_argument("--check", action="store_true", help="Check STATUS.md")
    parser.add_argument("--stats-json", action="store_true",
                        help="Print verification stats as JSON")
    args = parser.parse_args()

    if args.stats_json:
        sys.stdout.write(render_stats_json() + "\n")
        return

    content = render_status()
    if args.write:
        STATUS.write_text(content)
    elif args.check:
        current = STATUS.read_text() if STATUS.exists() else ""
        if current != content:
            print("STATUS.md is out of date; run `python3 scripts/generate_status.py --write`.", file=sys.stderr)
            raise SystemExit(1)
    else:
        sys.stdout.write(content)


if __name__ == "__main__":
    main()
