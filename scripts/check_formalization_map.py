#!/usr/bin/env python3
"""Validate FORMALIZATION_MAP.md against verification_manifest.json.

Checks:
  - Every manifest module appears in the map (no missing modules)
  - Every map module appears in the manifest (no phantom modules)
  - Status labels in the map match the manifest
  - Section header counts match actual entry counts
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MANIFEST_PATH = ROOT / "verification_manifest.json"
MAP_PATH = ROOT / "FORMALIZATION_MAP.md"

# Regex to extract module names from bullet entries like:
#   - `RLGeneralization.Foo.Bar` -- description. (exact)
MODULE_RE = re.compile(r"^- `(RLGeneralization\.[^`]+)`")

# Regex to extract trailing status label like (exact) or (conditional: ...)
STATUS_RE = re.compile(r"\((exact|conditional|weaker|wrapper|stub|vacuous)(?:[^)]*)\)\s*$")

# Regex to extract section header counts like: ### MDP Core (12 modules)
SECTION_RE = re.compile(r"^###\s+(.+?)\s+\((\d+)\s+modules?\)")


def load_manifest() -> dict:
    try:
        return json.loads(MANIFEST_PATH.read_text())
    except (FileNotFoundError, json.JSONDecodeError) as e:
        print(f"error: failed to load {MANIFEST_PATH}: {e}", file=sys.stderr)
        sys.exit(1)


def parse_map() -> tuple[list[tuple[str, str | None, int]], list[tuple[str, int, int]]]:
    """Parse FORMALIZATION_MAP.md.

    Returns:
      modules: list of (module_name, status_label_or_None, line_number)
      sections: list of (section_name, claimed_count, line_number)
      header_lines: list of line numbers where any markdown header (## or ###) appears
    """
    modules: list[tuple[str, str | None, int]] = []
    sections: list[tuple[str, int, int]] = []
    header_lines: list[int] = []

    try:
        lines = MAP_PATH.read_text().splitlines()
    except FileNotFoundError:
        print(f"error: {MAP_PATH} not found", file=sys.stderr)
        sys.exit(1)

    for i, line in enumerate(lines, 1):
        if line.startswith("## ") or line.startswith("### "):
            header_lines.append(i)

        sec_match = SECTION_RE.match(line)
        if sec_match:
            sections.append((sec_match.group(1), int(sec_match.group(2)), i))

        mod_match = MODULE_RE.match(line)
        if mod_match:
            mod_name = mod_match.group(1)
            status_match = STATUS_RE.search(line)
            status = status_match.group(1) if status_match else None
            modules.append((mod_name, status, i))

    return modules, sections, header_lines


def check() -> list[str]:
    """Run all consistency checks. Returns list of error messages."""
    errors: list[str] = []
    manifest = load_manifest()

    # Build manifest module -> status lookup (verified + draft + excluded)
    manifest_modules: dict[str, str] = {}
    for entry in manifest["verified_target"]["modules"]:
        manifest_modules[entry["module"]] = entry.get("status", "unknown")
    for entry in manifest.get("draft_target", {}).get("modules", []):
        manifest_modules[entry["module"]] = "draft"
    for entry in manifest.get("excluded_modules", []):
        manifest_modules[entry["module"]] = "excluded"

    map_modules, sections, header_lines = parse_map()
    map_names = {m[0] for m in map_modules}

    # Check 1: Missing modules (in manifest but not in map)
    for mod in manifest_modules:
        if mod not in map_names:
            errors.append(f"missing from map: {mod} (manifest status: {manifest_modules[mod]})")

    # Check 2: Phantom modules (in map but not in manifest)
    for mod_name, _, line_num in map_modules:
        if mod_name not in manifest_modules:
            errors.append(f"FORMALIZATION_MAP.md:{line_num}: phantom module {mod_name} (not in manifest)")

    # Check 3: Status mismatches (only for verified_target modules with explicit labels)
    verified_status = {
        entry["module"]: entry.get("status", "unknown")
        for entry in manifest["verified_target"]["modules"]
    }
    for mod_name, map_status, line_num in map_modules:
        if map_status is None:
            continue  # no explicit status label in the map — skip
        manifest_status = verified_status.get(mod_name)
        if manifest_status is None:
            continue  # draft/excluded module — skip status check
        if map_status != manifest_status:
            errors.append(
                f"FORMALIZATION_MAP.md:{line_num}: status mismatch for {mod_name}: "
                f"map says '{map_status}', manifest says '{manifest_status}'"
            )

    # Check 4: Section header counts
    # For each counted section, find the range [section_line, next_header_line)
    # and count modules within that range
    for sec_name, claimed, sec_line in sections:
        # Find the next header line after this section
        next_header = None
        for hl in header_lines:
            if hl > sec_line:
                next_header = hl
                break
        # Count modules in range [sec_line, next_header)
        actual = 0
        for _, _, mod_line in map_modules:
            if mod_line > sec_line and (next_header is None or mod_line < next_header):
                actual += 1
        if actual != claimed:
            errors.append(
                f"FORMALIZATION_MAP.md:{sec_line}: section '{sec_name}' claims {claimed} "
                f"modules but has {actual}"
            )

    return errors


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check", action="store_true",
        help="Validate FORMALIZATION_MAP.md against the manifest (exit 1 on mismatch)"
    )
    args = parser.parse_args()

    if not args.check:
        print("Usage: python3 scripts/check_formalization_map.py --check")
        sys.exit(1)

    errors = check()
    if errors:
        print("FORMALIZATION_MAP.md consistency errors:", file=sys.stderr)
        for err in errors:
            print(f"  {err}", file=sys.stderr)
        sys.exit(1)
    else:
        print("FORMALIZATION_MAP.md consistency checks passed")


if __name__ == "__main__":
    main()
