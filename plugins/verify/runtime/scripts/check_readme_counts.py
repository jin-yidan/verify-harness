#!/usr/bin/env python3
"""Validate that README.md module counts match verification_manifest.json."""

from __future__ import annotations

import json
import re
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "verification_manifest.json"
README = ROOT / "README.md"


def main() -> None:
    manifest = json.loads(MANIFEST.read_text())
    verified = manifest["verified_target"]["modules"]
    draft = manifest["draft_target"]["modules"]
    excluded = manifest.get("excluded_modules", [])
    counts = Counter(entry["status"] for entry in verified)

    expected = {
        "trusted root": len(verified),
        "exact": counts.get("exact", 0),
        "conditional": counts.get("conditional", 0),
        "draft root": len(draft),
        "excluded modules": len(excluded),
    }

    readme = README.read_text()
    errors: list[str] = []

    for label, expected_count in expected.items():
        pattern = rf"-\s+{re.escape(label)}:\s+(\d+)\s+modules?"
        match = re.search(pattern, readme)
        if not match:
            errors.append(f"  {label}: pattern not found in README.md")
            continue
        actual = int(match.group(1))
        if actual != expected_count:
            errors.append(
                f"  {label}: README says {actual}, manifest says {expected_count}"
            )

    # Validate theorem-level status counts (wrapper, weaker) mentioned in prose.
    # The README says "in the trusted root", so count only theorems whose
    # module is in verified_target.
    trusted_modules = {e["module"] for e in verified}
    theorems = manifest.get("theorems", [])
    trusted_thm_counts = Counter(
        t.get("status", "") for t in theorems if t["module"] in trusted_modules
    )

    thm_checks = {
        "wrapper": (r"(\w+)\s+wrapper\s+theorem", trusted_thm_counts.get("wrapper", 0)),
        "weaker": (r"(\w+)\s+theorems?\s+are\s+labeled\s+`weaker`", trusted_thm_counts.get("weaker", 0)),
    }
    _WORD_TO_INT = {
        "zero": 0, "one": 1, "two": 2, "three": 3, "four": 4, "five": 5,
        "six": 6, "seven": 7, "eight": 8, "nine": 9, "ten": 10,
        "eleven": 11, "twelve": 12, "thirteen": 13, "fourteen": 14,
        "fifteen": 15, "sixteen": 16, "seventeen": 17, "eighteen": 18,
        "nineteen": 19, "twenty": 20,
    }

    for label, (pattern, expected_count) in thm_checks.items():
        match = re.search(pattern, readme, re.IGNORECASE)
        if not match:
            errors.append(f"  {label} theorems: pattern not found in README.md")
            continue
        word = match.group(1).lower()
        actual = _WORD_TO_INT.get(word)
        if actual is None:
            try:
                actual = int(word)
            except ValueError:
                errors.append(f"  {label} theorems: could not parse count '{word}'")
                continue
        if actual != expected_count:
            errors.append(
                f"  {label} theorems: README says {actual}, manifest says {expected_count}"
            )

    if errors:
        print("README.md counts are out of date:", file=sys.stderr)
        for e in errors:
            print(e, file=sys.stderr)
        print(
            "\nUpdate the counts in README.md to match verification_manifest.json.",
            file=sys.stderr,
        )
        sys.exit(1)
    else:
        print("README.md counts match manifest")


if __name__ == "__main__":
    main()
