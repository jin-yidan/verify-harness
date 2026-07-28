#!/usr/bin/env python3
"""Validate verification_manifest.json consistency.

Checks that trusted/draft imports match the manifest, that no classification
overlaps exist, that all modules are classified, and that status values are
from the allowed set.
"""

import json
import re
import sys
from pathlib import Path


def parse_imports(path: Path) -> list[str]:
    text = path.read_text()
    return re.findall(r"^import\s+(.+)$", text, re.M)


def module_of(path: Path) -> str:
    return ".".join(path.with_suffix("").parts)


def fail(msg: str) -> None:
    print(msg, file=sys.stderr)
    raise SystemExit(1)


def main() -> None:
    root = Path(".")
    try:
        manifest = json.loads((root / "verification_manifest.json").read_text())
    except (FileNotFoundError, json.JSONDecodeError) as e:
        fail(f"failed to load verification_manifest.json: {e}")

    trusted_imports = parse_imports(root / "RLGeneralization.lean")
    draft_imports = parse_imports(root / "RLGeneralization" / "Draft.lean")

    trusted_manifest = [entry["module"] for entry in manifest["verified_target"]["modules"]]
    draft_manifest = [entry["module"] for entry in manifest["draft_target"]["modules"]]
    excluded_manifest = [entry["module"] for entry in manifest.get("excluded_modules", [])]
    theorem_modules = [entry["module"] for entry in manifest["theorems"]]

    if trusted_imports != trusted_manifest:
        fail(
            "trusted-root imports do not match verification_manifest.json verified_target.modules"
        )

    if draft_imports != draft_manifest:
        fail(
            "draft-root imports do not match verification_manifest.json draft_target.modules"
        )

    classified_sets = {
        "verified_target.modules": set(trusted_manifest),
        "draft_target.modules": set(draft_manifest),
        "excluded_modules": set(excluded_manifest),
    }

    for left_name, left_modules in classified_sets.items():
        for right_name, right_modules in classified_sets.items():
            if left_name >= right_name:
                continue
            overlap = sorted(left_modules & right_modules)
            if overlap:
                fail(
                    f"module classification overlap between {left_name} and {right_name}: "
                    + ", ".join(overlap)
                )

    repo_modules = {
        module_of(path.relative_to(root))
        for path in (root / "RLGeneralization").rglob("*.lean")
    }
    classified_modules = (
        set(trusted_manifest)
        | set(draft_manifest)
        | set(excluded_manifest)
        | {manifest["draft_target"]["root_module"]}
    )

    missing_modules = sorted(repo_modules - classified_modules)
    if missing_modules:
        fail(
            "Lean modules under RLGeneralization/ are not classified in verification_manifest.json: "
            + ", ".join(missing_modules)
        )

    extra_modules = sorted(classified_modules - repo_modules)
    if extra_modules:
        fail(
            "verification_manifest.json classifies modules that do not exist under RLGeneralization/: "
            + ", ".join(extra_modules)
        )

    excluded_root_imports = sorted(
        set(excluded_manifest) & (set(trusted_imports) | set(draft_imports))
    )
    if excluded_root_imports:
        fail(
            "excluded_modules must not be imported by trusted or draft roots: "
            + ", ".join(excluded_root_imports)
        )

    known_theorem_modules = set(trusted_manifest) | set(draft_manifest) | set(excluded_manifest)
    unknown_theorem_modules = sorted(set(theorem_modules) - known_theorem_modules)
    if unknown_theorem_modules:
        fail(
            "theorems list contains modules outside verified_target.modules, draft_target.modules, and excluded_modules: "
            + ", ".join(unknown_theorem_modules)
        )

    allowed_statuses = {"exact", "weaker", "conditional", "wrapper", "stub", "vacuous"}
    bad_verified_statuses = [
        entry["module"]
        for entry in manifest["verified_target"]["modules"]
        if entry.get("status") not in allowed_statuses
    ]
    if bad_verified_statuses:
        fail(
            "verified_target.modules contains unknown statuses for: "
            + ", ".join(bad_verified_statuses)
        )

    banned_verified_statuses = {"wrapper", "stub", "vacuous"}
    verified_banned = [
        f'{entry["module"]} ({entry.get("status")})'
        for entry in manifest["verified_target"]["modules"]
        if entry.get("status") in banned_verified_statuses
    ]
    if verified_banned:
        fail(
            "verified_target.modules must not contain wrapper/stub/vacuous statuses: "
            + ", ".join(verified_banned)
        )

    bad_theorem_statuses = [
        entry["name"]
        for entry in manifest["theorems"]
        if entry.get("status") not in allowed_statuses
    ]
    if bad_theorem_statuses:
        fail(
            "theorems contains unknown statuses for: " + ", ".join(bad_theorem_statuses)
        )

    print("manifest consistency checks passed")


if __name__ == "__main__":
    main()
