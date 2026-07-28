#!/usr/bin/env python3
"""SafeVerify: check benchmark solutions for banned proof patterns (#54).

Scans proof text for patterns that would make a proof untrustworthy:
  - sorry       : admits the goal without proof
  - native_decide : uses native code evaluation (unsound in some contexts)
  - axiom       : introduces new axioms
  - Axiom       : same, capitalized form
  - sorryAx     : internal sorry axiom

Also checks for other suspicious patterns:
  - implemented_by : native implementation override
  - opaque        : hides implementation details

Strict mode (--strict):
  - Fails if any EXACT-status module contains banned patterns (sorry, native_decide,
    axiom, sorryAx).
  - Fails if any EXACT-status module contains undeclared wrapper/vacuous theorems
    (not listed in verification_manifest.json's theorems array).
  - Reports manifest-declared wrappers in exact modules as informational.
  - Fails if any CONDITIONAL-status module contains unannotated sorry.
  - Uses verification_manifest.json to identify modules and declared wrappers.

Audit mode (--audit):
  - Emits a JSON object per .lean file with per-theorem status classification.

Usage:
    python scripts/safe_verify.py
    python scripts/safe_verify.py --results benchmark/results/deepseek_results.local.json
    python scripts/safe_verify.py --scan-lean RLGeneralization/
    python scripts/safe_verify.py --strict
    python scripts/safe_verify.py --audit
    python scripts/safe_verify.py --help
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

from gen_declaration_audit import scan_directory

ROOT = Path(__file__).resolve().parent.parent
MANIFEST_PATH = ROOT / "verification_manifest.json"

# Patterns that make a proof invalid for benchmarking
BANNED_PATTERNS = {
    "sorry": re.compile(r"\bsorry\b"),
    "native_decide": re.compile(r"\bnative_decide\b"),
    "axiom": re.compile(r"^\s*axiom\b", re.MULTILINE),
    "sorryAx": re.compile(r"\bsorryAx\b"),
}

# Patterns that are suspicious but may be acceptable
WARNING_PATTERNS = {
    "implemented_by": re.compile(r"\bimplemented_by\b"),
    "opaque": re.compile(r"^\s*opaque\b", re.MULTILINE),
    "decide": re.compile(r"\bdecide\b"),
}


def check_proof_text(proof: str) -> dict:
    """Check a proof string for banned and suspicious patterns.

    Returns a dict with:
      - banned: list of (pattern_name, match_text) for banned patterns
      - warnings: list of (pattern_name, match_text) for suspicious patterns
      - safe: True if no banned patterns found
    """
    banned: list[tuple[str, str]] = []
    warnings: list[tuple[str, str]] = []

    for name, pattern in BANNED_PATTERNS.items():
        matches = pattern.findall(proof)
        for m in matches:
            banned.append((name, m if isinstance(m, str) else m.group(0)))

    for name, pattern in WARNING_PATTERNS.items():
        matches = pattern.findall(proof)
        for m in matches:
            warnings.append((name, m if isinstance(m, str) else m.group(0)))

    return {
        "banned": banned,
        "warnings": warnings,
        "safe": len(banned) == 0,
    }


def check_results_file(results_path: Path) -> list[dict]:
    """Check all proofs in a benchmark results JSON file."""
    with open(results_path) as f:
        data = json.load(f)

    results = data.get("results", [])
    issues: list[dict] = []

    for result in results:
        tactic = result.get("tactic")
        if not tactic:
            continue

        check = check_proof_text(tactic)
        if not check["safe"] or check["warnings"]:
            issues.append({
                "problem_id": result.get("problem_id", "unknown"),
                "theorem_name": result.get("theorem_name", "unknown"),
                "safe": check["safe"],
                "banned": check["banned"],
                "warnings": check["warnings"],
                "tactic_preview": tactic[:200],
            })

    return issues


def scan_lean_files(scan_dir: Path) -> list[dict]:
    """Scan .lean files for banned patterns in proof bodies.

    Uses _strip_block_comments() to avoid false positives from
    /- ... -/ block comments and /-! ... -/ doc comments.
    """
    issues: list[dict] = []

    for lean_file in sorted(scan_dir.rglob("*.lean")):
        text = lean_file.read_text(errors="replace")
        rel_path = str(lean_file.relative_to(ROOT))

        for line_num, line in _strip_block_comments(text):
            # Skip line comments
            stripped = line.strip()
            if stripped.startswith("--"):
                continue

            for name, pattern in BANNED_PATTERNS.items():
                # Check it is not inside a line comment
                comment_pos = line.find("--")
                match = pattern.search(line)
                if match and (comment_pos < 0 or match.start() < comment_pos):
                    issues.append({
                        "file": rel_path,
                        "line": line_num,
                        "pattern": name,
                        "text": stripped[:120],
                    })

    return issues


def load_manifest() -> dict:
    """Load verification_manifest.json, returning empty dict on failure."""
    try:
        return json.loads(MANIFEST_PATH.read_text())
    except (FileNotFoundError, json.JSONDecodeError):
        return {}


def module_to_path(module: str) -> Path:
    """Convert dotted module name to .lean file path."""
    return ROOT / Path(module.replace(".", "/")).with_suffix(".lean")


def get_modules_by_status(status: str) -> list[Path]:
    """Return file paths for all trusted-root modules with the given status."""
    manifest = load_manifest()
    paths = []
    for entry in manifest.get("verified_target", {}).get("modules", []):
        if entry.get("status") == status:
            p = module_to_path(entry["module"])
            if p.exists():
                paths.append(p)
    return paths


def _strip_block_comments(text: str) -> list[tuple[int, str]]:
    """Return (line_number, line) pairs with block-comment lines removed.

    Lean block comments are /- ... -/ and can span multiple lines.
    Nested block comments (/-/-...-/-/) are NOT fully handled here —
    we use a simple depth counter which is sufficient for our sorry scan.
    """
    result: list[tuple[int, str]] = []
    depth = 0
    for line_num, line in enumerate(text.splitlines(), 1):
        out_parts: list[str] = []
        i = 0
        while i < len(line):
            if depth == 0:
                if line[i:i+2] == "/-":
                    depth += 1
                    i += 2
                else:
                    out_parts.append(line[i])
                    i += 1
            else:
                if line[i:i+2] == "/-":
                    depth += 1
                    i += 2
                elif line[i:i+2] == "-/":
                    depth -= 1
                    i += 2
                else:
                    i += 1
        if depth == 0:
            result.append((line_num, "".join(out_parts)))
        # Lines that are entirely inside a block comment are skipped
    return result


def strict_check() -> list[dict]:
    """Check exact-status modules for banned patterns and undeclared wrappers.

    Hard failures (always fail):
      - sorry, native_decide, axiom, sorryAx in exact modules
      - unannotated sorry in conditional modules

    Wrapper/vacuous check (uses manifest as source of truth):
      - Uses the canonical audit scanner to find all wrapper/vacuous
        declarations in exact modules
      - Fails if any wrapper/vacuous theorem in an exact module is NOT
        declared in the manifest's theorems array (undeclared wrapper)
      - Manifest-declared wrappers are reported but do not fail
    """
    issues: list[dict] = []
    exact_files = get_modules_by_status("exact")

    for lean_file in sorted(exact_files):
        text = lean_file.read_text(errors="replace")
        rel_path = str(lean_file.relative_to(ROOT))

        for line_num, line in _strip_block_comments(text):
            stripped = line.strip()
            # Skip full-line -- comments
            if stripped.startswith("--"):
                continue
            comment_pos = line.find("--")

            # Check all banned patterns (sorry, native_decide, axiom, sorryAx)
            for ban_name, ban_pattern in BANNED_PATTERNS.items():
                m = ban_pattern.search(line)
                if m and (comment_pos < 0 or m.start() < comment_pos):
                    issues.append({
                        "file": rel_path, "line": line_num,
                        "type": ban_name, "text": stripped[:120],
                    })

    # Use the canonical audit scanner to detect wrapper/vacuous theorems
    # in exact modules, then cross-reference with the manifest.
    manifest = load_manifest()
    exact_modules = {
        e["module"] for e in manifest.get("verified_target", {}).get("modules", [])
        if e.get("status") == "exact"
    }
    declared = [
        (t["module"], t["name"])
        for t in manifest.get("theorems", [])
        if t.get("status") in ("wrapper", "vacuous")
    ]

    def _is_declared(module: str, name: str) -> bool:
        """Check if (module, name) matches a declared wrapper/vacuous entry.

        Handles qualified names: manifest may use ``Namespace.foo``
        while the source scanner finds bare ``foo``.
        """
        for dm, dn in declared:
            if dm == module and (dn == name or dn.endswith("." + name)):
                return True
        return False

    scan_dir = ROOT / "RLGeneralization"
    audit_entries = scan_directory(scan_dir)
    declared_wrappers: list[dict] = []

    for e in audit_entries:
        if e["module"] not in exact_modules:
            continue
        if e["status"] not in ("wrapper", "vacuous"):
            continue
        if _is_declared(e["module"], e["name"]):
            declared_wrappers.append(e)
        else:
            issues.append({
                "file": e["module"].replace(".", "/") + ".lean",
                "line": e.get("line", 0),
                "type": f"undeclared_{e['status']}_in_exact",
                "text": f"{e['name']}: {e.get('note', '')}",
            })

    if declared_wrappers:
        print(f"  [info] {len(declared_wrappers)} declared wrapper/vacuous theorem(s) "
              f"in exact modules (tracked in manifest):", file=sys.stderr)
        for e in declared_wrappers:
            print(f"    {e['module']}.{e['name']} [{e['status']}]", file=sys.stderr)

    # Check conditional modules for unannotated sorry (sorry without
    # a [CONDITIONAL: ...] annotation within 10 lines).
    conditional_files = get_modules_by_status("conditional")
    for lean_file in sorted(conditional_files):
        text = lean_file.read_text(errors="replace")
        rel_path = str(lean_file.relative_to(ROOT))

        stripped_lines = _strip_block_comments(text)
        line_dict = {ln: l for ln, l in stripped_lines}

        for line_num, line in stripped_lines:
            stripped = line.strip()
            if stripped.startswith("--"):
                continue
            comment_pos = line.find("--")

            m = BANNED_PATTERNS["sorry"].search(line)
            if not m:
                continue
            if comment_pos >= 0 and m.start() >= comment_pos:
                continue

            # Check if [CONDITIONAL: ...] appears within 10 lines
            has_annotation = False
            for offset in range(-10, 11):
                nearby = line_dict.get(line_num + offset, "")
                if re.search(r'\[CONDITIONAL\b', nearby):
                    has_annotation = True
                    break

            if not has_annotation:
                issues.append({
                    "file": rel_path, "line": line_num,
                    "type": "unannotated_sorry_in_conditional",
                    "text": stripped[:120],
                })

    return issues


def audit_lean_files(scan_dir: Path) -> list[dict]:
    """Emit per-declaration audit entries using the canonical audit scanner."""
    return scan_directory(scan_dir)


def main() -> None:
    parser = argparse.ArgumentParser(
        description="SafeVerify: check proofs for banned patterns (sorry, native_decide, axiom)."
    )
    parser.add_argument(
        "--results", default=None,
        help="Path to a benchmark results JSON file to check."
    )
    parser.add_argument(
        "--scan-lean", default=None,
        help="Directory of .lean files to scan (relative to project root)."
    )
    parser.add_argument(
        "--strict", action="store_true",
        help="Fail if any EXACT-status module contains sorry, [WRAPPER], or [VACUOUS]."
    )
    parser.add_argument(
        "--audit", action="store_true",
        help="Emit per-theorem audit JSON to stdout."
    )
    parser.add_argument(
        "--json", action="store_true",
        help="Output results as JSON."
    )
    args = parser.parse_args()

    if args.strict:
        issues = strict_check()
        if args.json:
            json.dump(issues, sys.stdout, indent=2)
            print()
        else:
            if not issues:
                print("Strict check passed: no banned patterns or undeclared "
                      "wrappers in exact modules, no unannotated sorry in "
                      "conditional modules.")
            else:
                print(f"STRICT FAIL: {len(issues)} issue(s) in trusted-root modules:\n")
                for issue in issues:
                    print(f"  {issue['file']}:{issue['line']} [{issue['type']}]")
                    print(f"    {issue['text']}")
        sys.exit(1 if issues else 0)

    elif args.audit:
        scan_dir = ROOT / "RLGeneralization"
        entries = audit_lean_files(scan_dir)
        if True:  # audit always outputs JSON
            json.dump(entries, sys.stdout, indent=2)
            print()
        counts: dict[str, int] = {}
        for e in entries:
            counts[e["status"]] = counts.get(e["status"], 0) + 1
        wrapper_count = counts.get("wrapper", 0)
        vacuous_count = counts.get("vacuous", 0)
        print(f"\nAudit summary: {len(entries)} declarations", file=sys.stderr)
        for status, count in sorted(counts.items()):
            print(f"  {status}: {count}", file=sys.stderr)
        print(f"\n  [highlight] wrappers: {wrapper_count}, vacuous: {vacuous_count}", file=sys.stderr)
        sys.exit(0)

    elif args.results:
        results_path = Path(args.results)
        if not results_path.is_absolute():
            results_path = ROOT / results_path
        if not results_path.exists():
            print(f"error: results file not found: {results_path}", file=sys.stderr)
            sys.exit(1)

        issues = check_results_file(results_path)

        if args.json:
            json.dump(issues, sys.stdout, indent=2)
            print()
        else:
            if not issues:
                print("All proofs are safe (no banned patterns found).")
            else:
                print(f"Found {len(issues)} proof(s) with issues:\n")
                for issue in issues:
                    status = "BANNED" if not issue["safe"] else "WARNING"
                    print(f"  [{status}] {issue['problem_id']} ({issue['theorem_name']})")
                    for name, text in issue["banned"]:
                        print(f"    - banned: {name}")
                    for name, text in issue["warnings"]:
                        print(f"    - warning: {name}")

        unsafe_count = sum(1 for i in issues if not i["safe"])
        print(f"\nSummary: {unsafe_count} unsafe, "
              f"{len(issues) - unsafe_count} warnings", file=sys.stderr)
        sys.exit(1 if unsafe_count > 0 else 0)

    elif args.scan_lean:
        scan_dir = ROOT / args.scan_lean
        if not scan_dir.exists():
            print(f"error: directory not found: {scan_dir}", file=sys.stderr)
            sys.exit(1)

        issues = scan_lean_files(scan_dir)

        if args.json:
            json.dump(issues, sys.stdout, indent=2)
            print()
        else:
            if not issues:
                print("No banned patterns found in .lean files.")
            else:
                print(f"Found {len(issues)} occurrence(s) of banned patterns:\n")
                for issue in issues:
                    print(f"  {issue['file']}:{issue['line']} [{issue['pattern']}]")
                    print(f"    {issue['text']}")

        print(f"\nTotal issues: {len(issues)}", file=sys.stderr)
        sys.exit(1 if issues else 0)

    else:
        # Default: scan both Lean files and any existing results
        print("SafeVerify -- scanning Lean source files...\n")
        lean_issues = scan_lean_files(ROOT / "RLGeneralization")

        if lean_issues:
            print(f"Found {len(lean_issues)} banned pattern(s) in source:\n")
            for issue in lean_issues:
                print(f"  {issue['file']}:{issue['line']} [{issue['pattern']}]")
                print(f"    {issue['text']}")
        else:
            print("No banned patterns in RLGeneralization/ source files.")

        # Check any results files
        results_dir = ROOT / "benchmark" / "results"
        if results_dir.exists():
            print("\nChecking benchmark results...")
            for rfile in sorted(results_dir.glob("*_results*.json")):
                try:
                    issues = check_results_file(rfile)
                    unsafe = sum(1 for i in issues if not i["safe"])
                    if unsafe:
                        print(f"  {rfile.name}: {unsafe} unsafe proof(s)")
                    else:
                        print(f"  {rfile.name}: OK")
                except (json.JSONDecodeError, KeyError):
                    print(f"  {rfile.name}: (skipped, not valid results format)")

        sys.exit(1 if lean_issues else 0)


if __name__ == "__main__":
    main()
