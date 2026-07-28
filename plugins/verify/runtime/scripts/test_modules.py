#!/usr/bin/env python3
"""Build each trusted-root module individually and report timing.

Verifies that every module in the verified target can be built
independently with `lake build --wfail`. Reports per-module build times to
help identify slow modules and regressions.

Usage:
    python scripts/test_modules.py           # Build all verified modules
    python scripts/test_modules.py --limit 5 # Build first 5 only
    python scripts/test_modules.py --json    # Output JSON results
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def get_trusted_modules() -> list[str]:
    """Read module names from RLGeneralization.lean."""
    root_file = ROOT / "RLGeneralization.lean"
    modules = []
    for line in root_file.read_text().splitlines():
        m = re.match(r"^import\s+(RLGeneralization\.\S+)", line)
        if m:
            modules.append(m.group(1))
    return modules


def build_module(module: str, timeout: int = 300) -> dict:
    """Build a single module and return timing and status."""
    start = time.time()
    try:
        result = subprocess.run(
            ["lake", "build", "--wfail", module],
            capture_output=True,
            text=True,
            timeout=timeout,
            cwd=ROOT,
        )
        elapsed = time.time() - start
        # Filter SLT local changes warning
        warnings = [
            line for line in result.stderr.splitlines()
            if "warning" in line.lower() and "SLT" not in line
        ]
        errors = [
            line for line in result.stderr.splitlines()
            if "error" in line.lower() and "SLT" not in line
        ]
        return {
            "module": module,
            "success": result.returncode == 0 and not warnings and not errors,
            "elapsed_s": round(elapsed, 2),
            "warnings": len(warnings),
            "errors": errors[:5] if errors else [],
        }
    except subprocess.TimeoutExpired:
        return {
            "module": module,
            "success": False,
            "elapsed_s": timeout,
            "warnings": 0,
            "errors": [f"timeout after {timeout}s"],
        }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--limit", type=int, default=0,
                        help="Max modules to build (0 = all)")
    parser.add_argument("--json", action="store_true",
                        help="Output JSON results")
    parser.add_argument("--timeout", type=int, default=300,
                        help="Per-module timeout in seconds")
    args = parser.parse_args()

    modules = get_trusted_modules()
    if args.limit > 0:
        modules = modules[:args.limit]

    print(f"Building {len(modules)} trusted-root modules individually\n",
          file=sys.stderr)

    results = []
    passed = 0
    failed = 0
    total_time = 0.0

    for i, mod in enumerate(modules, 1):
        short = mod.replace("RLGeneralization.", "")
        r = build_module(mod, timeout=args.timeout)
        results.append(r)
        total_time += r["elapsed_s"]

        status = "OK" if r["success"] else "FAIL"
        if r["success"]:
            passed += 1
        else:
            failed += 1

        warn_str = f" ({r['warnings']}w)" if r["warnings"] else ""
        print(f"  [{i:2d}/{len(modules)}] [{status:4s}] {short:<45} "
              f"{r['elapsed_s']:6.1f}s{warn_str}", file=sys.stderr)

        if not r["success"]:
            for err in r["errors"]:
                print(f"           {err}", file=sys.stderr)

    print(f"\n{'='*60}", file=sys.stderr)
    print(f"Modules: {passed}/{len(modules)} passed, {failed} failed",
          file=sys.stderr)
    print(f"Total time: {total_time:.1f}s", file=sys.stderr)

    if args.json:
        print(json.dumps({
            "total_modules": len(modules),
            "passed": passed,
            "failed": failed,
            "total_time_s": round(total_time, 2),
            "results": results,
        }, indent=2))

    sys.exit(0 if failed == 0 else 1)


if __name__ == "__main__":
    main()
