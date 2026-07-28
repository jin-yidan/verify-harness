#!/usr/bin/env python3
"""Recalibrate difficulty labels in mlstatbench.json (#64).

Uses proof line count and module complexity to reassign difficulty labels.
This improves on the initial heuristic classification by considering:
  - Actual proof body length (lines)
  - Number of binders / hypotheses
  - Module depth (proxy for conceptual complexity)
  - Domain-specific calibration
  - Bridge problem detection

Usage:
    python scripts/calibrate_difficulty.py
    python scripts/calibrate_difficulty.py --benchmark benchmark/mlstatbench.json --output calibrated.json
    python scripts/calibrate_difficulty.py --dry-run
    python scripts/calibrate_difficulty.py --help
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# Calibration thresholds (tuned on existing benchmark)
EASY_MAX_LINES = 5
MEDIUM_MAX_LINES = 20
HARD_MIN_LINES = 20

# Domain-specific adjustments
HARD_DOMAINS = {"concentration", "sample_complexity"}
MEDIUM_DOMAINS = {"exploration", "policy_optimization", "simulation"}

# Module depth scoring: deeper modules tend to have harder theorems
# because they build on more prerequisite concepts
MODULE_DEPTH_WEIGHT = {
    1: 0,    # e.g., RLGeneralization.Basic
    2: 0,    # e.g., RLGeneralization.MDP.Basic
    3: 5,    # e.g., RLGeneralization.MDP.SimulationLemma
    4: 10,   # deeper nesting
}


def compute_complexity_score(problem: dict) -> float:
    """Compute a numerical complexity score for a problem."""
    score = 0.0

    # Proof length (primary signal)
    proof_lines = problem.get("proof_lines", 0)
    score += proof_lines * 2.0

    # Statement length
    statement = problem.get("statement", "")
    statement_lines = len(statement.splitlines())
    score += statement_lines * 1.5

    # Binder count
    binder_count = len(problem.get("proof_arg_names", []))
    score += binder_count * 1.0

    # Module depth
    module = problem.get("source_module", "")
    depth = len(module.split(".")) - 1  # subtract the root
    depth_bonus = MODULE_DEPTH_WEIGHT.get(depth, 10)
    score += depth_bonus

    # Domain adjustment
    domain = problem.get("domain", "other")
    if domain in HARD_DOMAINS:
        score *= 1.3
    elif domain in MEDIUM_DOMAINS:
        score *= 1.1

    # Has receiver args (namespace theorems tend to be more involved)
    if problem.get("has_receiver", False):
        score += 5

    return score


def calibrate_label(problem: dict, score: float) -> str:
    """Assign a calibrated difficulty label based on the complexity score."""
    proof_lines = problem.get("proof_lines", 0)
    domain = problem.get("domain", "other")
    status = problem.get("status", "unknown")
    name = problem.get("theorem_name", "")

    # Bridge problems: cross-domain theorems that combine multiple areas
    bridge_keywords = [
        "pac_rl_generative_model",
        "minimax_value_gap",
        "sample_complexity",
        "generative_model_pac",
        "value_iteration_epsilon_optimal",
        "pdl_occupancy_form",
        "empiricalGreedyValue_isValueOf",
        "minimax_from_empirical",
        "lsvi_sample_complexity",
    ]
    if any(kw in name for kw in bridge_keywords):
        return "bridge"

    # Score-based classification
    if score <= 15:
        return "easy"
    elif score <= 45:
        return "medium"
    else:
        return "hard"


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Recalibrate difficulty labels using proof line count and module complexity."
    )
    parser.add_argument(
        "--benchmark", default="benchmark/mlstatbench.json",
        help="Path to the benchmark JSON file."
    )
    parser.add_argument(
        "--output", default=None,
        help="Output path for calibrated benchmark. Defaults to overwriting input."
    )
    parser.add_argument(
        "--dry-run", action="store_true",
        help="Show changes without modifying files."
    )
    parser.add_argument(
        "--verbose", action="store_true",
        help="Show per-problem calibration details."
    )
    args = parser.parse_args()

    benchmark_path = ROOT / args.benchmark
    if not benchmark_path.exists():
        print(f"error: benchmark not found: {benchmark_path}", file=sys.stderr)
        sys.exit(1)

    with open(benchmark_path) as f:
        benchmark = json.load(f)

    problems = benchmark["problems"]
    changes: list[dict] = []

    for problem in problems:
        score = compute_complexity_score(problem)
        new_label = calibrate_label(problem, score)
        old_label = problem.get("difficulty", "unknown")

        if new_label != old_label:
            changes.append({
                "id": problem["id"],
                "theorem_name": problem["theorem_name"],
                "old": old_label,
                "new": new_label,
                "score": round(score, 1),
            })

        if not args.dry_run:
            problem["difficulty"] = new_label

        if args.verbose:
            marker = " *" if new_label != old_label else ""
            print(f"  {problem['id']} ({problem['theorem_name']}): "
                  f"score={score:.1f}  {old_label} -> {new_label}{marker}",
                  file=sys.stderr)

    # Summary
    print(f"\nCalibration summary:", file=sys.stderr)
    print(f"  Total problems: {len(problems)}", file=sys.stderr)
    print(f"  Changes: {len(changes)}", file=sys.stderr)

    if changes:
        # Count transitions
        transitions: dict[str, int] = {}
        for c in changes:
            key = f"{c['old']} -> {c['new']}"
            transitions[key] = transitions.get(key, 0) + 1
        for transition, count in sorted(transitions.items()):
            print(f"    {transition}: {count}", file=sys.stderr)

    # Distribution
    from collections import Counter
    dist = Counter(p.get("difficulty", "unknown") for p in problems)
    print(f"\n  New distribution:", file=sys.stderr)
    for label in ["easy", "medium", "hard", "bridge"]:
        print(f"    {label}: {dist.get(label, 0)}", file=sys.stderr)

    if args.dry_run:
        print("\n(dry run -- no files modified)", file=sys.stderr)
        if changes:
            print("\nChanges that would be applied:")
            for c in changes:
                print(f"  {c['id']} ({c['theorem_name']}): "
                      f"{c['old']} -> {c['new']} (score={c['score']})")
        sys.exit(0)

    # Write output
    out_path = Path(args.output) if args.output else benchmark_path
    if not out_path.is_absolute():
        out_path = ROOT / out_path

    benchmark["problems"] = problems
    out_path.write_text(json.dumps(benchmark, indent=2, ensure_ascii=False) + "\n")
    print(f"\nWritten to {out_path}", file=sys.stderr)


if __name__ == "__main__":
    main()
