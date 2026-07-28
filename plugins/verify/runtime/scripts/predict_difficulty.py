#!/usr/bin/env python3
"""Predict theorem difficulty using heuristics (#57).

A simple heuristic difficulty predictor based on proof length, import count,
domain, and statement complexity. This is a proxy for the full LeanProgress
model -- useful for benchmark curation and prover evaluation planning.

Features used:
  - proof_lines: number of lines in the proof body
  - statement_length: character count of the theorem statement
  - binder_count: number of explicit/implicit binders
  - domain: categorical domain tag
  - import_depth: number of imports needed
  - has_sorry: whether the current proof uses sorry
  - uses_concentration: whether the proof involves concentration inequalities

Output: JSON with predicted difficulty labels and confidence scores.

Usage:
    python scripts/predict_difficulty.py
    python scripts/predict_difficulty.py --benchmark benchmark/mlstatbench.json
    python scripts/predict_difficulty.py --output predictions.json
    python scripts/predict_difficulty.py --help
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# Domain difficulty multipliers (empirical)
DOMAIN_WEIGHTS = {
    "concentration": 1.5,
    "sample_complexity": 1.3,
    "exploration": 1.2,
    "policy_optimization": 1.1,
    "bellman": 1.0,
    "regression": 1.0,
    "simulation": 1.1,
    "other": 1.0,
}


def extract_features(problem: dict) -> dict:
    """Extract heuristic features from a benchmark problem."""
    statement = problem.get("statement", "")
    proof_lines = problem.get("proof_lines", 0)
    domain = problem.get("domain", "other")

    # Count binders
    binder_count = len(problem.get("proof_arg_names", []))

    # Statement complexity: length in characters
    statement_length = len(statement)

    # Count quantifiers and logical connectives in the statement
    quantifier_count = sum(
        statement.count(q) for q in ["forall", "exists", "∀", "∃"]
    )
    connective_count = sum(
        statement.count(c) for c in ["→", "∧", "∨", "↔", "¬"]
    )

    # Check for specific complexity indicators
    uses_finset_sum = "Finset.sum" in statement or "∑" in statement
    uses_measure = "Measure" in statement or "μ" in statement
    uses_norm = "‖" in statement or "norm" in statement.lower()
    has_receiver = problem.get("has_receiver", False)

    return {
        "proof_lines": proof_lines,
        "statement_length": statement_length,
        "binder_count": binder_count,
        "quantifier_count": quantifier_count,
        "connective_count": connective_count,
        "uses_finset_sum": uses_finset_sum,
        "uses_measure": uses_measure,
        "uses_norm": uses_norm,
        "has_receiver": has_receiver,
        "domain": domain,
    }


def predict_difficulty(features: dict) -> tuple[str, float]:
    """Predict difficulty from features.

    Returns (difficulty_label, confidence_score).
    Confidence is in [0, 1].
    """
    score = 0.0

    # Proof length contribution (0-40 points)
    pl = features["proof_lines"]
    if pl <= 3:
        score += 5
    elif pl <= 10:
        score += 15
    elif pl <= 25:
        score += 25
    else:
        score += 40

    # Statement complexity (0-20 points)
    sl = features["statement_length"]
    if sl <= 100:
        score += 3
    elif sl <= 300:
        score += 10
    else:
        score += 20

    # Binder count (0-15 points)
    bc = features["binder_count"]
    if bc <= 2:
        score += 2
    elif bc <= 5:
        score += 8
    else:
        score += 15

    # Quantifiers and connectives (0-10 points)
    score += min(features["quantifier_count"] * 3, 10)
    score += min(features["connective_count"] * 1.5, 5)

    # Domain multiplier
    domain_weight = DOMAIN_WEIGHTS.get(features["domain"], 1.0)
    score *= domain_weight

    # Bonus for special constructs
    if features["uses_finset_sum"]:
        score += 8
    if features["uses_measure"]:
        score += 10
    if features["uses_norm"]:
        score += 5
    if features["has_receiver"]:
        score += 3

    # Map score to difficulty label
    if score <= 20:
        label = "easy"
        confidence = min(1.0, (20 - score) / 20 * 0.5 + 0.5)
    elif score <= 50:
        label = "medium"
        # Confidence is highest in the middle of the range
        dist_from_center = abs(score - 35) / 15
        confidence = max(0.4, 1.0 - dist_from_center * 0.6)
    else:
        label = "hard"
        confidence = min(1.0, (score - 50) / 50 * 0.5 + 0.5)

    return label, round(confidence, 3)


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Predict theorem difficulty using heuristics (LeanProgress proxy)."
    )
    parser.add_argument(
        "--benchmark", default="benchmark/mlstatbench.json",
        help="Path to the benchmark JSON file."
    )
    parser.add_argument(
        "--output", default=None,
        help="Output file for predictions (JSON). Defaults to stdout."
    )
    parser.add_argument(
        "--compare", action="store_true",
        help="Compare predictions against existing difficulty labels."
    )
    args = parser.parse_args()

    benchmark_path = ROOT / args.benchmark
    if not benchmark_path.exists():
        print(f"error: benchmark not found: {benchmark_path}", file=sys.stderr)
        sys.exit(1)

    with open(benchmark_path) as f:
        benchmark = json.load(f)

    problems = benchmark["problems"]
    predictions: list[dict] = []
    match_count = 0
    total = 0

    for problem in problems:
        features = extract_features(problem)
        predicted, confidence = predict_difficulty(features)
        actual = problem.get("difficulty", "unknown")

        entry = {
            "id": problem["id"],
            "theorem_name": problem["theorem_name"],
            "actual_difficulty": actual,
            "predicted_difficulty": predicted,
            "confidence": confidence,
            "features": features,
        }
        predictions.append(entry)

        if actual != "unknown":
            total += 1
            if predicted == actual:
                match_count += 1

    if args.compare and total > 0:
        accuracy = match_count / total
        print(f"\nDifficulty prediction accuracy: {match_count}/{total} "
              f"({accuracy:.1%})", file=sys.stderr)

        # Confusion matrix
        labels = ["easy", "medium", "hard", "bridge"]
        print("\nConfusion matrix (rows=actual, cols=predicted):", file=sys.stderr)
        print(f"{'':>10}", end="", file=sys.stderr)
        for l in labels:
            print(f"{l:>10}", end="", file=sys.stderr)
        print(file=sys.stderr)
        for actual in labels:
            print(f"{actual:>10}", end="", file=sys.stderr)
            for predicted in labels:
                count = sum(
                    1 for p in predictions
                    if p["actual_difficulty"] == actual
                    and p["predicted_difficulty"] == predicted
                )
                print(f"{count:>10}", end="", file=sys.stderr)
            print(file=sys.stderr)

    out = open(args.output, "w") if args.output else sys.stdout
    try:
        json.dump(predictions, out, indent=2, ensure_ascii=False)
        out.write("\n")
    finally:
        if args.output:
            out.close()

    print(f"\nPredicted difficulty for {len(predictions)} problems",
          file=sys.stderr)


if __name__ == "__main__":
    main()
