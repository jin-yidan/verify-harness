#!/usr/bin/env python3
"""Extract goal states from benchmark problems for LLM provers (#52).

Reads the MLStatBench benchmark and extracts theorem statements as
goal states (the theorem statement without proof), outputting JSON
suitable for feeding to LLM provers.

Each output entry contains:
  - id: problem identifier
  - goal: the theorem statement (what needs to be proved)
  - hypotheses: extracted variable/hypothesis context
  - module: source module for imports
  - domain: problem domain tag
  - difficulty: difficulty label

Usage:
    python scripts/extract_goals.py
    python scripts/extract_goals.py --benchmark benchmark/mlstatbench.json --output goals.json
    python scripts/extract_goals.py --format jsonl --difficulty hard
    python scripts/extract_goals.py --help
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def extract_hypotheses(statement: str, context_prefix: list[str]) -> list[dict]:
    """Extract hypotheses from variable declarations and theorem binders.

    Returns a list of {"name": ..., "type": ...} dicts.
    """
    hypotheses: list[dict] = []

    # Extract from variable lines in context_prefix
    for line in context_prefix:
        stripped = line.strip()
        if not re.match(r"^(variable|variables)\b", stripped):
            continue
        # Find (name : Type) patterns
        for m in re.finditer(r"[\(\{]([^:(){}]+?)\s*:\s*([^(){}]+?)[\)\}]", stripped):
            names_part = m.group(1).strip()
            type_part = m.group(2).strip()
            for name in names_part.split():
                name = name.strip()
                if name and name != "_" and not name[0].isdigit():
                    hypotheses.append({"name": name, "type": type_part})

    # Extract from theorem binders in the statement itself
    # Look for (name : Type) patterns in the statement before the final `:`
    depth = 0
    type_colon_pos = -1
    for i, ch in enumerate(statement):
        if ch in "({[":
            depth += 1
        elif ch in ")}]":
            depth = max(depth - 1, 0)
        elif ch == ":" and depth == 0:
            type_colon_pos = i

    if type_colon_pos > 0:
        binder_part = statement[:type_colon_pos]
        for m in re.finditer(r"[\(\{]([^:(){}]+?)\s*:\s*([^(){}]+?)[\)\}]", binder_part):
            names_part = m.group(1).strip()
            type_part = m.group(2).strip()
            for name in names_part.split():
                name = name.strip()
                if name and name != "_" and not name[0].isdigit():
                    hypotheses.append({"name": name, "type": type_part})

    return hypotheses


def extract_goal_type(statement: str) -> str:
    """Extract the goal type (the part after the final top-level colon)."""
    depth = 0
    last_colon = -1
    for i, ch in enumerate(statement):
        if ch in "({[":
            depth += 1
        elif ch in ")}]":
            depth = max(depth - 1, 0)
        elif ch == ":" and depth == 0 and (i + 1 >= len(statement) or statement[i + 1] != "="):
            last_colon = i

    if last_colon >= 0:
        return statement[last_colon + 1:].strip()
    return statement


def make_goal_entry(problem: dict) -> dict:
    """Convert a benchmark problem to a goal entry for LLM provers."""
    statement = problem["statement"]
    context_prefix = problem.get("context_prefix", [])
    hypotheses = extract_hypotheses(statement, context_prefix)
    goal_type = extract_goal_type(statement)

    # Build the full prompt context
    imports = [f"import {problem['source_module']}"]
    for hint in problem.get("import_hints", []):
        imp = f"import {hint}"
        if imp not in imports:
            imports.append(imp)

    return {
        "id": problem["id"],
        "theorem_name": problem["theorem_name"],
        "goal": goal_type,
        "full_statement": statement,
        "hypotheses": hypotheses,
        "imports": imports,
        "context_prefix": context_prefix,
        "module": problem["source_module"],
        "domain": problem["domain"],
        "difficulty": problem["difficulty"],
        "informal_description": problem.get("informal_description", ""),
    }


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Extract goal states from MLStatBench for LLM provers."
    )
    parser.add_argument(
        "--benchmark", default="benchmark/mlstatbench.json",
        help="Path to the benchmark JSON file (relative to project root)."
    )
    parser.add_argument(
        "--output", default=None,
        help="Output file path. Defaults to stdout."
    )
    parser.add_argument(
        "--format", choices=["json", "jsonl"], default="json",
        help="Output format: 'json' (array) or 'jsonl' (one object per line)."
    )
    parser.add_argument(
        "--difficulty", default=None,
        choices=["easy", "medium", "hard", "bridge"],
        help="Filter by difficulty level."
    )
    parser.add_argument(
        "--domain", default=None,
        help="Filter by domain (e.g., 'concentration', 'bellman')."
    )
    parser.add_argument(
        "--limit", type=int, default=None,
        help="Maximum number of goals to extract."
    )
    args = parser.parse_args()

    benchmark_path = ROOT / args.benchmark
    if not benchmark_path.exists():
        print(f"error: benchmark file not found: {benchmark_path}", file=sys.stderr)
        sys.exit(1)

    with open(benchmark_path) as f:
        benchmark = json.load(f)

    problems = benchmark["problems"]

    # Apply filters
    if args.difficulty:
        problems = [p for p in problems if p["difficulty"] == args.difficulty]
    if args.domain:
        problems = [p for p in problems if p["domain"] == args.domain]
    if args.limit:
        problems = problems[:args.limit]

    goals = [make_goal_entry(p) for p in problems]

    out = open(args.output, "w") if args.output else sys.stdout
    try:
        if args.format == "json":
            json.dump(goals, out, indent=2, ensure_ascii=False)
            out.write("\n")
        else:
            for goal in goals:
                out.write(json.dumps(goal, ensure_ascii=False) + "\n")
    finally:
        if args.output:
            out.close()

    print(f"Extracted {len(goals)} goal states", file=sys.stderr)


if __name__ == "__main__":
    main()
