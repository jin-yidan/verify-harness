#!/usr/bin/env python3
"""Validate benchmark metadata and README summaries."""

from __future__ import annotations

import json
import re
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BENCHMARK = ROOT / "benchmark" / "mlstatbench.json"
README = ROOT / "benchmark" / "README.md"


def fail(message: str) -> None:
    print(message, file=sys.stderr)
    raise SystemExit(1)


def parse_table_counts(readme_text: str, header: str) -> dict[str, int]:
    marker = f"## {header}\n\n"
    start = readme_text.find(marker)
    if start == -1:
        fail(f"missing '{header}' table in benchmark/README.md")
    section = readme_text[start + len(marker):]
    next_header = section.find("\n## ")
    if next_header != -1:
        section = section[:next_header]

    counts: dict[str, int] = {}
    for raw_line in section.strip().splitlines():
        line = raw_line.strip()
        if not line.startswith("|"):
            continue
        cells = [cell.strip() for cell in line.strip("|").split("|")]
        if len(cells) < 2:
            continue
        try:
            counts[cells[0]] = int(cells[1])
        except ValueError:
            continue
    return counts


def main() -> None:
    try:
        benchmark = json.loads(BENCHMARK.read_text())
    except (FileNotFoundError, json.JSONDecodeError) as e:
        fail(f"failed to load {BENCHMARK}: {e}")
    problems = benchmark["problems"]

    if benchmark.get("total_problems") != len(problems):
        fail("benchmark/mlstatbench.json total_problems does not match problems length")

    try:
        readme_text = README.read_text()
    except FileNotFoundError:
        fail(f"missing {README}")

    domain_counts = dict(sorted(Counter(problem["domain"] for problem in problems).items()))
    readme_domain_counts = parse_table_counts(readme_text, "Domains")
    if readme_domain_counts != domain_counts:
        fail(
            "benchmark/README.md domain table is out of sync with benchmark/mlstatbench.json\n"
            f"README: {readme_domain_counts}\nJSON:   {domain_counts}"
        )

    difficulty_counts = dict(
        sorted(Counter(problem["difficulty"] for problem in problems).items())
    )
    readme_difficulty_counts = parse_table_counts(readme_text, "Difficulty Levels")
    if readme_difficulty_counts != difficulty_counts:
        fail(
            "benchmark/README.md difficulty table is out of sync with benchmark/mlstatbench.json\n"
            f"README: {readme_difficulty_counts}\nJSON:   {difficulty_counts}"
        )

    bridge_count = difficulty_counts.get("bridge", 0)
    bridge_mentions = re.findall(r"Yes \((\d+) cross-domain\)", readme_text)
    if not bridge_mentions or int(bridge_mentions[0]) != bridge_count:
        fail(
            "benchmark/README.md bridge-problem claim is out of sync with benchmark/mlstatbench.json"
        )

    if "benchmark/results/<prover>_results.json" in readme_text:
        fail("benchmark/README.md still points analysis at *_results.json instead of *.local.json")

    print("benchmark metadata checks passed")


if __name__ == "__main__":
    main()
