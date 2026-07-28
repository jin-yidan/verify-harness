#!/usr/bin/env python3
"""Generate plausible-but-false negative examples from verified theorems.

Reads theorem statements from proof traces (or retrieval corpus) and
produces perturbed variants that look plausible but are mathematically
false. Useful for training discriminators and evaluating proof
verification.

Perturbation types:
  - drop_factor:       Remove a critical multiplicative factor (e.g., 1/2)
  - swap_inequality:   Reverse inequality direction (le -> ge)
  - weaken_bound:      Replace a tight constant with a looser one
  - drop_hypothesis:   Remove a key hypothesis from the statement
  - sign_flip:         Negate a term or flip subtraction order

Output: benchmark/negative_examples.jsonl

Usage:
    python scripts/generate_negative_examples.py
    python scripts/generate_negative_examples.py --traces benchmark/proof_traces.jsonl
    python scripts/generate_negative_examples.py --max-per-theorem 3
"""

import argparse
import json
import random
import re
import sys
from pathlib import Path

# ---------------------------------------------------------------------------
# Perturbation strategies
# ---------------------------------------------------------------------------

# Patterns: (regex, replacement, perturbation_type, description)
PERTURBATIONS: list[tuple[str, str, str, str]] = [
    # Drop common factors like 1/2, 2*, (1-gamma)
    (r"\b2\s*\*\s*", "", "drop_factor",
     "Removed factor of 2"),
    (r"\/ 2\b", "", "drop_factor",
     "Removed division by 2"),
    (r"\/ \(2 \*", "/ (1 *", "drop_factor",
     "Replaced 2* denominator with 1*"),

    # Swap inequality directions
    (r"\u2264", "\u2265", "swap_inequality",
     "Swapped <= to >="),
    (r"\u2265", "\u2264", "swap_inequality",
     "Swapped >= to <="),

    # Weaken bounds by changing exponents
    (r"\^ 2\b", "^ 3", "weaken_bound",
     "Changed exponent from 2 to 3"),
    (r"\^ 3\b", "^ 2", "weaken_bound",
     "Changed exponent from 3 to 2"),

    # Change constants: sqrt -> id, log -> id
    (r"Real\.sqrt\s*\(", "(", "drop_factor",
     "Removed sqrt"),

    # Flip subtraction order
    (r"(\w+)\s*-\s*(\w+)\s*\u2264", r"\2 - \1 \u2264", "sign_flip",
     "Flipped subtraction order"),

    # Drop hypothesis lines that start with common patterns
    (r"\n\s*\(h\w+\s*:.*?\)", "", "drop_hypothesis",
     "Removed a hypothesis"),

    # Change strict to non-strict and vice versa
    (r"0 < ", "0 \u2264 ", "weaken_bound",
     "Weakened strict positivity to non-strict"),
]

# Additional targeted perturbations for concentration inequalities
CONCENTRATION_PERTURBATIONS: list[tuple[str, str, str, str]] = [
    # Hoeffding: remove the 2 in exp(-2n*eps^2)
    (r"exp\s*\(\s*-\s*2\s*\*", "exp (-1 *", "drop_factor",
     "Removed factor 2 in Hoeffding exponent"),
    # Bernstein: change variance term
    (r"\u03c3\s*\^\s*2", "\u03c3", "drop_factor",
     "Removed squared on variance term"),
    # Remove (1-gamma) denominator
    (r"\/ \(1 - ", "/ (2 - ", "weaken_bound",
     "Changed (1-gamma) to (2-gamma) in denominator"),
]

# Perturbations for bandit/regret bounds
BANDIT_PERTURBATIONS: list[tuple[str, str, str, str]] = [
    # UCB: change sqrt(log) to log
    (r"Real\.sqrt\s*\(.*?Real\.log", "(Real.log", "drop_factor",
     "Removed sqrt around log in UCB bound"),
    # Regret: change sqrt(T) to T
    (r"Real\.sqrt\s*\(.*?T\s*\)", "T", "weaken_bound",
     "Changed sqrt(T) to T in regret bound"),
]


def apply_perturbation(statement: str, pattern: str,
                       replacement: str) -> str | None:
    """Apply a regex perturbation and return the result, or None if no match."""
    result, count = re.subn(pattern, replacement, statement, count=1)
    if count == 0:
        return None
    if result == statement:
        return None
    return result


def generate_negatives_for_theorem(entry: dict,
                                   max_per_theorem: int,
                                   rng: random.Random) -> list[dict]:
    """Generate negative examples for a single theorem."""
    statement = entry.get("statement", "")
    if not statement:
        return []

    # Collect tags for specialized perturbations
    tags = entry.get("tags", [])
    module = entry.get("module", "")

    candidates: list[dict] = []

    # Try all general perturbations
    all_perts = list(PERTURBATIONS)
    if any(t in ("concentration", "hoeffding", "bernstein", "bennett")
           for t in tags) or "Concentration" in module:
        all_perts.extend(CONCENTRATION_PERTURBATIONS)
    if any(t in ("bandit", "ucb", "exploration", "regret")
           for t in tags) or "Bandits" in module or "Exploration" in module:
        all_perts.extend(BANDIT_PERTURBATIONS)

    for pattern, replacement, pert_type, description in all_perts:
        result = apply_perturbation(statement, pattern, replacement)
        if result is not None:
            candidates.append({
                "original_id": entry.get("id", entry.get("theorem_name", "")),
                "original_theorem": statement,
                "negative_statement": result,
                "perturbation_type": pert_type,
                "perturbation_description": description,
                "module": module,
                "original_status": entry.get("status", "unknown"),
            })

    # Deduplicate by negative_statement
    seen: set[str] = set()
    unique: list[dict] = []
    for c in candidates:
        ns = c["negative_statement"]
        if ns not in seen:
            seen.add(ns)
            unique.append(c)

    # Limit per theorem
    if len(unique) > max_per_theorem:
        unique = rng.sample(unique, max_per_theorem)

    return unique


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Generate plausible-but-false negative examples from theorems.")
    parser.add_argument("--root", type=Path,
                        default=Path(__file__).resolve().parent.parent,
                        help="Project root directory (default: auto-detect)")
    parser.add_argument("--traces", type=Path, default=None,
                        help="Input proof traces JSONL (default: <root>/benchmark/proof_traces.jsonl)")
    parser.add_argument("--corpus", type=Path, default=None,
                        help="Alternative: use retrieval corpus JSONL as input")
    parser.add_argument("--out", type=Path, default=None,
                        help="Output JSONL (default: <root>/benchmark/negative_examples.jsonl)")
    parser.add_argument("--max-per-theorem", type=int, default=3,
                        help="Maximum negative examples per theorem (default: 3)")
    parser.add_argument("--seed", type=int, default=42,
                        help="Random seed (default: 42)")
    args = parser.parse_args()

    root = args.root.resolve()
    out_path = (args.out or root / "benchmark" / "negative_examples.jsonl").resolve()
    rng = random.Random(args.seed)

    # Load input: prefer --traces, fall back to --corpus, then auto-detect
    input_path = None
    if args.traces:
        input_path = args.traces.resolve()
    elif args.corpus:
        input_path = args.corpus.resolve()
    else:
        # Auto-detect: try proof_traces.jsonl first, then retrieval_corpus.jsonl
        for candidate in ["benchmark/proof_traces.jsonl",
                          "rlverify/corpus.jsonl"]:
            p = root / candidate
            if p.exists():
                input_path = p
                break

    if input_path is None or not input_path.exists():
        print("error: no input file found. Run export_proof_traces.py or "
              "export_retrieval_corpus.py first, or pass --traces/--corpus.",
              file=sys.stderr)
        sys.exit(1)

    print(f"Reading theorems from {input_path}", file=sys.stderr)
    entries: list[dict] = []
    with open(input_path) as f:
        for line in f:
            line = line.strip()
            if line:
                entries.append(json.loads(line))

    print(f"Loaded {len(entries)} theorems", file=sys.stderr)

    # Generate negatives
    all_negatives: list[dict] = []
    for entry in entries:
        negatives = generate_negatives_for_theorem(
            entry, args.max_per_theorem, rng)
        all_negatives.extend(negatives)

    # Write output
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with open(out_path, "w") as f:
        for neg in all_negatives:
            f.write(json.dumps(neg) + "\n")

    # Summary
    by_type: dict[str, int] = {}
    for n in all_negatives:
        pt = n["perturbation_type"]
        by_type[pt] = by_type.get(pt, 0) + 1

    print(f"\nGenerated {len(all_negatives)} negative examples from "
          f"{len(entries)} theorems", file=sys.stderr)
    print(f"  Output: {out_path}", file=sys.stderr)
    print(f"  By perturbation type:", file=sys.stderr)
    for pt, count in sorted(by_type.items(), key=lambda x: -x[1]):
        print(f"    {pt}: {count}", file=sys.stderr)


if __name__ == "__main__":
    main()
