#!/usr/bin/env python3
"""Autoformalization pipeline: natural language to Lean 4 statements (#58, #65).

Takes a natural-language theorem statement as input and generates a Lean 4
statement template.  This is a template/placeholder for LLM integration --
the actual translation requires an LLM backend (GPT-4, Claude, etc.).

The pipeline:
  1. Parse the natural-language input.
  2. Identify mathematical domain and key concepts.
  3. Map concepts to Lean 4 / Mathlib types.
  4. Generate a Lean 4 theorem statement template.

Usage:
    python scripts/autoformalize.py --statement "For any MDP with discount factor gamma < 1, value iteration converges"
    python scripts/autoformalize.py --input theorems.txt --output formalized.json
    python scripts/autoformalize.py --help
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# ---------------------------------------------------------------------------
# Domain concept mappings
# ---------------------------------------------------------------------------

# Map natural-language concepts to Lean 4 types/definitions
CONCEPT_MAP = {
    # MDP concepts
    "mdp": ("FiniteMDP", "RLGeneralization.MDP.Basic"),
    "markov decision process": ("FiniteMDP", "RLGeneralization.MDP.Basic"),
    "discount factor": ("gamma : Real", "RLGeneralization.MDP.Basic"),
    "value function": ("V : M.S -> Real", "RLGeneralization.MDP.Basic"),
    "policy": ("pi : M.Policy", "RLGeneralization.MDP.Basic"),
    "bellman operator": ("M.bellman", "RLGeneralization.MDP.BellmanContraction"),
    "value iteration": ("M.valueIteration", "RLGeneralization.MDP.ValueIteration"),
    "transition": ("M.P", "RLGeneralization.MDP.Basic"),
    "reward": ("M.reward", "RLGeneralization.MDP.Basic"),

    # Concentration concepts
    "hoeffding": ("hoeffding_bound", "RLGeneralization.Concentration.Hoeffding"),
    "bernstein": ("bernstein_bound", "RLGeneralization.Concentration.Bernstein"),
    "sub-gaussian": ("SubGaussian", "RLGeneralization.Concentration.SubGaussian"),
    "concentration": ("", "RLGeneralization.Concentration"),
    "variance": ("Var", ""),

    # Sample complexity
    "sample complexity": ("sample_complexity", "RLGeneralization.Generalization.SampleComplexity"),
    "pac": ("pac_bound", "RLGeneralization.Generalization.SampleComplexity"),
    "generalization": ("", "RLGeneralization.Generalization"),

    # Analysis concepts
    "converges": ("Filter.Tendsto", "Mathlib.Topology.Order"),
    "bounded": ("IsBounded", "Mathlib.Topology.Bornology.Basic"),
    "continuous": ("Continuous", "Mathlib.Topology.ContinuousOn"),
    "norm": ("norm", "Mathlib.Analysis.Normed.Group.Basic"),
    "probability": ("MeasureTheory.Measure.IsProbabilityMeasure", "Mathlib.MeasureTheory"),
    "expectation": ("MeasureTheory.integral", "Mathlib.MeasureTheory"),
}

# Common mathematical patterns and their Lean 4 representations
PATTERN_MAP = {
    r"for all (\w+)": r"forall (\1 : _),",
    r"for any (\w+)": r"forall (\1 : _),",
    r"there exists (\w+)": r"exists (\1 : _),",
    r"(\w+) < (\w+)": r"\1 < \2",
    r"(\w+) <= (\w+)": r"\1 ≤ \2",
    r"(\w+) >= (\w+)": r"\1 ≥ \2",
    r"converges to (\w+)": r"Filter.Tendsto _ _ (nhds \1)",
    r"bounded by (\w+)": r"_ ≤ \1",
    r"with probability at least (\S+)": r"-- with probability ≥ \1",
}


def identify_domain(text: str) -> str:
    """Identify the mathematical domain from natural language."""
    text_lower = text.lower()

    domain_keywords = {
        "bellman": ["bellman", "value iteration", "policy iteration", "mdp",
                     "markov decision", "discount", "contraction"],
        "concentration": ["hoeffding", "bernstein", "azuma", "concentration",
                          "sub-gaussian", "martingale", "deviation"],
        "sample_complexity": ["sample complexity", "pac", "generalization",
                              "vc dimension", "rademacher"],
        "exploration": ["ucb", "exploration", "regret", "bandit", "thompson"],
        "policy_optimization": ["policy gradient", "natural policy",
                                 "conservative policy", "advantage"],
        "regression": ["regression", "lsvi", "linear", "least squares"],
    }

    scores = {}
    for domain, keywords in domain_keywords.items():
        scores[domain] = sum(1 for kw in keywords if kw in text_lower)

    best = max(scores, key=scores.get)
    return best if scores[best] > 0 else "other"


def identify_concepts(text: str) -> list[tuple[str, str, str]]:
    """Identify mathematical concepts and their Lean mappings.

    Returns list of (concept_name, lean_type, lean_module).
    """
    text_lower = text.lower()
    found = []
    for concept, (lean_type, module) in CONCEPT_MAP.items():
        if concept in text_lower:
            found.append((concept, lean_type, module))
    return found


def generate_template(text: str, domain: str,
                      concepts: list[tuple[str, str, str]]) -> str:
    """Generate a Lean 4 theorem statement template."""
    # Collect imports
    imports = set()
    for _, _, module in concepts:
        if module:
            imports.add(module)

    # Build the template
    lines = []

    # Imports
    for imp in sorted(imports):
        lines.append(f"import {imp}")
    if imports:
        lines.append("")

    lines.append("open Finset BigOperators")
    lines.append("")
    lines.append("noncomputable section")
    lines.append("")

    # Add a comment with the original statement
    lines.append(f"/-- {text} -/")

    # Generate a theorem skeleton
    theorem_name = re.sub(r"[^a-zA-Z0-9_]", "_", text[:60]).strip("_").lower()
    theorem_name = re.sub(r"_+", "_", theorem_name)

    lines.append(f"theorem {theorem_name}")

    # Add binders based on identified concepts
    added_mdp = False
    for concept, lean_type, _ in concepts:
        if "FiniteMDP" in lean_type and not added_mdp:
            lines.append(f"    (M : FiniteMDP)")
            added_mdp = True
        elif lean_type and "FiniteMDP" not in lean_type and ":" in lean_type:
            lines.append(f"    ({lean_type})")

    # Placeholder for the type
    lines.append(f"    : sorry  -- TODO: formalize the statement")
    lines.append(f"  := by")
    lines.append(f"  sorry  -- TODO: prove")
    lines.append("")

    return "\n".join(lines)


def formalize(text: str) -> dict:
    """Run the full autoformalization pipeline on a single statement."""
    domain = identify_domain(text)
    concepts = identify_concepts(text)
    template = generate_template(text, domain, concepts)

    return {
        "input": text,
        "domain": domain,
        "concepts": [
            {"name": c, "lean_type": t, "module": m}
            for c, t, m in concepts
        ],
        "lean_template": template,
        "status": "template_generated",
        "note": "This is a heuristic template. Manual refinement or LLM "
                "assistance is needed to produce a valid Lean 4 statement.",
    }


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Autoformalize natural-language theorems to Lean 4 statement templates."
    )
    parser.add_argument(
        "--statement", default=None,
        help="A single natural-language theorem statement to formalize."
    )
    parser.add_argument(
        "--input", default=None,
        help="File with one theorem statement per line."
    )
    parser.add_argument(
        "--output", default=None,
        help="Output file for formalized templates (JSON). Defaults to stdout."
    )
    args = parser.parse_args()

    statements: list[str] = []

    if args.statement:
        statements.append(args.statement)
    elif args.input:
        input_path = Path(args.input)
        if not input_path.is_absolute():
            input_path = ROOT / input_path
        if not input_path.exists():
            print(f"error: input file not found: {input_path}", file=sys.stderr)
            sys.exit(1)
        statements = [
            line.strip()
            for line in input_path.read_text().splitlines()
            if line.strip() and not line.strip().startswith("#")
        ]
    else:
        # Demo mode: show example
        statements = [
            "For any MDP with discount factor gamma < 1, the Bellman "
            "operator is a gamma-contraction in the sup-norm.",
            "Hoeffding's inequality: for n i.i.d. bounded random variables "
            "in [a,b], the sample mean deviates from the true mean by at "
            "most t with probability at most 2*exp(-2*n*t^2/(b-a)^2).",
        ]
        print("Running in demo mode with example statements.\n"
              "Use --statement or --input to provide your own.\n",
              file=sys.stderr)

    results = [formalize(s) for s in statements]

    out = open(args.output, "w") if args.output else sys.stdout
    try:
        json.dump(results, out, indent=2, ensure_ascii=False)
        out.write("\n")
    finally:
        if args.output:
            out.close()

    print(f"\nFormalized {len(results)} statement(s)", file=sys.stderr)


if __name__ == "__main__":
    main()
