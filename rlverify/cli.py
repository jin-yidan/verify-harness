"""RLVerify CLI — verify RL theory theorems via LLM + Lean 4."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

from .driver import DEFAULT_CORPUS


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        prog="rlverify",
        description="Verify RL theory theorems via LLM + Lean 4",
    )
    sub = parser.add_subparsers(dest="command", required=True)

    # -- paper -------------------------------------------------------------
    p_paper = sub.add_parser("paper", help="Extract theorems from a paper")
    p_paper.add_argument("file", help="LaTeX (.tex) or plain text file")
    p_paper.add_argument("--json", action="store_true", help="Output raw JSON")
    p_paper.add_argument("--corpus", help="Path to retrieval corpus JSONL")

    # -- retrieve ----------------------------------------------------------
    p_retrieve = sub.add_parser("retrieve", help="Search the premise library")
    p_retrieve.add_argument("query", help="Search query")
    p_retrieve.add_argument("--top-k", type=int, default=10)
    p_retrieve.add_argument("--corpus", help="Path to retrieval corpus JSONL")

    # -- falsify -----------------------------------------------------------
    p_falsify = sub.add_parser(
        "falsify",
        help="Run the numeric falsification gate on a claim (no Lean, no agent)")
    p_falsify.add_argument("sampler", nargs="?",
                           help="path to a sampler .py file (see rlverify/falsify_run.py)")
    p_falsify.add_argument("--example", metavar="NAME",
                           help="run a bundled example sampler (see --list)")
    p_falsify.add_argument("--list", action="store_true",
                           help="list the bundled example samplers and exit")
    p_falsify.add_argument("--n", type=int, help="number of samples to draw")
    p_falsify.add_argument("--seed", type=int, default=0, help="RNG seed")
    p_falsify.add_argument("--tol", type=float, help="relative violation tolerance")

    args = parser.parse_args(argv)

    if args.command == "paper":
        return _cmd_paper(args)
    elif args.command == "retrieve":
        return _cmd_retrieve(args)
    elif args.command == "falsify":
        return _cmd_falsify(args)
    return 1


def _cmd_paper(args: argparse.Namespace) -> int:
    from .extract import extract_file

    path = Path(args.file)
    if not path.exists():
        print(f"File not found: {path}", file=sys.stderr)
        return 1

    theorems = extract_file(path)
    if not theorems:
        print(f"No theorem/proof pairs found in {path.name}.", file=sys.stderr)
        print("Expected LaTeX \\begin{theorem}...\\end{proof} or plain text "
              "'Theorem: ... Proof: ...' format.", file=sys.stderr)
        return 1

    print(f"Found {len(theorems)} theorem/proof pairs in {path.name}.\n")
    for t in theorems:
        print(f"  [{t.kind}] {t.label}: {t.theorem[:80]}...")

    if args.json:
        fixtures = [t.to_fixture() for t in theorems]
        print(json.dumps(fixtures, indent=2))

    return 0


def _cmd_retrieve(args: argparse.Namespace) -> int:
    from .retriever import PremiseRetriever

    corpus = args.corpus or str(DEFAULT_CORPUS)
    retriever = PremiseRetriever(corpus)

    results = retriever.hybrid_search(args.query, top_k=args.top_k)
    for i, p in enumerate(results, 1):
        print(f"{i}. [{p.status}] {p.id}")
        print(f"   {p.signature_oneline()[:120]}")
        print(f"   score={p.score:.4f}  src={p.source_file}:{p.source_line}")
        print()

    print(f"{len(results)} results from {len(retriever)} premises.")
    return 0


def _cmd_falsify(args: argparse.Namespace) -> int:
    from .falsify_run import (EXAMPLES_DIR, SamplerError, list_examples,
                              load_sampler, render_card, run_sampler)

    examples = list_examples()
    if args.list:
        if not examples:
            print("No bundled examples found.")
            return 0
        print("Bundled falsify examples (run with --example NAME):")
        for name in examples:
            print(f"  {name}")
        return 0

    if args.example:
        if args.example not in examples:
            print(f"Unknown example '{args.example}'. Available: "
                  f"{', '.join(examples) or '(none)'}", file=sys.stderr)
            return 1
        path = EXAMPLES_DIR / f"{args.example}.py"
    elif args.sampler:
        path = Path(args.sampler)
    else:
        print("Provide a sampler file, or --example NAME, or --list.",
              file=sys.stderr)
        return 1

    try:
        mod = load_sampler(path)
    except (FileNotFoundError, ImportError, AttributeError, SamplerError) as e:
        print(f"Could not load sampler: {e}", file=sys.stderr)
        return 1

    try:
        report = run_sampler(mod, n=args.n, seed=args.seed, tol=args.tol)
    except SamplerError as e:
        print(f"Sampler error: {e}", file=sys.stderr)
        return 1
    print(render_card(report, seed=args.seed))
    return 0


if __name__ == "__main__":
    sys.exit(main())
