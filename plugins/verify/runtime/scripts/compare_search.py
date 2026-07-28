#!/usr/bin/env python3
"""Compare grep, BM25-only, and hybrid search on the real corpus.

Runs a set of representative queries against all three search methods
and shows which results each finds, highlighting differences.
"""

from __future__ import annotations

import sys
from pathlib import Path
from collections import Counter

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from rlverify.retriever import PremiseRetriever, _tokenize, corpus_entry_text
from copy import copy


QUERIES = [
    # Exact name matches (grep should win)
    "bellman_contraction",
    "hoeffding",
    "chi_squared",
    # Semantic / NL queries (BM25 should win)
    "concentration inequality for bounded random variables",
    "contraction mapping fixed point",
    "regret bound for upper confidence bound algorithm",
    # Mixed: partial name + concept
    "Finset sum nonneg",
    "policy gradient variance",
    "sample complexity PAC bound",
    # Edge cases: Mathlib-style names
    "exp_pos",
    "sq_nonneg",
    "mul_comm",
]


def grep_search(retriever: PremiseRetriever, query: str, top_k: int = 10):
    """Substring match (same as d.grep)."""
    pattern = query.lower()
    matches = []
    for p in retriever.premises:
        if pattern in p.id.lower() or pattern in p.statement.lower():
            matches.append(p)
    return matches[:top_k]


def bm25_only_search(retriever: PremiseRetriever, query: str, top_k: int = 10):
    """BM25-only (no grep fusion)."""
    query_tokens = _tokenize(query)
    scores = [
        (i, retriever._bm25_score(query_tokens, i))
        for i in range(len(retriever.premises))
    ]
    ranked = sorted(scores, key=lambda x: -x[1])[:top_k]
    results = []
    for idx, score in ranked:
        if score <= 0:
            break
        p = copy(retriever.premises[idx])
        p.score = score
        results.append(p)
    return results


def main():
    corpus_path = ROOT / "rlverify" / "corpus.jsonl"
    if not corpus_path.exists():
        print(f"Corpus not found: {corpus_path}")
        return 1

    retriever = PremiseRetriever(corpus_path)
    print(f"Loaded {len(retriever)} premises")

    methods = ["grep", "bm25", "hybrid"]
    print()

    wins: Counter[str] = Counter()
    unique_finds: Counter[str] = Counter()

    for query in QUERIES:
        print(f"{'='*70}")
        print(f"QUERY: {query}")
        print(f"{'='*70}")

        results = {}
        results["grep"] = grep_search(retriever, query, top_k=5)
        results["bm25"] = bm25_only_search(retriever, query, top_k=5)
        results["hybrid"] = retriever.hybrid_search(query, top_k=5)

        for method in methods:
            ids = [p.id for p in results[method]]
            short_ids = [i.split(".")[-1] for i in ids]
            count = len(ids)
            print(f"\n  {method:7s} ({count} hits): {', '.join(short_ids[:5])}")

        for method in methods:
            method_ids = {p.id for p in results[method]}
            other_ids = set()
            for other in methods:
                if other != method:
                    other_ids |= {p.id for p in results[other]}
            unique = method_ids - other_ids
            if unique:
                short = [i.split(".")[-1] for i in unique]
                print(f"  ** {method} uniquely found: {', '.join(short)}")
                unique_finds[method] += len(unique)

        for method in methods:
            if results[method]:
                wins[method] += 1

        print()

    print(f"\n{'='*70}")
    print("SUMMARY")
    print(f"{'='*70}")
    for method in methods:
        print(f"  {method}: {wins[method]}/{len(QUERIES)} queries with results, "
              f"{unique_finds[method]} unique finds")
    return 0


if __name__ == "__main__":
    sys.exit(main())
