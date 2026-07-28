"""Reuse report for library-expansion lemmas.

Answers: are the lemmas added by /expand-library actually getting used?

Two signals, kept separate because they mean different things:
- **matched**: a verification run used the premise to resolve a proof step
  (recorded via ``VerifyDriver._record_match``). This is the real signal.
- **retrieved**: the premise appeared in search results. Polluted by the
  expansion loop's own redundancy searches, so treat as weak evidence only.

Expansion lemmas are identified from the `keep` rows of
``rlverify/results/library_expansion.tsv``.

Usage:
    python3 scripts/corpus_reuse_report.py
"""

from __future__ import annotations

import csv
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CORPUS = ROOT / "rlverify" / "corpus.jsonl"
STATS = ROOT / "rlverify" / "corpus_retrieval_stats.json"
TSV = ROOT / "rlverify" / "results" / "library_expansion.tsv"


def load_expansion_names() -> list[str]:
    """TSV rows may list several theorems per attempt ('a+b' or 'a,b')."""
    names = []
    with open(TSV) as f:
        reader = csv.reader(f, delimiter="\t")
        next(reader, None)  # header
        for row in reader:
            if len(row) >= 5 and row[1] == "keep":
                for part in row[4].replace(",", "+").split("+"):
                    part = part.strip().rstrip("*").rstrip("_")
                    if part:
                        names.append(part)
    return names


def main() -> int:
    if not TSV.exists():
        print("no library_expansion.tsv — nothing to report")
        return 1

    expansion_names = load_expansion_names()

    stats = {"retrieved": {}, "matched": {}}
    if STATS.exists():
        stats = json.loads(STATS.read_text())
    retrieved = stats.get("retrieved", {})
    matched = stats.get("matched", {})

    # Map expansion theorem names -> corpus ids (suffix match on last segment)
    corpus_ids = []
    with open(CORPUS) as f:
        for line in f:
            line = line.strip()
            if line:
                corpus_ids.append(json.loads(line)["id"])
    by_name: dict[str, list[str]] = {}
    for cid in corpus_ids:
        by_name.setdefault(cid.split(".")[-1], []).append(cid)

    rows = []
    for name in expansion_names:
        ids = by_name.get(name, [])
        r = sum(retrieved.get(i, 0) for i in ids)
        m = sum(matched.get(i, 0) for i in ids)
        rows.append((name, len(ids), r, m))

    n_matched = sum(1 for _, _, _, m in rows if m > 0)
    n_retrieved = sum(1 for _, _, r, _ in rows if r > 0)
    total_matches_all = sum(matched.values())

    print("=== Expansion Lemma Reuse Report ===")
    print(f"Expansion lemmas (keep): {len(rows)}")
    print(f"  matched in a verification run : {n_matched}"
          f"  <-- the signal that matters")
    print(f"  ever retrieved (weak signal)  : {n_retrieved}")
    print(f"Corpus-wide matches recorded    : {total_matches_all}")
    if total_matches_all < 10:
        print("  [!] too few verification runs to judge reuse —"
              " run /verify-full-process on papers to generate match data")
    print()
    print(f"{'lemma':<45} {'in_corpus':>9} {'retrieved':>9} {'matched':>7}")
    for name, n_ids, r, m in sorted(rows, key=lambda x: (-x[3], -x[2])):
        flag = " *" if m > 0 else ""
        print(f"{name:<45} {n_ids:>9} {r:>9} {m:>7}{flag}")

    missing = [name for name, n_ids, _, _ in rows if n_ids == 0]
    if missing:
        print(f"\n[!] {len(missing)} kept lemmas not found in corpus: "
              f"{', '.join(missing[:10])}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
