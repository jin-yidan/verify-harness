"""Premise retrieval over the lean4-rl library corpus.

Uses BM25 ranking for search.
Tracks retrieval and match counts for reuse analysis.
"""

from __future__ import annotations

import json
import math
import re
from collections import Counter
from copy import copy
from dataclasses import dataclass
from pathlib import Path


@dataclass
class Premise:
    id: str
    statement: str
    tags: list[str]
    source_file: str
    source_line: int
    status: str
    docstring: str = ""
    score: float = 0.0

    def signature_oneline(self) -> str:
        return " ".join(self.statement.split())

    def short(self) -> str:
        name = self.id.split(".")[-1]
        sig = self.signature_oneline()
        if len(sig) > 200:
            sig = sig[:200] + "..."
        return f"{name}: {sig}"

    def import_path(self) -> str:
        """Derive Lean import path from source_file, e.g. 'RLGeneralization.MDP.Basic'."""
        return self.source_file.replace(".lean", "").replace("/", ".")

    def context_entry(self) -> str:
        """Full entry for context block: qualified name + statement."""
        return f"-- {self.id} (from {self.import_path()})\n{self.statement}"


def corpus_entry_text(entry: dict) -> str:
    """Build the text to index for a corpus entry."""
    parts = [entry.get("id", "").replace(".", " ").replace("_", " ")]
    if entry.get("tags"):
        parts.append(" ".join(entry["tags"]))
    if entry.get("docstring"):
        parts.append(entry["docstring"])
    parts.append(entry.get("statement", ""))
    return " | ".join(parts)


def _tokenize(text: str) -> list[str]:
    """Split text into lowercase tokens, filtering short ones."""
    tokens = re.split(r'[\s._|:(){}\[\]]+', text.lower())
    return [t for t in tokens if len(t) >= 2]


class PremiseRetriever:
    """BM25-based retriever over a JSONL corpus.

    Tracks two levels of reuse:
    - **retrieved**: premise appeared in a search result (candidate)
    - **matched**: premise was actually used to resolve a proof step

    Counts persist to ``{corpus_stem}_retrieval_stats.json`` and
    accumulate across sessions.
    """

    def __init__(self, corpus_path: str | Path, llm=None):
        self.premises: list[Premise] = []
        self._llm = llm
        self._corpus_path = Path(corpus_path)
        self._retrieval_counts: Counter[str] = Counter()
        self._match_counts: Counter[str] = Counter()
        self._load(self._corpus_path)
        self._load_stats()
        self._build_bm25_index()

    def _load(self, corpus_path: Path) -> None:
        with open(corpus_path) as f:
            for line in f:
                line = line.strip()
                if line:
                    e = json.loads(line)
                    self.premises.append(Premise(
                        id=e["id"],
                        statement=e["statement"],
                        tags=e.get("tags", []),
                        source_file=e.get("source_file", ""),
                        source_line=e.get("source_line", 0),
                        status=e.get("status", "unknown"),
                        docstring=e.get("docstring", ""),
                    ))

    def _stats_path(self) -> Path:
        return self._corpus_path.with_name(
            self._corpus_path.stem + "_retrieval_stats.json"
        )

    def _load_stats(self) -> None:
        path = self._stats_path()
        if path.exists():
            data = json.loads(path.read_text())
            self._retrieval_counts = Counter(data.get("retrieved", {}))
            self._match_counts = Counter(data.get("matched", {}))

    def _save_stats(self) -> None:
        path = self._stats_path()
        data = {
            "retrieved": dict(self._retrieval_counts),
            "matched": dict(self._match_counts),
        }
        path.write_text(json.dumps(data, indent=2) + "\n")

    def record_retrieval(self, premise_ids: list[str]) -> None:
        """Record that these premises were returned as search candidates."""
        for pid in premise_ids:
            self._retrieval_counts[pid] += 1
        self._save_stats()

    def record_match(self, premise_id: str) -> None:
        """Record that this premise was successfully used to resolve a proof step."""
        self._match_counts[premise_id] += 1
        self._save_stats()

    def retrieval_stats(self) -> dict:
        """Summary statistics for corpus reuse tracking."""
        total = len(self.premises)
        retrieved_ids = set(self._retrieval_counts)
        matched_ids = set(self._match_counts)
        never_retrieved = [
            p.id for p in self.premises if p.id not in retrieved_ids
        ]
        return {
            "total_premises": total,
            "ever_retrieved": len(retrieved_ids),
            "ever_matched": len(matched_ids),
            "never_retrieved": len(never_retrieved),
            "retrieval_rate": len(retrieved_ids) / total if total else 0,
            "match_rate": len(matched_ids) / total if total else 0,
            "top_retrieved": self._retrieval_counts.most_common(10),
            "top_matched": self._match_counts.most_common(10),
        }

    def never_retrieved(self, limit: int = 50) -> list[str]:
        """Return IDs of premises that have never been retrieved."""
        retrieved_ids = set(self._retrieval_counts)
        return [
            p.id for p in self.premises if p.id not in retrieved_ids
        ][:limit]

    def _build_bm25_index(self) -> None:
        """Build BM25 inverted-index structures over the corpus."""
        self._doc_tokens: list[list[str]] = []
        self._doc_freq: Counter[str] = Counter()
        for p in self.premises:
            text = corpus_entry_text({
                "id": p.id,
                "statement": p.statement,
                "tags": p.tags,
                "docstring": p.docstring,
            })
            tokens = _tokenize(text)
            self._doc_tokens.append(tokens)
            for tok in set(tokens):
                self._doc_freq[tok] += 1
        total_len = sum(len(d) for d in self._doc_tokens)
        self._avg_dl: float = total_len / len(self._doc_tokens) if self._doc_tokens else 1.0

    def _bm25_score(self, query_tokens: list[str], doc_idx: int) -> float:
        """Compute BM25 score for a single document against query tokens."""
        k1 = 1.5
        b = 0.75
        N = len(self.premises)
        doc = self._doc_tokens[doc_idx]
        dl = len(doc)
        freq_map: Counter[str] = Counter(doc)
        score = 0.0
        for qt in query_tokens:
            df = self._doc_freq.get(qt, 0)
            idf = math.log((N - df + 0.5) / (df + 0.5) + 1)
            freq = freq_map.get(qt, 0)
            tf = (freq * (k1 + 1)) / (freq + k1 * (1 - b + b * dl / self._avg_dl))
            score += idf * tf
        return score

    def hybrid_search(self, query: str, top_k: int = 10) -> list[Premise]:
        """BM25-ranked search over the corpus."""
        query_tokens = _tokenize(query)

        bm25_scored = [
            (idx, self._bm25_score(query_tokens, idx))
            for idx in range(len(self.premises))
        ]
        bm25_ranked = sorted(bm25_scored, key=lambda x: -x[1])

        results: list[Premise] = []
        for idx, sc in bm25_ranked[:top_k]:
            if sc <= 0:
                break
            p = copy(self.premises[idx])
            p.score = sc
            results.append(p)

        if results:
            self.record_retrieval([p.id for p in results])

        return results

    def add_premise(self, entry: dict) -> None:
        """Add a new premise to the retriever (in-memory BM25 index).

        Duplicate ids are ignored (the first entry wins).
        """
        if any(p.id == entry["id"] for p in self.premises):
            return
        premise = Premise(
            id=entry["id"],
            statement=entry["statement"],
            tags=entry.get("tags", []),
            source_file=entry.get("source_file", ""),
            source_line=entry.get("source_line", 0),
            status=entry.get("status", "unknown"),
            docstring=entry.get("docstring", ""),
        )
        self.premises.append(premise)

        text = corpus_entry_text(entry)
        tokens = _tokenize(text)
        self._doc_tokens.append(tokens)
        for tok in set(tokens):
            self._doc_freq[tok] += 1
        total_len = sum(len(d) for d in self._doc_tokens)
        self._avg_dl = total_len / len(self._doc_tokens) if self._doc_tokens else 1.0

    def __len__(self) -> int:
        return len(self.premises)


# ---------------------------------------------------------------------------
# Near-match log-argument scan (resolve-time corroboration)
# ---------------------------------------------------------------------------
#
# Mechanizes the "library witness" observation: a block claiming log(2K/δ)
# next to a kernel-checked library lemma requiring log(2KT/δ) is anomalous —
# the differing factor is exactly where missing-hypothesis flaws live.
#
# Design rule (empirically forced): ANNOTATE, NEVER SUPPRESS. Any heuristic
# that silences a `differs` line because some other hit `agrees` can hide the
# true flaw behind an innocent same-log cousin. Both groups are surfaced;
# adjudication is the agent's job and silence proves nothing.

_GREEK_NAMES = {
    "delta": "δ", "eps": "ε", "epsilon": "ε", "alpha": "α", "beta": "β",
    "gamma": "γ", "lambda": "λ", "theta": "θ", "sigma": "σ", "mu": "μ",
}

_LOG_HEAD_RE = re.compile(r"(?:Real\.)?\b(?:log|ln)\b\s*")


def norm_symbols(expr: str) -> frozenset[str]:
    """Canonical symbol set of an expression inside a log argument.

    Handles Lean (`2 * ↑K * ↑T / δ`, casts `(K : ℝ)`) and prose (`2KT/δ`):
    numbers and single-letter identifiers become symbols; compact products
    like `2KT` split into {2, K, T}; Greek-letter names map to the letter.
    """
    expr = expr.replace("↑", " ")
    expr = re.sub(r":\s*[ℝℕℚ𝕜A-Za-z]+", " ", expr)  # strip type ascriptions
    symbols: set[str] = set()
    for tok in re.split(r"[\s*/+\-^()⁻¹,]+", expr):
        if not tok:
            continue
        low = tok.lower()
        if low in _GREEK_NAMES:
            symbols.add(_GREEK_NAMES[low])
            continue
        if re.fullmatch(r"\d+(?:\.\d+)?", tok):
            symbols.add(tok)
            continue
        if len(tok) == 1:
            symbols.add(tok)
            continue
        # compact product like 2KT or KT: number prefix + capital letters
        m = re.fullmatch(r"(\d*)([A-Zδεαβγλθσμ]+)", tok)
        if m:
            if m.group(1):
                symbols.add(m.group(1))
            symbols.update(m.group(2))
            continue
        symbols.add(tok)  # multi-letter identifier, kept whole
    return frozenset(symbols)


def log_args(text: str) -> list[frozenset[str]]:
    """Symbol sets of every log/ln argument in `text` (statement + prose).

    Parenthesized arguments are scanned with balanced-paren tolerance;
    a bare following token (`log T`) is taken as a one-symbol argument.
    """
    out: list[frozenset[str]] = []
    for m in _LOG_HEAD_RE.finditer(text):
        rest = text[m.end():]
        if rest.startswith("("):
            depth, i = 0, 0
            for i, ch in enumerate(rest):
                if ch == "(":
                    depth += 1
                elif ch == ")":
                    depth -= 1
                    if depth == 0:
                        break
            arg = rest[1:i]
        else:
            tok = re.match(r"[^\s,;.)]+", rest)
            arg = tok.group(0) if tok else ""
        syms = norm_symbols(arg)
        if syms:
            out.append(syms)
    return out


def _structural(syms: frozenset[str]) -> frozenset[str]:
    """Non-numeric, non-confidence symbols — the scale parameters (K, T, n, H)."""
    return frozenset(s for s in syms
                     if not re.fullmatch(r"\d+(?:\.\d+)?", s) and s not in "δε")


def near_match_scan(claim_text: str, premises: list["Premise"]) -> dict:
    """Compare the claim's log arguments against each premise's.

    Returns {"claim_log_args", "agrees", "differs", "substitutions"}.
    A premise lands in `differs` when one of its log arguments is a strict
    superset/subset of a claim log argument sharing a structural symbol —
    `missing` lists what the BLOCK lacks. Exact matches land in `agrees`;
    same-structure replacements land in `substitutions` (lower salience).
    A premise can appear in several groups: annotate, never suppress.
    """
    claim_logs = log_args(claim_text)
    result: dict = {
        "claim_log_args": [sorted(s) for s in claim_logs],
        "agrees": [], "differs": [], "substitutions": [],
    }
    if not claim_logs:
        return result
    for p in premises:
        plogs = log_args(f"{p.statement}\n{p.docstring}")
        if not plogs:
            continue
        agreed = differed = subst = False
        diffs: list[dict] = []
        for c in claim_logs:
            for pl in plogs:
                if pl == c:
                    agreed = True
                elif (_structural(pl) & _structural(c)) and (pl > c or pl < c):
                    differed = True
                    diffs.append({
                        "lemma_log": sorted(pl),
                        "claim_log": sorted(c),
                        "missing": sorted(pl - c),   # what the block lacks
                        "extra": sorted(c - pl),     # what the block adds
                    })
                elif _structural(pl) & _structural(c):
                    subst = True
        if agreed:
            result["agrees"].append(
                {"id": p.id, "log_args": [sorted(s) for s in plogs]})
        if differed:
            result["differs"].append(
                {"id": p.id, "log_args": [sorted(s) for s in plogs],
                 "diffs": diffs})
        if subst and not (agreed or differed):
            result["substitutions"].append(
                {"id": p.id, "log_args": [sorted(s) for s in plogs]})
    return result
