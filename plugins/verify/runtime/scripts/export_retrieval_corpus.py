#!/usr/bin/env python3
"""Export a retrieval corpus of theorem statements (without proofs).

This is the CANONICAL way to (re)build rlverify/corpus.jsonl: the Lean
source tree is the single source of truth, the corpus is a derived cache.
Run it after library-expansion sessions to repair drift (duplicates,
empty statements, stale entries).

Scans all .lean files under RLGeneralization/ and outputs one JSON object
per line containing the theorem statement, module ID, verification status,
and domain tags derived from the module path. Metadata that cannot be
derived from source (extra tags, docstrings, statuses of entries added by
`d.add_novel`) is merged from the existing corpus by id.

Usage:
    python scripts/export_retrieval_corpus.py            # rebuild corpus
    python scripts/export_retrieval_corpus.py --check    # report drift only
    python scripts/export_retrieval_corpus.py --out rlverify/corpus.jsonl
"""

import argparse
import json
import re
import sys
from pathlib import Path

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

DECL_RE = re.compile(r"^(theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_'.]*)")

# Tag derivation from module path components
TAG_MAP: dict[str, list[str]] = {
    "Concentration": ["concentration"],
    "Hoeffding": ["concentration", "hoeffding"],
    "Bernstein": ["concentration", "bernstein"],
    "Bennett": ["concentration", "bennett"],
    "BennettMGF": ["concentration", "bennett"],
    "MatrixBernstein": ["concentration", "matrix"],
    "SelfNormalized": ["concentration", "self-normalized"],
    "SubGaussian": ["concentration", "sub-gaussian"],
    "AzumaHoeffding": ["concentration", "azuma-hoeffding"],
    "MDPConcentration": ["concentration", "mdp"],
    "McDiarmid": ["concentration", "mcdiarmid"],
    "McDiarmidFull": ["concentration", "mcdiarmid"],
    "JohnsonLindenstrauss": ["concentration", "jl"],
    "Talagrand": ["concentration", "talagrand"],
    "LargeDeviations": ["concentration", "large-deviations"],
    "Isoperimetric": ["concentration", "isoperimetric"],
    "PhiEntropy": ["concentration", "entropy-method"],
    "StochasticCalculus": ["concentration", "stochastic-calculus"],
    "CLT": ["concentration", "clt"],
    "GenerativeModel": ["concentration", "generative-model", "pac"],
    "GenerativeModelCore": ["concentration", "generative-model"],
    "DiscreteConcentration": ["concentration", "discrete"],
    "MarkovChain": ["concentration", "markov-chain"],
    "MDP": ["mdp"],
    "Basic": ["mdp", "definitions"],
    "BellmanContraction": ["mdp", "bellman", "contraction"],
    "SimulationLemma": ["mdp", "simulation"],
    "SimulationResolvent": ["mdp", "simulation", "resolvent"],
    "ValueIteration": ["mdp", "value-iteration"],
    "PolicyIteration": ["mdp", "policy-iteration"],
    "Resolvent": ["mdp", "resolvent"],
    "BanachFixedPoint": ["mdp", "fixed-point"],
    "PerformanceDifference": ["mdp", "pdl"],
    "OccupancyMeasure": ["mdp", "occupancy"],
    "MatrixResolvent": ["mdp", "matrix-resolvent"],
    "FiniteHorizon": ["mdp", "finite-horizon"],
    "LPFormulation": ["mdp", "lp"],
    "AverageReward": ["mdp", "average-reward"],
    "HJB": ["mdp", "continuous"],
    "POMDP": ["mdp", "pomdp"],
    "MultiAgent": ["mdp", "multi-agent"],
    "Bandits": ["bandit"],
    "UCB": ["bandit", "ucb"],
    "EXP3": ["bandit", "exp3", "adversarial"],
    "LowerBound": ["lower-bound"],
    "ThompsonSampling": ["bandit", "thompson-sampling", "bayesian"],
    "LinearBandits": ["bandit", "linear"],
    "BanditConcentration": ["bandit", "concentration"],
    "Generalization": ["generalization"],
    "SampleComplexity": ["sample-complexity"],
    "ComponentWise": ["generalization", "component-wise"],
    "MinimaxSampleComplexity": ["generalization", "minimax"],
    "PACBayes": ["pac-bayes"],
    "PolicyEvaluation": ["policy-evaluation"],
    "DudleyRL": ["generalization", "dudley", "covering-number"],
    "FiniteHorizonSampleComplexity": ["generalization", "finite-horizon"],
    "LinearFeatures": ["linear", "regression"],
    "LSVI": ["lsvi", "regression"],
    "RegressionBridge": ["regression", "bridge"],
    "BilinearRank": ["bilinear-rank"],
    "GOLF": ["bilinear-rank", "golf"],
    "Exploration": ["exploration"],
    "UCBVI": ["ucbvi", "exploration"],
    "VarianceUCBVI": ["ucbvi", "variance", "exploration"],
    "UCBVISimulation": ["ucbvi", "simulation"],
    "BatchUCBVI": ["ucbvi", "batch"],
    "PolicyOptimization": ["policy-optimization"],
    "PolicyGradient": ["policy-gradient"],
    "FiniteWeightedTailPolicyGradient": [
        "policy-gradient", "cpt", "distortion-risk", "finite-support"
    ],
    "CPI": ["cpi", "conservative"],
    "Optimality": ["optimality"],
    "NPG": ["npg", "natural-gradient"],
    "TRPO": ["trpo", "trust-region"],
    "ImitationLearning": ["imitation"],
    "MaxEntIRL": ["imitation", "irl", "max-entropy"],
    "OfflineRL": ["offline-rl"],
    "FQI": ["fqi", "regression"],
    "Pessimism": ["offline-rl", "pessimism"],
    "LinearMDP": ["linear-mdp"],
    "EllipticalPotential": ["linear-mdp", "elliptical-potential"],
    "Regret": ["regret"],
    "Complexity": ["complexity"],
    "VCDimension": ["vc-dimension", "complexity"],
    "Rademacher": ["rademacher", "complexity"],
    "Symmetrization": ["symmetrization", "complexity"],
    "CoveringPacking": ["covering-number", "complexity"],
    "GenericChaining": ["generic-chaining", "complexity"],
    "EluderDimension": ["eluder-dimension", "complexity"],
    "LowerBounds": ["lower-bound"],
    "FanoLeCam": ["lower-bound", "fano", "le-cam"],
    "Algorithms": ["algorithm"],
    "QLearning": ["q-learning", "algorithm"],
    "LinearTD": ["td-learning", "linear"],
    "Privacy": ["privacy"],
    "DPRewards": ["privacy", "differential-privacy"],
    "Optimization": ["optimization"],
    "SGD": ["sgd", "optimization"],
    "Approximation": ["approximation"],
    "RKHS": ["rkhs", "kernel"],
    "NeuralNetwork": ["neural-network"],
    "LQR": ["lqr", "control"],
    "RiccatiPolicy": ["lqr", "riccati"],
}


def derive_tags(module: str) -> list[str]:
    """Derive tags from module path components."""
    parts = module.replace("RLGeneralization.", "").split(".")
    tags: list[str] = []
    seen: set[str] = set()
    for part in parts:
        for tag in TAG_MAP.get(part, []):
            if tag not in seen:
                tags.append(tag)
                seen.add(tag)
    # If no specific tags, use the first path component lowercased
    if not tags and parts:
        tags.append(parts[0].lower())
    return tags


# ---------------------------------------------------------------------------
# Manifest loader
# ---------------------------------------------------------------------------


def load_manifest_statuses(root: Path) -> dict[str, str]:
    """Load module-level and theorem-level statuses from verification_manifest.json."""
    manifest_path = root / "verification_manifest.json"
    if not manifest_path.exists():
        return {}
    data = json.loads(manifest_path.read_text())
    statuses: dict[str, str] = {}
    for entry in data.get("verified_target", {}).get("modules", []):
        statuses[entry["module"]] = entry.get("status", "unknown")
    for entry in data.get("theorems", []):
        statuses[entry["name"]] = entry.get("status", "unknown")
    return statuses


# ---------------------------------------------------------------------------
# Statement extraction
# ---------------------------------------------------------------------------


def find_assignment(lines: list[str], start: int) -> tuple[int, int] | None:
    """Find the top-level `:=` that starts the proof body.

    A statement-level `let X := e` binder inside the signature owns the
    next top-level `:=` — without tracking this, statements like
    `theorem foo : let L := Real.log (...) ...` are cut at the `let`,
    losing the entire conclusion.
    """
    depth = 0
    pending_lets = 0
    for li in range(start, min(start + 80, len(lines))):
        line = lines[li]
        col = 0
        while col < len(line):
            if line.startswith("--", col):
                break
            ch = line[col]
            if ch in "({[":
                depth += 1
            elif ch in ")}]":
                depth = max(depth - 1, 0)
            elif (depth == 0 and line.startswith("let", col)
                    and (col == 0 or not (line[col - 1].isalnum()
                                          or line[col - 1] == "_"))
                    and (col + 3 >= len(line)
                         or not (line[col + 3].isalnum()
                                 or line[col + 3] == "_"))):
                pending_lets += 1
                col += 3
                continue
            elif ch == ":" and col + 1 < len(line) and line[col + 1] == "=" and depth == 0:
                if pending_lets > 0:
                    pending_lets -= 1
                    col += 2
                    continue
                return li, col
            col += 1
    return None


def extract_docstring(lines: list[str], decl_line: int) -> str:
    """Extract the /-- ... -/ doc comment immediately preceding a declaration."""
    k = decl_line - 1
    while k >= 0 and lines[k].strip() == "":
        k -= 1
    if k < 0:
        return ""
    if not (lines[k].strip().endswith("-/") or lines[k].strip() == "-/"):
        return ""
    doc_end = k
    while k >= 0 and "/--" not in lines[k]:
        k -= 1
    if k < 0:
        return ""
    raw = "\n".join(lines[k:doc_end + 1])
    raw = re.sub(r"/--?\s*", "", raw)
    raw = re.sub(r"\s*-/", "", raw)
    return raw.strip()[:500]


def extract_statements_from_file(filepath: Path, root: Path,
                                  statuses: dict[str, str]) -> list[dict]:
    """Extract theorem statements (without proofs) from a .lean file."""
    text = filepath.read_text()
    all_lines = text.splitlines()
    results: list[dict] = []

    try:
        rel = filepath.relative_to(root)
    except ValueError:
        rel = filepath
    module_name = str(rel).replace("/", ".").removesuffix(".lean")
    tags = derive_tags(module_name)

    i = 0
    while i < len(all_lines):
        m = DECL_RE.match(all_lines[i])
        if not m:
            i += 1
            continue

        kind = m.group(1)
        name = m.group(2)
        decl_start = i

        assignment = find_assignment(all_lines, i)
        if assignment is None:
            i += 1
            continue

        body_line, assign_col = assignment

        # Statement: everything up to (but not including) `:=`
        stmt_lines = all_lines[decl_start:body_line + 1]
        stmt_lines[-1] = stmt_lines[-1][:assign_col].rstrip()
        statement = "\n".join(stmt_lines).strip()

        # Extract docstring
        docstring = extract_docstring(all_lines, decl_start)

        # Determine status
        status = "unknown"
        qualified = f"{module_name}.{name}"
        for key in [qualified, name, module_name]:
            if key in statuses:
                status = statuses[key]
                break

        theorem_id = f"{module_name}.{name}"

        entry: dict = {
            "id": theorem_id,
            "kind": kind,
            "statement": statement,
            "status": status,
            "tags": tags,
            "source_file": str(rel),
            "source_line": decl_start + 1,
        }
        if docstring:
            entry["docstring"] = docstring

        results.append(entry)

        # Skip to end of proof
        proof_end = body_line + 1
        while proof_end < len(all_lines):
            stripped = all_lines[proof_end].strip()
            if DECL_RE.match(all_lines[proof_end]):
                break
            if stripped.startswith("/-"):
                break
            if re.match(r"^end\b", stripped):
                break
            if re.match(
                r"^(variable|variables|open|local|scoped|attribute|namespace|section|noncomputable)\b",
                stripped,
            ):
                break
            proof_end += 1
        i = proof_end

    return results


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------


def load_existing_corpus(out_path: Path) -> dict[str, dict]:
    """Load the current corpus keyed by id (first occurrence wins)."""
    existing: dict[str, dict] = {}
    if not out_path.exists():
        return existing
    for line in out_path.read_text().splitlines():
        line = line.strip()
        if not line:
            continue
        e = json.loads(line)
        existing.setdefault(e["id"], e)
    return existing


def merge_existing(entry: dict, old: dict | None) -> dict:
    """Merge non-derivable metadata from an existing corpus entry."""
    if not old:
        return entry
    old_tags = old.get("tags") or []
    merged_tags = list(entry.get("tags") or [])
    for t in old_tags:
        if t not in merged_tags:
            merged_tags.append(t)
    entry["tags"] = merged_tags
    if not entry.get("docstring") and old.get("docstring"):
        entry["docstring"] = old["docstring"]
    if entry.get("status") == "unknown" and old.get("status", "unknown") != "unknown":
        entry["status"] = old["status"]
    return entry


def module_built(root: Path, source_file: str) -> bool:
    """Check whether a module has a compiled .olean."""
    olean = (
        root / ".lake" / "build" / "lib" / "lean"
        / source_file.removesuffix(".lean")
    ).with_suffix(".olean")
    return olean.exists()


def check_drift(all_entries: list[dict], existing: dict[str, dict],
                root: Path, out_path: Path) -> int:
    """Report corpus drift against the source tree. Returns #problems."""
    problems = 0

    # Duplicate ids in the current corpus file
    seen: dict[str, int] = {}
    for line in out_path.read_text().splitlines() if out_path.exists() else []:
        line = line.strip()
        if line:
            eid = json.loads(line)["id"]
            seen[eid] = seen.get(eid, 0) + 1
    dups = {k: v for k, v in seen.items() if v > 1}
    if dups:
        problems += len(dups)
        print(f"DUPLICATE ids in corpus ({len(dups)}):")
        for k, v in dups.items():
            print(f"  {v}x {k}")

    # Empty statements
    empty = [e["id"] for e in existing.values() if not e.get("statement", "").strip()]
    if empty:
        problems += len(empty)
        print(f"EMPTY statements ({len(empty)}):")
        for eid in empty:
            print(f"  {eid}")

    # Corpus entries whose source no longer yields a declaration
    source_ids = {e["id"] for e in all_entries}
    stale = [eid for eid in existing if eid not in source_ids]
    if stale:
        problems += len(stale)
        print(f"STALE entries (id not found in source tree) ({len(stale)}):")
        for eid in stale[:20]:
            print(f"  {eid}")

    # Source declarations missing from corpus
    missing = [e["id"] for e in all_entries if e["id"] not in existing]
    if missing:
        problems += len(missing)
        print(f"MISSING from corpus ({len(missing)}):")
        for eid in missing[:20]:
            print(f"  {eid}")

    # Unbuilt modules
    unbuilt = sorted({
        e["source_file"] for e in all_entries
        if not module_built(root, e["source_file"])
    })
    if unbuilt:
        print(f"UNBUILT modules ({len(unbuilt)}) — theorems exist but cannot be imported:")
        for sf in unbuilt:
            print(f"  {sf}")

    print(f"\n{problems} drift problem(s); {len(unbuilt)} unbuilt module(s).")
    return problems


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Export theorem statements as a retrieval corpus.")
    parser.add_argument("--root", type=Path,
                        default=Path(__file__).resolve().parent.parent,
                        help="Project root directory (default: auto-detect)")
    parser.add_argument("--out", type=Path, default=None,
                        help="Output JSONL path (default: <root>/rlverify/corpus.jsonl)")
    parser.add_argument("--source-dir", type=str, default="RLGeneralization",
                        help="Subdirectory to scan (default: RLGeneralization)")
    parser.add_argument("--check", action="store_true",
                        help="Report drift between corpus and source tree; do not write")
    args = parser.parse_args()

    root = args.root.resolve()
    out_path = (args.out or root / "rlverify" / "corpus.jsonl").resolve()
    source_dir = root / args.source_dir

    if not source_dir.is_dir():
        print(f"error: {source_dir} is not a directory", file=sys.stderr)
        sys.exit(1)

    statuses = load_manifest_statuses(root)
    existing = load_existing_corpus(out_path)

    all_entries: list[dict] = []
    seen_ids: set[str] = set()
    lean_files = sorted(source_dir.rglob("*.lean"))
    print(f"Scanning {len(lean_files)} .lean files under {source_dir.name}/",
          file=sys.stderr)

    for filepath in lean_files:
        for entry in extract_statements_from_file(filepath, root, statuses):
            if entry["id"] in seen_ids:
                print(f"  warning: duplicate declaration id skipped: {entry['id']}",
                      file=sys.stderr)
                continue
            seen_ids.add(entry["id"])
            all_entries.append(merge_existing(entry, existing.get(entry["id"])))

    if args.check:
        sys.exit(1 if check_drift(all_entries, existing, root, out_path) else 0)

    # Write JSONL
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with open(out_path, "w") as f:
        for entry in all_entries:
            f.write(json.dumps(entry, ensure_ascii=False) + "\n")

    # Summary
    by_status: dict[str, int] = {}
    by_tag: dict[str, int] = {}
    for e in all_entries:
        by_status[e["status"]] = by_status.get(e["status"], 0) + 1
        for tag in e["tags"]:
            by_tag[tag] = by_tag.get(tag, 0) + 1

    print(f"\nExported {len(all_entries)} theorem statements", file=sys.stderr)
    print(f"  Output: {out_path}", file=sys.stderr)
    print(f"  By status: {json.dumps(by_status, indent=4)}", file=sys.stderr)
    top_tags = sorted(by_tag.items(), key=lambda x: -x[1])[:15]
    print(f"  Top tags: {json.dumps(dict(top_tags), indent=4)}", file=sys.stderr)


if __name__ == "__main__":
    main()
