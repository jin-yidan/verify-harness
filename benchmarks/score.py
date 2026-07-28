#!/usr/bin/env python3
"""Benchmark scorer: grade a runs/*.json record against a fixture's expected.json.

Fully deterministic — no agent needed. The agent-driven part of the battery is
ONLY producing the run record (one /verify-full-process invocation per fixture, see
README.md); everything after that is this script.

Usage:
    python3 benchmarks/score.py <fixture_dir> <run_record.json> [--tsv]

<fixture_dir> must contain sealed/expected.json. With --tsv, a result row is
appended to benchmarks/results.tsv.
"""
from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
# Single verdict authority (W1). `effective_verdict` is kept as the public name
# the scorer/tests use; it now delegates instead of being a hand-synced copy.
from rlverify.verdict import (  # noqa: E402
    STANDARD_AXIOMS,
    is_main_theorem_refutation,
    verdict_class,
)

effective_verdict = verdict_class


def blob_for_flaw_search(run: dict) -> str:
    """All free text where a detected flaw can legitimately surface."""
    parts = [run.get("verdict_reason", ""), run.get("verdict", "")]
    for lemma in run.get("lemmas", []):
        parts.append(lemma.get("statement", ""))
        parts.append(lemma.get("note", ""))
    for f in run.get("falsifications", []):
        parts.append(f.get("claim", ""))
        parts.append(json.dumps(f.get("certificate") or {}))
        parts.append(f.get("reason", ""))
    for ref in run.get("refutations", []):
        parts.append(ref.get("description", ""))
    return "\n".join(parts).lower()


def score(expected: dict, run: dict) -> dict:
    out = {"fixture": expected["fixture"], "checks": [], "needs_review": []}

    # 1. Verdict class (exact, or membership when the key gives a list).
    got = effective_verdict(run)
    want = expected.get("verdict_class_any") or [expected["verdict_class"]]
    ok = got in want
    out["checks"].append(("verdict_class", ok, f"expected one of {want}, got {got!r}"))
    out["effective_verdict"] = got

    # 2. Per-flaw detection: keyword signature over verdict_reason + block
    #    notes + falsification claims/certificates + refutation descriptions.
    #    UNMATCHED => needs_review, not silent fail — phrasing varies per run.
    blob = blob_for_flaw_search(run)
    detected = 0
    for flaw in expected.get("flaws", []):
        hits = [k for k in flaw["signature_keywords"] if k.lower() in blob]
        matched = len(hits) >= flaw.get("min_keyword_hits", 1)
        detected += matched
        out["checks"].append((f"flaw:{flaw['id']}", matched,
                              f"keyword hits {hits} "
                              f"(need {flaw.get('min_keyword_hits', 1)})"))
        if not matched:
            out["needs_review"].append(
                f"flaw {flaw['id']} not keyword-matched — re-read "
                "verdict_reason manually")
    out["detection_rate"] = (detected, len(expected.get("flaws", [])))

    # 3. False positives: REFUTED falsifications / violation / circular blocks
    #    on blocks the key lists as sound. For clean controls (flaws: []), ANY
    #    failure verdict is itself a false positive.
    sound = set(expected.get("sound_block_hints", []))
    fps = []
    for f in run.get("falsifications", []):
        if f.get("verdict") == "REFUTED" and f.get("block") in sound:
            fps.append(f"falsify REFUTED on sound block {f['block']}")
    for lemma in run.get("lemmas", []):
        if lemma.get("kind") in ("violation", "circular") \
                and lemma["name"] in sound:
            fps.append(f"{lemma['kind']} recorded on sound block {lemma['name']}")
    if not expected.get("flaws") and got.startswith("UNVERIFIED"):
        fps.append(f"failure verdict {got!r} on a clean-control fixture")
    out["checks"].append(("false_positives", not fps, fps or "none"))

    # 4. Kernel-backed evidence: library/instantiation blocks were previously
    #    kernel-proven; compiled blocks were proven this run. Named-result
    #    citations (textbook theorems) carry kind "instantiation" but were
    #    never kernel-proven — exclude them unless compiled this run.
    lemmas = run.get("lemmas", [])
    kernel_backed = sum(1 for l in lemmas
                        if (l.get("kind") in ("library", "instantiation")
                            and not l.get("named_result"))
                        or l.get("compiled"))
    out["kernel_backed_fraction"] = (kernel_backed, len(lemmas))
    out["refuted_with_certificate"] = sum(
        1 for f in run.get("falsifications", [])
        if f.get("verdict") == "REFUTED" and f.get("certificate"))
    kernel_backed_refutations = sum(
        1 for ref in run.get("refutations", [])
        if is_main_theorem_refutation(ref))
    out["kernel_backed_refutations"] = kernel_backed_refutations
    # Kernel-backed EVIDENCE counts both proven lemmas (the VERIFIED axis) and
    # scoped kernel-backed main-theorem refutations (the WRONG axis): a compiled counterexample with
    # a clean closure is the strongest failure evidence there is, so it must
    # satisfy "min_kernel_backed" for a refutation-style fixture — previously it
    # was tracked but never credited, so a correct kernel-backed WRONG scored 0.
    kernel_backed_evidence = kernel_backed + kernel_backed_refutations
    # For a DETECTION fixture (expected verdict is a failure class), ONE
    # scoped main-theorem refutation already CERTIFIES falsity — the WRONG verdict is
    # kernel-proven. Salvaging additional independent blocks is a quality bonus,
    # not a pass gate, so it must not turn a correctly-detected, kernel-certified
    # WRONG into a FAIL (the live ucb_regret_mutated artifact: threshold 2, but 1
    # refutation fully certifies). VERIFY fixtures still need the block threshold.
    want = expected.get("verdict_class_any") or [expected.get("verdict_class", "")]
    is_detection = any(str(v).startswith("UNVERIFIED/") and v != "UNVERIFIED/UNGATED"
                       for v in want)
    threshold = expected.get("min_kernel_backed_blocks", 0)
    if is_detection and kernel_backed_refutations >= 1:
        ok = True
        note = (f"kernel-certified flaw via {kernel_backed_refutations} refutation(s)"
                f" (+{kernel_backed} salvaged block(s))")
        # Do NOT silently MASK an incomplete salvage: if the fixture expected more
        # kernel-backed evidence than was produced, the flaw is certified but the
        # salvage rule (formalize independent correct blocks) was under-followed —
        # surface it as needs_review (visible, but not a hard FAIL of a correct
        # detection). The live ucb_regret_mutated left step6 unformalized.
        if kernel_backed_evidence < threshold:
            out["needs_review"].append(
                f"salvage incomplete: {kernel_backed_evidence}/{threshold} expected "
                "kernel-backed block(s) — flaw certified, but independent correct "
                "blocks were not all formalized (salvage rule)")
    else:
        ok = kernel_backed_evidence >= threshold
        note = (f"{kernel_backed} kernel-backed block(s) + "
                f"{kernel_backed_refutations} kernel-backed refutation(s)")
    out["checks"].append(("min_kernel_backed", ok, note))
    out["verdict_evidence"] = run.get("verdict_evidence", "")

    # 5. Expected library reuse.
    matches = " ".join(l.get("library_match", "") for l in lemmas)
    for want_match in expected.get("expected_library_matches", []):
        out["checks"].append((f"library:{want_match}",
                              want_match in matches, ""))

    # 6. Triage anchoring metric: every detected flaw NOT flagged by triage
    #    is recorded evidence that gate coverage survived the prose pass.
    triage = run.get("triage") or None
    if triage is not None:
        flagged = " ".join(
            f"{s.get('step', '')} {s.get('suspicion', '')}"
            for s in triage.get("suspects", [])).lower()

        def triage_flagged(flaw):
            if flaw["location"].lower() in flagged:
                return True
            return any(k.lower() in flagged
                       for k in flaw["signature_keywords"])

        unflagged_found = [f["id"] for f in expected.get("flaws", [])
                           if not triage_flagged(f)]
        out["anchoring_unflagged_flaws_found"] = unflagged_found
        out["triage_all_clear"] = triage.get("all_clear")

    out["passed"] = all(ok for _, ok, _ in out["checks"])
    return out


def append_tsv(result: dict, tsv_path: Path) -> None:
    commit = subprocess.run(["git", "rev-parse", "--short", "HEAD"],
                            capture_output=True, text=True).stdout.strip()
    from datetime import date
    d, n = result["detection_rate"]
    k, m = result["kernel_backed_fraction"]
    fp_ok = next(ok for name, ok, _ in result["checks"]
                 if name == "false_positives")
    row = "\t".join([
        str(date.today()), commit, result["fixture"],
        f"{d}/{n}", "0" if fp_ok else "FP",
        f"{k}/{m}", str(result["refuted_with_certificate"]),
        str(result["kernel_backed_refutations"]),
        result.get("verdict_evidence", ""),
        "PASS" if result["passed"] else "FAIL",
    ])
    with open(tsv_path, "a") as f:
        f.write(row + "\n")


def main() -> None:
    fixture_dir = Path(sys.argv[1])
    expected = json.loads((fixture_dir / "sealed" / "expected.json").read_text())
    run = json.loads(Path(sys.argv[2]).read_text())
    result = score(expected, run)
    for name, ok, detail in result["checks"]:
        print(f"  {'PASS' if ok else 'FAIL':4}  {name:45} {detail}")
    d, n = result["detection_rate"]
    k, m = result["kernel_backed_fraction"]
    print(f"\ndetection {d}/{n} | kernel-backed {k}/{m} blocks | "
          f"{result['refuted_with_certificate']} refuted-with-certificate | "
          f"{result['kernel_backed_refutations']} kernel-backed refutation(s)")
    if "anchoring_unflagged_flaws_found" in result:
        print(f"triage anchoring: flaws found despite no triage flag: "
              f"{result['anchoring_unflagged_flaws_found']}")
    if result["needs_review"]:
        print("NEEDS REVIEW:", *result["needs_review"], sep="\n  ")
    print("OVERALL:", "PASS" if result["passed"] else "FAIL")
    if "--tsv" in sys.argv:
        append_tsv(result, Path(__file__).parent / "results.tsv")
    sys.exit(0 if result["passed"] else 1)


if __name__ == "__main__":
    main()
