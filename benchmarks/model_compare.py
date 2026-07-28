#!/usr/bin/env python3
"""Model-comparison harness for the RLVerify benchmark battery.

Runs each fixture under several models (one headless `/verify-full-process` invocation per
model x fixture), grades every run with the existing deterministic scorer, and
logs verdict accuracy + cost + wall-clock to benchmarks/model_comparison.tsv.

The question it answers: if a cheaper model (sonnet/haiku) reaches the same
verdict and flaw detection as opus on these fixtures, the expensive tier isn't
needed for verification.

Usage:
    python3 benchmarks/model_compare.py \
        --models opus,sonnet,haiku \
        --fixtures ucb_regret_clean,ucb_regret_mutated \
        [--timeout 2400]

Sequential by construction: add_novel corpus appends and lake builds race, so
runs never overlap (same rule as run_batch.sh). Each run gets its own frozen
corpus snapshot. The canonical results.tsv is left untouched; this writes only
model_comparison.tsv.
"""
from __future__ import annotations

import argparse
import json
import shutil
import subprocess
import sys
import tempfile
import time
from datetime import date
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
from benchmarks.score import score, effective_verdict  # noqa: E402

TSV = Path(__file__).parent / "model_comparison.tsv"
TSV_HEADER = ("date\tmodel\tfixture\texpected\tgot\tverdict_match\t"
              "detection\tfalse_pos\tkernel_backed\toverall\t"
              "cost_usd\tduration_s\tnum_turns\n")


def newest_record(before: set[Path]) -> Path | None:
    """The run record that appeared in runs/ since `before` was snapshotted."""
    runs = ROOT / "runs"
    now = {p for p in runs.glob("*.json")}
    fresh = now - before
    if not fresh:
        return None
    return max(fresh, key=lambda p: p.stat().st_mtime)


def run_one(model: str, fixture: str, timeout: int) -> dict:
    fix_dir = ROOT / "benchmarks" / fixture
    statement = (fix_dir / "statement.md").read_text()
    expected = json.loads((fix_dir / "sealed" / "expected.json").read_text())

    snapshot = tempfile.mktemp(prefix="corpus_snapshot_", suffix=".jsonl")
    shutil.copy(ROOT / "rlverify" / "corpus.jsonl", snapshot)

    session = f"{fixture}_{model}"
    prompt = (
        f'/verify-full-process Use VerifyDriver(corpus_path="{snapshot}") for this run '
        f"(frozen-corpus benchmark protocol; do not add lemmas to the real "
        f'library). Session name: {session}. Verify the following theorem '
        f"and proof:\n\n{statement}"
    )

    before = {p for p in (ROOT / "runs").glob("*.json")}
    t0 = time.time()
    cost = duration_s = num_turns = None
    record = None
    status = "ok"
    try:
        proc = subprocess.run(
            ["claude", "-p", prompt, "--model", model,
             "--permission-mode", "acceptEdits", "--output-format", "json"],
            cwd=ROOT, capture_output=True, text=True, timeout=timeout,
        )
        wall = time.time() - t0
        if proc.returncode != 0:
            status = f"cli_exit_{proc.returncode}"
        try:
            meta = json.loads(proc.stdout)
            cost = meta.get("total_cost_usd")
            duration_s = round((meta.get("duration_ms") or 0) / 1000, 1)
            num_turns = meta.get("num_turns")
        except (json.JSONDecodeError, AttributeError):
            duration_s = round(wall, 1)
    except subprocess.TimeoutExpired:
        status = "timeout"
        duration_s = float(timeout)

    rec_path = newest_record(before)
    result = None
    if rec_path is not None:
        record = rec_path
        run = json.loads(rec_path.read_text())
        result = score(expected, run)

    want = expected.get("verdict_class_any") or [expected["verdict_class"]]
    got = result["effective_verdict"] if result else "(no record)"
    return {
        "model": model, "fixture": fixture, "status": status,
        "expected": "|".join(want), "got": got,
        "verdict_match": result is not None and got in want,
        "result": result, "record": str(record) if record else "",
        "cost_usd": cost, "duration_s": duration_s, "num_turns": num_turns,
        "snapshot": snapshot,
    }


def fmt_row(r: dict) -> str:
    res = r["result"]
    det = "-" if not res else "{}/{}".format(*res["detection_rate"])
    kb = "-" if not res else "{}/{}".format(*res["kernel_backed_fraction"])
    fp = "-"
    overall = r["status"] if r["status"] != "ok" else "(no record)"
    if res:
        fp_ok = next(ok for n, ok, _ in res["checks"] if n == "false_positives")
        fp = "0" if fp_ok else "FP"
        overall = "PASS" if res["passed"] else "FAIL"
    return "\t".join(str(x) for x in [
        date.today(), r["model"], r["fixture"], r["expected"], r["got"],
        "Y" if r["verdict_match"] else "N", det, fp, kb, overall,
        r["cost_usd"] if r["cost_usd"] is not None else "-",
        r["duration_s"] if r["duration_s"] is not None else "-",
        r["num_turns"] if r["num_turns"] is not None else "-",
    ])


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--models", default="opus,sonnet,haiku")
    ap.add_argument("--fixtures",
                    default="ucb_regret_clean,ucb_regret_mutated")
    ap.add_argument("--timeout", type=int, default=1200,
                    help="per-run wall-clock cap in seconds")
    args = ap.parse_args()

    models = [m.strip() for m in args.models.split(",") if m.strip()]
    fixtures = [f.strip() for f in args.fixtures.split(",") if f.strip()]

    if not TSV.exists():
        TSV.write_text(TSV_HEADER)

    # Fixture-major so the Sonnet-gates-Haiku rule can fire per fixture:
    # Haiku is strictly weaker than Sonnet, so if Sonnet can't pass a fixture
    # (wrong verdict or timeout), Haiku won't either — skip it, don't pay for it.
    rows = []
    for fixture in fixtures:
        sonnet_passed = None  # None = sonnet not in this run for this fixture
        for model in models:
            if (model == "haiku" and "sonnet" in models
                    and sonnet_passed is False):
                print(f"\n=== haiku x {fixture} === SKIPPED "
                      "(sonnet did not pass; haiku is weaker)", flush=True)
                with open(TSV, "a") as fh:
                    fh.write("\t".join([str(date.today()), "haiku", fixture,
                             "-", "(skipped: sonnet failed)", "N",
                             "-", "-", "-", "SKIP", "-", "-", "-"]) + "\n")
                continue
            print(f"\n=== {model} x {fixture} ===", flush=True)
            r = run_one(model, fixture, args.timeout)
            if model == "sonnet":
                sonnet_passed = bool(r["result"] and r["result"]["passed"])
            row = fmt_row(r)
            with open(TSV, "a") as fh:
                fh.write(row + "\n")
            rows.append(r)
            print(f"  status={r['status']} verdict_match="
                  f"{'Y' if r['verdict_match'] else 'N'} "
                  f"got={r['got']} cost=${r['cost_usd']} "
                  f"dur={r['duration_s']}s record={r['record'] or 'NONE'}",
                  flush=True)

    print("\n\n===== SUMMARY =====")
    print(TSV_HEADER.strip())
    for r in rows:
        print(fmt_row(r))


if __name__ == "__main__":
    main()
