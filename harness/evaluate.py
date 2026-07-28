#!/usr/bin/env python3
"""Run the BYO harness on benchmark fixtures and score against sealed truth.

This is the harness analog of `benchmarks/model_compare.py` (which exercises the
`/verify-full-process` skill). It drives the full harness path — `run_verification` +
`launch_agent` + the trusted gates — on each fixture, then scores the resulting
run record with the deterministic `benchmarks/score.py`. Output: a per-fixture
PASS/FAIL table plus the verdict each fixture reached vs expected.

Usage:
    python3 harness/evaluate.py fix1 fix2 ...    # specific fixtures
    python3 harness/evaluate.py --all            # every benchmark fixture
"""
from __future__ import annotations

import argparse
import glob
import json
import os
import re
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from harness.runner import run_verification, launch_agent, AgentBudgetExceeded
from harness.backends import get_backend
from benchmarks.score import score

BENCH = ROOT / "benchmarks"


def split_statement_proof(md: str) -> tuple[str, str]:
    """Split a fixture statement.md into (statement+context, proof). The proof
    is the `## Proof` section; everything before it is the claim + setting."""
    m = re.search(r"^##\s+Proof\b", md, re.MULTILINE)
    if not m:
        return md, ""
    return md[:m.start()].strip(), md[m.start():].strip()


def newest_record(runs_dir: str, fixture: str) -> dict | None:
    hits = sorted(glob.glob(os.path.join(runs_dir, f"{fixture}_*.json")))
    return json.loads(Path(hits[-1]).read_text()) if hits else None


def _model_for_backend(backend: str, model: str) -> str | None:
    if backend != "claude" and model == "opus":
        return None
    return model


def _effort_for_backend(backend: str, reasoning_effort: str | None) -> str | None:
    return reasoning_effort if backend == "codex" else None


def evaluate_one(fixture: str, *, backend: str, model: str | None,
                 reasoning_effort: str | None, budget: int) -> dict:
    fx = BENCH / fixture
    md = (fx / "statement.md").read_text()
    expected = json.loads((fx / "sealed" / "expected.json").read_text())
    statement, proof = split_statement_proof(md)

    t0 = time.time()
    out = run_verification(
        f"eval_{fixture}", statement, proof,
        call_model=get_backend(backend, model=model,
                               reasoning_effort=reasoning_effort),
        agent_drive=launch_agent(backend, model=model, timeout=budget,
                                  reasoning_effort=reasoning_effort),
        nl_claim=statement,
    )
    dur = time.time() - t0

    runs_dir = os.path.join(os.path.dirname(out["corpus"]), "runs")
    rec = newest_record(runs_dir, f"eval_{fixture}")
    if rec is None:
        return {"fixture": fixture, "status": "no record",
                "verdict_line": out["verdict_line"], "dur": dur, "result": None}
    res = score(expected, rec)
    want = expected.get("verdict_class_any") or [expected["verdict_class"]]
    return {"fixture": fixture, "status": "ok", "dur": dur,
            "expected": "|".join(want),
            "got": res["effective_verdict"],
            "verdict_match": res["effective_verdict"] in want,
            "detection": res["detection_rate"],
            "kernel_backed": res["kernel_backed_fraction"],
            "kb_refutations": res.get("kernel_backed_refutations", 0),
            "passed": res["passed"],
            "checks": res["checks"]}


def main() -> None:
    parser = argparse.ArgumentParser(description="Run harness benchmark evaluation")
    parser.add_argument("fixtures", nargs="*", help="benchmark fixture names")
    parser.add_argument("--all", action="store_true",
                        help="run every benchmark fixture")
    parser.add_argument("--backend", default=os.environ.get("HARNESS_BACKEND", "claude"),
                        help="agent backend (default: HARNESS_BACKEND or claude)")
    parser.add_argument("--model", default="opus",
                        help="model (default: opus for claude; codex default when omitted)")
    parser.add_argument("--reasoning-effort", choices=["low", "medium", "high", "xhigh"],
                        help="Codex model reasoning effort")
    parser.add_argument("--budget", type=int, default=600,
                        help="seconds for each driving-agent run (default: 600)")
    args = parser.parse_args()
    # This sweep owns its OWN rate-limit retry loop (below), so disable the
    # runner's inner per-launch retry to avoid COMPOUNDING (3 outer × 3 inner =
    # 9 launches + 3 gate re-spends on a persistent 429). setdefault so an
    # explicit env still wins.
    os.environ.setdefault("RLVERIFY_AGENT_RETRIES", "0")
    if args.all:
        fixtures = sorted(d.name for d in BENCH.iterdir()
                          if (d / "statement.md").exists())
    else:
        fixtures = args.fixtures
    model = _model_for_backend(args.backend, args.model)
    reasoning_effort = _effort_for_backend(args.backend, args.reasoning_effort)
    if not fixtures:
        parser.print_usage()
        return

    rows = []
    from harness.runner import RateLimited
    pause = float(os.environ.get("RLVERIFY_EVAL_PAUSE", "20"))  # courtesy gap between fixtures
    consec_fail = 0
    for i, fx in enumerate(fixtures):
        print(f"\n=== {fx} ===", flush=True)
        # Circuit-breaker: after 2 consecutive launch failures (e.g. a hard 403 /
        # outage), stop the sweep instead of grinding ~200s/fixture through all of
        # them. A success resets the counter.
        if consec_fail >= 2:
            r = {"fixture": fx, "status": "skipped (circuit-breaker: 2 consecutive "
                 "launch failures — fix auth/plan then re-run)", "result": None}
            rows.append(r); print(f"  {r['status']}", flush=True); continue
        if i > 0 and pause > 0:
            time.sleep(pause)  # avoid tripping rate limits on back-to-back heavy runs
        r = None
        for attempt in range(3):                     # retry-with-backoff on TRANSIENT rate-limit only
            try:
                r = evaluate_one(
                    fx, backend=args.backend, model=model,
                    reasoning_effort=reasoning_effort, budget=args.budget,
                )
                break
            except RateLimited as e:
                wait = 60 * (attempt + 1)
                print(f"  rate-limited (attempt {attempt+1}/3) — backing off {wait}s",
                      flush=True)
                if attempt < 2:
                    time.sleep(wait)
                else:
                    r = {"fixture": fx, "status": "rate-limited (gave up after 3 retries)",
                         "result": None}
            except AgentBudgetExceeded:
                # the build axis can exhaust the pinned 10-min agent budget on a
                # hard multi-lemma proof — report it cleanly, not as a dumped prompt.
                r = {"fixture": fx, "status": "timed out (agent budget exhausted — "
                     "proof too hard to complete in time)", "result": None}
                break
            except Exception as e:
                # a hard failure (403 plan/permission, auth, crash) — do NOT retry;
                # keep the status short (one line, no dumped prompt in the table).
                r = {"fixture": fx, "status": f"error: {str(e).splitlines()[0][:120]}",
                     "result": None}
                break
        consec_fail = 0 if (r and r.get("status") == "ok") else consec_fail + 1
        rows.append(r)
        if r["status"] == "ok":
            print(f"  expected={r['expected']} got={r['got']} "
                  f"match={'Y' if r['verdict_match'] else 'N'} "
                  f"detect={r['detection'][0]}/{r['detection'][1]} "
                  f"kb={r['kernel_backed'][0]}+{r['kb_refutations']}r "
                  f"{'PASS' if r['passed'] else 'FAIL'} ({r['dur']:.0f}s)", flush=True)
            for n, ok, d in r["checks"]:
                if not ok:
                    print(f"    FAIL {n}: {d}", flush=True)
        else:
            print(f"  {r['status']}", flush=True)

    print("\n\n===== HARNESS EVALUATION SUMMARY =====")
    print(f"{'fixture':<38} {'verdict':<8} {'detect':<7} {'overall'}")
    npass = 0
    for r in rows:
        if r["status"] != "ok":
            print(f"{r['fixture']:<38} {r['status']}"); continue
        npass += r["passed"]
        vm = "✓" if r["verdict_match"] else "✗"
        det = f"{r['detection'][0]}/{r['detection'][1]}"
        print(f"{r['fixture']:<38} {vm:<8} {det:<7} "
              f"{'PASS' if r['passed'] else 'FAIL'}")
    ok_runs = [r for r in rows if r['status'] == 'ok']
    vmatch = sum(1 for r in ok_runs if r['verdict_match'])
    print(f"\nverdict-match: {vmatch}/{len(ok_runs)} | full-PASS: {npass}/{len(ok_runs)}")


if __name__ == "__main__":
    main()
