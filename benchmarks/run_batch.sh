#!/bin/bash
# Headless batch runner: one /verifyRL invocation per fixture, SEQUENTIAL
# (add_novel corpus appends and lake builds race — never parallelize).
#
# Usage: bash benchmarks/run_batch.sh [fixture ...]
# Default: all fixtures. Requires the `claude` CLI.
#
# Each run gets a frozen corpus snapshot (see README protocol). The agent
# receives the statement CONTENT inline — never the fixture path.
set -euo pipefail
cd "$(dirname "$0")/.."

FIXTURES=("$@")
if [ ${#FIXTURES[@]} -eq 0 ]; then
    FIXTURES=()
    for d in benchmarks/*/; do
        [ -f "$d/statement.md" ] && FIXTURES+=("$(basename "$d")")
    done
fi

for f in "${FIXTURES[@]}"; do
    echo "=== fixture: $f ==="
    snapshot="$(mktemp /tmp/corpus_snapshot_XXXX.jsonl)"
    cp rlverify/corpus.jsonl "$snapshot"
    prompt="/verifyRL Use VerifyDriver(corpus_path=\"$snapshot\") for this run (frozen-corpus benchmark protocol; do not add lemmas to the real library). Session name: ${f}_bench. Verify the following theorem and proof:

$(cat "benchmarks/$f/statement.md")"
    claude -p "$prompt" --permission-mode acceptEdits || {
        echo "!! run failed for $f — continuing"; continue; }
    record="$(ls -t runs/${f}_bench_*.json 2>/dev/null | head -1 || true)"
    if [ -n "$record" ]; then
        python3 benchmarks/score.py "benchmarks/$f" "$record" --tsv || true
    else
        echo "!! no run record found for $f"
    fi
done
echo "=== batch done; see benchmarks/results.tsv ==="
