"""W1 — gate enforcement for untrusted/harness sessions (ADDITIVE).

Problem (from the design review): the driver's verdict comes from the kernel
(`effective_verdict`), which correctly prevents a *false* VERIFIED — but it does
NOT require that the flaw-hunting gates (sealed triage, falsification, sealed
back-translation) actually ran. The driver *computes* gate-coverage warnings in
`finish()` (`audit_warnings`) but they are advisory: a VERIFIED stands even with
every gate skipped. When an UNTRUSTED agent drives the pipeline, that is the
whole exposure — the kernel keeps the agent honest about *what compiled*, this
layer keeps it honest about *what was checked*.

This module is the enforcement the review said must exist. It is ADDITIVE: it
does not modify `driver.py`. It re-derives the verdict from a run record and,
in strict mode, DOWNGRADES a VERIFIED-class verdict to `UNVERIFIED/UNGATED`
when required gates are missing. It reuses `effective_verdict` from the scorer
rather than copying verdict logic a third time (the review flagged the existing
two-copy drift between driver and scorer — do not add a third).

Strict mode is intended ON for untrusted/harness sessions and OFF for trusted
local runs, so existing behaviour is unchanged. The cleaner long-term fix —
folding this into the driver so even the trusted path downgrades — touches the
frozen `driver.py` and needs owner approval (tracked in HARNESS_IMPLEMENTATION
.md W1); this module is the additive interim that the W2 MCP server calls.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
# Delegate to the single verdict authority (W1) — this module is the harness/
# CLI entry point; the logic lives in one place so driver, scorer, MCP server
# and this CLI can never drift.
from rlverify.verdict import (  # noqa: E402  (reuse, don't copy)
    VERIFIED_CLASS, enforce, gate_failures, verdict_class as effective_verdict,
)

__all__ = ["VERIFIED_CLASS", "enforce", "gate_failures", "effective_verdict"]


def main() -> int:
    if len(sys.argv) < 2:
        print("usage: python -m harness.enforce <run_record.json> [--permissive]")
        return 2
    run = json.loads(Path(sys.argv[1]).read_text())
    strict = "--permissive" not in sys.argv
    res = enforce(run, strict=strict)
    print(f"base verdict   : {res['base_verdict']}")
    print(f"enforced       : {res['verdict']}"
          + ("  (DOWNGRADED)" if res["downgraded"] else ""))
    if res["gate_failures"]:
        print("gate failures  :")
        for f in res["gate_failures"]:
            print(f"  - {f}")
    else:
        print("gate failures  : none")
    return 0


if __name__ == "__main__":
    sys.exit(main())
