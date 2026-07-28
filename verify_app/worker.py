"""Durable subprocess worker for product-level Verify runs."""

from __future__ import annotations

import json
import os
import signal
import sys
import time
from pathlib import Path

from .mcp_server import run_workflow


def _terminate_worker(_signum, _frame) -> None:
    """Stop model backends even though they run in their own process groups.

    The product worker is deliberately detached so it survives connector
    reconnects.  The runner also gives Codex/Claude their own process groups for
    reliable timeout cleanup, which means killing only the worker's group is not
    sufficient.  This handler bridges those two durability boundaries.
    """
    from harness.runner import terminate_active_agents

    terminate_active_agents()
    time.sleep(0.25)
    terminate_active_agents(force=True)
    os._exit(128 + signal.SIGTERM)


def _atomic_json(path: Path, value: dict) -> None:
    tmp = path.with_suffix(".tmp")
    with tmp.open("w") as handle:
        json.dump(value, handle, indent=2, sort_keys=True)
        handle.write("\n")
        handle.flush()
        os.fsync(handle.fileno())
    tmp.replace(path)


def main() -> int:
    if len(sys.argv) != 2:
        return 2
    run_dir = Path(sys.argv[1]).resolve()
    request_path = run_dir / "request.json"
    if not run_dir.is_dir() or not request_path.is_file():
        return 2
    signal.signal(signal.SIGTERM, _terminate_worker)
    signal.signal(signal.SIGINT, _terminate_worker)
    try:
        request = json.loads(request_path.read_text())
        result = run_workflow(**request)
    except BaseException as exc:
        result = {
            "execution": "SYSTEM_ERROR",
            "mathematics": "UNKNOWN",
            "error": f"{type(exc).__name__}: {exc}",
        }
    _atomic_json(run_dir / "result.json", result)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
