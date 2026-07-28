"""Append-only phase telemetry for resumable verification runs."""
from __future__ import annotations

import json
import os
import tempfile
import time
from contextlib import contextmanager
from pathlib import Path
from typing import Any


SCHEMA_VERSION = 2
FILENAME = "phase_telemetry.json"


@contextmanager
def _telemetry_lock(run_dir: str | Path):
    """Serialize cross-process telemetry writers for one run."""
    import fcntl

    directory = Path(run_dir)
    directory.mkdir(parents=True, exist_ok=True)
    lock_path = directory / ".phase_telemetry.lock"
    with lock_path.open("a+") as handle:
        fcntl.flock(handle.fileno(), fcntl.LOCK_EX)
        try:
            yield
        finally:
            fcntl.flock(handle.fileno(), fcntl.LOCK_UN)


def _atomic_write(path: Path, data: dict[str, Any]) -> None:
    """Durably replace telemetry without shared-temp collisions."""
    fd, raw_path = tempfile.mkstemp(
        prefix=".phase_telemetry.", suffix=".tmp", dir=str(path.parent)
    )
    tmp_path = Path(raw_path)
    try:
        with os.fdopen(fd, "w") as handle:
            json.dump(data, handle, indent=2)
            handle.write("\n")
            handle.flush()
            os.fsync(handle.fileno())
        tmp_path.replace(path)
    finally:
        tmp_path.unlink(missing_ok=True)


def load_phase_telemetry(run_dir: str | Path) -> dict[str, Any]:
    path = Path(run_dir) / FILENAME
    try:
        data = json.loads(path.read_text())
    except (OSError, ValueError, TypeError):
        data = {}
    phases = data.get("phases") if isinstance(data, dict) else None
    return {
        "schema_version": SCHEMA_VERSION,
        "phases": phases if isinstance(phases, list) else [],
    }


def append_phase(
    run_dir: str | Path,
    phase: str,
    *,
    status: str,
    wall_s: float,
    model_calls: int = 0,
    cost_usd: float | None = None,
    discoveries: list[dict] | None = None,
    detail: str = "",
    evidence: str = "NONE",
    blocks: list[str] | None = None,
    artifacts: dict[str, str] | None = None,
    producer: str = "harness",
) -> dict[str, Any]:
    """Append one execution event and derive incremental discoveries.

    A discovery is identified by its stable ``key``. Repeated/cached phases may
    report the same finding, but only its first appearance is incremental.
    """
    with _telemetry_lock(run_dir):
        data = load_phase_telemetry(run_dir)
        prior_keys = {
            str(item.get("key"))
            for event in data["phases"]
            for item in (event.get("discoveries") or [])
            if isinstance(item, dict) and item.get("key")
        }
        normalized: list[dict] = []
        for item in discoveries or []:
            if not isinstance(item, dict):
                continue
            row = dict(item)
            key = str(row.get("key") or "")
            row["incremental"] = bool(key and key not in prior_keys)
            if key:
                prior_keys.add(key)
            normalized.append(row)
        event = {
            "sequence": len(data["phases"]) + 1,
            "phase": phase,
            "status": status,
            "wall_s": round(max(0.0, float(wall_s)), 6),
            "model_calls": max(0, int(model_calls)),
            "cost_usd": cost_usd,
            "discoveries": normalized,
            "incremental_discoveries": sum(
                1 for row in normalized if row.get("incremental")
            ),
            "detail": detail,
            "evidence": str(evidence or "NONE"),
            "blocks": list(dict.fromkeys(str(item) for item in (blocks or []))),
            "artifacts": {
                str(key): str(value) for key, value in (artifacts or {}).items()
            },
            "producer": str(producer or "harness"),
            "recorded_at_unix": time.time(),
        }
        data["phases"].append(event)
        _atomic_write(Path(run_dir) / FILENAME, data)
    return event


def events_after(
    run_dir: str | Path,
    sequence: int = 0,
) -> dict[str, Any]:
    """Return durable phase events after ``sequence`` for polling clients."""
    data = load_phase_telemetry(run_dir)
    events = [
        event for event in data["phases"]
        if isinstance(event, dict)
        and int(event.get("sequence") or 0) > max(0, int(sequence))
    ]
    return {
        "schema_version": SCHEMA_VERSION,
        "after_sequence": max(0, int(sequence)),
        "next_sequence": max(
            [max(0, int(sequence))]
            + [int(event.get("sequence") or 0) for event in events]
        ),
        "events": events,
    }


def append_phase_once(
    run_dir: str | Path,
    phase: str,
    *,
    status: str,
    detail: str,
    evidence: str = "NONE",
) -> dict[str, Any] | None:
    """Record a zero-cost deferred/skipped state once across resumptions."""
    # The duplicate check and append are one transaction.  Calling
    # ``append_phase`` after an unlocked check lets concurrent resumptions both
    # observe absence and emit the same deferred event.
    with _telemetry_lock(run_dir):
        data = load_phase_telemetry(run_dir)
        if any(
            event.get("phase") == phase
            and event.get("status") == status
            and event.get("detail") == detail
            for event in data["phases"]
        ):
            return None
        event = {
            "sequence": len(data["phases"]) + 1,
            "phase": phase,
            "status": status,
            "wall_s": 0.0,
            "model_calls": 0,
            "cost_usd": None,
            "discoveries": [],
            "incremental_discoveries": 0,
            "detail": detail,
            "evidence": evidence,
            "blocks": [],
            "artifacts": {},
            "producer": "harness",
            "recorded_at_unix": time.time(),
        }
        data["phases"].append(event)
        _atomic_write(Path(run_dir) / FILENAME, data)
        return event


def discovery(
    kind: str,
    key: str,
    outcome: str,
    detail: str = "",
    *,
    evidence: str = "AUDIT",
) -> dict[str, str]:
    return {
        "kind": kind,
        "key": key,
        "outcome": outcome,
        "detail": detail,
        "evidence": evidence,
    }
