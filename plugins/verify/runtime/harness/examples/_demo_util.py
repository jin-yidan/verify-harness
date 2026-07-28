"""Demo-specific helpers: quiet the driver's logging, retry a stalled agent, and
save a certificate into examples/out/. The result panel (`print_result`,
`print_explanation`, `verdict_class_of`) now lives in `harness/render.py` and is
re-exported here so existing demo imports keep working."""
from __future__ import annotations

import contextlib
import glob
import io
import os
import shutil
import sys

# Shared presentation (the single home; CLI imports the same module).
from harness.render import (  # noqa: F401  (re-exported for demos)
    _c, print_result, print_explanation, verdict_class_of, _load_record,
)

OUT_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "out")


@contextlib.contextmanager
def quiet(label: str = "verifying"):
    """Hide the driver's internal log lines during the run. DEMO_VERBOSE=1 shows
    everything (useful when you WANT to narrate the phases live)."""
    if os.environ.get("DEMO_VERBOSE"):
        yield
        return
    print(_c(f"  ⏳ {label} …", "2"), flush=True)
    buf = io.StringIO()
    try:
        with contextlib.redirect_stdout(buf):
            yield
    except Exception:
        sys.stdout.write(buf.getvalue())  # on error, surface what was hidden
        raise


# Verdict classes that mean "the agent did not reach a real verdict" — the run
# stalled (e.g. it guessed a non-existent import and never compiled). These are
# transient and safe to retry; a real VERIFIED / UNVERIFIED/* is terminal.
_TRANSIENT = {"HAS GAPS", "COMPILED", ""}


def run_with_retry(attempt, attempts: int = 2):
    """Call `attempt()` (which returns a run_verification dict), retrying ONLY
    while the verdict is a transient non-verdict (HAS GAPS / COMPILED — the live
    agent stalled, often on a bad import guess). A real VERIFIED or UNVERIFIED/*
    is terminal and never retried — failures are reported, not hidden."""
    out = None
    for i in range(attempts):
        out = attempt()
        cls = verdict_class_of(out)
        if cls not in _TRANSIENT:
            return out
        if i + 1 < attempts:
            print(_c(f"  ↻ agent stalled at '{cls}' (often a bad import guess) "
                     f"— retrying once…", "33"), flush=True)
    return out


def save_certificate(out: dict, quiet_mode: bool = True) -> str | None:
    """Copy the run's `.lean` (+ `.json`) out of the ephemeral temp dir into
    out/. Returns the saved `.lean` path (or None if the run produced none)."""
    fixture = out["fixture"]
    runs_dir = os.path.join(os.path.dirname(out["corpus"]), "runs")
    leans = sorted(glob.glob(os.path.join(runs_dir, f"{fixture}_20*.lean")))
    if not leans:
        return None
    os.makedirs(OUT_DIR, exist_ok=True)
    src = leans[-1]
    dst = os.path.join(OUT_DIR, os.path.basename(src))
    shutil.copy(src, dst)
    js = src[:-5] + ".json"
    if os.path.exists(js):
        shutil.copy(js, os.path.join(OUT_DIR, os.path.basename(js)))
    return os.path.relpath(dst)
