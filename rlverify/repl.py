"""Persistent Lean REPL session for fast proof iteration.

Wraps leanprover-community/repl (vendored at ``tools/repl``, tag v4.28.0,
matching this project's toolchain). One warmup command imports Mathlib +
RLGeneralization (~30-60 s); every later check reuses that cached
environment and returns in well under a second, versus ~13-16 s for a
fresh wide-import ``lake env lean`` compile.

Trust note: this is the ITERATION fast path only. Verdict-bearing gates
(library_search, pre-add_novel re-runs, kernel closure) still go through
``lean.verify_lean_code`` — a fresh compile per check — so nothing the
pipeline certifies depends on REPL state.

Protocol: one JSON object per request terminated by a blank line; the
REPL answers with a pretty-printed JSON object terminated by a blank
line. ``{"cmd": ..., "env": N}`` re-enters the environment produced by
command N.
"""

from __future__ import annotations

import json
import subprocess
import threading
import time

from .lean import LeanResult, ROOT

REPL_BIN = ROOT / "tools" / "repl" / ".lake" / "build" / "bin" / "repl"

DEFAULT_IMPORTS = (
    "import Mathlib\nimport RLGeneralization\nopen Finset BigOperators Real"
)

WARMUP_TIMEOUT = 300
CHECK_TIMEOUT = 120


class ReplError(RuntimeError):
    """REPL process failed to start, died, or timed out."""


class ReplSession:
    """A long-lived Lean REPL with a pre-imported environment.

    >>> s = ReplSession()          # lazy: nothing spawned yet
    >>> s.check("example : 1 + 1 = 2 := by norm_num").success
    True

    The first ``check`` pays the warmup; later ones are sub-second.
    A dead process is restarted transparently on the next call.
    """

    def __init__(self, imports: str = DEFAULT_IMPORTS):
        self._imports = imports
        self._proc: subprocess.Popen | None = None
        self._base_env: int | None = None
        self._lock = threading.Lock()

    # ----- lifecycle -----

    def _alive(self) -> bool:
        return self._proc is not None and self._proc.poll() is None

    def _start(self) -> None:
        if not REPL_BIN.exists():
            raise ReplError(
                f"REPL binary not found at {REPL_BIN}. Build it with: "
                f"cd tools/repl && lake build"
            )
        self._proc = subprocess.Popen(
            ["lake", "env", str(REPL_BIN)],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            text=True,
            cwd=str(ROOT),
        )
        resp = self._roundtrip({"cmd": self._imports}, timeout=WARMUP_TIMEOUT)
        errors = [m for m in resp.get("messages", [])
                  if m.get("severity") == "error"]
        if errors or "env" not in resp:
            self.close()
            raise ReplError(f"REPL warmup failed: {errors or resp}")
        self._base_env = resp["env"]

    def close(self) -> None:
        if self._proc is not None:
            self._proc.kill()
            self._proc = None
        self._base_env = None

    # ----- protocol -----

    def _roundtrip(self, obj: dict, timeout: float) -> dict:
        """Send one JSON request, read the blank-line-terminated reply."""
        proc = self._proc
        assert proc is not None and proc.stdin and proc.stdout
        proc.stdin.write(json.dumps(obj, ensure_ascii=False) + "\n\n")
        proc.stdin.flush()

        lines: list[str] = []
        done = threading.Event()
        failure: list[BaseException] = []

        def read() -> None:
            try:
                while True:
                    line = proc.stdout.readline()
                    if line == "":  # EOF: process died
                        raise ReplError("REPL process exited unexpectedly")
                    if line.strip() == "" and lines:
                        return
                    if line.strip():
                        lines.append(line)
            except BaseException as e:  # noqa: BLE001 — relayed to caller
                failure.append(e)
            finally:
                done.set()

        t = threading.Thread(target=read, daemon=True)
        t.start()
        if not done.wait(timeout):
            self.close()
            raise ReplError(f"REPL timed out after {timeout}s")
        if failure:
            self.close()
            raise ReplError(str(failure[0]))
        try:
            return json.loads("".join(lines))
        except json.JSONDecodeError as e:
            self.close()
            raise ReplError(f"unparseable REPL reply: {e}") from e

    # ----- public API -----

    def check(self, code: str, allow_sorry: bool = False,
              timeout: float = CHECK_TIMEOUT) -> LeanResult:
        """Check ``code`` against the warm environment.

        Returns a ``LeanResult`` shaped like ``verify_lean_code``'s, so
        call sites can swap between the two paths freely.
        """
        with self._lock:
            start = time.monotonic()
            if not self._alive():
                self._start()
            resp = self._roundtrip(
                {"cmd": code, "env": self._base_env}, timeout=timeout)
            elapsed = time.monotonic() - start

        messages = resp.get("messages", [])
        errors = [m for m in messages if m.get("severity") == "error"]
        has_sorry = bool(resp.get("sorries")) or any(
            "declaration uses 'sorry'" in m.get("data", "")
            or "declaration uses `sorry`" in m.get("data", "")
            for m in messages)
        rendered = "\n".join(
            f"{m.get('severity')}: line {m.get('pos', {}).get('line')}: "
            f"{m.get('data', '')}"
            for m in messages)

        if errors:
            error_text = "\n".join(m.get("data", "") for m in errors)
            return LeanResult(
                success=False,
                errors=error_text[:3000],
                goals=[m["data"].split("unsolved goals", 1)[1].strip()
                       for m in errors
                       if "unsolved goals" in m.get("data", "")],
                elapsed=elapsed,
                has_sorry=has_sorry,
                output=rendered[:6000],
            )
        if has_sorry:
            return LeanResult(
                success=allow_sorry,
                errors="" if allow_sorry else "has sorry",
                elapsed=elapsed,
                has_sorry=True,
                output=rendered[:6000],
            )
        return LeanResult(success=True, elapsed=elapsed,
                          output=rendered[:6000])
