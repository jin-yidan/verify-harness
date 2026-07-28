#!/usr/bin/env python3
"""W0 acceptance test (HARNESS_W0_SCOPE.md §5; hardened after review #1).

Proves the untrusted-Lean compile path is safe: malicious fixtures must be
BLOCKED (no host read/write/network/exec), a benign proof must still compile
identically to the unsandboxed path, and latency overhead must be bounded.

Review #1 (CRITICAL): the original test only planted secrets in $HOME, but the
profile denies non-home secrets too — so we now plant a secret OUTSIDE $HOME
(/etc/passwd, /tmp) and assert it never appears in the returned output. The
read channel is the primary threat, so it is tested both with the linter ON
(default API) and OFF (sandbox-alone, M6-read).

Exit 0 = all pass (GO). Non-zero = at least one failure.
"""
from __future__ import annotations

import os
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from rlverify.sandbox import safe_verify                # noqa: E402
from rlverify.lean import verify_lean_code              # noqa: E402
from rlverify.lint_untrusted import lint_untrusted      # noqa: E402

HOME = Path(os.path.expanduser("~"))
HOME_SECRET = HOME / ".rlverify_canary_secret"
OUT_SECRET = Path("/tmp/.rlverify_canary_outside")      # secret OUTSIDE $HOME
HOME_TEXT = "HOME-CANARY-9f3a"
OUT_TEXT = "OUTSIDE-CANARY-7k2"
# real sensitive paths that must be unreadable
SENSITIVE = ["/etc/passwd", "/Library/Keychains/System.keychain",
             "/private/var/log/system.log"]
# canary paths attacks try to CREATE (must never exist afterward)
CANARIES = {k: Path(p) for k, p in {
    "write": HOME / ".rlverify_canary_write",
    "exec":  HOME / ".rlverify_canary_exec",
    "init":  HOME / ".rlverify_canary_init",
    "net":   "/tmp/.rlverify_canary_net",   # outside home, so not redundant w/ M3
    "m6":    HOME / ".rlverify_canary_m6",
    "clang": "/tmp/.rlverify_canary_clang",
}.items()}

results: list[tuple[str, bool, str]] = []


def record(name: str, ok: bool, detail: str) -> None:
    results.append((name, ok, detail))
    print(f"  [{'✓' if ok else '✗'}] {name:30} {detail}")


def clean() -> None:
    for p in CANARIES.values():
        p.unlink(missing_ok=True)


def leaked(r, *texts) -> bool:
    blob = (r.output or "") + (r.errors or "")
    return any(t in blob for t in texts)


# --- Read channel (the primary threat) --------------------------------------

def m1_read_home_secret() -> None:
    r = safe_verify(f'#eval IO.FS.readFile "{HOME_SECRET}" >>= IO.println\n')
    record("M1 read $HOME secret", not leaked(r, HOME_TEXT) and not r.success,
           "home secret not leaked")


def m1b_read_outside_home() -> None:
    # CRITICAL test from review: secret OUTSIDE $HOME must also be unreadable.
    code = (f'#eval IO.FS.readFile "{OUT_SECRET}" >>= IO.println\n')
    r = safe_verify(code)
    record("M1b read /tmp secret", not leaked(r, OUT_TEXT) and not r.success,
           "non-home secret not leaked")


def m6_read_sandbox_alone() -> None:
    # LINTER OFF: the OS sandbox alone must hold the READ channel — the
    # load-bearing case (the linter is assumed bypassable).
    r = safe_verify(f'#eval IO.FS.readFile "{OUT_SECRET}" >>= IO.println\n', lint=False)
    record("M6 read sandbox-alone", not leaked(r, OUT_TEXT) and not r.success,
           "no leak w/o linter (sandbox held)")


def sensitive_reads() -> None:
    # each real sensitive path, sandbox-alone, must be unreadable
    all_blocked = True
    for path in SENSITIVE:
        r = safe_verify(f'#eval IO.FS.readFile "{path}" >>= fun s => IO.println (s.take 16)\n',
                        lint=False)
        if r.success or "permitted" not in (r.errors + r.output).lower():
            # tolerate "no such file" (path may not exist), fail only on a read
            if "no such file" not in (r.errors + r.output).lower():
                all_blocked = False
    record("sensitive paths blocked", all_blocked, " ".join(SENSITIVE))


# --- Write / exec / network -------------------------------------------------

def m3_write() -> None:
    safe_verify(f'#eval IO.FS.writeFile "{CANARIES["write"]}" "pwned"\n')
    record("M3 write outside scratch", not CANARIES["write"].exists(),
           "home write blocked")


def m4_spawn() -> None:
    safe_verify(f'#eval do let _ ← IO.Process.run '
                f'{{cmd := "/usr/bin/touch", args := #["{CANARIES["exec"]}"]}}; pure ()\n')
    record("M4 spawn host process", not CANARIES["exec"].exists(), "exec blocked")


def m2_network() -> None:
    # sandbox-alone exec of a shell that curls + drops a canary in /tmp
    safe_verify(f'#eval do let _ ← IO.Process.run '
                f'{{cmd := "/bin/sh", args := #["-c", "curl -s http://127.0.0.1:9/x; '
                f'touch {CANARIES["net"]}"]}}; pure ()\n', lint=False)
    record("M2 network/exec-exfil", not CANARIES["net"].exists(),
           "shell/curl exec blocked (canary absent)")


def m5_import_initialize() -> None:
    safe_verify(f'import Lean\n'
                f'initialize : Unit ← IO.FS.writeFile "{CANARIES["init"]}" "x"\n')
    record("M5 import Lean+initialize", not CANARIES["init"].exists(), "blocked")


def m7_clang_exec() -> None:
    # HIGH-1 regression: the bundled clang must NOT be spawnable.
    import shutil as _sh
    lean_bin = (__import__("rlverify.sandbox", fromlist=["_lean_bin"])._lean_bin())
    clang = str(Path(lean_bin).parent / "clang")
    if not Path(clang).exists():
        record("M7 clang exec blocked", True, "(no clang in toolchain — n/a)")
        return
    r = safe_verify(f'#eval do let _ ← IO.Process.run '
                    f'{{cmd := "{clang}", args := #["-o", "{CANARIES["clang"]}", "/dev/null"]}}; '
                    f'pure ()\n', lint=False)
    record("M7 clang exec blocked", not CANARIES["clang"].exists(),
           "bundled clang not spawnable")


# --- Linter unit checks (defense-in-depth surface) --------------------------

def linter_checks() -> None:
    cases = ["#eval IO.println 1", "run_tac IO.println 1", "run_cmd pure ()",
             "import Lean", "initialize x : Nat := pure 1", "import System.IO"]
    rejected = [c for c in cases if not lint_untrusted(c).ok]
    record("linter rejects IO vectors", len(rejected) == len(cases),
           f"{len(rejected)}/{len(cases)} rejected")


# --- Benign parity + latency ------------------------------------------------

BENIGN_OK = "import Mathlib.Tactic\nexample : 1 + 1 = 2 := by norm_num\n"
BENIGN_BAD = "import Mathlib.Tactic\nexample : 1 + 1 = 3 := by norm_num\n"


def benign_parity() -> None:
    record("benign not lint-rejected", lint_untrusted(BENIGN_OK).ok, "")
    s = safe_verify(BENIGN_OK); u = verify_lean_code(BENIGN_OK)
    record("benign-true parity", s.success and u.success, f"sbx={s.success} plain={u.success}")
    sb = safe_verify(BENIGN_BAD); ub = verify_lean_code(BENIGN_BAD)
    record("benign-false parity", (not sb.success) and (not ub.success),
           f"sbx={sb.success} plain={ub.success}")


def latency() -> None:
    t = time.monotonic(); safe_verify(BENIGN_OK); s = time.monotonic() - t
    t = time.monotonic(); verify_lean_code(BENIGN_OK); u = time.monotonic() - t
    ratio = s / u if u else 0
    record("latency ≤ 1.5x", ratio <= 1.5, f"sbx={s:.1f}s plain={u:.1f}s ratio={ratio:.2f}x")


def main() -> int:
    print("W0 ACCEPTANCE — safe compilation of untrusted Lean (hardened)\n")
    HOME_SECRET.write_text(HOME_TEXT)
    OUT_SECRET.write_text(OUT_TEXT)
    clean()
    try:
        print("Read channel (primary threat):")
        for fn in (m1_read_home_secret, m1b_read_outside_home,
                   m6_read_sandbox_alone, sensitive_reads):
            _safe(fn)
        print("\nWrite / exec / network:")
        for fn in (m3_write, m4_spawn, m2_network, m5_import_initialize, m7_clang_exec):
            _safe(fn)
        print("\nLinter + benign parity + latency:")
        linter_checks(); benign_parity(); latency()
    finally:
        HOME_SECRET.unlink(missing_ok=True)
        OUT_SECRET.unlink(missing_ok=True)
        clean()

    passed = sum(1 for _, ok, _ in results if ok)
    total = len(results)
    print(f"\n{'='*52}\nRESULT: {passed}/{total} checks passed")
    print(f"W0 verdict: {'GO' if passed == total else 'NO-GO / INVESTIGATE'}")
    return 0 if passed == total else 1


def _safe(fn) -> None:
    try:
        fn()
    except Exception as e:
        record(fn.__name__, False, f"EXCEPTION {e!r}")


if __name__ == "__main__":
    sys.exit(main())
