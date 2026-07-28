"""Confined compilation of untrusted Lean (W0, primary security control).

The threat: Lean executes arbitrary ``IO`` at *elaboration* time (``#eval``,
``run_cmd``, ``initialize``, custom ``elab``/``macro``), as the harness user,
and the compile output is returned to the agent — so compiling untrusted Lean
is "run untrusted code with a data-return channel". The static linter
(``rlverify.lint_untrusted``) reduces surface but is evadable; THIS module is
the boundary we rely on.

Mechanism (macOS spike): run ``lean`` directly (no ``lake``/git) with a
captured ``LEAN_PATH`` under a deny-default ``sandbox-exec`` profile that:
  * denies network entirely;
  * allows process-exec ONLY of the toolchain (blocks spawning curl/rm/…);
  * allows file reads of the toolchain, the project build (``.lake``), and
    system dirs, but NOT the user's home (so ~/.ssh, ~/.aws, … are unreadable);
  * allows file writes ONLY to a per-call scratch dir outside the repo.

Returns the same ``LeanResult`` / ``AxiomClosure`` shapes as ``rlverify.lean``,
so callers are drop-in. Fail-closed: if ``sandbox-exec`` is unavailable we
raise rather than run unconfined.

This is the macOS spike path (HARNESS_W0_SCOPE.md §3). The Linux/hosted target
uses a container with the same policy; ``run_confined`` is the seam to swap.
"""

from __future__ import annotations

import os
import platform
import re
import resource
import shutil
import signal
import subprocess
import tempfile
import threading
import time
import uuid
from pathlib import Path

from .lean import (
    LeanResult, AxiomClosure, ROOT,
    _extract_goal_blocks, _sorry_warning_lines,
    _parse_axiom_closure, _classify_closure,
)
from .lint_untrusted import lint_untrusted
from .repl import ReplSession, ReplError, REPL_BIN, DEFAULT_IMPORTS, WARMUP_TIMEOUT

HOME = Path(os.path.expanduser("~"))
ELAN = HOME / ".elan"
LAKE_BUILD = ROOT / ".lake"
SANDBOX_EXEC = "/usr/bin/sandbox-exec"

_LEAN_ENV: dict[str, str] | None = None


class SandboxUnavailable(RuntimeError):
    """Raised when the OS sandbox cannot be set up — callers must fail closed."""


def _find_lake() -> str:
    """Locate the ``lake`` binary even when it is not on PATH (the agent's
    spawned MCP-server subprocess gets a minimal PATH). Falls back to the elan
    toolchain dir, same layout used for ``lean``."""
    cand = shutil.which("lake")
    if cand:
        return cand
    tcs = sorted((ELAN / "toolchains").glob("*/bin/lake"))
    return str(tcs[-1]) if tcs else "lake"


def _lean_env() -> dict[str, str]:
    """Capture LEAN_PATH once; cache it. Running ``lean`` directly with this env
    avoids invoking ``lake``/git inside the sandbox.

    Resolution order, robust to a minimal-PATH subprocess (the live agent run
    spawned the MCP server without ``lake`` on PATH):
      1. an explicit ``LEAN_PATH`` in the environment (the runner pre-injects it
         via the MCP-server config) — no ``lake`` call needed;
      2. ``lake env printenv LEAN_PATH``, resolving ``lake`` from the elan dir
         when it is not on PATH.
    """
    global _LEAN_ENV
    if _LEAN_ENV is None:
        lean_path = os.environ.get("LEAN_PATH", "").strip()
        if not lean_path:
            try:
                out = subprocess.run(
                    [_find_lake(), "env", "printenv", "LEAN_PATH"],
                    cwd=str(ROOT), capture_output=True, text=True, timeout=120,
                )
                lean_path = out.stdout.strip()
            except (OSError, subprocess.SubprocessError):
                lean_path = ""
        if not lean_path:
            raise SandboxUnavailable(
                "could not capture LEAN_PATH (no LEAN_PATH in env and `lake env` "
                "unavailable) — pass LEAN_PATH via the MCP-server env")
        _LEAN_ENV = {"LEAN_PATH": lean_path}
    return dict(_LEAN_ENV)


def _is_shim(path: str) -> bool:
    """A path under ``~/.elan/bin`` is the elan SHIM, which writes elan settings
    on run → denied under the scratch-only write policy (reproduced live). The
    real toolchain binary under ``~/.elan/toolchains/.../bin`` writes nothing."""
    return f"{os.sep}.elan{os.sep}bin{os.sep}" in path


def _toolchain_bin_from_elan_dir() -> str:
    """Resolve the real toolchain binary by reading the elan layout directly —
    independent of the ``elan`` command being invocable.

    Needed because an agent's spawned MCP-server subprocess may not have ``elan``
    on PATH (so ``elan which lean`` fails) yet still finds the shim — and the
    shim cannot run under the sandbox. The project's ``lean-toolchain`` names the
    toolchain (``leanprover/lean4:v4.28.0`` → dir ``leanprover--lean4---v4.28.0``).
    """
    toolchains = ELAN / "toolchains"
    tc_file = ROOT / "lean-toolchain"
    if tc_file.exists():
        name = tc_file.read_text().strip().replace("/", "--").replace(":", "---")
        cand = toolchains / name / "bin" / "lean"
        if cand.exists():
            return str(cand)
    # fall back to any installed toolchain's lean
    hits = sorted(toolchains.glob("*/bin/lean"))
    if hits:
        return str(hits[-1])
    return ""


def _lean_bin() -> str:
    """Resolve the REAL toolchain lean binary, NEVER the elan shim.

    Order: ``elan which lean`` → direct elan-dir resolution (PATH-independent) →
    ``shutil.which`` (shim rejected). Execing the concrete toolchain binary
    keeps the confined tree minimal, HOME-agnostic, and free of the elan shim's
    settings-file write (which the scratch-only write policy denies).
    """
    try:
        out = subprocess.run(["elan", "which", "lean"], capture_output=True,
                             text=True, timeout=30)
        binp = out.stdout.strip()
    except (OSError, subprocess.SubprocessError):
        binp = ""
    if not binp or _is_shim(binp) or not os.path.exists(binp):
        binp = _toolchain_bin_from_elan_dir()
    if not binp or _is_shim(binp) or not os.path.exists(binp):
        cand = shutil.which("lean") or ""
        binp = cand if (cand and not _is_shim(cand)) else ""
    if not binp or not os.path.exists(binp) or _is_shim(binp):
        raise SandboxUnavailable(
            "could not resolve the real lean toolchain binary (only the elan "
            "shim was found, which cannot run under the sandbox)")
    return binp


# Secret-bearing trees OUTSIDE the user's home that must NOT be readable even
# though they are not under $HOME. A pure system allow-list would be cleaner,
# but the exact dyld-cache path set on this macOS (Darwin 25) could not be
# pinned down (the trace directive emitted nothing), and a missed path aborts
# lean at startup. So we read-allow non-home paths but deny every sensitive
# tree explicitly, and the acceptance test asserts each is unreadable. The
# Linux/container target (W0-hardening) uses a genuinely minimal FS where a
# strict allow-list is clean — see HARNESS_W0_SCOPE.md §7.
_SENSITIVE_DENY = [
    "/Users",                       # all users' homes (incl. other accounts)
    "/etc", "/private/etc",         # host config, ssh host keys, hosts
    "/tmp", "/private/tmp",         # other processes' temp material
    "/var/log", "/private/var/log", # system logs
    "/Library/Keychains",           # system keychain
    "/private/var/db/dslocal",      # local account password hashes
    "/private/var/root",            # root home
    "/Volumes", "/cores",
]


def _profile(scratch: Path, lean_bin: str) -> str:
    """Generate the sandbox-exec SBPL profile for one confined compile.

    Reads: non-home paths, MINUS every tree in ``_SENSITIVE_DENY``; then the
    toolchain (``~/.elan``) and project build (``.lake``) — both under home —
    are re-allowed (last-match-wins, so they override the ``/Users`` deny).
    Writes: only ``scratch``. Exec: ONLY the concrete ``lean`` binary (so the
    bundled clang/leanc/lake/ld cannot be spawned). Network: denied.
    """
    denies = "\n".join(f'(deny file-read* (subpath "{d}"))' for d in _SENSITIVE_DENY)
    # Public, non-secret config under the denied /etc tree that the toolchain
    # may read at startup (CA certs + openssl.cnf). Re-allowed AFTER the deny
    # (last-match-wins) — denying it broke compiles in the live agent run
    # (fopen openssl.cnf → Operation not permitted) at no security benefit.
    reallow = "\n".join(f'(allow file-read* (subpath "{p}"))' for p in
                        ("/etc/ssl", "/private/etc/ssl", "/usr/lib/ssl",
                         "/System/Library/OpenSSL"))
    return f"""(version 1)
(deny default)
(allow process-fork)
(allow process-exec (literal "{lean_bin}"))
(allow sysctl-read)
(allow mach-lookup)
(deny network*)
(allow file-read-metadata)
(allow file-read* (require-all (subpath "/") (require-not (subpath "{HOME}"))))
{denies}
{reallow}
(allow file-read* (subpath "{ELAN}"))
(allow file-read* (subpath "{LAKE_BUILD}"))
(allow file-read* (subpath "{scratch}"))
(allow file-write*
  (subpath "{scratch}")
  (literal "/dev/null") (literal "/dev/dtracehelper") (literal "/dev/tty"))
"""


def _child_setup(cpu_seconds: int) -> None:
    """Child-side: new session (for group-kill) + CPU cap.

    No RLIMIT_NPROC: it caps processes for the whole real-UID, so a small value
    breaks benign compiles on a busy dev box. Process *spawning* is already
    prevented by exec=literal-lean (clang/sh/curl cannot run), and the wall-clock
    timeout + process-group kill bound any runaway. Memory/pids caps are deferred
    to the container target (HARNESS_W0_SCOPE.md §7).
    """
    os.setsid()
    try:
        resource.setrlimit(resource.RLIMIT_CPU, (cpu_seconds, cpu_seconds + 2))
    except (ValueError, OSError):
        pass


# --------------------------------------------------------------------------
# Platform-dispatched confinement. macOS = sandbox-exec (VALIDATED, the original
# W0). Linux = bubblewrap (UNVALIDATED — no acceptance run on real Linux yet, so
# it is gated behind an explicit at-your-own-risk opt-in and NEVER claims the
# proven guarantee silently). See HARNESS_DESIGN.md §8 P2.
# --------------------------------------------------------------------------

def _require_confiner() -> None:
    """Fail-closed gate shared by every confined-exec seam. Raises
    SandboxUnavailable (never returns unconfined) unless a usable confiner for
    this platform is present AND, on Linux, the unvalidated path is explicitly
    acknowledged. The whole point is that an absent/unproven sandbox stops the
    run rather than silently degrading to unconfined compilation."""
    sysname = platform.system()
    if sysname == "Darwin":
        if not os.path.exists(SANDBOX_EXEC):
            raise SandboxUnavailable(f"{SANDBOX_EXEC} not present — refusing to "
                                     "run untrusted Lean unconfined")
        return
    if sysname == "Linux":
        # The bwrap port is UNVALIDATED: refuse to imply a guarantee it hasn't
        # earned. An operator who understands that can opt in; otherwise stop.
        if os.environ.get("RLVERIFY_LINUX_SANDBOX") != "1":
            raise SandboxUnavailable(
                "the Linux bubblewrap sandbox is UNVALIDATED (no acceptance run on "
                "real Linux yet — HARNESS_DESIGN.md §8 P2); refusing to imply an "
                "untrusted-code guarantee it has not earned. To use it AT YOUR OWN "
                "RISK set RLVERIFY_LINUX_SANDBOX=1, or run trusted-local with "
                "--no-sandbox (RLVERIFY_SANDBOX=0).")
        if not shutil.which("bwrap"):
            raise SandboxUnavailable("bwrap (bubblewrap) not found on PATH — "
                                     "install it, or run --no-sandbox (trusted-local)")
        return
    raise SandboxUnavailable(f"no W0 sandbox for platform {sysname!r} — run "
                             "--no-sandbox (trusted-local) on this OS")


def _bwrap_prefix(scratch: Path) -> list[str]:
    """Best-effort bubblewrap confinement mirroring the SBPL profile's INTENT:
    no network (`--unshare-all`), read-only system + Lean toolchain, the ONLY
    writable path is ``scratch``. UNVALIDATED — the read-bind set below is a
    faithful first cut from the macOS profile's allowed trees, but completeness
    (does Lean find every shared lib / Mathlib oleans?) and the assurance gap vs
    sandbox-exec (bwrap cannot pin exec to the literal `lean` binary the way SBPL
    does — mitigated by no-network + namespace isolation + the RLIMIT_CPU cap)
    must be confirmed by the Linux acceptance suite before this is trusted."""
    env = _lean_env()
    ro = ["/usr", "/bin", "/lib", "/lib64", "/etc", str(ELAN), str(ROOT)]
    for d in env.get("LEAN_PATH", "").split(os.pathsep):
        if d:
            ro.append(d)
    args = ["bwrap", "--unshare-all", "--die-with-parent", "--new-session",
            "--proc", "/proc", "--dev", "/dev", "--tmpfs", "/tmp"]
    seen = set()
    for p in ro:
        rp = os.path.realpath(p)
        if rp in seen or not os.path.exists(rp):
            continue
        seen.add(rp)
        args += ["--ro-bind", rp, rp]
    args += ["--bind", str(scratch), str(scratch)]
    return args


def _confine_prefix(scratch: Path, profile_path: Path) -> list[str]:
    """The argv PREFIX that confines the program following it. On macOS this is
    byte-identical to the original ``[sandbox-exec, -f, <profile>]`` (so the
    validated path is unchanged); on Linux it is the bwrap prefix."""
    if platform.system() == "Darwin":
        return [SANDBOX_EXEC, "-f", str(profile_path)]
    return _bwrap_prefix(scratch)


def run_confined(code: str, timeout: int) -> tuple[int, str, float]:
    """Compile ``code`` with ``lean`` under the sandbox. Returns (rc, output, secs).

    No linting, no parsing — the raw confined run. Used by ``safe_verify`` and
    the acceptance test (which calls it with the linter disabled to prove the
    sandbox alone contains an attack). On timeout the whole process group is
    killed so no confined grandchild survives.
    """
    _require_confiner()
    env = _lean_env()
    lean = _lean_bin()
    # realpath: on macOS /tmp → /private/tmp (and /tmp is in _SENSITIVE_DENY), so
    # the profile's scratch-allow must use the path Lean actually accesses, or
    # the deny wins and writes/reads in scratch are refused.
    scratch = Path(os.path.realpath(tempfile.mkdtemp(prefix="rlverify_sbx_")))
    try:
        src = scratch / f"check_{uuid.uuid4().hex[:12]}.lean"
        src.write_text(code)
        prof = scratch / "profile.sb"
        prof.write_text(_profile(scratch, lean))
        # Confine lean's own temp files to scratch; HOME points at scratch so
        # any $HOME read by untrusted code lands in the disposable dir.
        # ELAN_HOME/XDG_CACHE_HOME point lean/elan cache+lock writes into the
        # writable scratch (a live agent run hit a denied write creating
        # `.elan` outside scratch under bare HOME=scratch).
        elan_home = scratch / ".elan"
        elan_home.mkdir(exist_ok=True)
        run_env = {"LEAN_PATH": env["LEAN_PATH"], "TMPDIR": str(scratch),
                   "PATH": "/usr/bin:/bin", "HOME": str(scratch),
                   "ELAN_HOME": str(elan_home),
                   "XDG_CACHE_HOME": str(scratch / ".cache")}
        start = time.monotonic()
        proc = subprocess.Popen(
            [*_confine_prefix(scratch, prof), lean, str(src)],
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
            cwd=str(scratch), env=run_env,
            preexec_fn=lambda: _child_setup(timeout),
        )
        try:
            out, err = proc.communicate(timeout=timeout)
        except subprocess.TimeoutExpired:
            try:
                os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
            except (ProcessLookupError, PermissionError):
                proc.kill()
            proc.communicate()
            return (-1, "timeout", time.monotonic() - start)
        elapsed = time.monotonic() - start
        combined = ((out or "") + "\n" + (err or "")).strip()
        return (proc.returncode, combined, elapsed)
    finally:
        shutil.rmtree(scratch, ignore_errors=True)


def safe_verify(code: str, timeout: int = 120, allow_sorry: bool = False,
                lint: bool = True) -> LeanResult:
    """Confined drop-in for ``rlverify.lean.verify_lean_code``.

    With ``lint=True`` (default) the static linter runs first; a violation is a
    fast rejection (no compile). ``lint=False`` skips it — used only by the
    acceptance test's sandbox-alone cases.
    """
    if lint:
        verdict = lint_untrusted(code)
        if not verdict.ok:
            return LeanResult(success=False,
                              errors="blocked by linter: " + "; ".join(verdict.reasons),
                              output="; ".join(verdict.reasons))
    rc, combined, elapsed = run_confined(code, timeout)
    if combined == "timeout" and rc == -1:
        return LeanResult(success=False, errors="timeout", elapsed=elapsed)
    if rc == 0:
        has_sorry = ("declaration uses 'sorry'" in combined
                     or "declaration uses `sorry`" in combined)
        if has_sorry:
            return LeanResult(
                success=allow_sorry,
                errors="" if allow_sorry else "has sorry",
                elapsed=elapsed, has_sorry=True, output=combined[:6000],
                sorry_lines=_sorry_warning_lines(combined),
            )
        return LeanResult(success=True, elapsed=elapsed, output=combined[:6000])
    lines = [l for l in combined.splitlines()
             if "has local changes" not in l and "manifest out of date" not in l]
    cleaned = "\n".join(lines)
    return LeanResult(success=False, errors=cleaned[:3000],
                      goals=_extract_goal_blocks(cleaned), elapsed=elapsed,
                      output=cleaned[:6000])


def safe_check_closure(code: str, theorem_name: str, timeout: int = 120,
                       lint: bool = True) -> AxiomClosure:
    """Confined drop-in for ``rlverify.lean.check_axiom_closure``."""
    if lint:
        verdict = lint_untrusted(code)
        if not verdict.ok:
            error = "blocked by linter: " + "; ".join(verdict.reasons)
            return AxiomClosure(
                theorem=theorem_name, ok=False, error=error,
                compile_result=LeanResult(success=False, errors=error),
            )
    augmented = code.rstrip() + f"\n\n#print axioms {theorem_name}\n"
    rc, combined, elapsed = run_confined(augmented, timeout)
    if rc == -1 and combined == "timeout":
        return AxiomClosure(
            theorem=theorem_name, ok=False, error="timeout",
            compile_result=LeanResult(
                success=False, errors="timeout", elapsed=elapsed),
        )
    # Fail closed even when a later declaration emitted a parseable closure:
    # Lean can continue after an earlier error (for example an unknown
    # namespace), so closure text alone is not successful compilation.
    if rc != 0:
        lines = [
            line for line in combined.splitlines()
            if "has local changes" not in line
            and "manifest out of date" not in line
        ]
        error = "\n".join(lines)[-3000:] or f"Lean exited {rc}"
        compiled = LeanResult(
            success=False, errors=error, elapsed=elapsed,
            output=combined[:6000],
        )
        return AxiomClosure(
            theorem=theorem_name, ok=False, error=error,
            compile_result=compiled,
        )
    closure = _parse_axiom_closure(combined, theorem_name)
    if closure is None:
        error = combined[-1500:] or "no #print axioms output"
        return AxiomClosure(
            theorem=theorem_name, ok=False, error=error,
            compile_result=LeanResult(
                success=False, errors=error, elapsed=elapsed,
                output=combined[:6000],
            ),
        )
    classified = _classify_closure(theorem_name, closure)
    classified.compile_result = LeanResult(
        success=True, elapsed=elapsed, output=combined[:6000],
    )
    return classified


# ---------------------------------------------------------------------------
# Warm confined REPL — fast ITERATION path (compile/sketch/discharge).
# ---------------------------------------------------------------------------
#
# Every cold compile pays the full `import Mathlib` cost (~8 s) because the
# warm REPL is disabled in sandbox mode; an agent iterating a hard block hits
# that 8 s on every attempt, which is what blew past the wall clock in the live
# UCB run. This re-introduces the warm REPL but UNDER the sandbox, so iteration
# is sub-second while confinement is unchanged.
#
# TWO INVARIANTS keep this safe:
#   1. CONFINEMENT — the warm REPL runs `sandbox-exec -f <profile> <repl-bin>`
#      with the SAME deny-default policy as `run_confined` (network denied, HOME
#      denied, scratch-only writes), plus exec/read of the repl binary itself.
#   2. VERDICT INTEGRITY — the warm path backs only `verify_lean_code` (the
#      "does it elaborate" check). The verdict-bearing kernel closure
#      (`check_axiom_closure` → `safe_check_closure`) stays COLD/fresh, so
#      nothing the pipeline CERTIFIES depends on warm REPL state. A warm
#      compile that over-permits (the warm env always has FULL Mathlib, so it
#      may accept code whose narrow imports are insufficient) is caught by the
#      cold `assemble` closure — the agent wastes an iteration, never a verdict.
# The static linter still runs before any code reaches the warm REPL.


def _repl_profile(scratch: Path, repl_bin: str, lean_bin: str) -> str:
    """SBPL profile for the confined warm REPL — identical policy to ``_profile``
    except it ALSO execs the REPL binary and re-allows reading the repl project
    tree (the 151 MB binary lives under ``tools/repl``, i.e. under HOME, so the
    HOME deny would otherwise block exec).

    Exec allows BOTH ``repl_bin`` and ``lean_bin``: the leanprover/repl binary
    spawns a child ``lean`` to build the import environment, so without lean-exec
    the warmup dies and every check silently falls back to the cold path (the
    warm speedup is inert). The child ``lean`` inherits this same profile, so this
    is EXACT confinement parity with ``_profile`` (which execs lean directly) —
    nothing is weakened."""
    repl_dir = str(ROOT / "tools" / "repl")
    denies = "\n".join(f'(deny file-read* (subpath "{d}"))' for d in _SENSITIVE_DENY)
    reallow = "\n".join(f'(allow file-read* (subpath "{p}"))' for p in
                        ("/etc/ssl", "/private/etc/ssl", "/usr/lib/ssl",
                         "/System/Library/OpenSSL"))
    return f"""(version 1)
(deny default)
(allow process-fork)
(allow process-exec (literal "{repl_bin}"))
(allow process-exec (literal "{lean_bin}"))
(allow sysctl-read)
(allow mach-lookup)
(deny network*)
(allow file-read-metadata)
(allow file-read* (require-all (subpath "/") (require-not (subpath "{HOME}"))))
{denies}
{reallow}
(allow file-read* (subpath "{ELAN}"))
(allow file-read* (subpath "{LAKE_BUILD}"))
(allow file-read* (subpath "{repl_dir}"))
(allow file-read* (subpath "{scratch}"))
(allow file-write*
  (subpath "{scratch}")
  (literal "/dev/null") (literal "/dev/dtracehelper") (literal "/dev/tty"))
"""


class ConfinedReplSession(ReplSession):
    """A warm Lean REPL launched under ``sandbox-exec``. Reuses the parent's JSON
    protocol (``_roundtrip``/``check``) but starts the process confined."""

    def __init__(self, imports: str = DEFAULT_IMPORTS):
        # Do NOT call super().__init__: enable_sandbox blocks the UNCONFINED
        # ReplSession.__init__. Set the same attributes directly.
        self._imports = imports
        self._proc = None
        self._base_env = None
        self._lock = threading.Lock()
        self._scratch: Path | None = None

    def _start(self) -> None:
        _require_confiner()  # second confinement seam — fail-closed like run_confined
        if not REPL_BIN.exists():
            raise ReplError(
                f"REPL binary not found at {REPL_BIN} (build: cd tools/repl && lake build)")
        lean_path = _lean_env()["LEAN_PATH"]
        repl_bin = str(REPL_BIN)
        lean_bin = _lean_bin()  # the repl spawns child `lean`; it must be execable
        lean_dir = os.path.dirname(lean_bin)
        self._scratch = Path(os.path.realpath(tempfile.mkdtemp(prefix="rlverify_replsbx_")))
        elan_home = self._scratch / ".elan"
        elan_home.mkdir(exist_ok=True)
        prof = self._scratch / "profile.sb"
        prof.write_text(_repl_profile(self._scratch, repl_bin, lean_bin))
        # lean_dir on PATH so the repl can spawn `lean`; HOME/TMPDIR/caches all
        # point into the disposable scratch (same hardening as run_confined).
        run_env = {"LEAN_PATH": lean_path, "TMPDIR": str(self._scratch),
                   "PATH": f"{lean_dir}:/usr/bin:/bin", "HOME": str(self._scratch),
                   "ELAN_HOME": str(elan_home),
                   "XDG_CACHE_HOME": str(self._scratch / ".cache")}
        # setsid: the repl + any child `lean` form one process group we group-kill
        # in close() (a per-check timeout must not orphan a child compiler). No
        # RLIMIT_CPU: this is a LONG-LIVED process; a cumulative cap would kill
        # the session — the per-check wall-clock timeout + group-kill bound runaways.
        self._proc = subprocess.Popen(
            [*_confine_prefix(self._scratch, prof), repl_bin],
            stdin=subprocess.PIPE, stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL, text=True,
            cwd=str(self._scratch), env=run_env, preexec_fn=os.setsid,
        )
        resp = self._roundtrip({"cmd": self._imports}, timeout=WARMUP_TIMEOUT)
        errors = [m for m in resp.get("messages", [])
                  if m.get("severity") == "error"]
        if errors or "env" not in resp:
            self.close()
            raise ReplError(f"confined REPL warmup failed: {errors or resp}")
        self._base_env = resp["env"]

    def close(self) -> None:
        # Group-kill: the repl is the session leader (setsid); killing the group
        # also reaps any child `lean` so a timeout/close can't orphan a compiler.
        if self._proc is not None:
            try:
                os.killpg(os.getpgid(self._proc.pid), signal.SIGKILL)
            except (ProcessLookupError, PermissionError, OSError):
                self._proc.kill()
            self._proc = None
        self._base_env = None
        if self._scratch is not None:
            shutil.rmtree(self._scratch, ignore_errors=True)
            self._scratch = None


_warm_session: ConfinedReplSession | None = None
_warm_lock = threading.Lock()

# Leading `import …` lines are stripped before a warm check: the base env already
# imports full Mathlib + RLGeneralization, and the REPL rejects re-imports in a
# continued env. (`open`/`section`/the proof body are kept.) Because the warm env
# is the Mathlib SUPERSET, this can only make the warm check MORE permissive than
# the agent's narrow-import file — never a false VERIFIED, since assemble re-checks
# the real imports cold.
_IMPORT_LINE = re.compile(r"^[ \t]*import[ \t]+\S.*$", re.MULTILINE)


def _strip_imports(code: str) -> str:
    return _IMPORT_LINE.sub("", code)


def _get_warm_session() -> ConfinedReplSession:
    global _warm_session
    with _warm_lock:
        if _warm_session is None:
            _warm_session = ConfinedReplSession()
        return _warm_session


def shutdown_warm_session() -> None:
    """Tear down the warm REPL (process + scratch). Safe to call repeatedly."""
    global _warm_session
    with _warm_lock:
        if _warm_session is not None:
            _warm_session.close()
            _warm_session = None


def warm_safe_verify(code: str, timeout: int = 120, allow_sorry: bool = False,
                     lint: bool = True) -> LeanResult:
    """Confined warm-REPL drop-in for ``verify_lean_code`` (ITERATION only).

    Linter first (same as cold), then the warm confined REPL. On ANY REPL error
    (warmup failure, dead process, protocol error) fall back to the cold
    ``safe_verify`` so iteration degrades gracefully instead of breaking."""
    if lint:
        verdict = lint_untrusted(code)
        if not verdict.ok:
            return LeanResult(success=False,
                              errors="blocked by linter: " + "; ".join(verdict.reasons),
                              output="; ".join(verdict.reasons))
    try:
        sess = _get_warm_session()
        return sess.check(_strip_imports(code), allow_sorry=allow_sorry,
                          timeout=timeout)
    except ReplError:
        shutdown_warm_session()  # drop the broken session; next call re-warms
        return safe_verify(code, timeout=timeout, allow_sorry=allow_sorry,
                           lint=False)  # already linted above


def enable_sandbox() -> bool:
    """Route every REACHABLE driver compile through the W0 sandbox (W2 harness).

    The driver binds ``verify_lean_code`` / ``check_axiom_closure`` as module
    globals and reaches the warm REPL via ``VerifyDriver.repl_verify``. Untrusted
    agent code flows through all three, so all three are swapped for confined
    equivalents here — without editing the frozen ``driver.py``.

    Fail-closed: raises ``SandboxUnavailable`` if the OS sandbox is absent, so a
    harness can never silently fall back to unconfined compilation (W0 review
    LOW-2). Idempotent.
    """
    _require_confiner()  # platform-dispatched, fail-closed (macOS sandbox-exec /
                         # Linux bwrap-with-opt-in); never falls back to unconfined
    from . import driver as _driver
    # ITERATION compiles (compile/sketch/discharge) → warm confined REPL
    # (sub-second). CERTIFICATION (kernel closure) stays COLD/fresh, so no
    # verdict depends on warm REPL state — see warm_safe_verify's invariants.
    _driver.verify_lean_code = warm_safe_verify
    _driver.check_axiom_closure = safe_check_closure  # COLD — verdict-bearing

    def _confined_repl(self, code, allow_sorry=False, quiet=False):
        # The driver's own warm path (#check @ident) → confined warm REPL.
        return warm_safe_verify(code, allow_sorry=allow_sorry)

    _driver.VerifyDriver.repl_verify = _confined_repl

    # Defense-in-depth: the driver still contains UNCONFINED lean/lake calls
    # not covered by the names above — `_register_in_build` (`lake build`) and a
    # raw UNCONFINED `ReplSession` (`lake env repl`). They are unreachable via
    # the coarse tool set today, but make them fail-closed so exposing them later
    # can't silently run unconfined. (The CONFINED warm REPL is a separate class,
    # ConfinedReplSession, whose own __init__ does not hit this block.)
    def _blocked_build(self, *a, **k):
        raise SandboxUnavailable("lake build is disabled in harness/sandbox mode")
    _driver.VerifyDriver._register_in_build = _blocked_build

    from . import repl as _repl
    _orig_repl_init = _repl.ReplSession.__init__
    def _blocked_repl_init(self, *a, **k):
        raise SandboxUnavailable("unconfined warm REPL is disabled in harness/"
                                 "sandbox mode (use ConfinedReplSession)")
    _repl.ReplSession.__init__ = _blocked_repl_init

    return True


if __name__ == "__main__":
    # Smoke test: a benign Mathlib proof must compile under the sandbox.
    r = safe_verify("import Mathlib.Tactic\nexample : 1 + 1 = 2 := by norm_num\n")
    print(f"benign: success={r.success} elapsed={r.elapsed:.1f}s err={r.errors[:200]!r}")
