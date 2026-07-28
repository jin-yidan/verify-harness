#!/usr/bin/env python3
"""First-use runtime manager for the Verify plugin.

The plugin itself is copied into an agent cache, so it cannot import engine
code from the marketplace checkout. This helper installs a versioned engine
checkout in user data after the agent has obtained explicit permission.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
import platform
import shutil
import subprocess
import sys
import tarfile
import tempfile
import urllib.request
import zipfile
from pathlib import Path
from typing import Sequence


ENGINE_REPOSITORY = "https://github.com/jin-yidan/verified-rl.git"
ENGINE_REF = "verify-v0.1.0"
MIN_PYTHON = (3, 10)
ELAN_VERSION = "4.2.1"
ELAN_RELEASE_ROOT = (
    f"https://github.com/leanprover/elan/releases/download/v{ELAN_VERSION}"
)
ELAN_ASSETS = {
    ("Darwin", "arm64"): (
        "elan-aarch64-apple-darwin.tar.gz",
        "3b3170eb6af7d89e28c7a98d25066a07efb41246e43d6333505dfa54069100c8",
    ),
    ("Darwin", "x86_64"): (
        "elan-x86_64-apple-darwin.tar.gz",
        "3bd377a1d767fabaad3b40d32bfa3d51b099ed40dbcd3c08ca66af2761ec1a70",
    ),
    ("Linux", "aarch64"): (
        "elan-aarch64-unknown-linux-gnu.tar.gz",
        "bb78726ace6a912c7122a389018bcd69d9122ce04659800101392f7db380d3b3",
    ),
    ("Linux", "x86_64"): (
        "elan-x86_64-unknown-linux-gnu.tar.gz",
        "4e717523217af592fa2d7b9c479410a31816c065d66ccbf0c2149337cfec0f5c",
    ),
    ("Windows", "x86_64"): (
        "elan-x86_64-pc-windows-msvc.zip",
        "ad4befa57060933d65464bca4eca34c334f714000b5969c49309755682541dc1",
    ),
}


def plugin_root() -> Path:
    return Path(__file__).resolve().parents[1]


def plugin_version() -> str:
    manifest = plugin_root() / ".codex-plugin" / "plugin.json"
    try:
        return str(json.loads(manifest.read_text())["version"])
    except (OSError, KeyError, TypeError, json.JSONDecodeError):
        return "0.1.0"


def engine_series() -> str:
    return plugin_version().split("+", 1)[0]


def data_root() -> Path:
    override = os.environ.get("VERIFY_DATA_DIR")
    if override:
        return Path(override).expanduser()
    claude_data = os.environ.get("CLAUDE_PLUGIN_DATA")
    if claude_data:
        return Path(claude_data).expanduser()
    if os.name == "nt":
        base = os.environ.get("LOCALAPPDATA")
        return Path(base).expanduser() / "Verify" if base else Path.home() / "Verify"
    if sys.platform == "darwin":
        return Path.home() / "Library" / "Application Support" / "Verify"
    base = os.environ.get("XDG_DATA_HOME")
    return (Path(base).expanduser() if base else Path.home() / ".local" / "share") / "verify"


def engine_root() -> Path:
    return data_root() / "engines" / engine_series()


def engine_source() -> Path:
    return engine_root() / "source"


def engine_python() -> Path:
    folder = "Scripts" if os.name == "nt" else "bin"
    executable = "python.exe" if os.name == "nt" else "python"
    return engine_root() / "venv" / folder / executable


def marker_path() -> Path:
    return engine_root() / "ready.json"


def _normalized_machine() -> str:
    value = platform.machine().lower()
    if value in {"amd64", "x64"}:
        return "x86_64"
    if value in {"arm64", "aarch64"}:
        return "arm64" if platform.system() == "Darwin" else "aarch64"
    return value


def _elan_asset() -> tuple[str, str]:
    key = (platform.system(), _normalized_machine())
    try:
        return ELAN_ASSETS[key]
    except KeyError as error:
        raise RuntimeError(
            f"automatic Lean setup is not supported on {key[0]} {key[1]}"
        ) from error


def _lean_tool(name: str) -> str | None:
    found = shutil.which(name)
    if found:
        return found
    executable = f"{name}.exe" if os.name == "nt" else name
    candidate = Path.home() / ".elan" / "bin" / executable
    return str(candidate) if candidate.is_file() else None


def _run(
    args: Sequence[str],
    *,
    cwd: Path | None = None,
    env: dict[str, str] | None = None,
    check: bool = True,
) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(
        list(args),
        cwd=str(cwd) if cwd else None,
        env=env,
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    if check and result.returncode != 0:
        command = Path(str(args[0])).name
        detail = (result.stdout or "").strip()[-4000:]
        raise RuntimeError(
            f"{command} exited with status {result.returncode}"
            + (f":\n{detail}" if detail else "")
        )
    return result


def _can_import_engine(python: Path) -> bool:
    if not python.is_file():
        return False
    result = _run(
        [
            str(python),
            "-c",
            "import harness.cli, rlverify.mcp_server, verify_app.mcp_server",
        ],
        check=False,
    )
    return result.returncode == 0


def _read_marker() -> dict:
    try:
        value = json.loads(marker_path().read_text())
        return value if isinstance(value, dict) else {}
    except (OSError, json.JSONDecodeError):
        return {}


def _system_engine() -> tuple[Path, Path] | None:
    if os.environ.get("VERIFY_IGNORE_SYSTEM_ENGINE") == "1":
        return None
    spec = importlib.util.find_spec("rlverify.mcp_server")
    if spec is None or spec.origin is None:
        return None
    source = Path(spec.origin).resolve().parents[1]
    return Path(sys.executable).resolve(), source


def runtime_status() -> dict:
    marker = _read_marker()
    python_ok = sys.version_info >= MIN_PYTHON
    managed_ok = _can_import_engine(engine_python())
    system = _system_engine()
    engine_ok = managed_ok or system is not None
    active_python = engine_python() if managed_ok else system[0] if system else engine_python()
    active_source = engine_source() if managed_ok else system[1] if system else engine_source()
    lake = _lean_tool("lake")
    lean = _lean_tool("lean")
    lean_ready = bool(
        engine_ok
        and (
            (managed_ok and marker.get("lean_ready"))
            or (system is not None and (active_source / ".lake" / "build").exists())
        )
    )
    return {
        "plugin_version": plugin_version(),
        "engine_series": engine_series(),
        "data_root": str(data_root()),
        "engine_root": str(engine_root()),
        "python": {
            "executable": sys.executable,
            "version": platform.python_version(),
            "supported": python_ok,
        },
        "engine": {
            "installed": engine_ok,
            "managed": managed_ok,
            "python": str(active_python),
            "source": str(active_source),
        },
        "lean": {
            "lake": lake,
            "lean": lean,
            "installer_version": ELAN_VERSION,
            "ready": lean_ready,
        },
        "ready_for_lightweight_workflows": engine_ok,
        "ready_for_full_verification": engine_ok and lean_ready,
        "action": (
            "upgrade_python"
            if not python_ok
            else "install_engine"
            if not engine_ok
            else "install_lean"
            if not lake or not lean
            else "build_lean"
            if not lean_ready
            else "ready"
        ),
    }


def _copy_local_source(source: Path, destination: Path) -> None:
    ignored = shutil.ignore_patterns(
        ".git",
        ".lake",
        ".pytest_cache",
        "__pycache__",
        "*.pyc",
        "runs",
    )
    shutil.copytree(source, destination, ignore=ignored)


def _obtain_source(destination: Path, source: str | None, ref: str) -> None:
    if source:
        local = Path(source).expanduser().resolve()
        if not (local / "pyproject.toml").is_file():
            raise RuntimeError(f"not a Verify source checkout: {local}")
        _copy_local_source(local, destination)
        return
    git = shutil.which("git")
    if not git:
        raise RuntimeError("git is required to download the Verify engine")
    repository = os.environ.get("VERIFY_ENGINE_REPOSITORY", ENGINE_REPOSITORY)
    _run([git, "clone", "--depth", "1", "--branch", ref, repository, str(destination)])


def _write_marker(*, lean_ready: bool, ref: str) -> None:
    payload = {
        "plugin_version": plugin_version(),
        "engine_series": engine_series(),
        "engine_ref": ref,
        "lean_ready": lean_ready,
    }
    marker_path().write_text(json.dumps(payload, indent=2) + "\n")


def _build_lean(source_dir: Path) -> None:
    lake = _lean_tool("lake")
    lean = _lean_tool("lean")
    if not lake or not lean:
        raise RuntimeError(
            "Lean is not installed. Install elan, then ask Verify to continue "
            "runtime setup."
        )
    _run([lake, "update", "SLT"], cwd=source_dir)
    prepare = source_dir / "scripts" / "prepare_slt.sh"
    if prepare.is_file():
        bash = shutil.which("bash")
        if not bash:
            raise RuntimeError("bash is required to prepare the Lean dependency")
        _run([bash, str(prepare)], cwd=source_dir)
    _run([lake, "exe", "cache", "get"], cwd=source_dir, check=False)
    _run([lake, "build", "RLGeneralization"], cwd=source_dir)


def _download(url: str, destination: Path) -> None:
    request = urllib.request.Request(
        url,
        headers={"User-Agent": f"Verify/{plugin_version()}"},
    )
    with urllib.request.urlopen(request, timeout=120) as response:
        with destination.open("wb") as output:
            shutil.copyfileobj(response, output)


def _safe_extract(archive: Path, destination: Path) -> None:
    destination_resolved = destination.resolve()
    if archive.name.endswith(".zip"):
        with zipfile.ZipFile(archive) as bundle:
            for member in bundle.infolist():
                target = (destination / member.filename).resolve()
                if not target.is_relative_to(destination_resolved):
                    raise RuntimeError("unsafe path in elan archive")
            bundle.extractall(destination)
        return
    with tarfile.open(archive, "r:gz") as bundle:
        for member in bundle.getmembers():
            if member.issym() or member.islnk():
                raise RuntimeError("links are not allowed in the elan archive")
            target = (destination / member.name).resolve()
            if not target.is_relative_to(destination_resolved):
                raise RuntimeError("unsafe path in elan archive")
        if sys.version_info >= (3, 12):
            bundle.extractall(destination, filter="fully_trusted")
        else:
            bundle.extractall(destination)


def install_lean(*, confirmed: bool) -> dict:
    if not confirmed:
        raise PermissionError(
            "Lean installation requires explicit user confirmation"
        )
    if not _lean_tool("lake") or not _lean_tool("lean"):
        filename, expected_sha256 = _elan_asset()
        with tempfile.TemporaryDirectory(prefix="verify-elan-") as temp:
            temp_dir = Path(temp)
            archive = temp_dir / filename
            _download(f"{ELAN_RELEASE_ROOT}/{filename}", archive)
            actual = hashlib.sha256(archive.read_bytes()).hexdigest()
            if actual != expected_sha256:
                raise RuntimeError(
                    "elan download checksum mismatch; refusing to execute it"
                )
            unpacked = temp_dir / "unpacked"
            unpacked.mkdir()
            _safe_extract(archive, unpacked)
            executable = "elan-init.exe" if os.name == "nt" else "elan-init"
            candidates = list(unpacked.rglob(executable))
            if len(candidates) != 1:
                raise RuntimeError("elan release did not contain one installer")
            installer = candidates[0]
            installer.chmod(installer.stat().st_mode | 0o100)
            _run(
                [
                    str(installer),
                    "-y",
                    "--no-modify-path",
                    "--default-toolchain",
                    "none",
                ]
            )

    elan_bin = Path.home() / ".elan" / "bin"
    os.environ["PATH"] = f"{elan_bin}{os.pathsep}{os.environ.get('PATH', '')}"
    current = runtime_status()
    if current["ready_for_lightweight_workflows"] and not current[
        "ready_for_full_verification"
    ]:
        source_dir = Path(current["engine"]["source"])
        python = Path(current["engine"]["python"])
        _build_lean(source_dir)
        _smoke_test(python, source_dir)
        if current["engine"]["managed"]:
            ref = str(_read_marker().get("engine_ref") or ENGINE_REF)
            _write_marker(lean_ready=True, ref=ref)
    return runtime_status()


def _smoke_test(python: Path, source_dir: Path) -> None:
    smoke = _run(
        [
            str(python),
            "-m",
            "rlverify",
            "falsify",
            "--example",
            "ucb_clean",
            "--n",
            "100",
        ],
        cwd=source_dir,
        check=False,
    )
    if smoke.returncode != 0:
        raise RuntimeError(f"Verify self-test failed:\n{smoke.stdout[-2000:]}")


def install_runtime(
    *,
    confirmed: bool,
    source: str | None = None,
    ref: str = ENGINE_REF,
    build_lean: bool = True,
) -> dict:
    if not confirmed:
        raise PermissionError(
            "runtime installation requires explicit user confirmation"
        )
    if sys.version_info < MIN_PYTHON:
        raise RuntimeError("Verify requires Python 3.10 or newer")

    current = runtime_status()
    if current["ready_for_full_verification"] or (
        current["ready_for_lightweight_workflows"] and not build_lean
    ):
        return current
    if current["ready_for_lightweight_workflows"]:
        source_dir = Path(current["engine"]["source"])
        python = Path(current["engine"]["python"])
        if not _lean_tool("lake") or not _lean_tool("lean"):
            return current
        _build_lean(source_dir)
        _smoke_test(python, source_dir)
        if current["engine"]["managed"]:
            _write_marker(lean_ready=True, ref=ref)
        return runtime_status()

    root = engine_root()
    root.parent.mkdir(parents=True, exist_ok=True)
    staging = Path(tempfile.mkdtemp(prefix=f".{engine_series()}-", dir=root.parent))
    try:
        source_dir = staging / "source"
        _obtain_source(source_dir, source, ref)
        venv_dir = staging / "venv"
        _run([sys.executable, "-m", "venv", str(venv_dir)])
        folder = "Scripts" if os.name == "nt" else "bin"
        executable = "python.exe" if os.name == "nt" else "python"
        staged_python = venv_dir / folder / executable
        _run(
            [
                str(staged_python),
                "-m",
                "pip",
                "install",
                "--disable-pip-version-check",
                "-e",
                str(source_dir),
            ]
        )

        lean_ready = bool(
            build_lean and _lean_tool("lake") and _lean_tool("lean")
        )
        if lean_ready:
            _build_lean(source_dir)
        _smoke_test(staged_python, source_dir)

        if root.exists():
            raise RuntimeError(
                f"incomplete runtime already exists at {root}; preserve it and "
                "ask the user before replacing it"
            )
        os.replace(staging, root)
        _write_marker(lean_ready=lean_ready, ref=ref)
        return runtime_status()
    except Exception:
        shutil.rmtree(staging, ignore_errors=True)
        raise


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Manage the Verify plugin runtime")
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument("--status", action="store_true", help="show runtime readiness")
    action.add_argument("--install", action="store_true", help="install the runtime")
    action.add_argument(
        "--install-lean",
        action="store_true",
        help="install pinned elan and build the Lean runtime",
    )
    parser.add_argument(
        "--yes",
        action="store_true",
        help="confirm the agent already obtained explicit user permission",
    )
    parser.add_argument("--source", help=argparse.SUPPRESS)
    parser.add_argument("--ref", default=ENGINE_REF, help=argparse.SUPPRESS)
    parser.add_argument("--skip-lean-build", action="store_true", help=argparse.SUPPRESS)
    parser.add_argument("--json", action="store_true")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    try:
        if args.status:
            result = runtime_status()
        elif args.install_lean:
            result = install_lean(confirmed=args.yes)
        else:
            result = install_runtime(
                confirmed=args.yes,
                source=args.source,
                ref=args.ref,
                build_lean=not args.skip_lean_build,
            )
    except (PermissionError, RuntimeError, subprocess.SubprocessError) as error:
        payload = {"ok": False, "error": str(error), "status": runtime_status()}
        print(json.dumps(payload, indent=2) if args.json else f"ERROR: {error}")
        return 2
    except KeyboardInterrupt:
        payload = {
            "ok": False,
            "cancelled": True,
            "error": "runtime setup interrupted; installed data was preserved",
            "status": runtime_status(),
        }
        print(
            json.dumps(payload, indent=2)
            if args.json
            else "CANCELLED: runtime setup interrupted; installed data was preserved"
        )
        return 130
    payload = {"ok": True, "status": result}
    print(json.dumps(payload, indent=2) if args.json else json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
