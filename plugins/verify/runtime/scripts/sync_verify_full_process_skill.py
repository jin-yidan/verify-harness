#!/usr/bin/env python3
"""Keep the Codex verify-full-process duplicate byte-aligned with the golden.

The wrapper is Codex-specific; everything from the golden command's title
onward is generated from `.claude/commands/verify-full-process.md`.
"""
from __future__ import annotations

import argparse
import os
import shutil
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
GOLDEN = ROOT / ".claude" / "commands" / "verify-full-process.md"
CODEX_SKILL = ROOT / "codex-skills" / "verify-full-process" / "SKILL.md"
MARKER = "# /verify-full-process — RLVerify:"


def rendered() -> str:
    current = CODEX_SKILL.read_text()
    offset = current.find(MARKER)
    if offset < 0:
        raise RuntimeError(f"{CODEX_SKILL} has no wrapper/body marker")
    wrapper = current[:offset]
    golden = GOLDEN.read_text().rstrip()
    if not golden.startswith(MARKER):
        raise RuntimeError(f"{GOLDEN} no longer starts with {MARKER!r}")
    return wrapper + golden + "\n"


def atomic_write(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary = tempfile.mkstemp(
        prefix=path.name + ".", dir=path.parent
    )
    try:
        with os.fdopen(fd, "w") as handle:
            handle.write(content)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
    finally:
        try:
            os.unlink(temporary)
        except FileNotFoundError:
            pass


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--check",
        action="store_true",
        help="fail if the repository duplicate is stale",
    )
    parser.add_argument(
        "--install",
        action="store_true",
        help="also refresh ~/.codex/skills/verify-full-process",
    )
    args = parser.parse_args()
    expected = rendered()
    stale = CODEX_SKILL.read_text() != expected
    if args.check:
        if stale:
            print(f"stale: {CODEX_SKILL}")
            return 1
    elif stale:
        atomic_write(CODEX_SKILL, expected)
        print(f"updated: {CODEX_SKILL}")
    else:
        print(f"current: {CODEX_SKILL}")
    if args.install:
        destination = (
            Path.home() / ".codex" / "skills"
            / "verify-full-process" / "SKILL.md"
        )
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(CODEX_SKILL, destination)
        print(f"installed: {destination}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
