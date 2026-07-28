#!/usr/bin/env python3
"""Synchronize faithful copies of the canonical Claude command specifications."""

from __future__ import annotations

import argparse
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]
CANONICAL = ROOT / ".claude" / "commands"
DESTINATIONS = (
    ROOT / "commands",
    ROOT / "plugins" / "verify" / "commands",
    ROOT / "plugins" / "verify" / "runtime" / ".claude" / "commands",
)


def command_files(directory: Path) -> dict[str, Path]:
    return {path.name: path for path in sorted(directory.glob("*.md"))}


def drift() -> list[str]:
    expected = command_files(CANONICAL)
    problems: list[str] = []
    for destination in DESTINATIONS:
        actual = command_files(destination) if destination.is_dir() else {}
        for name, source in expected.items():
            target = actual.get(name)
            if target is None:
                problems.append(f"missing: {target or destination / name}")
            elif target.read_bytes() != source.read_bytes():
                problems.append(f"content differs: {target}")
        for name, target in actual.items():
            if name not in expected:
                problems.append(f"unexpected command copy: {target}")
    return problems


def sync() -> None:
    expected = command_files(CANONICAL)
    for destination in DESTINATIONS:
        destination.mkdir(parents=True, exist_ok=True)
        for name, source in expected.items():
            (destination / name).write_bytes(source.read_bytes())


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--check",
        action="store_true",
        help="report drift without changing files",
    )
    args = parser.parse_args()
    if not args.check:
        sync()
    problems = drift()
    if problems:
        print("\n".join(problems), file=sys.stderr)
        return 1
    count = len(command_files(CANONICAL))
    print(f"{count} canonical commands match {len(DESTINATIONS)} copy surfaces")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
