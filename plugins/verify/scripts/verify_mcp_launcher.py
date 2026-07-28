#!/usr/bin/env python3
"""Launch the installed Verify MCP engine from a cached plugin directory."""

from __future__ import annotations

import os
import sys
from pathlib import Path

from verify_runtime import engine_python


def main() -> int:
    override = os.environ.get("VERIFY_ENGINE_PYTHON")
    installed = Path(override).expanduser() if override else engine_python()
    if installed.is_file():
        os.execv(str(installed), [str(installed), "-m", "verify_app.mcp_server"])

    print(
        "The bundled Verify engine is not installed yet. The Verify skill can "
        "run scripts/verify_runtime.py after obtaining user permission.",
        file=sys.stderr,
    )
    return 78


if __name__ == "__main__":
    raise SystemExit(main())
