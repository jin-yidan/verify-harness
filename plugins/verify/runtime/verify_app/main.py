from __future__ import annotations

import sys

from .config import ConfigStore
from .credentials import CredentialError, KeyringCredentialStore
from .onboarding import ensure_configured, interactive_setup
from .repl import VerifyREPL


def main(argv: list[str] | None = None) -> int:
    argv = list(sys.argv[1:] if argv is None else argv)
    if argv in (["--version"], ["-V"]):
        from . import __version__
        print(f"Verify {__version__}")
        return 0
    if argv in (["--help"], ["-h"]):
        print(
            "Verify is a conversational mathematical verification agent.\n\n"
            "Launch it with:\n  verify\n\n"
            "Open backend setup with:\n  verify setup\n\n"
            "Once running, type /help for available actions."
        )
        return 0
    if argv in (["setup"], ["--setup"]):
        config_store = ConfigStore()
        credentials = KeyringCredentialStore()
        try:
            config = interactive_setup(config_store, credentials)
        except (CredentialError, ValueError) as exc:
            print(f"Setup could not be completed: {exc}", file=sys.stderr)
            return 1
        print(
            f"\nSetup complete. Active backend: {config.default_backend}\n"
            "Launch Verify with: verify"
        )
        return 0
    if argv:
        print(
            "Verify is conversational. Use `verify`, `verify setup`, "
            "or `verify --help`.",
            file=sys.stderr,
        )
        return 2

    config_store = ConfigStore()
    credentials = KeyringCredentialStore()
    try:
        config = ensure_configured(config_store, credentials)
    except (CredentialError, ValueError) as exc:
        print(f"Setup could not be completed: {exc}", file=sys.stderr)
        return 1
    return VerifyREPL(config_store, credentials, config).run()


if __name__ == "__main__":
    raise SystemExit(main())
