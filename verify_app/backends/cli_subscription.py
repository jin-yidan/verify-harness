from __future__ import annotations

import shutil

from harness.backends import get_backend
from harness.runner import launch_agent

from .protocol import BackendBundle, Capabilities, HealthReport


def cli_bundle(name: str, model: str | None = None,
               reasoning_effort: str | None = None,
               timeout_s: int | None = None,
               provider_env: dict[str, str] | None = None,
               bundle_name: str | None = None) -> BackendBundle:
    if name not in {"claude", "codex"}:
        raise ValueError(f"unsupported subscription backend: {name}")
    command = "claude" if name == "claude" else "codex"
    resolved_model = model or ("opus" if name == "claude" else "")

    call_model = get_backend(
        name,
        model=(resolved_model or None),
        reasoning_effort=reasoning_effort,
        provider_env=provider_env,
    )
    drive = launch_agent(
        backend=name,
        model=resolved_model,
        timeout=timeout_s,
        reasoning_effort=reasoning_effort,
        provider_env=provider_env,
    )

    def health() -> HealthReport:
        installed = shutil.which(command) is not None
        return HealthReport(
            ok=installed,
            provider=name,
            model=resolved_model or "CLI default",
            detail=(f"{command} CLI found" if installed
                    else f"{command} CLI is not installed"),
            capabilities=Capabilities(
                provider=name,
                model=resolved_model or "CLI default",
                tool_calls=True,
                structured_json=True,
                streaming=(name == "claude"),
                usage=True,
            ),
        )

    return BackendBundle(
        name=bundle_name or name,
        model=resolved_model or "CLI default",
        call_model=call_model,
        agent_drive=drive,
        health_check=health,
    )
