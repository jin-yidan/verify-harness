from __future__ import annotations

import getpass
import shutil
from collections.abc import Callable

from .config import AppConfig, BackendConfig, ConfigStore
from .credentials import CredentialError, CredentialStore


Output = Callable[[str], None]
Input = Callable[[str], str]
SecretInput = Callable[[str], str]


def ensure_configured(
    config_store: ConfigStore,
    credentials: CredentialStore,
    *,
    input_fn: Input = input,
    secret_input: SecretInput = getpass.getpass,
    output: Output = print,
) -> AppConfig:
    config = config_store.load()
    if config.default_backend and config.default_backend in config.backends:
        return config
    return interactive_setup(
        config_store,
        credentials,
        input_fn=input_fn,
        secret_input=secret_input,
        output=output,
    )


def interactive_setup(
    config_store: ConfigStore,
    credentials: CredentialStore,
    *,
    input_fn: Input = input,
    secret_input: SecretInput = getpass.getpass,
    output: Output = print,
) -> AppConfig:
    output("Welcome to Verify.\n")
    output("Choose a reasoning backend:")
    output("  1. Codex subscription")
    output("  2. Claude Code subscription")
    output("  3. Claude Code coding agent + another model API")
    choice = input_fn("\n> ").strip().lower()

    if choice in {"1", "codex", "codex subscription"}:
        return _save_cli("codex", "codex", config_store, output)
    if choice in {"2", "claude", "claude code", "claude code subscription"}:
        return _save_cli("claude", "claude", config_store, output)
    if choice in {
        "3", "api", "other model", "other models",
        "claude code + api", "claude code coding agent + another model api",
        "deepseek", "deepseek api",
    }:
        return _configure_claude_provider(
            config_store=config_store,
            credentials=credentials,
            input_fn=input_fn,
            secret_input=secret_input,
            output=output,
        )
    raise ValueError(
        "choose Codex subscription, Claude Code subscription, or "
        "Claude Code with another model API"
    )


def _save_cli(name: str, command: str, store: ConfigStore,
              output: Output) -> AppConfig:
    if shutil.which(command) is None:
        output(f"Warning: {command} is not currently installed or on PATH.")
    config = store.load()
    config.backends[name] = BackendConfig(
        name=name, kind="cli", command=command,
        model=("opus" if name == "claude" else ""),
    )
    config.default_backend = name
    store.save(config)
    output(f"✓ {name} selected")
    return config


def _configure_claude_provider(
    *,
    config_store: ConfigStore,
    credentials: CredentialStore,
    input_fn: Input,
    secret_input: SecretInput,
    output: Output,
) -> AppConfig:
    if shutil.which("claude") is None:
        output("Warning: Claude Code is not currently installed or on PATH.")

    output("Choose the model API used by Claude Code:")
    output("  1. DeepSeek (recommended)")
    output("  2. Custom Anthropic-compatible provider")
    preset = input_fn("\n> ").strip().lower()
    if preset in {"", "1", "deepseek", "deepseek api"}:
        provider = "deepseek"
        base_url = "https://api.deepseek.com/anthropic"
        model = "deepseek-v4-pro[1m]"
        subagent_model = "deepseek-v4-flash"
        effort = "max"
    elif preset in {"2", "custom"}:
        provider = input_fn("Provider name: ").strip() or "custom"
        base_url = input_fn("Anthropic-compatible API base URL: ").strip()
        model = input_fn("Primary model name: ").strip()
        subagent_model = (
            input_fn("Fast/subagent model name [same as primary]: ").strip()
            or model
        )
        effort = input_fn("Claude Code effort level [high]: ").strip() or "high"
        if not base_url or not model:
            raise ValueError("base URL and primary model name are required")
    else:
        if _looks_like_api_key(preset):
            raise CredentialError(
                "an API key was entered at the provider-selection prompt. "
                "It was not stored. Rotate that key, choose provider 1 or 2, "
                "then enter the replacement only at the hidden key prompt"
            )
        raise ValueError("choose provider 1 (DeepSeek) or 2 (custom)")

    backend_name = f"claude-{provider}"
    credential_id = f"backend/{backend_name}"
    key = secret_input(f"Paste your {provider} API key: ").strip()
    if not key:
        raise CredentialError("API key cannot be empty")
    credentials.set(credential_id, key)
    config = config_store.load()
    config.backends[backend_name] = BackendConfig(
        name=backend_name,
        kind="claude-provider",
        provider=provider,
        command="claude",
        base_url=base_url.rstrip("/"),
        model=model,
        subagent_model=subagent_model,
        effort=effort,
        credential_id=credential_id,
    )
    config.default_backend = backend_name
    config_store.save(config)
    output("✓ Credential stored in the system keychain")
    output(f"✓ Claude Code + {provider} selected")
    return config


def _looks_like_api_key(value: str) -> bool:
    compact = value.strip()
    return (
        compact.lower().startswith(("sk-", "ds-"))
        or (len(compact) >= 24 and " " not in compact)
    )
