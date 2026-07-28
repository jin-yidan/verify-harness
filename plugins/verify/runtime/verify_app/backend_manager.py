from __future__ import annotations

from .backends.api_agent import api_bundle
from .backends.cli_subscription import cli_bundle
from .backends.openai_compatible import OpenAICompatibleBackend
from .backends.protocol import BackendBundle
from .config import AppConfig, BackendConfig
from .credentials import CredentialStore


class BackendManager:
    def __init__(self, config: AppConfig, credentials: CredentialStore):
        self.config = config
        self.credentials = credentials
        self._bundle: BackendBundle | None = None

    @property
    def active_config(self) -> BackendConfig:
        name = self.config.default_backend
        if not name or name not in self.config.backends:
            raise RuntimeError("Verify has no configured reasoning backend")
        return self.config.backends[name]

    def bundle(self, *, timeout_s: int = 900) -> BackendBundle:
        if self._bundle is not None:
            return self._bundle
        cfg = self.active_config
        if cfg.kind == "cli":
            self._bundle = cli_bundle(
                cfg.name,
                model=(cfg.model or None),
                timeout_s=timeout_s,
                # A subscription selection must not accidentally inherit a
                # previously exported external-provider endpoint or key.
                provider_env={} if cfg.name == "claude" else None,
            )
            return self._bundle
        if cfg.kind == "claude-provider":
            key = (self.credentials.get(cfg.credential_id) or "").strip()
            if not key:
                raise RuntimeError(
                    f"{cfg.provider or cfg.name} is not connected"
                )
            primary = cfg.model
            fast = cfg.subagent_model or primary
            provider_env = {
                "ANTHROPIC_BASE_URL": cfg.base_url,
                "ANTHROPIC_AUTH_TOKEN": key,
                "ANTHROPIC_MODEL": primary,
                "ANTHROPIC_DEFAULT_OPUS_MODEL": primary,
                "ANTHROPIC_DEFAULT_SONNET_MODEL": primary,
                "ANTHROPIC_DEFAULT_HAIKU_MODEL": fast,
                "CLAUDE_CODE_SUBAGENT_MODEL": fast,
                "CLAUDE_CODE_EFFORT_LEVEL": cfg.effort or "high",
            }
            self._bundle = cli_bundle(
                "claude",
                model=(primary or None),
                timeout_s=timeout_s,
                provider_env=provider_env,
                bundle_name=cfg.name,
            )
            return self._bundle
        if cfg.kind == "openai-compatible":
            backend = OpenAICompatibleBackend(
                provider=cfg.name,
                model=cfg.model,
                base_url=cfg.base_url,
                api_key=lambda: self.credentials.get(cfg.credential_id),
            )
            self._bundle = api_bundle(
                backend,
                name=cfg.name,
                timeout_s=timeout_s,
            )
            return self._bundle
        raise RuntimeError(f"unsupported backend kind: {cfg.kind}")

    def close(self) -> None:
        if self._bundle and self._bundle.close:
            self._bundle.close()
        self._bundle = None
