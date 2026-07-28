from __future__ import annotations

import json
from dataclasses import asdict, dataclass, field
from pathlib import Path

from platformdirs import user_config_dir, user_data_dir


APP_NAME = "verify"


@dataclass
class BackendConfig:
    name: str
    kind: str
    model: str = ""
    base_url: str = ""
    credential_id: str = ""
    command: str = ""
    provider: str = ""
    subagent_model: str = ""
    effort: str = ""


@dataclass
class AppConfig:
    default_backend: str = ""
    default_mode: str = "standard"
    backends: dict[str, BackendConfig] = field(default_factory=dict)

    @classmethod
    def from_dict(cls, value: dict) -> "AppConfig":
        raw = value.get("backends") or {}
        backends = {
            name: BackendConfig(name=name, **{
                k: v for k, v in item.items() if k != "name"
            })
            for name, item in raw.items()
            if isinstance(item, dict)
        }
        return cls(
            default_backend=str(value.get("default_backend") or ""),
            default_mode=str(value.get("default_mode") or "standard"),
            backends=backends,
        )

    def to_dict(self) -> dict:
        return {
            "default_backend": self.default_backend,
            "default_mode": self.default_mode,
            "backends": {name: asdict(cfg) for name, cfg in self.backends.items()},
        }


class ConfigStore:
    def __init__(self, path: Path | None = None):
        self.path = path or Path(user_config_dir(APP_NAME)) / "config.json"

    def load(self) -> AppConfig:
        if not self.path.exists():
            return AppConfig()
        try:
            value = json.loads(self.path.read_text())
        except (OSError, ValueError, TypeError):
            return AppConfig()
        return AppConfig.from_dict(value if isinstance(value, dict) else {})

    def save(self, config: AppConfig) -> None:
        self.path.parent.mkdir(parents=True, exist_ok=True)
        tmp = self.path.with_suffix(".tmp")
        tmp.write_text(json.dumps(config.to_dict(), indent=2, sort_keys=True))
        tmp.chmod(0o600)
        tmp.replace(self.path)


def data_dir() -> Path:
    path = Path(user_data_dir(APP_NAME))
    path.mkdir(parents=True, exist_ok=True)
    return path
