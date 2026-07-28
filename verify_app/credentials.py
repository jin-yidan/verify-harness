from __future__ import annotations

from dataclasses import dataclass, field
from typing import Protocol


SERVICE_NAME = "verify"


class CredentialError(RuntimeError):
    pass


class CredentialStore(Protocol):
    def get(self, credential_id: str) -> str | None: ...
    def set(self, credential_id: str, secret: str) -> None: ...
    def delete(self, credential_id: str) -> None: ...


class KeyringCredentialStore:
    """Store provider keys in the operating-system credential service."""

    def __init__(self, service_name: str = SERVICE_NAME):
        self.service_name = service_name

    def get(self, credential_id: str) -> str | None:
        try:
            import keyring
            return keyring.get_password(self.service_name, credential_id)
        except Exception as exc:
            raise CredentialError(f"credential service unavailable: {exc}") from exc

    def set(self, credential_id: str, secret: str) -> None:
        if not secret.strip():
            raise CredentialError("API key cannot be empty")
        try:
            import keyring
            keyring.set_password(self.service_name, credential_id, secret.strip())
        except Exception as exc:
            raise CredentialError(f"could not store credential securely: {exc}") from exc

    def delete(self, credential_id: str) -> None:
        try:
            import keyring
            keyring.delete_password(self.service_name, credential_id)
        except Exception as exc:
            # Deleting an already-absent key should be harmless across backends.
            if "not found" not in str(exc).lower():
                raise CredentialError(f"could not remove credential: {exc}") from exc


@dataclass
class MemoryCredentialStore:
    """Test and session-only credential store."""

    values: dict[str, str] = field(default_factory=dict)

    def get(self, credential_id: str) -> str | None:
        return self.values.get(credential_id)

    def set(self, credential_id: str, secret: str) -> None:
        if not secret.strip():
            raise CredentialError("API key cannot be empty")
        self.values[credential_id] = secret.strip()

    def delete(self, credential_id: str) -> None:
        self.values.pop(credential_id, None)
