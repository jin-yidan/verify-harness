from __future__ import annotations

from dataclasses import dataclass, field
from typing import Callable, Protocol


class BackendError(RuntimeError):
    def __init__(self, message: str, *, category: str = "provider_error",
                 retryable: bool = False, status_code: int | None = None):
        super().__init__(message)
        self.category = category
        self.retryable = retryable
        self.status_code = status_code


@dataclass(frozen=True)
class Capabilities:
    provider: str
    model: str
    tool_calls: bool = False
    structured_json: bool = False
    streaming: bool = False
    usage: bool = False


@dataclass(frozen=True)
class HealthReport:
    ok: bool
    provider: str
    model: str
    detail: str
    capabilities: Capabilities


@dataclass(frozen=True)
class ToolCall:
    id: str
    name: str
    arguments: str

    def as_openai_dict(self) -> dict:
        return {
            "id": self.id,
            "type": "function",
            "function": {"name": self.name, "arguments": self.arguments},
        }


@dataclass
class ModelTurn:
    content: str = ""
    tool_calls: list[ToolCall] = field(default_factory=list)
    usage: dict = field(default_factory=dict)
    finish_reason: str = ""


class ToolCallingBackend(Protocol):
    @property
    def capabilities(self) -> Capabilities: ...
    def call_sealed(self, prompt: str, timeout_s: int = 600) -> str: ...
    def complete(self, messages: list[dict], tools: list[dict],
                 timeout_s: int = 600) -> ModelTurn: ...
    def health_check(self) -> HealthReport: ...
    def close(self) -> None: ...


@dataclass
class BackendBundle:
    name: str
    model: str
    call_model: Callable[[str], str]
    agent_drive: Callable[[str, str, str, str], None]
    health_check: Callable[[], HealthReport] | None = None
    close: Callable[[], None] | None = None
