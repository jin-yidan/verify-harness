from __future__ import annotations

import json
from collections.abc import Callable

import httpx

from .protocol import (
    BackendError,
    Capabilities,
    HealthReport,
    ModelTurn,
    ToolCall,
)


class OpenAICompatibleBackend:
    """Minimal OpenAI Chat Completions adapter.

    The API key is requested lazily for each call and is never stored on this
    object.  This works with DeepSeek and other compatible endpoints while
    keeping provider-specific behavior outside the verification pipeline.
    """

    def __init__(
        self,
        *,
        provider: str,
        model: str,
        base_url: str,
        api_key: Callable[[], str | None],
        client: httpx.Client | None = None,
        default_timeout_s: int = 600,
    ):
        self.provider = provider
        self.model = model
        self.base_url = base_url.rstrip("/")
        self._api_key = api_key
        self._client = client or httpx.Client()
        self._owns_client = client is None
        self.default_timeout_s = default_timeout_s

    @property
    def capabilities(self) -> Capabilities:
        return Capabilities(
            provider=self.provider,
            model=self.model,
            tool_calls=True,
            structured_json=True,
            streaming=False,
            usage=True,
        )

    @property
    def endpoint(self) -> str:
        if self.base_url.endswith("/chat/completions"):
            return self.base_url
        return f"{self.base_url}/chat/completions"

    def _headers(self) -> dict[str, str]:
        key = (self._api_key() or "").strip()
        if not key:
            raise BackendError(
                f"{self.provider} is not connected",
                category="authentication",
                status_code=401,
            )
        return {
            "Authorization": f"Bearer {key}",
            "Content-Type": "application/json",
        }

    def _post(self, payload: dict, timeout_s: int) -> dict:
        try:
            response = self._client.post(
                self.endpoint,
                headers=self._headers(),
                json=payload,
                timeout=timeout_s or self.default_timeout_s,
            )
        except httpx.TimeoutException as exc:
            raise BackendError(
                f"{self.provider} request timed out",
                category="timeout",
                retryable=True,
            ) from exc
        except httpx.HTTPError as exc:
            raise BackendError(
                f"could not reach {self.provider}: {type(exc).__name__}",
                category="network",
                retryable=True,
            ) from exc

        if response.status_code >= 400:
            detail = _safe_error_detail(response)
            if response.status_code in {401, 403}:
                category, retryable = "authentication", False
            elif response.status_code == 429:
                category, retryable = "rate_limit", True
            elif response.status_code >= 500:
                category, retryable = "provider_outage", True
            else:
                category, retryable = "invalid_request", False
            raise BackendError(
                f"{self.provider} returned HTTP {response.status_code}: {detail}",
                category=category,
                retryable=retryable,
                status_code=response.status_code,
            )
        try:
            value = response.json()
        except ValueError as exc:
            raise BackendError(
                f"{self.provider} returned invalid JSON",
                category="invalid_response",
            ) from exc
        if not isinstance(value, dict):
            raise BackendError(
                f"{self.provider} returned an invalid response envelope",
                category="invalid_response",
            )
        return value

    def call_sealed(self, prompt: str, timeout_s: int = 600) -> str:
        value = self._post(
            {
                "model": self.model,
                "messages": [
                    {
                        "role": "system",
                        "content": (
                            "Follow the user's instructions exactly. You have no "
                            "tools and no context other than this request."
                        ),
                    },
                    {"role": "user", "content": prompt},
                ],
                "temperature": 0,
            },
            timeout_s,
        )
        message, _finish = _first_message(value)
        return str(message.get("content") or "")

    def complete(self, messages: list[dict], tools: list[dict],
                 timeout_s: int = 600) -> ModelTurn:
        payload = {
            "model": self.model,
            "messages": messages,
            "tools": tools,
            "tool_choice": "auto",
            "temperature": 0,
        }
        value = self._post(payload, timeout_s)
        message, finish = _first_message(value)
        calls: list[ToolCall] = []
        for item in message.get("tool_calls") or []:
            if not isinstance(item, dict):
                continue
            function = item.get("function") or {}
            calls.append(ToolCall(
                id=str(item.get("id") or f"call_{len(calls)}"),
                name=str(function.get("name") or ""),
                arguments=str(function.get("arguments") or "{}"),
            ))
        return ModelTurn(
            content=str(message.get("content") or ""),
            tool_calls=calls,
            usage=value.get("usage") if isinstance(value.get("usage"), dict) else {},
            finish_reason=str(finish or ""),
        )

    def health_check(self) -> HealthReport:
        try:
            answer = self.call_sealed(
                'Reply with exactly: {"ok":true}', timeout_s=30,
            )
            ok = "true" in answer.lower()
            detail = "connection succeeded" if ok else "provider responded unexpectedly"
        except BackendError as exc:
            ok, detail = False, str(exc)
        return HealthReport(
            ok=ok,
            provider=self.provider,
            model=self.model,
            detail=detail,
            capabilities=self.capabilities,
        )

    def close(self) -> None:
        if self._owns_client:
            self._client.close()


def _first_message(value: dict) -> tuple[dict, str]:
    choices = value.get("choices")
    if not isinstance(choices, list) or not choices:
        raise BackendError("provider response had no choices",
                           category="invalid_response")
    first = choices[0]
    if not isinstance(first, dict) or not isinstance(first.get("message"), dict):
        raise BackendError("provider response had no message",
                           category="invalid_response")
    return first["message"], str(first.get("finish_reason") or "")


def _safe_error_detail(response: httpx.Response) -> str:
    try:
        value = response.json()
    except ValueError:
        return response.text[:300] or "request failed"
    if isinstance(value, dict):
        error = value.get("error")
        if isinstance(error, dict):
            return str(error.get("message") or error.get("type") or "request failed")[:300]
        if error:
            return str(error)[:300]
    return json.dumps(value)[:300]
