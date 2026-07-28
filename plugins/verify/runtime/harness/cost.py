"""Heuristic cost estimates for harness verification runs.

The harness can only know exact spend after a backend run returns its metering
envelope. This module gives a pre-run, post-extraction estimate from the
materialized statement/proof text so users can decide whether to launch the
formal proof attempt.
"""
from __future__ import annotations

import math
from dataclasses import dataclass
from typing import Iterable


@dataclass(frozen=True)
class VerificationUnit:
    name: str
    statement: str
    proof: str
    claim: str | None = None


@dataclass(frozen=True)
class CostEstimate:
    theorem_count: int
    total_chars: int
    approx_input_tokens: int
    agent_runs: int
    sealed_gate_calls: int
    backend: str
    model: str | None
    reasoning_effort: str | None
    agent_timeout_s: int
    gate_timeout_s: int
    usd_low: float
    usd_high: float
    wall_low_min: float
    wall_high_min: float
    configured_cap_min: float


def _approx_tokens(text: str) -> int:
    return max(1, math.ceil(len(text) / 4))


def _effort_factor(reasoning_effort: str | None) -> float:
    return {
        "low": 0.7,
        "medium": 1.0,
        "high": 1.4,
        "xhigh": 2.0,
    }.get(reasoning_effort or "", 1.0)


def _model_factor(backend: str, model: str | None) -> float:
    m = (model or "").lower()
    b = backend.lower()
    if b == "claude":
        if "sonnet" in m:
            return 0.65
        if "opus" in m or not m:
            return 1.35
    if b == "codex":
        if "mini" in m or "nano" in m:
            return 0.6
    return 1.0


def estimate_verification_cost(
    units: Iterable[VerificationUnit],
    *,
    backend: str,
    model: str | None,
    reasoning_effort: str | None,
    agent_timeout_s: int,
    gate_timeout_s: int,
) -> CostEstimate:
    rows = list(units)
    theorem_count = len(rows)
    total_chars = sum(len(u.statement) + len(u.proof) + len(u.claim or "") for u in rows)
    approx_input_tokens = _approx_tokens("".join(
        u.statement + "\n" + u.proof + "\n" + (u.claim or "") for u in rows
    ))
    factor = _model_factor(backend, model) * _effort_factor(reasoning_effort)

    usd_low = usd_high = 0.0
    wall_low = wall_high = 0.0
    for u in rows:
        toks = _approx_tokens(u.statement + "\n" + u.proof + "\n" + (u.claim or ""))
        size = max(1.0, toks / 2000.0)
        root_size = math.sqrt(size)
        # Low end: mostly library hits / short Lean proof. High end: several
        # failed proof attempts and gate retries, still bounded separately by the
        # configured wall-clock cap.
        usd_low += 0.75 * root_size * factor
        usd_high += (2.0 + 4.5 * size) * factor
        wall_low += 5.0 + 2.0 * root_size
        wall_high += min(agent_timeout_s / 60.0, 18.0 + 10.0 * size)

    sealed_gate_calls = theorem_count * 5
    configured_cap_min = theorem_count * (
        agent_timeout_s / 60.0 + 5 * gate_timeout_s / 60.0
    )

    return CostEstimate(
        theorem_count=theorem_count,
        total_chars=total_chars,
        approx_input_tokens=approx_input_tokens,
        agent_runs=theorem_count,
        sealed_gate_calls=sealed_gate_calls,
        backend=backend,
        model=model,
        reasoning_effort=reasoning_effort,
        agent_timeout_s=agent_timeout_s,
        gate_timeout_s=gate_timeout_s,
        usd_low=usd_low,
        usd_high=max(usd_high, usd_low),
        wall_low_min=wall_low,
        wall_high_min=max(wall_high, wall_low),
        configured_cap_min=configured_cap_min,
    )


def render_cost_estimate(est: CostEstimate) -> str:
    model = est.model or "backend default"
    effort = f", effort={est.reasoning_effort}" if est.reasoning_effort else ""
    return "\n".join([
        "  formal-proof cost estimate (heuristic, shown before agent launch):",
        f"    theorem fixtures: {est.theorem_count}",
        f"    approx input: {est.approx_input_tokens:,} tokens "
        f"({est.total_chars:,} chars of statement/proof/claim)",
        f"    backend/model: {est.backend}/{model}{effort}",
        f"    expected model calls: {est.agent_runs} driving agent run(s) + "
        f"{est.sealed_gate_calls} sealed gate call(s)",
        f"    estimated model spend: ${est.usd_low:.2f}-${est.usd_high:.2f}",
        f"    estimated wall time: {est.wall_low_min:.0f}-{est.wall_high_min:.0f} min "
        f"(configured hard cap: {est.configured_cap_min:.0f} min)",
        "    excludes paper extraction already completed; actual provider billing may differ.",
    ])
