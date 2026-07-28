"""Researcher-facing falsification wrapper.

The underlying engine lives in :mod:`rlverify.falsify_run`: it executes a Python
sampler and derives a seeded report. This module adds the sealed prose-to-sampler
adapter used by ``python3 -m harness falsify``.
"""
from __future__ import annotations

import hashlib
import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Callable

ROOT = Path(__file__).resolve().parent.parent
DEFAULT_OUT = ROOT / "rlverify-out" / "falsify"

CallModel = Callable[[str], str]

SAMPLER_INSTRUCTION = """You are writing a numeric falsification sampler.
You have no tools. Convert the claim into a self-contained Python sampler for
the contract in rlverify/falsify_run.py. The sampler checks claims of the form
lhs(inst) <= rhs(inst), using stdlib Python only.

Return JSON only:
{
  "block": "<short block name>",
  "claim": "<verbatim claim checked>",
  "sampler_code": "<Python module defining sample, hypotheses, lhs, rhs, and ideally recheck>"
}

Sampler requirements:
- define sample(rng), hypotheses(inst), lhs(inst), rhs(inst)
- use only stdlib modules such as math and random
- avoid network, subprocess, file IO, imports outside stdlib, and global side effects
- set N conservatively if the claim needs many samples
- add recheck(inst) when a separate formula can confirm a counterexample
- if the prose claim is not numerically falsifiable, still return JSON with a
  sampler that will be VACUOUS and a CLAIM explaining why
"""


@dataclass
class SamplerSpec:
    block: str
    claim: str
    sampler_code: str


def build_sampler_prompt(claim_text: str, *, block: str = "", n: int | None = None,
                         tol: float | None = None) -> str:
    lines = [SAMPLER_INSTRUCTION]
    if block:
        lines.append(f"Requested block: {block}")
    if n is not None:
        lines.append(f"Sample budget override: {n}")
    if tol is not None:
        lines.append(f"Tolerance override: {tol}")
    lines.append("\nCLAIM / CONTEXT:\n" + claim_text.strip())
    return "\n\n".join(lines)


def _json_obj(raw: str) -> dict | None:
    raw = raw.strip()
    start, end = raw.find("{"), raw.rfind("}")
    if start == -1 or end <= start:
        return None
    try:
        obj = json.loads(raw[start:end + 1])
    except json.JSONDecodeError:
        return None
    return obj if isinstance(obj, dict) else None


def parse_sampler_spec(raw: str, *, default_block: str = "claim") -> SamplerSpec | None:
    obj = _json_obj(raw)
    if obj is None:
        return None
    code = obj.get("sampler_code")
    if not isinstance(code, str) or not code.strip():
        return None
    block = obj.get("block") if isinstance(obj.get("block"), str) else default_block
    claim = obj.get("claim") if isinstance(obj.get("claim"), str) else ""
    return SamplerSpec(block=block.strip() or default_block,
                       claim=claim.strip(), sampler_code=code.strip() + "\n")


def generate_sampler_spec(claim_text: str, call_model: CallModel, *, block: str = "",
                          n: int | None = None, tol: float | None = None) -> SamplerSpec:
    prompt = build_sampler_prompt(claim_text, block=block, n=n, tol=tol)
    default_block = block or "claim"
    for _ in range(2):
        spec = parse_sampler_spec(call_model(prompt), default_block=default_block)
        if spec is not None:
            if block:
                spec.block = block
            return spec
    raise RuntimeError("sealed falsify sampler generation returned malformed JSON")


def _slug(value: str, default: str = "claim") -> str:
    value = re.sub(r"[^A-Za-z0-9_.-]+", "_", value).strip("._-")
    return value[:48] or default


def _metadata_suffix(spec: SamplerSpec) -> str:
    suffix = [
        "",
        "# Harness-supplied defaults; model code above may define these itself.",
        "try:",
        "    BLOCK",
        "except NameError:",
        f"    BLOCK = {spec.block!r}",
        "try:",
        "    CLAIM",
        "except NameError:",
        f"    CLAIM = {spec.claim!r}",
        "",
    ]
    return "\n".join(suffix)


def write_generated_sampler(spec: SamplerSpec, *, path: str | Path | None = None) -> Path:
    if path is None:
        DEFAULT_OUT.mkdir(parents=True, exist_ok=True)
        digest = hashlib.sha256(
            f"{spec.block}\n{spec.claim}\n{spec.sampler_code}".encode()
        ).hexdigest()[:10]
        path = DEFAULT_OUT / f"{_slug(spec.block)}_{digest}.py"
    out = Path(path)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(spec.sampler_code.rstrip() + _metadata_suffix(spec))
    return out
