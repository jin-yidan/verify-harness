from __future__ import annotations

import re

from harness.ingest import ingest_to_fixture

from ..backends.protocol import BackendBundle
from ..types import ResolvedInput


def ensure_theorem_input(value: ResolvedInput,
                         backend: BackendBundle) -> ResolvedInput:
    if value.statement.strip() and value.proof.strip():
        return value
    if value.target:
        fixture = ingest_to_fixture(
            value.target,
            theorem=value.theorem_selector or None,
            call_model=backend.call_model,
            selection_request=value.selection_request,
        )
        return ResolvedInput(
            statement=fixture.statement,
            proof=fixture.proof,
            claim=fixture.claim,
            source=fixture.source.source,
            target=value.target,
            name=fixture.name,
        )
    raise ValueError(
        "This workflow needs both a theorem statement and a proof sketch. "
        "Paste them with 'Theorem:' and 'Proof:', or reference a file/folder."
    )


def safe_run_name(name: str) -> str:
    name = re.sub(r"[^A-Za-z0-9_.-]+", "_", name).strip("._-")
    return name[:80] or "interactive"
