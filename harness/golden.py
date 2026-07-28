"""Canonical workflow loading for the RLVerify harness.

The human-maintained Claude commands are the product specification.  Harness,
MCP, plugin, and Codex surfaces may adapt *mechanics* (for example, replacing a
``VerifyDriver`` Python call with the corresponding MCP tool), but must not
maintain an independent copy of the mathematical workflow.
"""
from __future__ import annotations

from dataclasses import dataclass
import hashlib
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
GOLDEN_DIR = ROOT / ".claude" / "commands"

_FILES = {
    "audit-papers": "audit-papers.md",
    "expand-library": "expand-library.md",
    "extract-proofs": "extract-proofs.md",
    "formalize": "formalize.md",
    "verify-assemble": "verify-assemble.md",
    "verify-backtranslate": "verify-backtranslate.md",
    "verify-discharge": "verify-discharge.md",
    "verify-falsify": "verify-falsify.md",
    "verify-full-process": "verify-full-process.md",
    "verify-hypothesis-audit": "verify-hypothesis-audit.md",
    "verify-library": "verify-library.md",
    "verify-output-contract": "verify-output-contract.md",
    "verify-resolve": "verify-resolve.md",
    "verify-sketch": "verify-sketch.md",
    "verify-triage": "verify-triage.md",
    "verifyRL-paper": "verifyRL-paper.md",
}

_INTENT_COMMANDS = {
    "falsify": "verify-falsify",
    "hypotheses": "verify-hypothesis-audit",
    "check": "verify-full-process",
    "statement": "verify-backtranslate",
    "retrieve": "verify-resolve",
    "recheck": "verify-assemble",
    "triage": "verify-triage",
}

_REQUIRED_SECTIONS = {
    "verify-full-process": (
        "### Phase 0: Adversarial prose triage",
        "### Phase 1–2: Extract and Resolve",
        "#### Hypothesis Audit",
        "#### Falsification gate",
        "#### Sketch",
        "### Phase 3: Discharge Each Block",
        "#### Anti-vacuity checks",
        "#### Back-translation audit",
        "### Phase 4: Final Compile + Kernel Audit",
        "#### Axiom lifecycle",
        "### Phase 5: Library Growth",
        "### Phase 6: Verdict",
        "## Rules — Verification Integrity",
    ),
    "verifyRL-paper": (
        "## Execution Entry Point — Harness Only",
        "### Phase 0: Parse and Order",
        "#### Step 0.3: Identify Dependencies",
        "#### Step 0.4: Check for Circularity",
        "#### Step 0.5: Topological Sort",
        "#### Step 0.6: Paper-level sketch",
        "### Per-Component Verification",
        "### Phase 4: Assemble",
        "### Phase 5: Library Growth",
        "### Phase 6: Verdict and Report",
        "#### Structured paper record",
        "#### Terminal Output",
        "#### Write Report File",
        "## Rules — Verification Integrity",
    ),
}


@dataclass(frozen=True)
class GoldenWorkflow:
    name: str
    path: Path
    text: str
    sha256: str

    def provenance(self) -> dict[str, str]:
        return {
            "name": self.name,
            "path": str(self.path.relative_to(ROOT)),
            "sha256": self.sha256,
        }


def load_golden_workflow(name: str) -> GoldenWorkflow:
    """Load and validate one authoritative workflow."""
    try:
        filename = _FILES[name]
    except KeyError as exc:
        raise ValueError(f"unknown golden workflow: {name}") from exc
    path = GOLDEN_DIR / filename
    payload = path.read_bytes()
    text = payload.decode()
    missing = [
        section for section in _REQUIRED_SECTIONS.get(name, ())
        if section not in text
    ]
    if missing:
        raise RuntimeError(
            f"golden workflow {path} is missing required sections: {missing}"
        )
    return GoldenWorkflow(
        name=name,
        path=path,
        text=text,
        sha256=hashlib.sha256(payload).hexdigest(),
    )


def command_for_intent(intent: str) -> GoldenWorkflow | None:
    """Return the exact command specification selected by a product route."""
    name = _INTENT_COMMANDS.get(intent)
    return load_golden_workflow(name) if name else None


def golden_manifest(*names: str) -> dict[str, dict[str, str]]:
    selected = names or tuple(_FILES)
    return {
        name: load_golden_workflow(name).provenance()
        for name in selected
    }


def build_mcp_agent_instructions() -> str:
    """Embed the exact full-process specification plus its MCP binding.

    The short operational binding comes first so a fresh child immediately sees
    its available tools and terminal obligation. The golden command is still
    included verbatim and remains authoritative on every mathematical rule.
    """
    golden = load_golden_workflow("verify-full-process")
    adapter_path = ROOT / "harness" / "profile" / "verify-full-process.md"
    adapter = adapter_path.read_text()
    return (
        "# RLVerify proof-agent execution contract\n\n"
        "You are the proof-building child inside an already-authorized trusted "
        "harness run. Call `begin` first, use only the injected RLVerify MCP "
        "tools, preserve the submitted theorem and proof, and do not return "
        "until you reach one terminal tool path named in the binding below. "
        "The trusted parent—not you—runs sealed gates and finalizes the "
        "verdict.\n\n"
        "<harness-mcp-binding>\n"
        f"{adapter.rstrip()}\n"
        "</harness-mcp-binding>\n\n"
        "# Normative golden mathematical workflow\n\n"
        f"Golden source: `{golden.path.relative_to(ROOT)}`\n"
        f"Golden SHA-256: `{golden.sha256}`\n\n"
        "The embedded golden instructions below are normative for phase order, "
        "coverage, mathematical classifications, evidence, salvage, reporting, "
        "and integrity. The MCP binding after them changes execution mechanics "
        "only. If the binding and golden workflow differ semantically, follow "
        "the golden workflow and report the missing harness capability.\n\n"
        "<golden-workflow name=\"verify-full-process\">\n"
        f"{golden.text.rstrip()}\n"
        "</golden-workflow>\n"
    )
