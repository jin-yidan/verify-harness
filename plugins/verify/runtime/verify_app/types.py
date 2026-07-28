from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from pathlib import Path
from typing import Any


class Intent(str, Enum):
    FALSIFY = "falsify"
    HYPOTHESES = "hypotheses"
    CHECK = "check"
    STATEMENT = "statement"
    RETRIEVE = "retrieve"
    RECHECK = "recheck"
    TRIAGE = "triage"
    RUNS = "runs"
    RESUME = "resume"
    SETTINGS = "settings"
    HELP = "help"
    QUIT = "quit"
    UNKNOWN = "unknown"


class ExecutionStatus(str, Enum):
    COMPLETED = "COMPLETED"
    PAUSED = "PAUSED"
    TIMED_OUT = "TIMED_OUT"
    SYSTEM_ERROR = "SYSTEM_ERROR"
    CANCELLED = "CANCELLED"


class MathStatus(str, Enum):
    VERIFIED = "VERIFIED"
    THEOREM_VERIFIED_ALTERNATIVE_PROOF = "THEOREM_VERIFIED_ALTERNATIVE_PROOF"
    REFUTED = "REFUTED"
    SUSPECTED = "SUSPECTED"
    INCOMPLETE = "INCOMPLETE"
    MISMATCH = "MISMATCH"
    HYPOTHESIS_VIOLATION = "HYPOTHESIS_VIOLATION"
    PROOF_INVALID = "PROOF_INVALID"
    CIRCULAR = "CIRCULAR"
    NO_COUNTEREXAMPLE = "NO_COUNTEREXAMPLE"
    UNKNOWN = "UNKNOWN"


class StatementStatus(str, Enum):
    WELL_SPECIFIED = "WELL_SPECIFIED"
    REQUIRES_RESTATEMENT = "REQUIRES_RESTATEMENT"
    MISMATCH = "MISMATCH"
    UNKNOWN = "UNKNOWN"


class TheoremStatus(str, Enum):
    VERIFIED = "VERIFIED"
    REFUTED = "REFUTED"
    UNKNOWN = "UNKNOWN"


class ProofStatus(str, Enum):
    VALID = "VALID"
    ALTERNATIVE_PROOF = "ALTERNATIVE_PROOF"
    INVALID = "INVALID"
    INCOMPLETE = "INCOMPLETE"
    MISMATCH = "MISMATCH"
    NOT_ASSESSED = "NOT_ASSESSED"


@dataclass(frozen=True)
class RoutingDecision:
    intent: Intent
    confidence: float
    reason: str
    forbids_full_check: bool = False


@dataclass
class ResolvedInput:
    statement: str = ""
    proof: str = ""
    claim: str = ""
    source: str = "pasted text"
    target: str | None = None
    theorem_selector: str = ""
    selection_request: str = ""
    name: str = "interactive"

    @property
    def has_math(self) -> bool:
        return bool(self.statement.strip() or self.proof.strip() or self.claim.strip())


@dataclass
class ResultCard:
    execution: ExecutionStatus
    mathematics: MathStatus
    evidence: list[str] = field(default_factory=list)
    summary: str = ""
    details: list[str] = field(default_factory=list)
    actions: list[str] = field(default_factory=list)
    artifacts: dict[str, str] = field(default_factory=dict)
    elapsed_s: float | None = None
    cost_usd: float | None = None
    raw: dict[str, Any] = field(default_factory=dict)
    statement_status: StatementStatus = StatementStatus.UNKNOWN
    theorem_status: TheoremStatus = TheoremStatus.UNKNOWN
    proof_status: ProofStatus = ProofStatus.NOT_ASSESSED
    evidence_by_claim: dict[str, str] = field(default_factory=dict)


@dataclass(frozen=True)
class ProgressEvent:
    phase: str
    message: str
    elapsed_s: float | None = None


@dataclass
class RunRecord:
    run_id: str
    intent: Intent
    source: str
    result: ResultCard
    created_at: str
    report_path: Path | None = None
