from __future__ import annotations

from rlverify.driver import DEFAULT_CORPUS
from rlverify.retriever import PremiseRetriever

from .backend_manager import BackendManager
from .types import (
    ExecutionStatus,
    Intent,
    MathStatus,
    ResolvedInput,
    ResultCard,
    RoutingDecision,
)
from .workflows import (
    run_check,
    resume_check,
    run_falsify,
    run_hypotheses,
    run_recheck,
    run_triage,
)


class VerifyController:
    def __init__(self, backends: BackendManager):
        self.backends = backends

    def execute(self, decision: RoutingDecision,
                value: ResolvedInput) -> ResultCard:
        intent = decision.intent
        if intent == Intent.RECHECK:
            return run_recheck(value)
        if intent == Intent.RETRIEVE:
            return self._retrieve(value)
        if intent == Intent.STATEMENT:
            return ResultCard(
                ExecutionStatus.COMPLETED,
                MathStatus.UNKNOWN,
                evidence=["NONE"],
                summary=(
                    "Statement-only formalization is not connected in this "
                    "prototype yet. No mathematical conclusion was drawn."
                ),
            )

        bundle = self.backends.bundle()
        if intent == Intent.FALSIFY:
            return run_falsify(value, bundle)
        if intent == Intent.HYPOTHESES:
            return run_hypotheses(value, bundle)
        if intent == Intent.TRIAGE:
            return run_triage(value, bundle)
        if intent == Intent.CHECK:
            if decision.forbids_full_check:
                return ResultCard(
                    ExecutionStatus.CANCELLED,
                    MathStatus.UNKNOWN,
                    summary=(
                        "Full verification was not started because the request "
                        "explicitly limited the scope."
                    ),
                )
            return run_check(value, bundle)
        return ResultCard(
            ExecutionStatus.CANCELLED,
            MathStatus.UNKNOWN,
            summary="Choose falsification, hypothesis checking, or full verification.",
        )

    def resume_check(self, state_dir: str, *, mode: str) -> ResultCard:
        return resume_check(
            state_dir,
            self.backends.bundle(),
            mode=mode,
        )

    def _retrieve(self, value: ResolvedInput) -> ResultCard:
        query = value.claim or value.statement or value.proof
        if not query.strip():
            return ResultCard(
                ExecutionStatus.SYSTEM_ERROR,
                MathStatus.UNKNOWN,
                summary="Provide a theorem description to search for.",
            )
        retriever = PremiseRetriever(str(DEFAULT_CORPUS))
        hits = retriever.hybrid_search(query, top_k=8)
        details = [
            f"{getattr(hit, 'id', '?')}: "
            f"{getattr(hit, 'statement', '')[:240]}"
            for hit in hits
        ]
        return ResultCard(
            ExecutionStatus.COMPLETED,
            MathStatus.UNKNOWN,
            evidence=["LIBRARY_INDEX"],
            summary=f"Found {len(details)} related formalized result(s).",
            details=details,
            actions=["Inspect one result", "Use a result in full verification"],
        )
