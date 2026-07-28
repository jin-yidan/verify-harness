from __future__ import annotations

import json
import shutil
import time
from pathlib import Path

from harness.report import build_report, load_record, render_markdown
from harness.ingest import TheoremSelectionCancelled
from harness.runner import (
    AgentBudgetExceeded,
    RateLimited,
    _validated_input_json,
    run_verification,
)

from ..backends.protocol import BackendBundle, BackendError
from ..config import data_dir
from ..types import (
    ExecutionStatus,
    MathStatus,
    ProofStatus,
    ResolvedInput,
    ResultCard,
    StatementStatus,
    TheoremStatus,
)
from .common import ensure_theorem_input, safe_run_name


def run_check(value: ResolvedInput, backend: BackendBundle,
              *, resume: bool = False,
              state_dir: str | Path | None = None,
              continue_unresolved: bool = False,
              continue_structural: bool = False) -> ResultCard:
    started = time.monotonic()
    try:
        if resume:
            if state_dir is None:
                raise ValueError("resume requires a saved state directory")
            resolved, fixture, source_meta = _load_saved_input(Path(state_dir))
        else:
            resolved = ensure_theorem_input(value, backend)
            fixture = safe_run_name(resolved.name)
            state_dir = data_dir() / "state" / fixture
            source_meta = {
                "source": resolved.source,
                "product": "verify",
            }
        out = run_verification(
            fixture,
            resolved.statement,
            resolved.proof,
            call_model=backend.call_model,
            agent_drive=backend.agent_drive,
            nl_claim=(resolved.claim or resolved.statement),
            state_dir=state_dir,
            resume=resume,
            continue_unresolved=continue_unresolved,
            continue_structural=continue_structural,
            source_meta=source_meta,
        )
    except TheoremSelectionCancelled:
        return ResultCard(
            ExecutionStatus.CANCELLED,
            MathStatus.UNKNOWN,
            summary=(
                "Theorem selection was cancelled. No full-theorem Lean "
                "verification was started."
            ),
            elapsed_s=time.monotonic() - started,
            actions=["Submit the paper request again with a theorem label"],
        )
    except AgentBudgetExceeded as exc:
        return ResultCard(
            ExecutionStatus.TIMED_OUT,
            MathStatus.UNKNOWN,
            summary=str(exc),
            elapsed_s=time.monotonic() - started,
            actions=["Resume this run", "Inspect saved obligations"],
        )
    except RateLimited as exc:
        return ResultCard(
            ExecutionStatus.SYSTEM_ERROR,
            MathStatus.UNKNOWN,
            summary=f"Provider rate limit prevented completion: {exc}",
            elapsed_s=time.monotonic() - started,
            actions=["Try again later"],
        )
    except BackendError as exc:
        execution = (
            ExecutionStatus.TIMED_OUT
            if exc.category == "timeout"
            else ExecutionStatus.SYSTEM_ERROR
        )
        return ResultCard(
            execution,
            MathStatus.UNKNOWN,
            summary=str(exc),
            details=[f"Provider error category: {exc.category}"],
            elapsed_s=time.monotonic() - started,
            actions=["Check the backend connection", "Try another backend"],
        )
    except KeyboardInterrupt:
        return ResultCard(
            ExecutionStatus.CANCELLED,
            MathStatus.UNKNOWN,
            summary="The run was cancelled. Saved state was preserved.",
            elapsed_s=time.monotonic() - started,
            actions=["Resume this run"],
        )
    except Exception as exc:
        return ResultCard(
            ExecutionStatus.SYSTEM_ERROR,
            MathStatus.UNKNOWN,
            summary=f"Verify could not complete the run: {type(exc).__name__}: {exc}",
            elapsed_s=time.monotonic() - started,
        )

    return _result_card(
        out,
        resolved,
        started=started,
        state_dir=Path(state_dir) if state_dir is not None else None,
    )


def resume_check(state_dir: str | Path, backend: BackendBundle,
                 *, mode: str = "full") -> ResultCard:
    if mode not in {"full", "structural"}:
        raise ValueError("resume mode must be 'full' or 'structural'")
    return run_check(
        ResolvedInput(),
        backend,
        resume=True,
        state_dir=state_dir,
        continue_unresolved=(mode == "full"),
        continue_structural=(mode == "structural"),
    )


def _load_saved_input(state_dir: Path) -> tuple[ResolvedInput, str, dict]:
    path = state_dir / "input.json"
    if not path.exists():
        raise FileNotFoundError(f"saved verification input not found: {path}")
    value = json.loads(path.read_text())
    _validated_input_json(value, path)
    fixture = str(value.get("fixture") or "").strip()
    statement = str(value.get("statement") or "")
    proof = str(value.get("proof") or "")
    if not fixture or not statement or not proof:
        raise ValueError(f"saved verification input is incomplete: {path}")
    source_meta = value.get("source_meta")
    source_meta = source_meta if isinstance(source_meta, dict) else {}
    source = str(source_meta.get("source") or state_dir)
    return (
        ResolvedInput(
            statement=statement,
            proof=proof,
            claim=str(value.get("claim") or statement),
            source=source,
            name=fixture,
        ),
        fixture,
        source_meta,
    )


def _result_card(out: dict, resolved: ResolvedInput, *,
                 started: float, state_dir: Path | None) -> ResultCard:
    line = str(out.get("verdict_line") or "")
    paused = bool(out.get("paused"))
    rec = load_record(out)
    structured = build_report(out, rec)
    verdict = structured.get("verdict") or {}
    math, evidence = _map_verdict_class(
        str(verdict.get("class") or line),
        str(verdict.get("evidence") or "none"),
    )
    statement_status, theorem_status, proof_status = _status_axes(
        str(verdict.get("class") or line)
    )
    preflight = out.get("preflight") or {}
    if paused:
        preflight_evidence = str(preflight.get("evidence") or "AUDIT").upper()
        evidence = (
            ["LEAN_KERNEL"]
            if "KERNEL" in preflight_evidence
            else ["AUDIT"]
        )

    state = str(out.get("state_dir") or state_dir or "")
    artifacts = {"Saved state": state} if state and paused else {}
    details = (
        _preflight_details(preflight) + _phase_details(out)
        if paused else []
    )
    report_artifacts = _write_reports(
        out,
        resolved,
        state_dir=Path(state) if state else state_dir,
    )
    artifacts.update(report_artifacts)
    if not paused and state:
        state_path = Path(state).resolve()
        expected_parent = (data_dir() / "state").resolve()
        if state_path.parent == expected_parent and state_path.is_dir():
            shutil.rmtree(state_path)
            out["state_dir"] = None
            out["intermediates_cleaned"] = True

    if paused:
        status = str(preflight.get("status") or "UNRESOLVED")
        actions = (
            ["Continue structural verification", "Stop and keep saved state"]
            if status in {
                "CONFIRMED_THEOREM_REFUTATION",
                "CONFIRMED_PROOF_STEP_FAILURE",
                "CONFIRMED_WELL_DEFINEDNESS_GAP",
            }
            else [
                "Continue full Lean verification",
                "Continue structural verification",
                "Stop and keep saved state",
            ]
        )
    else:
        actions = _actions(math)
    return ResultCard(
        ExecutionStatus.PAUSED if paused else ExecutionStatus.COMPLETED,
        math,
        evidence=evidence,
        summary=line or "Verification completed without a readable verdict line.",
        details=details,
        elapsed_s=(
            float(out["wall_s"]) if out.get("wall_s") is not None
            else time.monotonic() - started
        ),
        cost_usd=out.get("cost_usd"),
        artifacts=artifacts,
        actions=actions,
        raw=out,
        statement_status=statement_status,
        theorem_status=theorem_status,
        proof_status=proof_status,
        evidence_by_claim={
            "top-level mathematical status": (
                evidence[0] if evidence else "NONE"
            ),
            "strongest artifact": str(
                verdict.get("artifact_evidence") or "none"
            ).upper(),
        },
    )


def _preflight_details(preflight: dict) -> list[str]:
    details: list[str] = []
    for finding in preflight.get("findings") or []:
        if not isinstance(finding, dict):
            continue
        details.append(
            f"{finding.get('source', 'audit')} · "
            f"{finding.get('location', '?')} "
            f"[{finding.get('outcome', 'SUSPECT')}]: "
            f"{finding.get('detail', '')}"
        )
        missed = str(finding.get("missed_hypothesis") or "").strip()
        if missed:
            details.append(f"  Missing/violated hypothesis: {missed}")
    confirmation = preflight.get("confirmation") or {}
    confirmation_detail = str(
        confirmation.get("detail") or preflight.get("detail") or ""
    ).strip()
    if confirmation_detail:
        details.append(f"Targeted confirmation: {confirmation_detail}")
    for certificate in (
        confirmation.get("refutation_certificates")
        or confirmation.get("certificates")
        or []
    ):
        if not isinstance(certificate, dict):
            continue
        details.append(
            "  Kernel certificate: "
            f"{certificate.get('block') or certificate.get('theorem') or '?'}"
            + (
                f" → {certificate.get('artifact')}"
                if certificate.get("artifact") else ""
            )
        )
    for rejected in confirmation.get("rejected_candidates") or []:
        if not isinstance(rejected, dict):
            continue
        details.append(
            "  Rejected confirmation candidate: "
            f"{rejected.get('block', '?')} — "
            f"{rejected.get('reason', 'no trusted certificate')}"
        )
    if confirmation.get("agent_error"):
        details.append(
            f"  Targeted confirmation agent error: "
            f"{confirmation['agent_error']}"
        )
    return details


def _phase_details(out: dict) -> list[str]:
    rows: list[str] = []
    telemetry = out.get("phase_telemetry") or {}
    for phase in telemetry.get("phases") or []:
        if not isinstance(phase, dict):
            continue
        bits = [
            f"status={phase.get('status', 'UNKNOWN')}",
            f"calls={phase.get('model_calls', 0)}",
            f"wall={phase.get('wall_s', 0)}s",
        ]
        if phase.get("cost_usd") is not None:
            bits.append(f"cost=${float(phase['cost_usd']):.4f}")
        detail = str(phase.get("detail") or "").strip()
        if detail:
            bits.append(detail)
        rows.append(
            f"Phase {phase.get('phase', '?')}: " + " · ".join(bits)
        )
    return rows


def _write_reports(out: dict, resolved: ResolvedInput,
                   *, state_dir: Path | None) -> dict[str, str]:
    if state_dir is None:
        return {}
    try:
        paused = bool(out.get("paused"))
        destination = (
            state_dir
            if paused else
            data_dir() / "results" / str(
                out.get("fixture") or resolved.name or state_dir.name
            )
        )
        destination.mkdir(parents=True, exist_ok=True)
        if paused:
            report = build_report(out, load_record(out))
        else:
            # Use the same final evidence copier and canonical report object as
            # the harness CLI before deleting resumable scratch.
            from harness.cli import _final_report_object, _save_artifacts

            saved = _save_artifacts(out, destination)
            report = _final_report_object(out, saved)
        json_path = destination / "verify-report.json"
        markdown_path = destination / "verify-report.md"
        json_path.write_text(
            json.dumps(report, indent=2, sort_keys=True) + "\n"
        )
        markdown_path.write_text(
            render_markdown(
                report,
                original_claim=(resolved.claim or resolved.statement),
                source=resolved.source,
            )
        )
        json_path.chmod(0o600)
        markdown_path.chmod(0o600)
        return {
            "Full report": str(markdown_path),
            "Structured report": str(json_path),
        }
    except Exception:
        # Report generation is presentation-only and must never change the
        # mathematical result or turn a completed run into a system failure.
        return {}


def _map_verdict_class(
    verdict_class: str, evidence_tier: str = "none"
) -> tuple[MathStatus, list[str]]:
    upper = verdict_class.upper()
    tier = evidence_tier.lower()
    kernel = tier == "kernel"
    certificate = tier == "certificate"
    evidence = (
        ["LEAN_KERNEL"] if kernel
        else ["INDEPENDENT_CERTIFICATE"] if certificate
        else ["AUDIT"]
    )
    if "VERIFIED/ALTERNATIVE-PROOF" in upper:
        return MathStatus.THEOREM_VERIFIED_ALTERNATIVE_PROOF, ["LEAN_KERNEL"]
    if "UNVERIFIED/SUSPECTED" in upper:
        return MathStatus.SUSPECTED, evidence
    if "UNVERIFIED/HYPOTHESIS_VIOLATION" in upper:
        return MathStatus.HYPOTHESIS_VIOLATION, evidence
    if "UNVERIFIED/PROOF_INVALID" in upper:
        return MathStatus.PROOF_INVALID, evidence
    if "UNVERIFIED/CIRCULAR" in upper:
        return MathStatus.SUSPECTED, evidence
    if "UNVERIFIED/MISMATCH" in upper:
        return MathStatus.SUSPECTED, evidence
    if "UNVERIFIED/WRONG" in upper:
        return (
            MathStatus.REFUTED
            if kernel or certificate
            else MathStatus.SUSPECTED,
            evidence,
        )
    if "UNVERIFIED" in upper or "HAS GAPS" in upper:
        return MathStatus.INCOMPLETE, evidence
    if "VERIFIED" in upper:
        return MathStatus.VERIFIED, ["LEAN_KERNEL"]
    return MathStatus.UNKNOWN, ["NONE"]


def _map_verdict(line: str) -> tuple[MathStatus, list[str]]:
    """Compatibility wrapper for callers that only have a legacy line."""
    upper = line.upper()
    evidence = (
        "kernel" if "KERNEL-BACKED" in upper or "EVIDENCE: KERNEL" in upper
        else "certificate" if "EVIDENCE: CERTIFICATE" in upper
        else "audit-only"
    )
    return _map_verdict_class(line, evidence)


def _status_axes(
    verdict_class: str,
) -> tuple[StatementStatus, TheoremStatus, ProofStatus]:
    upper = verdict_class.upper()
    if "VERIFIED/ALTERNATIVE-PROOF" in upper:
        return (
            StatementStatus.WELL_SPECIFIED,
            TheoremStatus.VERIFIED,
            ProofStatus.ALTERNATIVE_PROOF,
        )
    if "UNVERIFIED/WRONG" in upper:
        return (
            StatementStatus.WELL_SPECIFIED,
            TheoremStatus.REFUTED,
            ProofStatus.INVALID,
        )
    if "UNVERIFIED/PROOF_INVALID" in upper:
        return (
            StatementStatus.WELL_SPECIFIED,
            TheoremStatus.UNKNOWN,
            ProofStatus.INVALID,
        )
    if "UNVERIFIED/HYPOTHESIS_VIOLATION" in upper:
        return (
            StatementStatus.REQUIRES_RESTATEMENT,
            TheoremStatus.UNKNOWN,
            ProofStatus.INCOMPLETE,
        )
    if "UNVERIFIED/MISMATCH" in upper:
        return (
            StatementStatus.MISMATCH,
            TheoremStatus.UNKNOWN,
            ProofStatus.MISMATCH,
        )
    if upper.startswith("VERIFIED"):
        return (
            StatementStatus.WELL_SPECIFIED,
            TheoremStatus.VERIFIED,
            ProofStatus.VALID,
        )
    if "INCOMPLETE" in upper or "HAS GAPS" in upper:
        return (
            StatementStatus.UNKNOWN,
            TheoremStatus.UNKNOWN,
            ProofStatus.INCOMPLETE,
        )
    return (
        StatementStatus.UNKNOWN,
        TheoremStatus.UNKNOWN,
        ProofStatus.NOT_ASSESSED,
    )


def _actions(status: MathStatus) -> list[str]:
    if status == MathStatus.VERIFIED:
        return ["Recheck the Lean certificate", "Open the saved report"]
    if status == MathStatus.REFUTED:
        return ["Inspect the counterexample", "Check the hypotheses"]
    if status == MathStatus.PROOF_INVALID:
        return ["Inspect the invalid inference", "Seek an alternative proof"]
    if status == MathStatus.HYPOTHESIS_VIOLATION:
        return ["Restate the missing hypothesis", "Inspect the statement contract"]
    if status == MathStatus.SUSPECTED:
        return ["Independently recheck the finding", "Inspect the audit evidence"]
    if status == MathStatus.THEOREM_VERIFIED_ALTERNATIVE_PROOF:
        return ["Inspect the proof-faithfulness gaps", "Open the Lean certificate"]
    if status == MathStatus.INCOMPLETE:
        return ["Explain the remaining gap", "Resume verification"]
    return ["Inspect the evidence", "Try a focused subtool"]
