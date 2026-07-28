"""Structured report data for harness runs.

This module is intentionally presentation-light: verdict decisions stay in
``rlverify.verdict`` and renderers consume the dict built here.
"""
from __future__ import annotations

import glob
import json
import os
from pathlib import Path
from typing import Any

from rlverify import verdict as _verdict


def _runs_dir(out: dict) -> Path:
    return Path(out["corpus"]).parent / "runs"


def load_record(out: dict) -> dict:
    """Load the latest finished run record for ``out["fixture"]``.

    The timestamped driver file is ``<fixture>_20*.json``. Requiring the
    underscore before the timestamp avoids prefix collisions such as
    ``paper_3_1`` accidentally loading ``paper_3_10_...json``.
    """
    runs_dir = _runs_dir(out)
    recs = sorted(glob.glob(str(runs_dir / f"{out['fixture']}_20*.json")))
    if not recs:
        return {}
    path = Path(recs[-1])
    rec = json.loads(path.read_text())
    if isinstance(rec, dict):
        rec["_record_path"] = str(path)
    return rec if isinstance(rec, dict) else {}


def _reason_for(rec: dict, cls: str) -> str:
    reason = (rec.get("verdict_reason") or "").strip()
    if reason:
        return reason
    if cls.startswith("VERIFIED"):
        ax = ", ".join(rec.get("kernel_axioms", []))
        return f"kernel closure: {{{ax}}}" if ax else ""
    if cls == "UNVERIFIED/WRONG":
        refs = [r.get("block") or r.get("theorem") or "?"
                for r in rec.get("refutations", []) if r.get("kernel_backed")]
        if refs:
            return "kernel-backed refutation: " + ", ".join(refs)
        fals = [f.get("block") or "?"
                for f in rec.get("falsifications", [])
                if f.get("verdict") == "REFUTED"]
        if fals:
            return "falsification REFUTED: " + ", ".join(fals)
    if cls == "UNVERIFIED/PROOF_INVALID":
        return "a submitted proof inference was refuted; theorem truth is unknown"
    if cls == "UNVERIFIED/HYPOTHESIS_VIOLATION":
        return (
            "the submitted statement or proof omits a load-bearing hypothesis; "
            "no theorem counterexample was established"
        )
    if cls == "UNVERIFIED/MISMATCH":
        return "the formal statement does not faithfully match the submission"
    if rec.get("has_sorry_ax"):
        return "kernel closure contains sorryAx"
    return "; ".join(_verdict.gate_failures(rec))


def _main_artifact(rec: dict) -> dict | None:
    record_path = rec.get("_record_path")
    if not record_path or not rec.get("main_code"):
        return None
    path = str(Path(record_path).with_suffix(".lean"))
    return {"kind": "main_certificate", "label": "main certificate",
            "path": path, "reproduce": f"lake env lean {path}"}


def _structural_artifact(rec: dict) -> dict | None:
    path = rec.get("structural_artifact")
    if not path:
        return None
    return {
        "kind": "structural_proof",
        "label": "conditional structural proof",
        "path": path,
        "reproduce": f"lake env lean {path}",
    }


def _block_artifacts(rec: dict) -> list[dict]:
    artifacts: list[dict] = []
    seen: set[str] = set()
    for lemma in rec.get("lemmas") or []:
        path = lemma.get("artifact")
        if not path or path in seen:
            continue
        seen.add(path)
        artifacts.append({
            "kind": "block_certificate",
            "label": f"block certificate: {lemma.get('name') or '?'}",
            "path": path,
            "block": lemma.get("name", ""),
            "kernel_backed": bool(lemma.get("trusted_rechecked")),
            "reproduce": f"lake env lean {path}",
        })
    # Compatibility with records written before LemmaResult.artifact existed:
    # trusted recheck already retained content-addressed block source files.
    for block in (rec.get("trusted_recheck") or {}).get("blocks") or []:
        path = block.get("source_artifact")
        if not path or path in seen:
            continue
        seen.add(path)
        artifacts.append({
            "kind": "block_certificate",
            "label": f"block certificate: {block.get('block') or '?'}",
            "path": path,
            "block": block.get("block", ""),
            "kernel_backed": bool(block.get("trusted")),
            "reproduce": f"lake env lean {path}",
        })
    return artifacts


def _decomposition_rows(rec: dict) -> list[dict]:
    rows: list[dict] = []
    falsify = {
        item.get("block"): item.get("verdict", "")
        for item in rec.get("falsifications") or []
    }
    searches = {
        item.get("block"): item
        for item in rec.get("library_searches") or []
        if item.get("block")
    }
    for index, lemma in enumerate(rec.get("lemmas") or [], 1):
        kind = lemma.get("kind", "novel")
        if lemma.get("compiled"):
            state = "compiled"
        elif kind == "library" and not lemma.get("citation_invalid"):
            state = "library"
        elif lemma.get("skipped"):
            state = "skipped"
        elif lemma.get("citation_invalid"):
            state = "bad citation"
        else:
            state = "gap"
        rows.append({
            "index": index,
            "block": lemma.get("name", ""),
            "statement": lemma.get("statement", ""),
            "depends_on": lemma.get("depends_on") or [],
            "hypotheses": lemma.get("hypotheses") or [],
            "kind": kind,
            "match": lemma.get("library_match")
                     or lemma.get("named_result") or "",
            "match_statement": lemma.get("library_statement", ""),
            "source_file": lemma.get("library_source_file", ""),
            "source_line": lemma.get("library_source_line", 0),
            "import": lemma.get("library_import", ""),
            "found_in_repo": bool(lemma.get("library_found_in_repo")),
            "state": state,
            "falsification": falsify.get(lemma.get("name"), ""),
            "notes": lemma.get("note", ""),
            "near_match_adjudication": (
                lemma.get("near_match_adjudication", "")
            ),
            "anti_vacuity_checks": lemma.get("anti_vacuity_checks") or {},
            "discharge_attempts": int(
                lemma.get("discharge_attempts") or 0
            ),
            "artifact": lemma.get("artifact", ""),
            "type_search": searches.get(lemma.get("name"), {}),
        })
    return rows


def _refutation_artifacts(rec: dict) -> list[dict]:
    artifacts: list[dict] = []
    for ref in rec.get("refutations") or []:
        path = ref.get("artifact")
        if not path:
            continue
        artifacts.append({
            "kind": "refutation",
            "label": f"refutation: {ref.get('block') or ref.get('theorem') or '?'}",
            "path": path,
            "block": ref.get("block", ""),
            "kernel_backed": bool(ref.get("kernel_backed")),
            "target_scope": ref.get("target_scope", "UNSCOPED"),
            "finding_kind": ref.get("finding_kind", "UNCLASSIFIED"),
            "reproduce": f"lake env lean {path}",
        })
    return artifacts


def _step_certificate_artifacts(rec: dict) -> list[dict]:
    artifacts: list[dict] = []
    for cert in rec.get("step_certificates") or []:
        path = cert.get("artifact")
        if not path:
            continue
        artifacts.append({
            "kind": "step-certificate",
            "label": (
                f"positive step certificate: "
                f"{cert.get('block') or cert.get('theorem') or '?'}"
            ),
            "path": path,
            "block": cert.get("block", ""),
            "kernel_backed": bool(cert.get("kernel_backed")),
            "reproduce": f"lake env lean {path}",
        })
    return artifacts


def _triage_reconciliation(rec: dict) -> list[dict]:
    """Reconcile sealed triage with findings from the independent pipeline."""
    triage = rec.get("triage") or {}
    suspects = [
        row for row in triage.get("suspects") or []
        if isinstance(row, dict)
    ]
    preflight = rec.get("preflight") or {}
    confirmation = preflight.get("confirmation") or {}
    confirmation_status = str(confirmation.get("status") or "")
    rows: list[dict] = []
    for suspect in suspects:
        step = str(suspect.get("step", "?"))
        if confirmation_status.startswith("CONFIRMED_"):
            resolution = "CONFIRMED"
            evidence = str(confirmation.get("evidence") or "AUDIT")
        elif confirmation_status == "NOT_CONFIRMED":
            resolution = "CLEARED"
            evidence = str(confirmation.get("evidence") or "LEAN_KERNEL")
        else:
            resolution = "UNRESOLVED"
            evidence = "AUDIT"
        rows.append({
            "kind": "triage-suspect",
            "location": step,
            "finding": str(suspect.get("suspicion") or ""),
            "triage_flagged": True,
            "resolution": resolution,
            "evidence": evidence,
        })

    suspect_locations = {str(row.get("step", "?")) for row in suspects}
    hypothesis = rec.get("hypothesis_audit") or {}
    for finding in hypothesis.get("findings") or []:
        if not isinstance(finding, dict):
            continue
        outcome = str(finding.get("outcome") or "")
        if outcome == "CLEAR":
            continue
        location = str(finding.get("site") or "?")
        rows.append({
            "kind": "pipeline-finding",
            "location": location,
            "finding": (
                f"{outcome}: {finding.get('why', '')}"
            ).strip(),
            "triage_flagged": location in suspect_locations,
            "resolution": outcome or "UNCERTAIN",
            "evidence": "AUDIT",
        })
    for ref in rec.get("refutations") or []:
        if not isinstance(ref, dict) or not ref.get("kernel_backed"):
            continue
        rows.append({
            "kind": "pipeline-finding",
            "location": str(ref.get("block") or "?"),
            "finding": (
                f"{ref.get('target_scope', 'UNSCOPED')}/"
                f"{ref.get('finding_kind', 'UNCLASSIFIED')}"
            ),
            "triage_flagged": str(ref.get("block") or "?")
            in suspect_locations,
            "resolution": "CONFIRMED",
            "evidence": "LEAN_KERNEL",
        })
    for bt in rec.get("backtranslations") or []:
        if not isinstance(bt, dict) or bt.get("verdict") != "MISMATCH":
            continue
        location = str(bt.get("target") or "?")
        rows.append({
            "kind": "pipeline-finding",
            "location": location,
            "finding": f"statement MISMATCH: {bt.get('notes', '')}",
            "triage_flagged": location in suspect_locations,
            "resolution": "CONFIRMED",
            "evidence": "AUDIT",
        })
    if not rows and triage.get("all_clear"):
        rows.append({
            "kind": "coverage-signature",
            "location": "all",
            "finding": (
                "Triage was all-clear and the independent pipeline found no "
                "classified flaw."
            ),
            "triage_flagged": False,
            "resolution": "NO-FINDING",
            "evidence": "AUDIT",
        })
    return rows


def build_report(out: dict, rec: dict | None = None) -> dict[str, Any]:
    """Build the structured report object consumed by ANSI/Markdown renderers."""
    rec = rec or {}
    if not rec:
        lines = (out.get("verdict_line") or "").splitlines()
        cls = lines[0].replace("VERDICT:", "").strip() if lines else ""
        preflight = out.get("preflight") or {}
        confirmation = preflight.get("confirmation") or {}
        certificates = (
            confirmation.get("refutation_certificates")
            or confirmation.get("certificates")
            or []
        )
        positive_certificates = (
            confirmation.get("positive_certificates") or []
        )
        refutations = [
            {
                "block": cert.get("block", ""),
                "theorem": cert.get("theorem", ""),
                "description": cert.get("description", ""),
                "artifact": cert.get("artifact", ""),
                "kernel_backed": bool(cert.get("kernel_backed")),
                "target_scope": cert.get("target_scope", "UNSCOPED"),
                "finding_kind": cert.get("finding_kind", "UNCLASSIFIED"),
                "premises_satisfied": bool(cert.get("premises_satisfied")),
                "objects_well_defined": bool(
                    cert.get("objects_well_defined")),
                "conclusion_negated": bool(cert.get("conclusion_negated")),
                "statement_faithful": bool(cert.get("statement_faithful")),
            }
            for cert in certificates
            if isinstance(cert, dict)
        ]
        artifacts = [
            {
                "kind": "refutation",
                "label": f"refutation: {ref.get('block') or '?'}",
                "path": ref.get("artifact"),
                "block": ref.get("block", ""),
                "kernel_backed": bool(ref.get("kernel_backed")),
                "reproduce": f"lake env lean {ref.get('artifact')}",
            }
            for ref in refutations if ref.get("artifact")
        ]
        step_certificates = [
            {
                "block": cert.get("block", ""),
                "theorem": cert.get("theorem", ""),
                "description": cert.get("description", ""),
                "artifact": cert.get("artifact", ""),
                "kernel_backed": bool(cert.get("kernel_backed")),
            }
            for cert in positive_certificates
            if isinstance(cert, dict)
        ]
        artifacts.extend({
            "kind": "step-certificate",
            "label": (
                f"positive step certificate: "
                f"{cert.get('block') or '?'}"
            ),
            "path": cert.get("artifact"),
            "block": cert.get("block", ""),
            "kernel_backed": bool(cert.get("kernel_backed")),
            "reproduce": f"lake env lean {cert.get('artifact')}",
        } for cert in step_certificates if cert.get("artifact"))
        return {
            "name": out.get("fixture", ""),
            "verdict": {
                "class": cls,
                "reason": confirmation.get("detail", ""),
                "evidence": "none",
                "artifact_evidence": (
                    "kernel"
                    if any(ref.get("kernel_backed") for ref in refutations)
                    else "none"
                ),
                "gate_failures": [],
                "line": out.get("verdict_line", ""),
            },
            "formal": {},
            "gates": {},
            "preflight": preflight,
            "structural": out.get("structural") or {},
            "phase_telemetry": out.get("phase_telemetry") or {},
            "refutations": refutations,
            "step_certificates": step_certificates,
            "artifacts": artifacts,
            "cost": {"agent_usd": out.get("cost_usd"), "wall_s": out.get("wall_s"),
                     "sealed_gate_calls_metered": False},
            "provenance": {
                "sandbox": out.get("sandbox"),
                "corpus": out.get("corpus"),
                "record_path": "",
                "golden_workflows": out.get("golden_workflows") or {},
            },
        }

    cls = _verdict.verdict_class(rec)
    triage = rec.get("triage") or {}
    hypothesis_audit = rec.get("hypothesis_audit") or {}
    backtranslations = list(rec.get("backtranslations") or [])
    falsifications = list(rec.get("falsifications") or [])
    refutations = list(rec.get("refutations") or [])
    artifacts = [
        a for a in [_main_artifact(rec), _structural_artifact(rec)] if a
    ] + _block_artifacts(rec) + _refutation_artifacts(rec) + _step_certificate_artifacts(rec)
    decomposition = _decomposition_rows(rec)
    return {
        "name": rec.get("fixture") or out.get("fixture", ""),
        "verdict": {
            "class": cls,
            "reason": _reason_for(rec, cls),
            "evidence": _verdict.evidence_tier(rec),
            "artifact_evidence": _verdict.strongest_artifact_evidence(rec),
            "gate_failures": _verdict.gate_failures(rec),
            "line": out.get("verdict_line", ""),
        },
        "formal": {
            "statement": (rec.get("main_statement") or "").strip(),
            "proof": (rec.get("main_proof") or "").strip(),
            "compiled": bool(rec.get("compiled")),
            "compile_error": rec.get("compile_error", ""),
            "kernel_axioms": rec.get("kernel_axioms", []),
            "main_unformalizable": rec.get("main_unformalizable", ""),
            "proof_faithfulness": rec.get("proof_faithfulness", "unassessed"),
            "proof_faithfulness_detail": (
                rec.get("proof_faithfulness_detail") or []
            ),
            "proof_mapping": [
                {
                    "block": lemma.get("name", ""),
                    "source_excerpt": lemma.get("source_excerpt", ""),
                    "source_excerpt_sha256": (
                        lemma.get("source_excerpt_sha256", "")
                    ),
                    "source_excerpt_verified": bool(
                        lemma.get("source_excerpt_verified")),
                    "hypotheses": lemma.get("hypotheses") or [],
                    "depends_on": lemma.get("depends_on") or [],
                    "discharged": bool(lemma.get("discharged")),
                    "certificate_sha256": (
                        lemma.get("discharge_certificate_sha256", "")
                    ),
                    "trusted_rechecked": bool(lemma.get("trusted_rechecked")),
                }
                for lemma in rec.get("lemmas", [])
                if lemma.get("kind") in ("novel", "instantiation")
            ],
        },
        "decomposition": {
            "rows": decomposition,
            "total": len(decomposition),
            "library": sum(
                row["kind"] == "library" for row in decomposition
            ),
            "instantiation": sum(
                row["kind"] == "instantiation" for row in decomposition
            ),
            "novel": sum(
                row["kind"] == "novel" for row in decomposition
            ),
            "prior": sum(
                row["kind"] == "prior" for row in decomposition
            ),
        },
        "preflight": rec.get("preflight") or out.get("preflight") or {},
        "triage_reconciliation": _triage_reconciliation(rec),
        "invocation_audits": list(rec.get("invocation_audits") or []),
        "library_evaluations": list(rec.get("library_evaluations") or []),
        "axiom_lifecycle": list(rec.get("axiom_lifecycle") or []),
        "structural": {
            "mode": bool(rec.get("structural_mode")),
            "status": (
                "COMPILES MODULO PLACEHOLDERS"
                if (rec.get("structural_trusted_recheck") or {}).get("compiled")
                else "INCOMPLETE"
            ),
            "compiled": bool(
                (rec.get("structural_trusted_recheck") or {}).get("compiled")
            ),
            "placeholders": rec.get("structural_placeholders") or [],
            "independent_discharged": (
                rec.get("structural_independent_discharged") or []
            ),
            "error": rec.get("structural_error", ""),
            "trusted_recheck": rec.get("structural_trusted_recheck") or {},
        },
        "phase_telemetry": out.get("phase_telemetry") or {},
        "gates": {
            "triage": {
                "present": bool(triage),
                "all_clear": bool(triage.get("all_clear")),
                "suspect_count": len(triage.get("suspects") or []),
                "suspects": triage.get("suspects") or [],
                "executed_by": triage.get("executed_by", ""),
            },
            "hypothesis_audit": hypothesis_audit,
            "workflow": {
                "contract_version": rec.get("workflow_contract_version", 1),
                "sketch_verified": bool(rec.get("sketch_verified")),
                "sketch_expected_blocks": rec.get("sketch_expected_blocks", []),
                "active_nonlibrary_blocks": [
                    l.get("name", "")
                    for l in rec.get("lemmas", [])
                    if l.get("kind") in ("novel", "instantiation")
                    and not l.get("skipped")
                ],
                "discharge_order": rec.get("discharge_order", []),
                "dependencies": {
                    l.get("name", ""): l.get("depends_on", [])
                    for l in rec.get("lemmas", [])
                    if l.get("name")
                },
            },
            "backtranslations": backtranslations,
            "falsifications": falsifications,
            "falsification_summary": _verdict.falsify_summary(rec),
            "audit_warnings": rec.get("audit_warnings", []),
        },
        "refutations": refutations,
        "step_certificates": list(rec.get("step_certificates") or []),
        "artifacts": artifacts,
        "cost": {
            "agent_usd": out.get("cost_usd"),
            "wall_s": out.get("wall_s"),
            "sealed_gate_calls_metered": False,
        },
        "provenance": {
            "sandbox": out.get("sandbox"),
            "corpus": out.get("corpus"),
            "record_path": rec.get("_record_path", ""),
            "golden_workflows": (
                rec.get("workflow_provenance")
                or out.get("golden_workflows")
                or {}
            ),
        },
    }


def _md_escape_cell(value: object) -> str:
    return str(value).replace("|", "\\|").replace("\n", "<br>")


def _artifact_table(artifacts: list[dict]) -> str:
    if not artifacts:
        return "_No Lean artifact was saved._"
    rows = ["| Kind | Path | Reproduce |", "|---|---|---|"]
    for art in artifacts:
        rows.append("| "
                    + " | ".join([
                        _md_escape_cell(art.get("label") or art.get("kind") or ""),
                        _md_escape_cell(art.get("path") or ""),
                        _md_escape_cell(art.get("reproduce") or ""),
                    ])
                    + " |")
    return "\n".join(rows)


def _proof_mapping_table(rows_data: list[dict]) -> str:
    if not rows_data:
        return "_No submitted-proof block mapping was recorded._"
    rows = [
        "| Block | Submitted proof excerpt | Hypotheses | Dependencies | "
        "Discharge certificate | Trusted recheck |",
        "|---|---|---|---|---|---|",
    ]
    for item in rows_data:
        excerpt = item.get("source_excerpt") or ""
        rows.append("| " + " | ".join([
            _md_escape_cell(item.get("block", "")),
            _md_escape_cell(excerpt),
            _md_escape_cell(item.get("hypotheses") or []),
            _md_escape_cell(item.get("depends_on") or []),
            _md_escape_cell(item.get("certificate_sha256") or "—"),
            "yes" if item.get("trusted_rechecked") else "no",
        ]) + " |")
    return "\n".join(rows)


def _decomposition_table(data: dict) -> str:
    rows_data = data.get("rows") or []
    if not rows_data:
        return "_No decomposition was recorded._"
    rows = [
        "| # | Block | Statement | Depends on | Classification | "
        "Repository theorem / source | State | Artifact |",
        "|---:|---|---|---|---|---|---|---|",
    ]
    for item in rows_data:
        source = item.get("match") or "—"
        if item.get("source_file"):
            location = item["source_file"]
            if item.get("source_line"):
                location += f":{item['source_line']}"
            source += f"<br>{location}"
        if item.get("match_statement"):
            source += f"<br>{item['match_statement']}"
        type_search = item.get("type_search") or {}
        if type_search:
            if type_search.get("found"):
                found = (
                    type_search.get("suggestion")
                    or type_search.get("head_symbol")
                    or "proof found"
                )
                source += f"<br>type-directed: {found}"
            elif type_search.get("inconclusive"):
                source += "<br>type-directed: inconclusive"
            elif type_search.get("error"):
                source += "<br>type-directed: invalid statement"
            else:
                source += "<br>type-directed: no exact match"
        elif item.get("kind") == "novel":
            source += "<br>type-directed: not recorded"
        rows.append("| " + " | ".join([
            str(item.get("index", "")),
            _md_escape_cell(item.get("block", "")),
            _md_escape_cell(item.get("statement", "")),
            _md_escape_cell(item.get("depends_on") or []),
            _md_escape_cell(item.get("kind", "")),
            _md_escape_cell(source),
            _md_escape_cell(item.get("state", "")),
            _md_escape_cell(item.get("artifact", "") or "—"),
        ]) + " |")
    return "\n".join(rows)


def _gate_table(report: dict) -> str:
    gates = report.get("gates") or {}
    tri = gates.get("triage") or {}
    rows = ["| Gate | Outcome | Notes |", "|---|---|---|"]
    if tri.get("present"):
        outcome = "CLEAR" if tri.get("all_clear") else "SUSPECTS"
        rows.append(f"| Sealed triage | {outcome} | {tri.get('suspect_count', 0)} suspect(s); "
                    f"executed_by={_md_escape_cell(tri.get('executed_by', ''))} |")
    else:
        rows.append("| Sealed triage | MISSING | required gate record absent |")
    audit = gates.get("hypothesis_audit") or {}
    if audit:
        rows.append(
            f"| Sealed hypothesis audit | {_md_escape_cell(audit.get('overall', 'UNCERTAIN'))} | "
            f"{len(audit.get('findings') or [])} finding(s); "
            f"executed_by={_md_escape_cell(audit.get('executed_by', ''))}; "
            "prioritization-only |")
    workflow = gates.get("workflow") or {}
    if workflow.get("contract_version", 1) >= 2:
        active = workflow.get("active_nonlibrary_blocks") or []
        sketch_outcome = (
            "PASS" if workflow.get("sketch_verified")
            else ("NOT REQUIRED" if not active else "MISSING/FAILED")
        )
        rows.append(
            f"| Decomposition sketch | "
            f"{sketch_outcome} | "
            f"{len(workflow.get('sketch_expected_blocks') or [])} expected block(s) |")
        rows.append(
            f"| Per-block discharge | recorded | "
            f"order={_md_escape_cell(workflow.get('discharge_order') or [])} |")
    for bt in gates.get("backtranslations") or []:
        note = bt.get("notes") or bt.get("reason") or ""
        rows.append(f"| Back-translation `{_md_escape_cell(bt.get('target', '?'))}` | "
                    f"{_md_escape_cell(bt.get('verdict', '?'))} | {_md_escape_cell(note)} |")
    fs = gates.get("falsification_summary") or {}
    if fs.get("total", 0):
        counts = fs.get("counts") or {}
        rows.append("| Falsification | recorded | "
                    f"{counts.get('REFUTED', 0)} refuted / {counts.get('PASSED', 0)} passed / "
                    f"{counts.get('VACUOUS', 0)} vacuous / {counts.get('SKIPPED', 0)} skipped |")
    return "\n".join(rows)


def _triage_reconciliation_table(rows_data: list[dict]) -> str:
    if not rows_data:
        return "_No triage reconciliation data was recorded._"
    rows = [
        "| Source | Location | Finding | Flagged by triage | Resolution | Evidence |",
        "|---|---|---|---|---|---|",
    ]
    for item in rows_data:
        rows.append("| " + " | ".join([
            _md_escape_cell(item.get("kind", "")),
            _md_escape_cell(item.get("location", "")),
            _md_escape_cell(item.get("finding", "")),
            "yes" if item.get("triage_flagged") else "no",
            _md_escape_cell(item.get("resolution", "")),
            _md_escape_cell(item.get("evidence", "")),
        ]) + " |")
    return "\n".join(rows)


def render_markdown(report: dict, *, original_claim: str = "",
                    source: str = "CLI input", source_notes: list[str] | None = None,
                    generated_at: str = "") -> str:
    """Render a durable Markdown report from ``build_report`` output.

    ``source_notes`` carries ingestion provenance (e.g. `source: PDF text
    layer`) so a reader can tell extraction noise from a formalization defect.
    """
    verdict = report.get("verdict") or {}
    formal = report.get("formal") or {}
    prov = report.get("provenance") or {}
    cost = report.get("cost") or {}
    artifacts = report.get("saved_artifacts") or report.get("artifacts") or []
    title = report.get("name") or "run"
    lines = [
        f"# RLVerify Report: {title}",
        "",
        f"**Source:** {source}",
    ]
    for note in (source_notes or []):
        lines.append(f"**Source note:** {note}")
    if generated_at:
        lines.append(f"**Date:** {generated_at}")
    lines += [
        "",
        f"**Verdict:** `{verdict.get('class', '')}`",
        f"**Verdict evidence:** `{verdict.get('evidence', '')}`",
        f"**Strongest artifact evidence:** "
        f"`{verdict.get('artifact_evidence', verdict.get('evidence', ''))}`",
    ]
    if verdict.get("reason"):
        lines.append(f"**Reason:** {verdict['reason']}")
    lines += [
        "",
        "## Original Claim",
        "",
        original_claim.strip() or "_No original claim text was supplied._",
        "",
    ]
    decomposition = report.get("decomposition") or {}
    lines += [
        "## Decomposition and Repository Resolution",
        "",
        _decomposition_table(decomposition),
        "",
        f"- Total blocks: {decomposition.get('total', 0)}",
        f"- Library: {decomposition.get('library', 0)}",
        f"- Instantiation: {decomposition.get('instantiation', 0)}",
        f"- Novel: {decomposition.get('novel', 0)}",
    ]
    if decomposition.get("prior", 0):
        lines.append(f"- Prior paper components: {decomposition.get('prior', 0)}")
    lines.append("")
    preflight = report.get("preflight") or {}
    if preflight:
        lines += ["## Preflight Decision Gate", "",
                  f"- Status: `{preflight.get('status', '')}`",
                  f"- Evidence: `{preflight.get('evidence', 'AUDIT')}`",
                  f"- Weight: `{preflight.get('weight', 'prioritization-only')}`"]
        for finding in preflight.get("findings") or []:
            lines.append(
                f"- `{finding.get('source', '?')}` at "
                f"`{finding.get('location', '?')}` "
                f"[{finding.get('outcome', '?')}]: "
                f"{finding.get('detail', '')}"
            )
        lines.append("")
    structural = report.get("structural") or {}
    if structural.get("mode") or structural.get("compiled"):
        lines += [
            "## Conditional Structural Verification",
            "",
            f"- Status: `{structural.get('status', 'INCOMPLETE')}`",
            "- This is not theorem verification and can never yield `VERIFIED`.",
            f"- Named placeholders: `{structural.get('placeholders') or []}`",
            "- Independently discharged blocks: "
            f"`{structural.get('independent_discharged') or []}`",
        ]
        if structural.get("error"):
            lines.append(f"- Error: {structural['error']}")
        lines.append("")
    telemetry = report.get("phase_telemetry") or {}
    phases = telemetry.get("phases") or []
    if phases:
        lines += [
            "## Phase Telemetry",
            "",
            "| # | Phase | Status | New findings | Calls | Wall (s) | Cost (USD) |",
            "|---:|---|---|---:|---:|---:|---:|",
        ]
        for event in phases:
            cost_value = event.get("cost_usd")
            lines.append(
                f"| {event.get('sequence', '')} | "
                f"{_md_escape_cell(event.get('phase', ''))} | "
                f"{_md_escape_cell(event.get('status', ''))} | "
                f"{event.get('incremental_discoveries', 0)} | "
                f"{event.get('model_calls', 0)} | "
                f"{event.get('wall_s', 0)} | "
                f"{'' if cost_value is None else cost_value} |"
            )
        lines.append("")
    lines += [
        "## Formalization",
        "",
    ]
    if formal.get("statement"):
        lines += ["```lean", formal["statement"], "```", ""]
    else:
        lines += ["_No assembled Lean statement._", ""]
    if formal.get("proof"):
        lines += ["**Agent proof:**", "", "```lean", formal["proof"], "```", ""]
    lines += [
        f"**Proof relationship:** `{formal.get('proof_faithfulness', 'unassessed')}`",
    ]
    for detail in formal.get("proof_faithfulness_detail") or []:
        lines.append(f"- {detail}")
    lines += [
        "",
        "### Submitted proof-step mapping",
        "",
        _proof_mapping_table(formal.get("proof_mapping") or []),
        "",
    ]
    lines += [
        "## Harness Checks",
        "",
        _gate_table(report),
        "",
        "### Triage Reconciliation",
        "",
        _triage_reconciliation_table(
            report.get("triage_reconciliation") or []
        ),
        "",
    ]
    invocation_audits = report.get("invocation_audits") or []
    if invocation_audits:
        lines += [
            "### Invocation Hypothesis Audit",
            "",
            "| Caller | Invoked | Hypotheses | Checks | Outcome | Conditioning |",
            "|---|---|---|---|---|---|",
        ]
        for row in invocation_audits:
            lines.append("| " + " | ".join([
                _md_escape_cell(row.get("caller", "")),
                _md_escape_cell(row.get("invoked", "")),
                _md_escape_cell(row.get("hypotheses") or []),
                _md_escape_cell(row.get("checks") or []),
                _md_escape_cell(row.get("outcome", "")),
                _md_escape_cell(row.get("conditioning", "")),
            ]) + " |")
        lines.append("")
    library_evaluations = report.get("library_evaluations") or []
    if library_evaluations:
        lines += ["### Library-Growth Evaluation", ""]
        for row in library_evaluations:
            lines.append(
                f"- `{row.get('generalized_from') or row.get('name', '?')}`: "
                f"`{row.get('outcome', '')}` — {row.get('reason', '')}"
                + (
                    f"; back-translation="
                    f"`{row.get('backtranslation', '')}`"
                    if row.get("backtranslation") else ""
                )
                + (
                    f"; promotion={row.get('promotion_error', '')}"
                    if row.get("promotion_error") else ""
                )
            )
        lines.append("")
    axiom_lifecycle = report.get("axiom_lifecycle") or []
    if axiom_lifecycle:
        lines += ["### Custom Axiom Lifecycle", ""]
        for row in axiom_lifecycle:
            lines.append(
                f"- `{row.get('name', '?')}`: reference="
                f"`{row.get('reference', '')}`; backlog="
                f"`{row.get('backlog_entry', '')}`; hypotheses_checked="
                f"`{row.get('hypotheses_checked', False)}`; "
                f"backlog_verified=`{row.get('backlog_verified', False)}`; "
                f"back-translation=`{row.get('backtranslation', '')}`"
            )
        lines.append("")
    refutations = report.get("refutations") or []
    if refutations:
        lines += ["## Flaw / Refutation Evidence", ""]
        for ref in refutations:
            label = "kernel-backed" if ref.get("kernel_backed") else "audit-only"
            desc = ref.get("description") or ref.get("error") or ""
            lines.append(
                f"- `{ref.get('block', '?')}`: {label}; "
                f"scope=`{ref.get('target_scope', 'UNSCOPED')}`; "
                f"kind=`{ref.get('finding_kind', 'UNCLASSIFIED')}`"
                         + (f" - {desc}" if desc else ""))
        lines.append("")
    lines += [
        "## Artifacts",
        "",
        _artifact_table(artifacts),
        "",
        "## Cost And Provenance",
        "",
        f"- Agent cost: {cost.get('agent_usd') if cost.get('agent_usd') is not None else 'unavailable'}",
        f"- Wall time: {cost.get('wall_s') if cost.get('wall_s') is not None else 'unavailable'}",
        "- Sealed gate calls: not metered",
        f"- Sandbox: {prov.get('sandbox') or 'unknown'}",
        f"- Run record: {prov.get('saved_record') or prov.get('record_path') or 'unavailable'}",
    ]
    golden = prov.get("golden_workflows") or {}
    if golden:
        lines += ["", "### Golden workflow provenance", ""]
        for name, row in golden.items():
            lines.append(
                f"- `{name}`: `{row.get('path', '')}` · SHA-256 "
                f"`{row.get('sha256', '')}`"
            )
    return "\n".join(lines).rstrip() + "\n"


def render_terminal(report: dict) -> str:
    """Render terminal output from the same final report object as Markdown."""
    verdict = report.get("verdict") or {}
    decomposition = report.get("decomposition") or {}
    artifacts = report.get("saved_artifacts") or report.get("artifacts") or []
    lines = [
        f"RLVERIFY FINAL REPORT: {report.get('name') or 'run'}",
        f"VERDICT      {verdict.get('class', '')}",
        f"EVIDENCE     {verdict.get('evidence', '')}",
        f"ARTIFACT_EVIDENCE {verdict.get('artifact_evidence', '')}",
    ]
    if verdict.get("reason"):
        lines.append(f"REASON       {verdict['reason']}")
    lines += [
        "",
        "DECOMPOSITION AND REPOSITORY RESOLUTION",
        "# | block | statement | depends on | classification | "
        "repository theorem / source | state | artifact",
    ]
    rows = decomposition.get("rows") or []
    if not rows:
        lines.append("(none recorded)")
    for row in rows:
        source = row.get("match") or "—"
        if row.get("source_file"):
            source += f" @ {row['source_file']}"
            if row.get("source_line"):
                source += f":{row['source_line']}"
        lines.append(
            " | ".join([
                str(row.get("index", "")),
                str(row.get("block", "")),
                str(row.get("statement", "")).replace("\n", " "),
                str(row.get("depends_on") or []),
                str(row.get("kind", "")),
                str(source),
                str(row.get("state", "")),
                str(row.get("artifact", "") or "—"),
            ])
        )
    totals = (
        f"TOTALS       {decomposition.get('total', 0)} blocks; "
        f"{decomposition.get('library', 0)} library; "
        f"{decomposition.get('instantiation', 0)} instantiation; "
        f"{decomposition.get('novel', 0)} novel"
    )
    if decomposition.get("prior", 0):
        totals += f"; {decomposition.get('prior', 0)} prior"
    lines += ["", totals, "", "HARNESS CHECKS"]
    gates = report.get("gates") or {}
    triage = gates.get("triage") or {}
    lines.append(
        "Sealed triage: "
        + (
            ("CLEAR" if triage.get("all_clear") else "SUSPECTS")
            if triage.get("present") else "MISSING"
        )
        + f"; suspects={triage.get('suspect_count', 0)}"
    )
    audit = gates.get("hypothesis_audit") or {}
    lines.append(
        f"Hypothesis audit: {audit.get('overall', 'NOT RECORDED')}; "
        f"findings={len(audit.get('findings') or [])}"
    )
    for bt in gates.get("backtranslations") or []:
        lines.append(
            f"Back-translation {bt.get('target', '?')}: "
            f"{bt.get('verdict', '?')}"
        )
    lines += ["", "FINAL ARTIFACTS"]
    if not artifacts:
        lines.append("(none saved)")
    for artifact in artifacts:
        lines.append(
            f"{artifact.get('label') or artifact.get('kind')}: "
            f"{artifact.get('path', '')}"
        )
        if artifact.get("reproduce"):
            lines.append(f"  reproduce: {artifact['reproduce']}")
    provenance = report.get("provenance") or {}
    golden = provenance.get("golden_workflows") or {}
    if golden:
        lines += ["", "GOLDEN WORKFLOWS"]
        for name, row in golden.items():
            lines.append(
                f"{name}: {row.get('path', '')} sha256={row.get('sha256', '')}"
            )
    return "\n".join(lines).rstrip()


def render_triage_card(result: dict) -> str:
    suspects = result.get("suspects") or []
    if result.get("error"):
        outcome = "TRIAGE_ERROR"
    elif suspects:
        outcome = "SUSPECTS-FOUND"
    elif result.get("all_clear"):
        outcome = "ALL-CLEAR"
    else:
        outcome = "UNCERTAIN"
    lines = [
        "harness triage",
        f"OUTCOME      {outcome}",
        "EVIDENCE     audit-only",
        "WEIGHT       prioritization-only - not a verdict",
        f"EXECUTED_BY  {result.get('executed_by', 'harness')}",
    ]
    if result.get("error"):
        lines.append(f"ERROR        {result['error']}")
    if suspects:
        lines.append("SUSPECTS")
        for s in suspects:
            lines.append(f"- step {s.get('step', '?')} [{s.get('severity', '?')}]: "
                         f"{s.get('suspicion', '')}")
    else:
        lines.append("SUSPECTS     none")
    lines.append("NEXT         use this only to prioritize scrutiny; run `verify` for a verdict")
    return "\n".join(lines)


def render_audit_card(result: dict) -> str:
    findings = result.get("findings") or []
    overall = result.get("overall") or "UNCERTAIN"
    lines = [
        "harness audit",
        f"OUTCOME      {overall}",
        "EVIDENCE     audit-only",
        "WEIGHT       prioritization-only - not a verdict",
        f"EXECUTED_BY  {result.get('executed_by', 'harness')}",
        "PARTIAL      " + ("yes" if result.get("partial") else "no"),
    ]
    if result.get("reason"):
        lines.append(f"ERROR       {result['reason']}")
    if findings:
        lines.append("FINDINGS")
        for f in findings:
            outcome = f.get("outcome", "UNCERTAIN")
            why = f.get("why") or ("check by hand" if outcome == "UNCERTAIN" else "")
            missed = f.get("missed_hypothesis") or ""
            suffix = f"; missed hypothesis: {missed}" if missed else ""
            lines.append(f"- {f.get('site', '?')} -> {f.get('invoked', '?')} "
                         f"[{outcome}]: {why}{suffix}")
    else:
        lines.append("FINDINGS    none")
    if result.get("resolved"):
        lines.append("RESOLVED    " + ", ".join(result.get("resolved") or []))
    lines.append("NEXT         use this only to prioritize scrutiny; run `verify` for a verdict")
    return "\n".join(lines)


def render_falsify_card(report, *, seed: int = 0,
                        sampler_path: str | None = None) -> str:
    """Render the standalone falsify result without proof-verdict language."""
    from rlverify.falsify_run import render_card

    lines = []
    for line in render_card(report, seed=seed).splitlines():
        if report.verdict == "REFUTED" and line.startswith("NEXT"):
            lines.append("NEXT         block is wrong; skip its dependents")
        else:
            lines.append(line)
    if report.verdict == "REFUTED":
        if sampler_path:
            lines.append(f"RERUN        python3 -m harness falsify --sampler {sampler_path} "
                         f"--seed {seed} --n {report.instances} --trust-samplers")
        else:
            lines.append(f"RERUN        use the same sampler with --seed {seed}")
    elif report.verdict == "PASSED":
        lines.append("DETAIL       no counterexample found at this sampling depth; "
                     "evidence, not proof")
    elif report.verdict == "VACUOUS":
        lines.append("DETAIL       hypotheses were not exercised enough; the claim was "
                     "not actually tested")
    lines.append("VERDICT      none - standalone falsify is not full verification")
    return "\n".join(lines)
