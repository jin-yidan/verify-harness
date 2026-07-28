"""Plugin-facing MCP tools for Verify.

This is deliberately separate from :mod:`rlverify.mcp_server`.  The latter is
the low-level, ordered proof-construction session used by the trusted harness.
This module exposes product-level operations to Codex and Claude Code.
"""

from __future__ import annotations

import json
import hashlib
import os
import re
import signal
import subprocess
import sys
import tempfile
import time
import uuid
from pathlib import Path
from typing import Any

from harness.telemetry import events_after
from rlverify.driver import DEFAULT_CORPUS
from rlverify.retriever import PremiseRetriever

from .router import route


ENGINE_ROOT = Path(__file__).resolve().parents[1]
_SCOPES = {"triage", "hypotheses", "falsify", "full"}
_BACKENDS = {"codex", "claude"}
_REASONING_EFFORTS = {"low", "medium", "high", "xhigh"}
_SERVICE_TIERS = {"default", "priority"}
_PRODUCT_RUNS = ENGINE_ROOT / "rlverify-out" / ".product_runs"
_RUN_ID_RE = re.compile(r"^vr_[0-9a-f]{32}$")
_ROUTE_UI = {
    "falsify": (
        "Falsification",
        "Counterexample search only; no full verification.",
    ),
    "hypotheses": (
        "Hypothesis audit",
        "Assumptions and lemma applications only; no full verification.",
    ),
    "check": (
        "Full verification",
        "Trusted Lean verification, sealed gates, and kernel audit.",
    ),
    "statement": (
        "Statement audit",
        "Formal/intended statement match only; no proof verdict.",
    ),
    "retrieve": (
        "Library search",
        "Related formal results only; applicability is not yet established.",
    ),
    "recheck": (
        "Certificate recheck",
        "Recompile the supplied Lean artifact; do not reconstruct the proof.",
    ),
    "triage": (
        "Proof triage",
        "Adversarial prioritization only; no correctness verdict.",
    ),
}


def _safe_state_name(value: str) -> str:
    """Mirror the harness's state-name canonicalization at the product edge."""
    return re.sub(r"[^A-Za-z0-9_.-]+", "_", value).strip("._-")[:120] or "run"


def _json(value: dict[str, Any]) -> str:
    return json.dumps(value, indent=2, sort_keys=True)


def _input_hash(statement: str, proof: str, claim: str) -> str:
    return hashlib.sha256(
        "\0".join((statement, proof, claim)).encode()
    ).hexdigest()


def _generated_state_name(statement: str, proof: str, claim: str) -> str:
    return f"verify_{_input_hash(statement, proof, claim)[:12]}"


def _codex_config_defaults() -> dict[str, str]:
    """Read only capability-affecting Codex defaults.

    The isolated proof process deliberately ignores user configuration.  Unless
    these values are copied explicitly, a product run can silently use a
    different model/effort from the foreground Codex session.
    """
    configured = os.environ.get("CODEX_HOME")
    root = Path(configured).expanduser() if configured else Path.home() / ".codex"
    try:
        text = (root / "config.toml").read_text()
    except OSError:
        return {}
    values: dict[str, str] = {}
    for key in ("model", "model_reasoning_effort", "service_tier"):
        match = re.search(
            rf'(?m)^\s*{re.escape(key)}\s*=\s*"([^"\r\n]+)"\s*$',
            text,
        )
        if match:
            values[key] = match.group(1)
    return values


def _resolve_backend_options(
    backend: str,
    model: str,
    reasoning_effort: str,
    service_tier: str,
) -> tuple[str, str, str]:
    if backend != "codex":
        return model, "", ""
    defaults = _codex_config_defaults()
    return (
        model.strip() or defaults.get("model", ""),
        reasoning_effort.strip()
        or defaults.get("model_reasoning_effort", ""),
        service_tier.strip() or defaults.get("service_tier", ""),
    )


def _matching_saved_state(name: str, expected_hash: str) -> bool:
    path = ENGINE_ROOT / "rlverify-out" / ".state" / _safe_state_name(name)
    try:
        saved = json.loads((path / "input.json").read_text())
    except (OSError, ValueError, TypeError):
        return False
    return str(saved.get("input_hash") or "") == expected_hash


def route_request(request: str) -> dict[str, Any]:
    """Return the deterministic Verify route without starting any workflow."""
    decision = route(request)
    label, boundary = _ROUTE_UI.get(
        decision.intent.value,
        ("No verification route", "No Verify workflow has started."),
    )
    return {
        "intent": decision.intent.value,
        "confidence": decision.confidence,
        "reason": decision.reason,
        "forbids_full_check": decision.forbids_full_check,
        "receipt": {
            "title": f"Verify \u2192 {label}",
            "scope": boundary,
            "full_verification": (
                "awaiting confirmation"
                if decision.intent.value == "check"
                and not decision.forbids_full_check
                else "not started"
            ),
        },
    }


def search_library(query: str, limit: int = 8) -> dict[str, Any]:
    """Search the bundled formal corpus.  Retrieval is not proof."""
    if not query.strip():
        return {"execution": "SYSTEM_ERROR", "error": "query is empty"}
    top_k = max(1, min(int(limit), 25))
    retriever = PremiseRetriever(str(DEFAULT_CORPUS))
    hits = retriever.hybrid_search(query, top_k=top_k)
    return {
        "execution": "COMPLETED",
        "mathematics": "UNKNOWN",
        "evidence": "LIBRARY_INDEX",
        "note": "Related results are candidates, not verification.",
        "results": [
            {
                "id": hit.id,
                "statement": hit.statement,
                "source_file": hit.source_file,
                "source_line": hit.source_line,
                "status": hit.status,
                "score": hit.score,
            }
            for hit in hits
        ],
    }


def _input_args(
    command: list[str],
    *,
    target: str,
    statement: str,
    proof: str,
    claim: str,
    agent_context: str = "",
    staging_dir: Path | None = None,
) -> list[str]:
    if target.strip():
        command.append(target)
    for flag, name, value in (
        ("--statement", "statement.txt", statement),
        ("--proof", "proof.txt", proof),
        ("--claim", "claim.txt", claim),
        ("--agent-context", "agent-context.txt", agent_context),
    ):
        if not value.strip():
            continue
        if staging_dir is None:
            command.extend([flag, value])
            continue
        path = staging_dir / name
        path.write_text(value)
        path.chmod(0o600)
        if path.read_text() != value:
            raise OSError(
                f"input integrity failure while staging {name}; workflow not started"
            )
        command.extend([flag, str(path)])
    return command


def _last_json(text: str) -> dict[str, Any] | None:
    """Recover a JSON object when warnings precede the harness payload."""
    decoder = json.JSONDecoder()
    for index, char in enumerate(text):
        if char != "{":
            continue
        try:
            value, end = decoder.raw_decode(text[index:])
        except ValueError:
            continue
        if isinstance(value, dict) and not text[index + end :].strip():
            return value
    return None


def run_workflow(
    scope: str,
    *,
    target: str = "",
    statement: str = "",
    proof: str = "",
    claim: str = "",
    backend: str = "codex",
    model: str = "",
    reasoning_effort: str = "",
    service_tier: str = "",
    agent_budget_s: int = 1800,
    gate_timeout_s: int = 600,
    agent_context: str = "",
    confirmed: bool = False,
    timeout_s: int = 3600,
    resume_name: str = "",
    continue_structural: bool = False,
    continue_unresolved: bool = False,
) -> dict[str, Any]:
    """Run one trusted high-level workflow after explicit user confirmation.

    ``confirmed`` covers provider/token use.  For falsification it also covers
    local execution of the generated sampler.  A caller cannot request a scope
    outside the closed vocabulary, and a full run is never inferred here.
    """
    if scope not in _SCOPES:
        return {
            "execution": "SYSTEM_ERROR",
            "mathematics": "UNKNOWN",
            "error": f"scope must be one of {sorted(_SCOPES)}",
        }
    if backend not in _BACKENDS:
        return {
            "execution": "SYSTEM_ERROR",
            "mathematics": "UNKNOWN",
            "error": f"backend must be one of {sorted(_BACKENDS)}",
        }
    model, reasoning_effort, service_tier = _resolve_backend_options(
        backend, model, reasoning_effort, service_tier
    )
    if reasoning_effort and reasoning_effort not in _REASONING_EFFORTS:
        return {
            "execution": "SYSTEM_ERROR",
            "mathematics": "UNKNOWN",
            "error": (
                "reasoning_effort must be empty or one of "
                f"{sorted(_REASONING_EFFORTS)}"
            ),
        }
    if service_tier and service_tier not in _SERVICE_TIERS:
        return {
            "execution": "SYSTEM_ERROR",
            "mathematics": "UNKNOWN",
            "error": (
                "service_tier must be empty or one of "
                f"{sorted(_SERVICE_TIERS)}"
            ),
        }
    if (resume_name or continue_structural or continue_unresolved) and scope != "full":
        return {
            "execution": "SYSTEM_ERROR",
            "mathematics": "UNKNOWN",
            "error": (
                "resume_name and continuation modes are available only for "
                "scope='full'"
            ),
        }
    if continue_structural and continue_unresolved:
        return {
            "execution": "SYSTEM_ERROR",
            "mathematics": "UNKNOWN",
            "error": "choose either structural or unresolved-full continuation",
        }
    if (continue_structural or continue_unresolved) and not resume_name:
        return {
            "execution": "SYSTEM_ERROR",
            "mathematics": "UNKNOWN",
            "error": "continuation requires resume_name",
        }
    if not confirmed:
        return {
            "execution": "CANCELLED",
            "mathematics": "UNKNOWN",
            "confirmation_required": True,
            "scope": scope,
            "detail": (
                (
                    "Ask for a separate user confirmation after routing and "
                    "before starting Lean or spending provider tokens"
                    if scope == "full"
                    else "Ask the user before spending provider tokens"
                )
                + (
                    " and executing a generated Python sampler."
                    if scope == "falsify"
                    else "."
                )
            ),
        }
    if resume_name and any(
        value.strip() for value in (target, statement, proof, claim)
    ):
        return {
            "execution": "SYSTEM_ERROR",
            "mathematics": "UNKNOWN",
            "error": "resume_name loads saved input; do not also pass new input",
        }
    if not resume_name and not any(
        value.strip() for value in (target, statement, proof, claim)
    ):
        return {
            "execution": "SYSTEM_ERROR",
            "mathematics": "UNKNOWN",
            "error": "provide pasted math or a target path",
        }

    harness_command = {
        "triage": "triage",
        "hypotheses": "audit",
        "falsify": "falsify",
        "full": "verify",
    }[scope]
    generated_name = ""
    auto_resumed = False
    if scope == "full" and not resume_name and not target.strip():
        generated_name = _generated_state_name(statement, proof, claim)
        auto_resumed = _matching_saved_state(
            generated_name, _input_hash(statement, proof, claim)
        )
    with tempfile.TemporaryDirectory(prefix="verify_input_") as tmp:
        command = [
            sys.executable,
            "-m",
            "harness",
            harness_command,
        ]
        effective_resume = resume_name or (
            generated_name if auto_resumed else ""
        )
        if effective_resume:
            command.extend(["--resume", effective_resume])
            if agent_context.strip():
                context_path = Path(tmp) / "agent-context.txt"
                context_path.write_text(agent_context)
                context_path.chmod(0o600)
                command.extend(["--agent-context", str(context_path)])
        else:
            _input_args(
                command,
                target=target,
                statement=statement,
                proof=proof,
                claim=claim,
                agent_context=agent_context if scope == "full" else "",
                staging_dir=Path(tmp),
            )
            if generated_name:
                command.extend(["--name", generated_name])
        command.extend(["--backend", backend, "--json"])
        if model:
            command.extend(["--model", model])
        if reasoning_effort:
            command.extend(["--reasoning-effort", reasoning_effort])
        if service_tier:
            command.extend(["--service-tier", service_tier])
        command.extend([
            "--gate-timeout", str(max(30, min(int(gate_timeout_s), 3600))),
        ])
        if scope == "falsify":
            command.append("--trust-samplers")
        elif scope == "full":
            command.extend([
                "--report",
                "-y",
                "--budget",
                str(max(60, min(int(agent_budget_s), 14_400))),
            ])
            if continue_structural:
                command.append("--continue-structural")
            elif continue_unresolved:
                command.append("--continue-unresolved")

        try:
            proc = subprocess.run(
                command,
                cwd=ENGINE_ROOT,
                capture_output=True,
                text=True,
                timeout=max(30, min(int(timeout_s), 14_400)),
            )
        except subprocess.TimeoutExpired as exc:
            return {
                "execution": "TIMED_OUT",
                "mathematics": "UNKNOWN",
                "scope": scope,
                "detail": str(exc),
            }
        except OSError as exc:
            return {
                "execution": "SYSTEM_ERROR",
                "mathematics": "UNKNOWN",
                "scope": scope,
                "detail": str(exc),
            }

    stdout = proc.stdout.strip()
    stderr = proc.stderr.strip()
    payload = _last_json(stdout)
    execution = "COMPLETED" if proc.returncode in {0, 1} else "SYSTEM_ERROR"
    result: dict[str, Any] = {
        "execution": execution,
        "scope": scope,
        "returncode": proc.returncode,
        "backend": backend,
        "model": model,
        "reasoning_effort": reasoning_effort,
        "service_tier": service_tier,
        "auto_resumed": auto_resumed,
    }
    if payload is not None:
        result["result"] = payload
        verdict = payload.get("verdict") or {}
        verdict = verdict if isinstance(verdict, dict) else {}
        verdict_class = str(verdict.get("class") or "")
        evidence = str(verdict.get("evidence") or "none").upper()
        result["evidence"] = evidence
        if verdict_class == "UNVERIFIED/WRONG":
            result["mathematics"] = (
                "REFUTED"
                if evidence in {"KERNEL", "CERTIFICATE"}
                else "SUSPECTED"
            )
        elif verdict_class == "UNVERIFIED/PROOF_INVALID":
            result["mathematics"] = "PROOF_INVALID"
        elif verdict_class == "UNVERIFIED/HYPOTHESIS_VIOLATION":
            result["mathematics"] = "HYPOTHESIS_VIOLATION"
        elif verdict_class == "UNVERIFIED/MISMATCH":
            result["mathematics"] = "MISMATCH"
        elif verdict_class.startswith("VERIFIED/ALTERNATIVE-PROOF"):
            result["mathematics"] = "THEOREM_VERIFIED_ALTERNATIVE_PROOF"
        elif verdict_class.startswith("VERIFIED"):
            result["mathematics"] = "VERIFIED"
        elif verdict_class:
            result["mathematics"] = "INCOMPLETE"
        if payload.get("decision_required"):
            # Compatibility for records produced by an older engine. The
            # caller's one full-run confirmation already covers continuation;
            # do not instruct the agent to ask the user again.
            result["decision_required"] = False
            result["mathematics"] = "UNKNOWN"
            result["evidence"] = "AUDIT"
            result["next"] = (
                "Resume automatically under the existing full-run "
                "authorization. Use structural continuation for a confirmed "
                "fatal step and full continuation for an unresolved finding."
            )
    elif stdout:
        result["output"] = stdout[-12_000:]
    if stderr:
        result["diagnostics"] = stderr[-4_000:]
    if execution == "SYSTEM_ERROR":
        result["mathematics"] = "UNKNOWN"
    return result


def _product_run_dir(run_id: str) -> Path:
    """Resolve an opaque registered product run without path traversal."""
    if not _RUN_ID_RE.fullmatch(run_id):
        raise ValueError("invalid run_id")
    root = _PRODUCT_RUNS.resolve()
    path = (_PRODUCT_RUNS / run_id).resolve()
    if path.parent != root or not path.is_dir():
        raise ValueError("unknown run_id")
    return path


def _compact_terminal_product_run(
    run_dir: Path,
    result: dict[str, Any],
    metadata: dict[str, Any],
) -> dict[str, Any]:
    """Retain one self-contained terminal receipt and remove worker scratch."""
    final = dict(result)
    final["run_id"] = str(metadata.get("run_id") or run_dir.name)
    final["backend"] = str(
        final.get("backend") or metadata.get("backend") or ""
    )
    for key in ("model", "reasoning_effort", "service_tier"):
        final[key] = str(final.get(key) or metadata.get(key) or "")
    final["input_sha256"] = str(
        final.get("input_sha256") or metadata.get("input_sha256") or ""
    )
    tmp = run_dir / "result.final.json"
    tmp.write_text(json.dumps(final, indent=2, sort_keys=True) + "\n")
    tmp.replace(run_dir / "result.json")
    for name in (
        "request.json",
        "metadata.json",
        "worker.stdout",
        "worker.stderr",
    ):
        try:
            (run_dir / name).unlink()
        except FileNotFoundError:
            pass
    return final


def start_workflow(**request: Any) -> dict[str, Any]:
    """Launch a durable worker and return immediately with an opaque run ID."""
    if not request.get("confirmed"):
        return run_workflow(**request)
    scope = str(request.get("scope") or "")
    backend = str(request.get("backend") or "codex")
    if scope not in _SCOPES or backend not in _BACKENDS:
        return {
            "execution": "SYSTEM_ERROR",
            "mathematics": "UNKNOWN",
            "error": "invalid scope or backend",
        }
    resume_name = str(request.get("resume_name") or "")
    state_name = _safe_state_name(resume_name) if resume_name else ""
    if not state_name and scope == "full" and not str(
        request.get("target") or ""
    ).strip():
        state_name = _generated_state_name(
            str(request.get("statement") or ""),
            str(request.get("proof") or ""),
            str(request.get("claim") or ""),
        )
    state_root = (ENGINE_ROOT / "rlverify-out" / ".state").resolve()
    state_dir = (state_root / state_name).resolve() if state_name else None
    if state_dir is not None and state_dir.parent != state_root:
        return {
            "execution": "SYSTEM_ERROR",
            "mathematics": "UNKNOWN",
            "error": "invalid resume name",
        }
    _PRODUCT_RUNS.mkdir(parents=True, exist_ok=True)
    # Idempotent start: a connector retry must not launch a second token-
    # spending worker for the same durable mathematical state.
    if state_dir is not None:
        for meta_path in _PRODUCT_RUNS.glob("vr_*/metadata.json"):
            try:
                prior = json.loads(meta_path.read_text())
                prior_pid = int(prior.get("pid") or 0)
            except (OSError, ValueError, TypeError):
                continue
            if str(prior.get("state_dir") or "") != str(state_dir):
                continue
            if prior.get("backend") and prior.get("backend") != backend:
                return {
                    "execution": "SYSTEM_ERROR",
                    "mathematics": "UNKNOWN",
                    "error": (
                        "backend identity is immutable for a run; start a new "
                        f"run instead of resuming {prior.get('backend')} state "
                        f"with {backend}"
                    ),
                }
            prior_run_dir = meta_path.parent
            if (prior_run_dir / "result.json").exists():
                continue
            try:
                os.kill(prior_pid, 0)
            except (OSError, ProcessLookupError):
                continue
            return {
                "execution": "RUNNING",
                "mathematics": "UNKNOWN",
                "run_id": str(prior.get("run_id") or prior_run_dir.name),
                "next_sequence": 0,
                "reused_existing_worker": True,
            }
    run_id = f"vr_{uuid.uuid4().hex}"
    run_dir = _PRODUCT_RUNS / run_id
    run_dir.mkdir(mode=0o700)
    request_path = run_dir / "request.json"
    request_payload = json.dumps(request, indent=2, sort_keys=True) + "\n"
    request_path.write_text(request_payload)
    request_path.chmod(0o600)

    if state_dir is not None:
        for meta_path in _PRODUCT_RUNS.glob("vr_*/metadata.json"):
            try:
                prior = json.loads(meta_path.read_text())
            except (OSError, ValueError, TypeError):
                continue
            if (
                str(prior.get("state_dir") or "") == str(state_dir)
                and prior.get("backend")
                and prior.get("backend") != backend
            ):
                return {
                    "execution": "SYSTEM_ERROR",
                    "mathematics": "UNKNOWN",
                    "error": (
                        "backend identity is immutable for a run; start a new "
                        f"run instead of resuming {prior.get('backend')} state "
                        f"with {backend}"
                    ),
                }
    stdout_handle = (run_dir / "worker.stdout").open("w")
    stderr_handle = (run_dir / "worker.stderr").open("w")
    try:
        proc = subprocess.Popen(
            [sys.executable, "-m", "verify_app.worker", str(run_dir)],
            cwd=ENGINE_ROOT,
            stdin=subprocess.DEVNULL,
            stdout=stdout_handle,
            stderr=stderr_handle,
            start_new_session=True,
        )
    finally:
        stdout_handle.close()
        stderr_handle.close()
    metadata = {
        "run_id": run_id,
        "pid": proc.pid,
        "started_at_unix": time.time(),
        "state_dir": str(state_dir) if state_dir else "",
        "scope": scope,
        "backend": backend,
        "model": str(request.get("model") or ""),
        "reasoning_effort": str(request.get("reasoning_effort") or ""),
        "service_tier": str(request.get("service_tier") or ""),
        "agent_budget_s": int(request.get("agent_budget_s") or 1800),
        "request_sha256": hashlib.sha256(request_payload.encode()).hexdigest(),
        "input_sha256": hashlib.sha256(
            "\0".join(
                str(request.get(key) or "")
                for key in ("target", "statement", "proof", "claim")
            ).encode()
        ).hexdigest(),
    }
    (run_dir / "metadata.json").write_text(json.dumps(metadata, indent=2) + "\n")
    return {
        "execution": "RUNNING",
        "mathematics": "UNKNOWN",
        "run_id": run_id,
        "next_sequence": 0,
    }


def workflow_events(run_id: str, after_sequence: int = 0) -> dict[str, Any]:
    """Poll durable phase events; safe across MCP reconnects."""
    try:
        run_dir = _product_run_dir(run_id)
    except ValueError as exc:
        return {"execution": "SYSTEM_ERROR", "error": str(exc)}
    result_data: dict[str, Any] = {}
    if (run_dir / "result.json").exists():
        try:
            result_data = json.loads((run_dir / "result.json").read_text())
        except (OSError, ValueError, TypeError):
            result_data = {}
    try:
        metadata = json.loads((run_dir / "metadata.json").read_text())
    except (OSError, ValueError, TypeError):
        metadata = result_data
    state_dir = metadata.get("state_dir")
    payload = (
        events_after(state_dir, after_sequence)
        if state_dir and Path(state_dir).is_dir()
        else {
            "schema_version": 2,
            "after_sequence": max(0, int(after_sequence)),
            "next_sequence": max(0, int(after_sequence)),
            "events": [],
        }
    )
    terminal_execution = ""
    if result_data:
        terminal_execution = str(
            result_data.get("execution") or "COMPLETED"
        )
    payload.update({
        "execution": terminal_execution or "RUNNING",
        "run_id": run_id,
        "backend": metadata.get("backend", ""),
    })
    return payload


def workflow_result(run_id: str) -> dict[str, Any]:
    """Return the terminal result, or a nonblocking RUNNING receipt."""
    try:
        run_dir = _product_run_dir(run_id)
    except ValueError as exc:
        return {"execution": "SYSTEM_ERROR", "error": str(exc)}
    result_path = run_dir / "result.json"
    if result_path.exists():
        try:
            result = json.loads(result_path.read_text())
            try:
                metadata = json.loads(
                    (run_dir / "metadata.json").read_text()
                )
            except (OSError, ValueError, TypeError):
                metadata = result
            return _compact_terminal_product_run(
                run_dir, result, metadata
            )
        except (OSError, ValueError) as exc:
            return {"execution": "SYSTEM_ERROR", "error": str(exc)}
    metadata = json.loads((run_dir / "metadata.json").read_text())
    pid = int(metadata["pid"])
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        diagnostics = ""
        try:
            diagnostics = (run_dir / "worker.stderr").read_text()[-4000:]
        except OSError:
            pass
        return {
            "execution": "SYSTEM_ERROR",
            "mathematics": "UNKNOWN",
            "run_id": run_id,
            "error": "worker exited without a result",
            "diagnostics": diagnostics,
        }
    return {
        "execution": "RUNNING",
        "mathematics": "UNKNOWN",
        "run_id": run_id,
    }


def cancel_workflow(run_id: str) -> dict[str, Any]:
    """Cancel a running worker and its complete process group."""
    try:
        run_dir = _product_run_dir(run_id)
    except ValueError as exc:
        return {"execution": "SYSTEM_ERROR", "error": str(exc)}
    if (run_dir / "result.json").exists():
        return {"execution": "COMPLETED", "run_id": run_id}
    metadata = json.loads((run_dir / "metadata.json").read_text())
    pid = int(metadata["pid"])
    try:
        os.killpg(pid, signal.SIGTERM)
    except ProcessLookupError:
        pass
    # Give the worker's signal handler time to terminate independently
    # sessioned Codex/Claude children.  Only report cancellation after the
    # worker exits; otherwise token spend could continue behind a CANCELLED UI.
    deadline = time.monotonic() + 1.0
    alive = True
    while alive and time.monotonic() < deadline:
        try:
            waited, _ = os.waitpid(pid, os.WNOHANG)
            alive = waited == 0
        except ChildProcessError:
            try:
                os.kill(pid, 0)
            except ProcessLookupError:
                alive = False
        if alive:
            time.sleep(0.05)
    if alive:
        try:
            os.killpg(pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
    payload = {
        "execution": "CANCELLED",
        "mathematics": "UNKNOWN",
        "run_id": run_id,
    }
    (run_dir / "result.json").write_text(json.dumps(payload, indent=2) + "\n")
    return payload


def build_mcp():
    from mcp.server.fastmcp import FastMCP

    mcp = FastMCP("verify")

    @mcp.tool()
    def verify_route(request: str) -> str:
        """Choose the smallest Verify workflow for a natural-language request.
        This only routes; it never starts verification."""
        return _json(route_request(request))

    @mcp.tool()
    def verify_search_library(query: str, limit: int = 8) -> str:
        """Search the bundled Lean theorem corpus.  Hits are candidates, not
        proof and not a mathematical verdict."""
        return _json(search_library(query, limit))

    @mcp.tool()
    def verify_run(
        scope: str,
        target: str = "",
        statement: str = "",
        proof: str = "",
        claim: str = "",
        backend: str = "codex",
        model: str = "",
        reasoning_effort: str = "",
        service_tier: str = "",
        agent_budget_s: int = 1800,
        gate_timeout_s: int = 600,
        agent_context: str = "",
        confirmed: bool = False,
        timeout_s: int = 3600,
        resume_name: str = "",
        continue_structural: bool = False,
        continue_unresolved: bool = False,
    ) -> str:
        """Run exactly one scope: triage, hypotheses, falsify, or full.
        Pasted text is accepted directly. Set confirmed=true only after the
        user separately approves the routed scope and provider/token use (and
        sampler execution for falsify). For full verification, that one
        confirmation covers the entire Lean 4 attempt. Serious preflight
        findings select full or structural continuation automatically and do
        not create another user-confirmation pause. Resume options remain for
        interrupted legacy runs."""
        return _json(
            run_workflow(
                scope,
                target=target,
                statement=statement,
                proof=proof,
                claim=claim,
                backend=backend,
                model=model,
                reasoning_effort=reasoning_effort,
                service_tier=service_tier,
                agent_budget_s=agent_budget_s,
                gate_timeout_s=gate_timeout_s,
                agent_context=agent_context,
                confirmed=confirmed,
                timeout_s=timeout_s,
                resume_name=resume_name,
                continue_structural=continue_structural,
                continue_unresolved=continue_unresolved,
            )
        )

    @mcp.tool()
    def verify_start(
        scope: str,
        target: str = "",
        statement: str = "",
        proof: str = "",
        claim: str = "",
        backend: str = "codex",
        model: str = "",
        reasoning_effort: str = "",
        service_tier: str = "",
        agent_budget_s: int = 1800,
        gate_timeout_s: int = 600,
        agent_context: str = "",
        confirmed: bool = False,
        timeout_s: int = 3600,
        resume_name: str = "",
        continue_structural: bool = False,
        continue_unresolved: bool = False,
    ) -> str:
        """Start a durable workflow and return a run_id immediately."""
        return _json(start_workflow(
            scope=scope, target=target, statement=statement, proof=proof,
            claim=claim, backend=backend, model=model,
            reasoning_effort=reasoning_effort, service_tier=service_tier,
            agent_budget_s=agent_budget_s, gate_timeout_s=gate_timeout_s,
            agent_context=agent_context, confirmed=confirmed,
            timeout_s=timeout_s, resume_name=resume_name,
            continue_structural=continue_structural,
            continue_unresolved=continue_unresolved,
        ))

    @mcp.tool()
    def verify_events(run_id: str, after_sequence: int = 0) -> str:
        """Return completed phase events after a durable sequence cursor."""
        return _json(workflow_events(run_id, after_sequence))

    @mcp.tool()
    def verify_result(run_id: str) -> str:
        """Poll a durable workflow's terminal result without blocking."""
        return _json(workflow_result(run_id))

    @mcp.tool()
    def verify_cancel(run_id: str) -> str:
        """Cancel a durable workflow and its child process group."""
        return _json(cancel_workflow(run_id))

    return mcp


def main() -> None:
    build_mcp().run()


if __name__ == "__main__":
    main()
