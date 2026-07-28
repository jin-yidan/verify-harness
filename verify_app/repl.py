from __future__ import annotations

import json
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path

from prompt_toolkit import PromptSession
from prompt_toolkit.history import FileHistory

from .backend_manager import BackendManager
from .config import AppConfig, ConfigStore, data_dir
from .controller import VerifyController
from .credentials import CredentialError, CredentialStore
from .history import HistoryStore
from .inputs import parse_pasted_math, resolve_from_message
from .onboarding import interactive_setup
from .render import HELP_TEXT, render_card
from .router import route
from .types import ExecutionStatus, Intent, ResolvedInput, ResultCard


@dataclass
class ConversationState:
    current_input: ResolvedInput | None = None
    last_result: ResultCard | None = None
    last_intent: Intent | None = None
    transcript: list[tuple[str, str]] = field(default_factory=list)
    active_run: dict | None = None


class VerifyREPL:
    def __init__(
        self,
        config_store: ConfigStore,
        credentials: CredentialStore,
        config: AppConfig,
        *,
        prompt_session: PromptSession | None = None,
        history_store: HistoryStore | None = None,
        output=print,
    ):
        self.config_store = config_store
        self.credentials = credentials
        self.config = config
        self.output = output
        self.session = prompt_session or PromptSession(
            history=FileHistory(str(data_dir() / "conversation-history.txt")),
        )
        self.backends = BackendManager(config, credentials)
        self.controller = VerifyController(self.backends)
        self.history = history_store or HistoryStore()
        self.session_state_path = self.history.path.with_name(
            "conversation-session.json"
        )
        self._pending_intent: Intent | None = None
        self.conversation = ConversationState()
        self._restore_session()

    def run(self) -> int:
        self.output(
            "\nVerify is ready. Tell me what you are working on, paste a proof, "
            "or reference @file.\n"
        )
        while True:
            try:
                message = self.session.prompt("Verify> ").strip()
            except EOFError:
                self.output("")
                return 0
            except KeyboardInterrupt:
                self.output("\nNo active request. Type /quit to leave Verify.")
                continue
            if not message:
                continue
            if not self.handle(message):
                return 0

    def handle(self, message: str) -> bool:
        self.conversation.transcript.append(("user", message))
        decision = route(message)
        if decision.intent == Intent.QUIT:
            self.backends.close()
            self.output("Goodbye.")
            return False
        if decision.intent == Intent.HELP:
            self.output(HELP_TEXT)
            return True
        if decision.intent == Intent.SETTINGS:
            self._settings()
            return True
        if decision.intent == Intent.RUNS:
            self._show_runs()
            return True
        if decision.intent == Intent.RESUME:
            self._offer_continuation(show_evidence=True)
            return True

        requested_mode = _continuation_mode(message)
        if requested_mode and self.conversation.active_run is not None:
            self._continue_active(requested_mode)
            return True
        if (
            self.conversation.active_run is not None
            and _is_pause_question(message)
        ):
            self._explain_active_pause()
            return True

        try:
            value = resolve_from_message(message)
        except (FileNotFoundError, ValueError) as exc:
            self._say(f"I could not open that input: {exc}")
            return True

        if decision.intent == Intent.UNKNOWN:
            if self._pending_intent is not None:
                decision = route(f"/{self._pending_intent.value}")
                value = value or parse_pasted_math(message)
                self._pending_intent = None
            elif value is not None and (value.has_math or value.target):
                self.conversation.current_input = value
                self._say(
                    "I have that as the current proof. Tell me what you want "
                    "to do with it—for example, try to falsify it, inspect its "
                    "hypotheses, or fully verify it."
                )
                return True
            elif self.conversation.last_result is not None:
                self._answer_followup(message)
                return True
            elif message.strip().lower() in {
                "hi", "hello", "hey", "hello verify", "hi verify",
            }:
                self._say(
                    "Hi. Paste a theorem or proof, point me to @file, or tell "
                    "me what mathematical claim you want to investigate."
                )
                return True
            else:
                self._say(
                    "I can work with a theorem, proof sketch, or formalization. "
                    "Paste it or reference @file, then tell me what you want to "
                    "find out."
                )
                return True

        if value is None and self.conversation.current_input is not None:
            value = self.conversation.current_input

        if value is None or not (value.has_math or value.target):
            self._pending_intent = decision.intent
            self._say(
                "Show me the theorem or proof you mean. You can paste it now "
                "or reference @file or @folder."
            )
            return True

        self.conversation.current_input = value

        if decision.intent == Intent.CHECK:
            self._say(
                "Verify → Full verification\n"
                "Full verification: awaiting confirmation\n\n"
                "No Lean verification has started."
            )
            answer = self.session.prompt(
                "Full verification may take several minutes and use your "
                "configured backend. Start? [Y/n] "
            ).strip().lower()
            if answer not in {"", "y", "yes"}:
                self._say("Full verification was not started.")
                return True

        try:
            card = self.controller.execute(decision, value)
        except KeyboardInterrupt:
            self.output(
                "\nThe active request was cancelled. Any saved verification "
                "state was preserved."
            )
            return True
        rendered = render_card(card)
        self._say("\n" + rendered + "\n")
        self.conversation.last_result = card
        self.conversation.last_intent = decision.intent
        self._record(decision.intent, value, card)
        if card.raw.get("paused"):
            self._remember_pause(card)
            self._offer_continuation()
        elif decision.intent == Intent.CHECK:
            self._clear_active_run()
        return True

    def _answer_followup(self, message: str) -> None:
        result = self.conversation.last_result
        value = self.conversation.current_input
        if result is None:
            self._say("There is no result in this conversation to discuss yet.")
            return
        if result.raw.get("paused"):
            self._explain_active_pause()
            return
        prompt = (
            "You are the conversational explanation layer for Verify, a "
            "Lean-backed mathematical verification tool. Answer the user's "
            "follow-up briefly and precisely. Treat the recorded result as "
            "authoritative. Never upgrade UNKNOWN, NO_COUNTEREXAMPLE, an audit, "
            "or an incomplete run to VERIFIED. Only a recorded VERIFIED result "
            "with LEAN_KERNEL evidence may be described as verified. Format "
            "all mathematical notation in Markdown-compatible LaTeX: use "
            "\\(...\\) inline and \\[...\\] for display math. Keep status "
            "tokens, prose, file paths, and Lean source outside math "
            "delimiters.\n\n"
            f"Current source: {value.source if value else 'unknown'}\n"
            f"Current statement: {(value.statement or value.claim) if value else ''}\n"
            f"Current proof: {value.proof if value else ''}\n\n"
            f"Recorded result:\n{render_card(result)}\n\n"
            "Complete preflight evidence:\n"
            f"{json.dumps(result.raw.get('preflight') or {}, indent=2)}\n\n"
            f"User follow-up: {message}"
        )
        try:
            answer = self.backends.bundle(timeout_s=180).call_model(prompt)
        except Exception as exc:
            self._say(
                "I could not ask the reasoning backend to explain that result "
                f"({type(exc).__name__}: {exc}). The recorded result itself "
                "has not changed."
            )
            return
        self._say(answer.strip() or "The backend returned no explanation.")

    def _say(self, message: str) -> None:
        self.output(message)
        self.conversation.transcript.append(("assistant", message))

    def _settings(self) -> None:
        cfg = self.config.backends.get(self.config.default_backend)
        if cfg:
            self.output(
                f"Backend: {cfg.name}\n"
                f"Type: {cfg.kind}\n"
                f"Model: {cfg.model or 'provider default'}"
            )
        answer = self.session.prompt("Change backend? [y/N] ").strip().lower()
        if answer in {"y", "yes"}:
            self.backends.close()
            try:
                self.config = interactive_setup(
                    self.config_store,
                    self.credentials,
                    input_fn=lambda prompt: self.session.prompt(prompt),
                    output=self.output,
                )
            except (CredentialError, ValueError) as exc:
                self.output(
                    f"Backend setup was not changed: {exc}\n"
                    "Run /settings to try again."
                )
                return
            self.backends = BackendManager(self.config, self.credentials)
            self.controller = VerifyController(self.backends)

    def _show_runs(self) -> None:
        rows = self.history.recent()
        if not rows:
            self.output("No conversational runs have been recorded yet.")
            return
        for row in rows:
            state = row.get("state_dir") or (
                (row.get("artifacts") or {}).get("Saved state")
            )
            suffix = f" · state={state}" if state else ""
            self.output(
                f"{row.get('created_at', '?')} · {row.get('intent', '?')} · "
                f"{row.get('execution', '?')} · "
                f"{row.get('mathematics', '?')} · {row.get('source', '?')}"
                f"{suffix}"
            )

    def _record(self, intent: Intent, value: ResolvedInput, card) -> None:
        self.history.append({
            "created_at": datetime.now(timezone.utc).isoformat(),
            "intent": intent.value,
            "source": value.source,
            "execution": card.execution.value,
            "mathematics": card.mathematics.value,
            "summary": card.summary,
            "artifacts": card.artifacts,
            "paused": bool(card.raw.get("paused")),
            "run_name": card.raw.get("fixture"),
            "state_dir": card.raw.get("state_dir"),
        })

    def _remember_pause(self, card: ResultCard) -> None:
        state_dir = str(card.raw.get("state_dir") or "")
        fixture = str(card.raw.get("fixture") or "")
        if not state_dir or not fixture:
            return
        self.conversation.active_run = {
            "fixture": fixture,
            "state_dir": state_dir,
            "preflight_status": (
                (card.raw.get("preflight") or {}).get("status")
                or "UNRESOLVED"
            ),
            "updated_at": datetime.now(timezone.utc).isoformat(),
        }
        self._persist_session()

    def _clear_active_run(self) -> None:
        self.conversation.active_run = None
        self._persist_session()

    def _offer_continuation(self, *, show_evidence: bool = False) -> None:
        active = self.conversation.active_run
        if not active:
            self._say(
                "There is no paused verification in this session. Use /runs "
                "to inspect earlier saved results."
            )
            return
        if show_evidence:
            self._show_active_preflight(active)
        status = str(active.get("preflight_status") or "UNRESOLVED")
        self._say(
            "\nThe full-theorem Lean phase is paused. Targeted checking may "
            "already have compiled local certificates, but no complete theorem "
            "certificate has been attempted yet."
        )
        if status in {
            "CONFIRMED_THEOREM_REFUTATION",
            "CONFIRMED_PROOF_STEP_FAILURE",
            "CONFIRMED_WELL_DEFINEDNESS_GAP",
        }:
            self.output(
                "Choose the next action:\n"
                "  1. Continue structurally with the confirmed failed step as "
                "a named placeholder\n"
                "  2. Stop and keep the saved state"
            )
            answer = self.session.prompt("\n> ").strip().lower()
            if answer in {"1", "structural", "continue structural"}:
                self._continue_active("structural")
            else:
                self._say(
                    "Stopped. The saved state remains available through /resume."
                )
            return

        self.output(
            "Choose the next action:\n"
            "  1. Continue full Lean verification despite the unresolved finding\n"
            "  2. Continue structurally with a named placeholder\n"
            "  3. Stop and keep the saved state"
        )
        answer = self.session.prompt("\n> ").strip().lower()
        if answer in {"1", "full", "continue full", "authorize anyway"}:
            self._continue_active("full")
        elif answer in {"2", "structural", "continue structural"}:
            self._continue_active("structural")
        else:
            self._say(
                "Stopped. The saved state remains available through /resume."
            )

    def _show_active_preflight(self, active: dict) -> None:
        state_dir = Path(str(active.get("state_dir") or ""))
        try:
            preflight = json.loads(
                (state_dir / "preflight.json").read_text()
            )
        except (OSError, ValueError, TypeError):
            preflight = {}
        self.output("\nSaved preflight evidence:")
        findings = preflight.get("findings") or []
        if not findings:
            self.output("  No readable finding records were found.")
        for finding in findings:
            if not isinstance(finding, dict):
                continue
            self.output(
                f"  {finding.get('source', 'audit')} · "
                f"{finding.get('location', '?')} "
                f"[{finding.get('outcome', 'SUSPECT')}]\n"
                f"    {finding.get('detail', '')}"
            )
            if finding.get("missed_hypothesis"):
                self.output(
                    "    Missing/violated hypothesis: "
                    f"{finding['missed_hypothesis']}"
                )
        confirmation = preflight.get("confirmation") or {}
        detail = confirmation.get("detail") or preflight.get("detail")
        if detail:
            self.output(f"  Targeted confirmation: {detail}")
        try:
            telemetry = json.loads(
                (state_dir / "phase_telemetry.json").read_text()
            )
        except (OSError, ValueError, TypeError):
            telemetry = {}
        for phase in telemetry.get("phases") or []:
            if not isinstance(phase, dict):
                continue
            self.output(
                f"  Phase {phase.get('phase', '?')}: "
                f"{phase.get('status', 'UNKNOWN')} · "
                f"{phase.get('model_calls', 0)} model call(s) · "
                f"{phase.get('wall_s', 0)}s"
            )
        self.output(f"  Full saved state: {state_dir}")

    def _explain_active_pause(self) -> None:
        active = self.conversation.active_run
        if not active:
            self._say("There is no paused verification to explain.")
            return
        self._say(
            "This run is PAUSED, not mathematically completed. Preflight found "
            "a specific concern and the targeted confirmation did not produce "
            "a trusted certificate that settled it. Targeted Lean checks may "
            "already have run, but the complete theorem has not yet received a "
            "kernel certificate. Therefore the honest mathematical status is "
            "UNKNOWN—not disproved and not verified."
        )
        self._show_active_preflight(active)
        self._say(
            "Type /resume to choose whether to continue into full Lean "
            "verification, continue structurally with a named placeholder, or "
            "stop while keeping this state."
        )

    def _continue_active(self, mode: str) -> None:
        active = self.conversation.active_run
        if not active:
            self._say("There is no paused verification to continue.")
            return
        if (
            mode == "full"
            and active.get("preflight_status") in {
                "CONFIRMED_THEOREM_REFUTATION",
                "CONFIRMED_PROOF_STEP_FAILURE",
                "CONFIRMED_WELL_DEFINEDNESS_GAP",
            }
        ):
            self._say(
                "Full continuation is unavailable because the disputed step "
                "has a trusted fatal certificate. Structural continuation is "
                "the only permitted continuation."
            )
            return
        label = (
            "full Lean verification"
            if mode == "full"
            else "conditional structural verification"
        )
        self._say(
            f"Resuming {active.get('fixture')} into {label}. "
            "Previously completed gates will be reused."
        )
        try:
            card = self.controller.resume_check(
                str(active["state_dir"]),
                mode=mode,
            )
        except KeyboardInterrupt:
            self._say(
                "Continuation was cancelled. The saved state was preserved."
            )
            return
        except Exception as exc:
            self._say(
                f"Could not resume the saved verification: "
                f"{type(exc).__name__}: {exc}"
            )
            return

        self._say("\n" + render_card(card) + "\n")
        self.conversation.last_result = card
        self.conversation.last_intent = Intent.CHECK
        value = self.conversation.current_input or ResolvedInput(
            source=str(active["state_dir"]),
            name=str(active.get("fixture") or "resumed"),
        )
        self._record(Intent.CHECK, value, card)
        if card.raw.get("paused"):
            self._remember_pause(card)
        elif card.execution in {
            ExecutionStatus.SYSTEM_ERROR,
            ExecutionStatus.TIMED_OUT,
            ExecutionStatus.CANCELLED,
        }:
            self._say(
                "The saved verification remains active because the "
                "continuation did not reach a mathematical terminal state."
            )
        else:
            self._clear_active_run()

    def _persist_session(self) -> None:
        payload = {
            "schema_version": 1,
            "active_run": self.conversation.active_run,
        }
        self.session_state_path.parent.mkdir(parents=True, exist_ok=True)
        tmp = self.session_state_path.with_suffix(".tmp")
        tmp.write_text(json.dumps(payload, indent=2) + "\n")
        tmp.chmod(0o600)
        tmp.replace(self.session_state_path)

    def _restore_session(self) -> None:
        try:
            payload = json.loads(self.session_state_path.read_text())
        except (OSError, ValueError, TypeError):
            payload = {}
        active = payload.get("active_run")
        if not isinstance(active, dict):
            active = self._latest_paused_history_run()
        if not isinstance(active, dict):
            return
        state_dir = Path(str(active.get("state_dir") or ""))
        input_path = state_dir / "input.json"
        if not input_path.exists():
            return
        self.conversation.active_run = active
        try:
            saved = json.loads(input_path.read_text())
            source_meta = saved.get("source_meta")
            source_meta = (
                source_meta if isinstance(source_meta, dict) else {}
            )
            self.conversation.current_input = ResolvedInput(
                statement=str(saved.get("statement") or ""),
                proof=str(saved.get("proof") or ""),
                claim=str(saved.get("claim") or saved.get("statement") or ""),
                source=str(source_meta.get("source") or state_dir),
                name=str(saved.get("fixture") or active.get("fixture") or ""),
            )
        except (OSError, ValueError, TypeError):
            return

    def _latest_paused_history_run(self) -> dict | None:
        for row in self.history.recent(limit=50):
            summary = str(row.get("summary") or "")
            if not (row.get("paused") or summary.startswith("PAUSED:")):
                continue
            state_dir = row.get("state_dir") or (
                (row.get("artifacts") or {}).get("Saved state")
            )
            if not state_dir:
                continue
            input_path = Path(str(state_dir)) / "input.json"
            try:
                saved = json.loads(input_path.read_text())
            except (OSError, ValueError, TypeError):
                continue
            preflight_path = Path(str(state_dir)) / "preflight.json"
            try:
                preflight = json.loads(preflight_path.read_text())
            except (OSError, ValueError, TypeError):
                preflight = {}
            return {
                "fixture": str(
                    saved.get("fixture") or row.get("run_name") or ""
                ),
                "state_dir": str(state_dir),
                "preflight_status": str(
                    preflight.get("status") or "UNRESOLVED"
                ),
                "updated_at": str(row.get("created_at") or ""),
            }
        return None


def _continuation_mode(message: str) -> str | None:
    lower = " ".join(message.lower().split())
    if lower in {
        "continue full verification",
        "continue full lean verification",
        "authorize anyway",
        "proceed anyway",
        "continue anyway",
    }:
        return "full"
    if lower in {
        "continue structurally",
        "continue structural verification",
        "structural salvage",
    }:
        return "structural"
    return None


def _is_pause_question(message: str) -> bool:
    lower = " ".join(message.lower().split())
    if lower in {
        "why",
        "why did it stop",
        "why did it pause",
        "why is it paused",
        "why is it not fully proven",
        "why it's not fully proven",
        "why was lean not run",
        "why did lean not run",
    }:
        return True
    return (
        lower.startswith("why ")
        and any(
            phrase in lower
            for phrase in ("pause", "stop", "lean", "fully proven", "unknown")
        )
    )
