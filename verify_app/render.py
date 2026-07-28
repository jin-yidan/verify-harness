from __future__ import annotations

from .types import ProgressEvent, ResultCard


def render_card(card: ResultCard) -> str:
    lines = [
        f"Execution: {card.execution.value}",
        f"Mathematics: {card.mathematics.value}",
        f"Evidence: {' + '.join(card.evidence) if card.evidence else 'NONE'}",
        f"Statement: {card.statement_status.value}",
        f"Theorem: {card.theorem_status.value}",
        f"Submitted proof: {card.proof_status.value}",
    ]
    if card.evidence_by_claim:
        lines.append("Scoped evidence:")
        lines.extend(
            f"  {claim}: {evidence}"
            for claim, evidence in card.evidence_by_claim.items()
        )
    if card.elapsed_s is not None:
        lines.append(f"Time: {card.elapsed_s:.1f}s")
    if card.cost_usd is not None:
        lines.append(f"Cost: ${card.cost_usd:.4f}")
    if card.summary:
        lines.extend(("", card.summary))
    if card.details:
        lines.extend(("", *card.details))
    if card.artifacts:
        lines.append("")
        lines.extend(f"{label}: {path}" for label, path in card.artifacts.items())
    if card.actions:
        lines.extend(("", "Available next actions:"))
        lines.extend(f"  {i}. {action}" for i, action in enumerate(card.actions, 1))
    return "\n".join(lines)


def render_progress(event: ProgressEvent) -> str:
    prefix = f"[{event.phase}]"
    if event.elapsed_s is not None:
        return f"{prefix} {event.message} ({event.elapsed_s:.1f}s)"
    return f"{prefix} {event.message}"


HELP_TEXT = """Verify checks mathematical claims, proof sketches, and Lean certificates.

Speak naturally or use an optional action:
  /falsify     look only for counterexamples
  /hypotheses  audit assumptions and lemma applications
  /check       run full Lean-backed verification
  /statement   inspect statement faithfulness
  /retrieve    search formalized results
  /recheck     recheck a saved Lean certificate
  /resume      continue the active paused verification
  /runs        show previous runs
  /settings    inspect or change the reasoning backend
  /quit        leave Verify

Reference a local input with @file or @folder, or paste a theorem and proof."""
