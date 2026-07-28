"""Shared result presentation for the harness — the verdict panel + explanation.

Extracted from harness/examples/_demo_util so the CLI (a product surface) no
longer depends on demo code. Presentation ONLY: every verdict-class decision is
delegated to `rlverify.verdict` (the single authority) — never re-encode it here.
Both `harness/cli.py` and the demo scripts import from this module.
"""
from __future__ import annotations

import sys

from rlverify import verdict as _verdict  # the SINGLE verdict authority
from harness.report import build_report, load_record, render_terminal


def _c(s: str, code: str) -> str:
    return f"\033[{code}m{s}\033[0m" if sys.stdout.isatty() else s


def _load_record(out: dict) -> dict:
    """The structured run record — the source of truth the panel reads from."""
    return load_record(out)


def verdict_class_of(out: dict) -> str:
    rec = _load_record(out)
    if rec:
        return _verdict.verdict_class(rec)
    return out["verdict_line"].splitlines()[0].replace("VERDICT:", "").strip()


# Presentation ONLY — how to render a class, not how to decide it. Keyed on the
# class string that `rlverify.verdict.verdict_class` returns; falls back to the
# prefix (VERIFIED… green / UNVERIFIED… red) so a new class still renders sanely.
def _style(cls: str) -> tuple[str, str]:
    if cls.startswith("VERIFIED"):
        return "✓", "1;32"
    if "UNGATED" in cls or "INCOMPLETE" in cls:
        return "▲", "1;33"
    if cls.startswith("UNVERIFIED"):
        return "✗", "1;31"
    return "•", "0"


def _field(label: str, body: str, label_w: int = 12) -> None:
    """Print a left-labeled, indented multi-line field."""
    lines = body.splitlines() or [""]
    pad = " " * (2 + label_w + 2)
    print(f"  {_c(label.ljust(label_w), '36')}  {lines[0]}")
    for ln in lines[1:]:
        print(pad + ln)


def _fmt_wall(seconds) -> str | None:
    if seconds is None:
        return None
    try:
        total = int(float(seconds))
    except (TypeError, ValueError):
        return None
    mins, secs = divmod(total, 60)
    return f"{mins}m {secs}s" if mins else f"{secs}s"


def print_explanation(out: dict, rec: dict | None = None) -> None:
    """Print the AGENT'S work + the trusted gates' findings, in plain terms.
    Everything is read from the run record — nothing here is hardcoded."""
    rec = rec if rec is not None else _load_record(out)
    if not rec:
        return
    report = build_report(out, rec)
    bar = _c("─" * 64, "2")
    print()
    print(bar)
    print(f"  {_c('What the agent did, and what the harness checked', '1')}")
    print(bar)

    stmt = report["formal"].get("statement", "")
    proof = report["formal"].get("proof", "")
    if stmt:
        _field("Formal stmt", stmt)
    if proof:
        _field("Agent proof", proof)

    decomposition = report.get("decomposition") or {}
    blocks = decomposition.get("rows") or []
    if blocks:
        print()
        print("  Decomposition and repository resolution")
        print(
            f"  {'#':>2}  {'block':<30} {'kind':<15} "
            f"{'depends on':<24} repository theorem / source"
        )
        for item in blocks:
            deps = ",".join(item.get("depends_on") or []) or "—"
            match = item.get("match") or "—"
            if item.get("source_file"):
                match += f" ({item['source_file']}"
                if item.get("source_line"):
                    match += f":{item['source_line']}"
                match += ")"
            print(
                f"  {item.get('index', ''):>2}  "
                f"{str(item.get('block', ''))[:30]:<30} "
                f"{str(item.get('kind', ''))[:15]:<15} "
                f"{deps[:24]:<24} {match}"
            )
        print(
            "  totals: "
            f"{decomposition.get('total', 0)} blocks; "
            f"{decomposition.get('library', 0)} library / "
            f"{decomposition.get('instantiation', 0)} instantiation / "
            f"{decomposition.get('novel', 0)} novel"
        )

    # Trusted gate 1: sealed adversarial triage.
    tri = report["gates"].get("triage") or {}
    if tri.get("present"):
        n = tri.get("suspect_count", 0)
        msg = ("no suspect steps (sealed; carries zero weight — full audit still ran)"
               if tri.get("all_clear") else f"{n} suspect step(s) flagged for scrutiny")
        _field("Triage", msg)

    # Trusted gate 2: back-translation (faithfulness of the Lean to the claim).
    for bt in report["gates"].get("backtranslations") or []:
        if bt.get("target") == "main":
            note = (bt.get("notes") or bt.get("reason") or "").strip()
            _field("Faithfulness", f"{bt.get('verdict', '?')}" + (f" — {note}" if note else ""))
            break
    faithfulness = (report.get("formal") or {}).get("proof_faithfulness")
    if faithfulness:
        _field("Proof path", faithfulness)

    # Falsification gate (numeric counterexample search).
    for f in report["gates"].get("falsifications") or []:
        v, blk = f.get("verdict", "?"), f.get("block", "?")
        if v == "PASSED":
            detail = f"PASSED — no counterexample in {int(f.get('hyp_satisfied', 0)):,} instances"
        elif v == "REFUTED":
            certified = (
                f.get("certificate_validated") is True
                and f.get("independent_checker") == "deterministic"
            )
            strength = "independently certified" if certified else "audit-only candidate"
            detail = (
                f"REFUTED ({strength}) — counterexample found: "
                f"{f.get('certificate')}"
            )
        else:
            detail = f"{v}" + (f" — {f.get('reason')}" if f.get("reason") else "")
        _field("Falsify", f"{blk}: {detail}")

    # Kernel-backed negative artifacts, labeled by their trusted scope.
    for r in report.get("refutations") or []:
        if r.get("kernel_backed"):
            scope = r.get("target_scope", "UNSCOPED")
            kind = r.get("finding_kind", "UNCLASSIFIED")
            label = "Counterex." if scope == "MAIN_THEOREM" else "Finding"
            _field(
                label,
                f"compiled in Lean; scope={scope}; kind={kind}: "
                f"{r.get('description', '')}",
            )


def print_result(out: dict, expect: str | None = None, cert: str | None = None,
                 explain: bool = True, artifacts: list[dict] | None = None,
                 report: dict | None = None) -> None:
    rec = _load_record(out)
    if out.get("paused"):
        preflight = out.get("preflight") or {}
        bar = _c("─" * 64, "2")
        print()
        print(bar)
        print(f"  {_c('Preflight findings — decision required', '1;33')}")
        print(bar)
        for finding in preflight.get("findings") or []:
            location = finding.get("location", "?")
            source = finding.get("source", "audit")
            outcome = finding.get("outcome", "SUSPECT")
            detail = finding.get("detail", "")
            _field(
                f"{source}",
                f"{location} [{outcome}] — {detail}",
            )
        status = preflight.get("status", "UNRESOLVED")
        _field(
            "Confirmation",
            f"{status} — {preflight.get('evidence', 'AUDIT')}",
        )
        if status in {
            "CONFIRMED_THEOREM_REFUTATION",
            "CONFIRMED_PROOF_STEP_FAILURE",
            "CONFIRMED_WELL_DEFINEDNESS_GAP",
        }:
            _field("Options", "stop, or explicitly continue structural verification")
        else:
            _field(
                "Options",
                "stop, explicitly continue full verification, or continue structurally",
            )
    report = report if report is not None else build_report(out, rec)
    if artifacts:
        report["saved_artifacts"] = artifacts
    elif cert:
        report["saved_artifacts"] = [{
            "kind": "main_certificate",
            "label": "main certificate",
            "path": cert,
            "reproduce": f"lake env lean {cert}",
        }]
    print()
    print(render_terminal(report))
    if expect:
        print(f"  {_c('expected: ' + expect, '2')}")
        print()
