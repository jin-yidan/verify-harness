"""Command-line front door for the RLVerify BYO-agent harness.

    python3 -m harness verify <dir>           # verify a theorem+proof folder
    python3 -m harness verify -s s.md -p p.txt # …or explicit files / inline text
    python3 -m harness doctor                  # provision + health-check (setup.sh)

This is the TRUSTED, parent-side path (HARNESS_DESIGN.md §8.0): the sealed gates
(triage, back-translation) run in THIS process, which spawns your agent as a
child — so a gated verdict comes from here. This is the only supported entry
point (CLI-only v1 — HARNESS_DESIGN.md §10.2).

Your input is INFORMAL math (prose/LaTeX) — you do NOT write Lean; your agent
formalizes it. A run spends tokens on YOUR account in two roles: the *driving
agent* that writes the Lean, and a separate *sealed grader* that runs the gates.
"""
from __future__ import annotations

import argparse
import os
import platform
import shutil
import sys
import time
from datetime import date
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))


# --------------------------------------------------------------------------
# input resolution: a folder convention OR explicit files / inline text
# --------------------------------------------------------------------------

def _read_maybe_file(value: str | None) -> str | None:
    """A flag value is a path if it exists on disk, else literal text."""
    if value is None:
        return None
    p = Path(value)
    if p.exists() and p.is_file():
        return p.read_text()
    return value


def _first_existing(d: Path, *names: str) -> Path | None:
    for n in names:
        p = d / n
        if p.exists():
            return p
    return None


def _resolve_inputs(args) -> tuple[str, str, str, str | None]:
    """Return (name, statement, proof, nl_claim).

    Folder convention (positional `target` is a dir): `statement.md|.txt`,
    `proof.lean|.txt|.md`, optional `claim.txt|.md`. Explicit flags override.
    """
    statement = _read_maybe_file(args.statement)
    proof = _read_maybe_file(args.proof)
    claim = _read_maybe_file(args.claim)
    name = args.name

    if args.target:
        d = Path(args.target)
        if not d.is_dir():
            _die(f"target '{d}' is not a directory. Pass a folder with "
                 "statement/proof files, or use -s/-p explicitly.")
        if statement is None:
            f = _first_existing(d, "statement.md", "statement.txt")
            statement = f.read_text() if f else None
        if proof is None:
            f = _first_existing(d, "proof.lean", "proof.txt", "proof.md")
            proof = f.read_text() if f else None
        if claim is None:
            f = _first_existing(d, "claim.txt", "claim.md")
            claim = f.read_text() if f else None
        if name is None:
            name = d.resolve().name.replace(" ", "_")

    if not statement or not proof:
        _die("need a statement and a proof. Provide a folder containing "
             "statement.md + proof.txt, or pass -s/--statement and -p/--proof "
             "(each may be a file path or inline text).")
    return (name or "cli_run", statement.strip(), proof.strip(),
            claim.strip() if claim else None)


def _resolve_advisory_input(args, call_model=None) -> tuple[str, str, str]:
    """Input resolver for standalone advisory components."""
    if (args.target == "-" and not args.statement and not args.proof
            and not getattr(args, "theorem", None)):
        text = sys.stdin.read().strip()
        if not text:
            _die("stdin was empty")
        return (args.name or "stdin", text, "")
    try:
        from harness.ingest import ingest_to_fixture, needs_ingest
        if needs_ingest(args.target, args.statement, args.proof):
            if call_model is None:
                _die("paper input needs a sealed extraction backend")
            fixture = ingest_to_fixture(args.target, theorem=getattr(args, "theorem", None),
                                        call_model=call_model)
            return fixture.name, fixture.statement, fixture.proof
    except SystemExit:
        raise
    except Exception as e:
        _die(str(e))
    name, statement, proof, _claim = _resolve_inputs(args)
    return name, statement, proof


def _is_sampler_path(value: str | None) -> bool:
    if not value:
        return False
    p = Path(value)
    return p.exists() and p.is_file() and p.suffix.lower() == ".py"


def _looks_like_verification_input(args) -> bool:
    if args.statement and args.proof:
        return True
    target = args.target
    if not target:
        return False
    if target == "-":
        return True
    if _is_sampler_path(target):
        return False
    try:
        from harness.ingest import needs_ingest
        if needs_ingest(target, args.statement, args.proof):
            return True
    except Exception:
        pass
    return Path(target).is_dir()


def _resolve_falsify_claim(args, call_model=None) -> tuple[str, str]:
    """Return (name, claim/context text) for prose-to-sampler falsification."""
    explicit_claim = _read_maybe_file(getattr(args, "claim", None))
    if explicit_claim:
        return (args.name or args.block or "claim", explicit_claim.strip())
    statement = _read_maybe_file(getattr(args, "statement", None))
    proof = _read_maybe_file(getattr(args, "proof", None))
    if statement or proof:
        parts = []
        if statement:
            parts.append(statement.strip())
        if proof:
            parts.append("Proof/context:\n" + proof.strip())
        return (args.name or args.block or "claim", "\n\n".join(parts).strip())
    if _looks_like_verification_input(args):
        name, statement, proof = _resolve_advisory_input(args, call_model=call_model)
        text = statement.strip()
        if proof.strip():
            text += "\n\nProof/context:\n" + proof.strip()
        return name, text
    if args.target:
        return (args.name or args.block or "claim", _read_maybe_file(args.target).strip())
    _die("provide a claim, a sampler .py file, '-', a folder, or -s/--statement")


def _confirm_sampler_execution(args) -> bool:
    if args.trust_samplers or os.environ.get("RLVERIFY_TRUST_SAMPLERS") == "1":
        return True
    if not sys.stdin.isatty():
        _die("sampler execution requires explicit consent: pass "
             "--trust-samplers or set RLVERIFY_TRUST_SAMPLERS=1")
    print(_c("  harness falsify will execute sampler Python locally. "
             "Proceed? [y/N] ", "1"), end="", file=sys.stderr, flush=True)
    resp = sys.stdin.readline()
    if resp.strip().lower() not in ("y", "yes"):
        print("  aborted — sampler not generated or executed.", file=sys.stderr)
        return False
    return True


# --------------------------------------------------------------------------
# sandbox posture: loud, honest, never a silent downgrade
# --------------------------------------------------------------------------

def _resolve_sandbox(args) -> None:
    """Set RLVERIFY_SANDBOX and warn when the untrusted guarantee is off.

    The W0 sandbox is macOS-only today. On Linux the only option is to run
    unconfined — which DROPS the untrusted-agent guarantee. We refuse to do that
    silently: either the user passes --no-sandbox (acknowledging it) or we stop
    with an explanation. On macOS the sandbox stays on unless --no-sandbox.
    """
    if args.no_sandbox:
        os.environ["RLVERIFY_SANDBOX"] = "0"
        _warn("sandbox DISABLED (--no-sandbox). Untrusted-agent guarantee is OFF — "
              "only verify proofs you trust, driven by an agent you trust.")
        return
    sysname = platform.system()
    if sysname == "Linux":
        # The bwrap sandbox exists but is UNVALIDATED — gated behind an explicit
        # opt-in so it never silently implies the proven macOS guarantee.
        if os.environ.get("RLVERIFY_LINUX_SANDBOX") == "1":
            _warn("Linux bubblewrap sandbox is UNVALIDATED (RLVERIFY_LINUX_SANDBOX=1) "
                  "— confinement is best-effort and NOT yet acceptance-tested on "
                  "Linux; do not rely on the untrusted-code guarantee until it is.")
            return
        _die(
            "the untrusted-Lean sandbox is VALIDATED on macOS only. A Linux "
            "bubblewrap port exists but is UNVALIDATED (HARNESS_DESIGN.md §8 P2): "
            "set RLVERIFY_LINUX_SANDBOX=1 to use it AT YOUR OWN RISK (best-effort, "
            "not acceptance-tested), or re-run with --no-sandbox to proceed "
            "UNCONFINED (trusted-local — use only when you trust the proof AND the agent).")
    elif sysname != "Darwin":
        _die(
            f"the untrusted-Lean sandbox is macOS-only today; you are on {sysname}. "
            "Re-run with --no-sandbox to proceed UNCONFINED (drops the guarantee — "
            "use only when you trust the proof AND the agent).")


# --------------------------------------------------------------------------
# presentation
# --------------------------------------------------------------------------

def _c(s: str, code: str) -> str:
    return f"\033[{code}m{s}\033[0m" if sys.stdout.isatty() else s


def _warn(msg: str) -> None:
    print(_c(f"  ⚠ {msg}", "33"), file=sys.stderr)


def _die(msg: str):
    """Tool/usage/auth error → exit code 2 (distinct from a valid non-VERIFIED
    verdict, which is exit 1)."""
    print(_c(f"  ✗ {msg}", "31"), file=sys.stderr)
    raise SystemExit(2)


def _confirm_spend(args) -> bool:
    if not sys.stdin.isatty() or args.yes:
        return True
    try:
        resp = input(_c("  proceed? [y/N] ", "1"))
    except EOFError:
        resp = ""
    if resp.strip().lower() not in ("y", "yes"):
        print("  aborted — no tokens spent.")
        return False
    return True


def _unit_from_parts(name: str, statement: str, proof: str,
                     claim: str | None = None):
    from harness.cost import VerificationUnit
    return VerificationUnit(name=name, statement=statement, proof=proof, claim=claim)


def _unit_from_fixture(fixture):
    return _unit_from_parts(
        getattr(fixture, "name", "fixture"),
        getattr(fixture, "statement", ""),
        getattr(fixture, "proof", ""),
        getattr(fixture, "claim", None),
    )


def _print_cost_estimate(args, units, model, reasoning_effort,
                         agent_timeout_s: int) -> None:
    from harness.cost import estimate_verification_cost, render_cost_estimate

    est = estimate_verification_cost(
        units,
        backend=args.backend,
        model=model,
        reasoning_effort=reasoning_effort,
        agent_timeout_s=agent_timeout_s,
        gate_timeout_s=args.gate_timeout,
    )
    print(render_cost_estimate(est))


def _resolve_artifact_source(path: str) -> Path:
    src = Path(path)
    if src.is_absolute() or src.exists():
        return src
    return ROOT / src


def _copy_lean_artifact(src: Path, out_dir: Path, sandbox: str | None) -> str:
    out_dir.mkdir(parents=True, exist_ok=True)
    dst = out_dir / src.name
    # Execution-safety provenance on the durable certificate. An unsandboxed run
    # drops the untrusted-code guarantee, so stamp the COPY (a leading Lean
    # comment — inert for `lake env lean`, keeps the kernel re-check identical).
    # Sandboxed certs stay byte-identical to the driver's original.
    if sandbox == "off":
        header = ("-- PROVENANCE: sandbox OFF (RLVERIFY_SANDBOX=0) — the untrusted-code\n"
                  "-- execution guarantee was NOT in effect for this run; the verdict\n"
                  "-- trusts the proof source and the driving agent.\n")
        dst.write_text(header + src.read_text())
    else:
        shutil.copy(src, dst)
    return os.path.relpath(dst)


def _save_artifacts(out: dict, out_dir: Path) -> dict:
    """Copy main/refutation Lean artifacts using the run record, not glob order."""
    from harness.report import build_report, load_record

    rec = load_record(out)
    report = build_report(out, rec)
    saved: list[dict] = []
    main_certificate = None
    for art in report.get("artifacts") or []:
        src = _resolve_artifact_source(art.get("path", ""))
        if not src.exists() or src.suffix != ".lean":
            continue
        copied = _copy_lean_artifact(src, out_dir, out.get("sandbox"))
        saved_art = {**art, "path": copied, "reproduce": f"lake env lean {copied}"}
        saved.append(saved_art)
        if art.get("kind") == "main_certificate":
            main_certificate = copied

    record_copy = None
    rec_path = Path(rec.get("_record_path", "")) if rec else None
    if rec_path and rec_path.exists():
        out_dir.mkdir(parents=True, exist_ok=True)
        dst = out_dir / rec_path.name
        shutil.copy(rec_path, dst)
        record_copy = os.path.relpath(dst)

    integrity_copy = None
    integrity_src = Path(out.get("integrity_manifest", ""))
    if integrity_src.is_file():
        out_dir.mkdir(parents=True, exist_ok=True)
        dst = out_dir / f"{out.get('fixture', 'run')}-integrity.json"
        shutil.copy(integrity_src, dst)
        integrity_copy = os.path.relpath(dst)

    input_copy = None
    state_dir = out.get("state_dir")
    input_src = Path(state_dir) / "input.json" if state_dir else None
    if input_src is not None and input_src.is_file():
        out_dir.mkdir(parents=True, exist_ok=True)
        dst = out_dir / f"{out.get('fixture', 'run')}-input.json"
        shutil.copy(input_src, dst)
        input_copy = os.path.relpath(dst)

    return {"artifacts": saved, "main_certificate": main_certificate,
            "record": record_copy, "record_data": rec,
            "integrity_manifest": integrity_copy, "input": input_copy}


def _save_certificate(out: dict, out_dir: Path) -> str | None:
    """Compatibility wrapper: return only the copied main certificate path."""
    return _save_artifacts(out, out_dir)["main_certificate"]


def _report_path(args, name: str) -> Path:
    if args.report:
        return Path(args.report)
    return Path(args.out) / f"{name}-report.md"


def _source_from_fixture_dir(target: str | None) -> tuple[str | None, list[str]]:
    """Recover ingestion provenance from a materialized fixture folder.

    The advertised flow after ingestion is `verify <fixture.path>` (a rerun on
    the folder). Without this, that rerun would drop the arXiv link and the
    `source: PDF text layer` stamp that the first run's report carried."""
    if not target:
        return None, []
    meta = Path(target) / "metadata.json"
    if not meta.is_file():
        return None, []
    try:
        import json
        data = json.loads(meta.read_text())
    except (OSError, ValueError):
        return None, []
    if not isinstance(data, dict):
        return None, []
    label = str(data.get("source") or "").strip()
    kind = str(data.get("kind") or "").strip()
    # metadata.json is user-editable (T11 invites fixture review), so a
    # hand-mangled `notes` must degrade to "no notes", never to a traceback or
    # to a string exploded into one bogus note per character.
    raw_notes = data.get("notes")
    notes = [str(n) for n in raw_notes] if isinstance(raw_notes, list) else []
    if not label:
        return None, notes
    return (f"{label} ({kind})" if kind else label), notes


def _source_meta(fixture) -> dict | None:
    """Ingestion provenance persisted into the state dir, so a `--resume` run's
    report still names the paper rather than regressing to "CLI input:"."""
    source, notes = _fixture_source(fixture)
    if not source and not notes:
        return None
    return {"source": source, "notes": notes}


def _fixture_source(fixture) -> tuple[str | None, list[str]]:
    """(source label, provenance notes) for an ingested fixture's report header.

    The report is a durable surface, so it must name WHERE the claim came from
    (the arXiv link / file) and carry the ingestion stamps — notably `source:
    PDF text layer`, without which a downstream MISMATCH is uninterpretable
    (extraction noise vs. a real formalization defect)."""
    src = getattr(fixture, "source", None)
    if src is None:
        return None, []
    label = str(getattr(src, "source", "") or "").strip()
    kind = str(getattr(src, "kind", "") or "").strip()
    raw_notes = getattr(src, "notes", None)
    notes = [str(n) for n in raw_notes] if isinstance(raw_notes, list) else []
    if not label:
        return None, notes
    return (f"{label} ({kind})" if kind else label), notes


def _write_markdown_report(args, name: str, out: dict, saved: dict,
                           original_claim: str, source: str | None = None,
                           source_notes: list[str] | None = None,
                           path: Path | None = None) -> tuple[str, dict] | None:
    """Write one theorem's Markdown report. Returns (relative path, report dict)
    so paper mode can reuse the structured report for its aggregate sections."""
    if args.report is None:
        return None
    from harness.report import render_markdown

    report = _final_report_object(out, saved)
    path = path or _report_path(args, name)
    path.parent.mkdir(parents=True, exist_ok=True)
    md = render_markdown(report, original_claim=original_claim,
                         source=source or f"CLI input: {name}",
                         source_notes=source_notes,
                         generated_at=date.today().isoformat())
    path.write_text(md)
    return os.path.relpath(path), report


def _final_report_object(out: dict, saved: dict) -> dict:
    """One structured representation shared by terminal and Markdown output."""
    from harness.report import build_report

    rec = saved.get("record_data") or {}
    report = build_report(out, rec)
    report["saved_artifacts"] = saved.get("artifacts") or []
    if saved.get("record"):
        report["provenance"]["saved_record"] = saved["record"]
    if saved.get("integrity_manifest"):
        report["provenance"]["integrity_manifest"] = saved["integrity_manifest"]
    if saved.get("input"):
        report["provenance"]["saved_input"] = saved["input"]
    return report


def _is_clean_verdict(line: str) -> bool:
    return ("VERIFIED" in line and "UNVERIFIED" not in line
            and "MODULO" not in line and "GAPS" not in line)


def _write_paper_report(args, name: str, rows: list[dict],
                        paper_record: dict,
                        source: str | None = None,
                        source_notes: list[str] | None = None) -> str | None:
    """Write the one final, self-contained golden verifyRL-paper report."""
    if args.report is None:
        return None
    path = _report_path(args, name)
    path.parent.mkdir(parents=True, exist_ok=True)
    lines = [
        f"# Verification Report: {name}",
        "",
        f"**Date**: {date.today().isoformat()}",
        f"**Input**: {source or name}",
        f"**Overall Verdict**: {paper_record.get('verdict', 'UNVERIFIED')}",
    ]
    for note in (source_notes or []):
        lines.append(f"**Source note:** {note}")
    components = paper_record.get("components") or []
    axioms = sorted({
        axiom
        for component in components
        for axiom in component.get("kernel_axioms") or []
        if axiom not in {"propext", "Classical.choice", "Quot.sound"}
    })
    lines += ["", "## Axioms", ""]
    lines += (
        [f"- `{axiom}`" for axiom in axioms]
        if axioms else ["none"]
    )
    lines += ["", "## Dependency Graph", "", "```text"]
    for component in components:
        if component.get("external") or component.get("kind") == "definition":
            continue
        deps = ", ".join(component.get("deps") or []) or "(none)"
        lines.append(f"{component.get('label')} → {deps}")
    if paper_record.get("cycle"):
        lines.append("CIRCULAR: " + " → ".join(paper_record["cycle"]))
    lines += ["```", "", "## Verification Order", "",
              "| # | Component | Dependencies | Status |",
              "|---:|---|---|---|"]
    by_label = {component.get("label"): component for component in components}
    order = paper_record.get("order") or [
        component.get("label") for component in components
    ]
    for index, label in enumerate(order, 1):
        component = by_label.get(label) or {}
        status = component.get("verdict") or component.get("status") or "pending"
        if component.get("note"):
            status += f" — {component['note']}"
        lines.append(
            f"| {index} | {label} | "
            f"{', '.join(component.get('deps') or []) or '(none)'} | "
            f"{status} |"
        )

    known_costs = [r.get("cost_usd") for r in rows if r.get("cost_usd") is not None]
    missing = len(rows) - len(known_costs)
    verified = [c for c in components if c.get("status") == "verified"]
    failed = [c for c in components if c.get("status") == "failed"]
    skipped = [c for c in components if c.get("status") == "skipped"]
    lines += [
        "",
        "## Summary",
        "",
        f"- Total components: {len(components)}",
        f"- Verified: {len(verified)}",
        f"- Failed: {len(failed)}",
        f"- Skipped: {len(skipped)}",
    ]
    for component in failed:
        lines.append(
            f"  - `{component.get('label')}`: "
            f"{component.get('verdict') or 'FAILED'} — "
            f"{component.get('note') or 'no reason recorded'}"
        )
    for component in skipped:
        lines.append(
            f"  - `{component.get('label')}`: "
            f"{component.get('note') or 'skipped'}"
        )
    lines += [
        f"- Agent total: ${sum(known_costs):.4f} known; "
        f"unavailable for {missing} run(s)",
        "- Sealed gate calls: not metered",
        "",
        "## Detailed Results",
        "",
    ]

    for row in rows:
        lines += [f"### {row['name']} — {row['verdict']}", ""]
        if row.get("evidence"):
            lines.append(f"**Evidence**: `{row['evidence']}`")
        if row.get("reason"):
            lines.append(f"**Failure/Reason**: {row['reason']}")
        report = row.get("report_obj") or {}
        formal = report.get("formal") or {}
        lines += ["", "**Statement**:", ""]
        lines.append(formal.get("statement") or row.get("statement") or "_Unavailable._")
        lines += ["", "**Building blocks**:", ""]
        from harness.report import _decomposition_table
        lines.append(_decomposition_table(report.get("decomposition") or {}))
        if formal.get("proof"):
            lines += ["", "**Lean proof**:", "", "```lean",
                      formal["proof"], "```"]
        if row.get("status") == "skipped":
            lines += ["", f"**Blocked by**: {row.get('reason') or 'dependency failure'}"]
        if row.get("artifacts"):
            lines += ["", "**Final artifacts**:"]
            for artifact in row["artifacts"]:
                lines.append(
                    f"- `{artifact.get('path', '')}`"
                    + (
                        f" — `{artifact['reproduce']}`"
                        if artifact.get("reproduce") else ""
                    )
                )
        lines.append("")

    lines += ["## Assembled Lean Code", ""]
    assembly = (paper_record.get("metadata") or {}).get("assembly") or {}
    lines += [
        f"**Assembly status**: {assembly.get('status', 'NOT RECORDED')}",
        f"**Assembly artifact**: `{assembly.get('artifact', '') or 'none'}`",
    ]
    if assembly.get("reason"):
        lines.append(f"**Assembly failure**: {assembly['reason']}")
    lines.append("")
    if assembly.get("code"):
        lines += ["```lean", assembly["code"], "```", ""]
    else:
        lines += ["_No complete Lean component was assembled._", ""]
    golden = (paper_record.get("metadata") or {}).get("golden_workflows") or {}
    if golden:
        lines += ["## Golden Workflow Provenance", ""]
        for workflow, provenance in golden.items():
            lines.append(
                f"- `{workflow}`: `{provenance.get('path', '')}` · SHA-256 "
                f"`{provenance.get('sha256', '')}`"
            )
        lines.append("")
    path.write_text("\n".join(lines).rstrip() + "\n")
    return os.path.relpath(path)


def _render_paper_terminal(name: str, rows: list[dict],
                           paper_record: dict) -> str:
    """Brief terminal rendering of the same final paper record as the report."""
    lines = [
        f"RLVERIFY FINAL PAPER REPORT: {name}",
        f"OVERALL VERDICT {paper_record.get('verdict', 'UNVERIFIED')}",
        "VERIFICATION ORDER",
    ]
    by_name = {row.get("name"): row for row in rows}
    for index, label in enumerate(paper_record.get("order") or [], 1):
        row = by_name.get(label) or {}
        status = row.get("verdict") or row.get("status") or "pending"
        lines.append(
            f"{index}. {label}: {status} "
            f"| evidence={row.get('evidence') or ''}"
        )
    components = paper_record.get("components") or []
    known_costs = [
        row.get("cost_usd")
        for row in rows
        if row.get("cost_usd") is not None
    ]
    missing_costs = len(rows) - len(known_costs)
    lines += [
        "SUMMARY",
        f"total={len(components)} "
        f"verified={sum(c.get('status') == 'verified' for c in components)} "
        f"failed={sum(c.get('status') == 'failed' for c in components)} "
        f"skipped={sum(c.get('status') == 'skipped' for c in components)}",
        f"agent total: ${sum(known_costs):.4f} known; "
        f"unavailable for {missing_costs} run(s)",
    ]
    assembly = (paper_record.get("metadata") or {}).get("assembly") or {}
    lines.append(
        f"ASSEMBLY {assembly.get('status', 'NOT RECORDED')} "
        f"| artifact={assembly.get('artifact') or 'none'}"
    )
    if paper_record.get("cycle"):
        lines.append("CYCLE " + " -> ".join(paper_record["cycle"]))
    return "\n".join(lines)


def _assemble_paper_final(paper, rows: list[dict],
                          out_root: Path) -> dict:
    """Compile one deduplicated final Lean file for all verified components.

    Per-component certificates remain evidence, while this aggregate check is
    the golden paper workflow's Phase 4 integration/kernel audit.
    """
    import re
    from rlverify.driver import check_axiom_closure

    clean_rows = {
        str(row.get("name")): row
        for row in rows
        if row.get("status") == "verified" and row.get("lean_code")
    }
    if not clean_rows:
        return {
            "status": "SKIPPED",
            "reason": "no verified Lean component source was available",
            "code": "",
            "artifact": "",
            "kernel_axioms": [],
        }

    order = [
        label for label in paper.topo_order()
        if label in clean_rows
    ]
    main_candidates = [
        label for label in order
        if paper.components[label].is_main
    ]
    target_label = main_candidates[-1] if main_candidates else order[-1]

    imports: list[str] = []
    bodies: dict[str, str] = {}
    for label in order:
        code = str(clean_rows[label].get("lean_code") or "")
        body_lines: list[str] = []
        for line in code.splitlines():
            if line.startswith("import "):
                if line not in imports:
                    imports.append(line)
            else:
                body_lines.append(line)
        bodies[label] = "\n".join(body_lines).strip()

    # A dependent component's exact certificate normally embeds the source of
    # its `prior` blocks. Remove an earlier component only when its complete
    # body is already present verbatim in a later certificate.
    selected_reversed: list[str] = []
    accumulated = ""
    for label in reversed(order):
        body = bodies[label]
        if body and body not in accumulated:
            selected_reversed.append(label)
            accumulated = body + "\n\n" + accumulated
    selected = list(reversed(selected_reversed))
    source = "\n".join(imports or ["import Mathlib"])
    source += "\n\n" + "\n\n".join(
        bodies[label] for label in selected if bodies[label]
    )
    source = source.rstrip() + "\n"

    target_record = clean_rows[target_label].get("record") or {}
    target_statement = str(target_record.get("main_statement") or "")
    match = re.search(
        r"(?:theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_'.]*)",
        target_statement,
    )
    if match is None:
        result = {
            "status": "FAILED",
            "reason": f"no Lean theorem identifier for {target_label}",
            "code": source,
            "artifact": "",
            "kernel_axioms": [],
        }
    else:
        closure = check_axiom_closure(source, match.group(1))
        compile_ok = bool(
            closure.compile_result is not None
            and closure.compile_result.success
        )
        passed = bool(closure.ok and compile_ok and not closure.has_sorry_ax)
        result = {
            "status": "VERIFIED" if passed else "FAILED",
            "reason": "" if passed else str(
                closure.error
                or (
                    closure.compile_result.errors
                    if closure.compile_result is not None else
                    "kernel closure unavailable"
                )
            ),
            "target_component": target_label,
            "target_theorem": match.group(1),
            "code": source,
            "artifact": "",
            "kernel_axioms": list(closure.axioms or []),
            "has_sorry_ax": bool(closure.has_sorry_ax),
        }

    out_root.mkdir(parents=True, exist_ok=True)
    artifact = out_root / f"{paper.name}-final.lean"
    artifact.write_text(source)
    result["artifact"] = os.path.relpath(artifact)
    return result


def _cleanup_finished_run(state_dir: str | os.PathLike | None,
                          out_root: str | os.PathLike) -> bool:
    """Remove one completed resumable state directory, never a broader path."""
    if not state_dir:
        return False
    target = Path(state_dir).resolve()
    allowed_parent = (Path(out_root).resolve() / ".state")
    if target.parent != allowed_parent or target == allowed_parent:
        raise RuntimeError(
            f"refusing to clean unexpected state directory: {target}"
        )
    if target.is_dir():
        shutil.rmtree(target)
        return True
    return False


def _cleanup_materialized_fixture(path: Path) -> bool:
    """Remove a harness-generated fixture after its final bundle is durable."""
    from harness.ingest import OUT_ROOT

    target = path.resolve()
    root = OUT_ROOT.resolve()
    if root not in target.parents or target == root:
        # Only the ingestion layer's private materialization tree is disposable.
        # A caller or test double may return an existing/user-owned fixture;
        # preserve it instead of turning finalization into a failure.
        return False
    if target.is_dir():
        shutil.rmtree(target)
        parent = target.parent
        while parent != root:
            try:
                parent.rmdir()
            except OSError:
                break
            parent = parent.parent
        return True
    return False


def _resume_inputs(args) -> tuple[str, str, str, str | None, str | None, list[str]]:
    from harness.runner import load_state_input

    if any([args.target, args.statement, args.proof, args.claim, args.theorem,
            args.all_theorems]):
        _die("--resume loads the saved statement/proof from state; do not pass "
             "a target, --theorem, -s, -p, -c, or --all-theorems in the same command")
    try:
        data = load_state_input(args.resume, args.out)
    except Exception as e:
        _die(str(e))
    meta = data.get("source_meta")
    meta = meta if isinstance(meta, dict) else {}
    raw_notes = meta.get("notes")
    return (data["fixture"], data["statement"], data["proof"], data.get("claim"),
            meta.get("source") or None,
            [str(n) for n in raw_notes] if isinstance(raw_notes, list) else [])


# --------------------------------------------------------------------------
# subcommands
# --------------------------------------------------------------------------

def _cmd_verify(args) -> int:
    from harness.runner import (run_verification, launch_agent, AgentBudgetExceeded,
                                default_state_dir, _resolved_agent_timeout)
    from harness.backends import get_backend
    from harness.render import print_result  # presentation (reads the verdict authority)

    if args.continue_structural and not args.resume:
        _die("--continue-structural is a second-stage action; first run verify "
             "normally, then pass the returned name with --resume")
    if args.continue_unresolved and not args.resume:
        _die("--continue-unresolved is a second-stage action; first run verify "
             "normally, then pass the returned name with --resume")
    if args.continue_structural and args.continue_unresolved:
        _die("choose one continuation mode: --continue-structural or "
             "--continue-unresolved")

    # Per-backend model resolution: `--model` defaults to the claude-shaped
    # "opus", which is meaningless to codex. For a non-claude backend, treat the
    # default sentinel as "unset" → let the backend use its own config default
    # (None), rather than passing a guessed model id. An explicit --model always
    # wins.
    model = args.model
    if args.backend != "claude" and model == "opus":
        model = None
    reasoning_effort = _reasoning_effort_for_backend(args)
    service_tier = getattr(args, "service_tier", None)
    agent_timeout_s = _resolved_agent_timeout(args.budget)
    agent_context = _read_maybe_file(
        getattr(args, "agent_context", None)
    ) or ""

    formal_units = None
    formal_estimate_printed = False
    generated_fixture_path: Path | None = None
    report_source: str | None = None
    report_notes: list[str] = []
    if args.resume:
        ingesting = False
        (name, statement, proof, claim,
         report_source, report_notes) = _resume_inputs(args)
        formal_units = [_unit_from_parts(name, statement, proof, claim)]
    else:
        try:
            from harness.ingest import ingest_all_to_fixtures, ingest_to_fixture, needs_ingest
            ingesting = needs_ingest(args.target, args.statement, args.proof)
        except Exception:
            ingesting = False
    if args.all_theorems and not ingesting:
        _die("--all-theorems requires a paper/link/stdin input, not an existing fixture folder")
    if ingesting:
        _warn("paper/link/paste input: extraction spends one sealed call before verification.")
        _warn("a formal-proof cost estimate will be shown after theorem extraction.")
        if not _confirm_spend(args):
            return 130
        if args.all_theorems:
            try:
                fixtures = ingest_all_to_fixtures(
                    args.target,
                    call_model=get_backend(args.backend, model=model,
                                           timeout=args.gate_timeout,
                                           reasoning_effort=reasoning_effort,
                                           service_tier=service_tier),
                )
            except Exception as e:
                _die(str(e))
            print(f"  materialized {len(fixtures)} theorem fixture(s):")
            for fx in fixtures:
                print(f"    {fx.name}: {fx.path}")
            formal_units = [_unit_from_fixture(fx) for fx in fixtures]
            _print_cost_estimate(args, formal_units, model, reasoning_effort,
                                 agent_timeout_s)
            formal_estimate_printed = True
            if args.dry_run:
                return 0
            if not _confirm_spend(args):
                return 130
            _resolve_sandbox(args)
            rows: list[dict] = []
            paper_name = args.name or (fixtures[0].source.paper_id if fixtures else "paper")
            from harness.golden import golden_manifest
            from harness.ingest import build_paper_session, capped_paper_order

            paper = build_paper_session(paper_name, fixtures)
            paper.metadata = {
                "golden_workflows": golden_manifest(
                    "verify-full-process", "verifyRL-paper"
                ),
                "source": (
                    getattr(fixtures[0].source, "source", args.target)
                    if fixtures else args.target
                ),
            }
            for component in paper.components.values():
                if component.external:
                    component.status = "skipped"
                    component.verdict = "EXTERNAL/LIBRARY_LANE"
                    component.note = "external cited result; routed outside the paper plan"
                elif component.kind == "definition":
                    component.status = "skipped"
                    component.verdict = "CONTEXT"
                    component.note = "definition tracked as shared context"
            fixture_by_name = {fixture.name: fixture for fixture in fixtures}
            unknown_deps = paper.unknown_deps()
            cycle = paper.detect_cycle()
            if unknown_deps:
                paper.metadata["unknown_dependencies"] = unknown_deps
                for label, component in paper.components.items():
                    if not component.verifiable:
                        continue
                    missing = unknown_deps.get(label) or []
                    component.status = "failed" if missing else "skipped"
                    component.verdict = (
                        "UNVERIFIED/INCOMPLETE" if missing else "SKIPPED"
                    )
                    component.note = (
                        "unresolved dependency reference(s): "
                        + ", ".join(missing)
                        if missing else
                        "not attempted because the dependency graph is unresolved"
                    )
                    rows.append({
                        "name": label,
                        "verdict": component.verdict,
                        "status": component.status,
                        "reason": component.note,
                        "evidence": "deterministic graph",
                        "statement": component.statement,
                        "cost_usd": None,
                        "artifacts": [],
                    })
                order = []
                omitted = []
            elif cycle:
                for label, component in paper.components.items():
                    component.status = (
                        "failed" if label in cycle else "skipped"
                    )
                    component.verdict = (
                        "CIRCULAR" if label in cycle else "SKIPPED"
                    )
                    component.note = (
                        "dependency cycle: " + " -> ".join(cycle)
                        if label in cycle else
                        "not attempted because the paper dependency graph is circular"
                    )
                    rows.append({
                        "name": label,
                        "verdict": component.verdict,
                        "status": component.status,
                        "reason": component.note,
                        "evidence": "deterministic graph",
                        "statement": component.statement,
                        "cost_usd": None,
                        "artifacts": [],
                    })
                order: list[str] = []
                omitted: list[str] = []
            else:
                order, omitted = capped_paper_order(paper, limit=15)
                for label in omitted:
                    component = paper.components[label]
                    component.status = "skipped"
                    component.verdict = "NOT_ATTEMPTED_CAP"
                    component.note = "not attempted (15-component cap)"

            # Exact prior sources, indexed by paper node, become MCP `prior`
            # blocks for dependent components.
            verified_prior: dict[str, dict] = {}
            completed_states: list[str] = []
            for label in order:
                fx = fixture_by_name[label]
                component = paper.components[label]
                if component.status == "skipped":
                    rows.append({
                        "name": label,
                        "verdict": "SKIPPED",
                        "status": "skipped",
                        "reason": component.note,
                        "evidence": "dependency graph",
                        "statement": component.statement,
                        "cost_usd": None,
                        "artifacts": [],
                    })
                    continue
                print(f"\n{_c('Verifying', '1')}: {fx.name}")
                direct_prior_labels = {
                    dep.label for dep in paper.verified_deps(label)
                }
                priors: list[str | dict] = [
                    verified_prior[dep.label]
                    for dep in paper.verified_deps(label)
                    if dep.label in verified_prior
                ]
                # Older extractors did not emit dependency edges. Preserve
                # already-verified names as context-only strings; only exact
                # declared dependencies above carry source and can become MCP
                # `prior` blocks.
                priors.extend(
                    prior_label
                    for prior_label in verified_prior
                    if prior_label not in direct_prior_labels
                )
                try:
                    out = run_verification(
                        fx.name, statement=fx.statement, proof=fx.proof,
                        nl_claim=fx.claim,
                        call_model=get_backend(args.backend, model=model,
                                               timeout=args.gate_timeout,
                                               reasoning_effort=reasoning_effort,
                                               service_tier=service_tier),
                        agent_drive=launch_agent(backend=args.backend, model=model,
                                                 timeout=args.budget,
                                                 quiet=args.quiet,
                                                 reasoning_effort=reasoning_effort,
                                                 service_tier=service_tier),
                        agent_context=agent_context,
                        state_dir=default_state_dir(fx.name, args.out),
                        continue_structural=args.continue_structural,
                        continue_unresolved=args.continue_unresolved,
                        upstream_verified=priors,
                        source_meta=_source_meta(fx),
                    )
                except AgentBudgetExceeded as e:
                    print(_c(f"  ✗ {e}", "31"), file=sys.stderr)
                    print(f"  state kept at {default_state_dir(fx.name, args.out)}",
                          file=sys.stderr)
                    print(f"  resume with: python3 -m harness verify --resume {fx.name}",
                          file=sys.stderr)
                    rows.append({"name": fx.name, "verdict": "BUDGET_EXHAUSTED",
                                 "status": "incomplete", "cost_usd": None})
                    continue
                except RuntimeError as e:
                    # A leftover state dir from a previous run of the SAME paper
                    # must not kill the whole paper at theorem 1 — and `--resume`
                    # (which the runner's message suggests) is rejected alongside
                    # `--all-theorems`, so that advice would be a dead end here.
                    # Record it, name the real fix, and keep going.
                    if "already exists" in str(e):
                        state = default_state_dir(fx.name, args.out)
                        _warn(f"skipping {fx.name}: leftover state at {state}. "
                              f"Delete it (rm -rf '{state}') for a fresh run, or "
                              f"finish it with: python3 -m harness verify "
                              f"--resume {fx.name}")
                        rows.append({"name": fx.name, "verdict": "STATE_EXISTS",
                                     "cost_usd": None})
                        continue
                    _die(str(e))
                saved = _save_artifacts(out, Path(args.out))
                report_obj = _final_report_object(out, saved)
                print_result(
                    out,
                    cert=saved.get("main_certificate"),
                    artifacts=saved.get("artifacts"),
                    report=report_obj,
                )
                clean = _is_clean_verdict(out["verdict_line"])
                record = saved.get("record_data") or {}
                verdict_class = (
                    (report_obj.get("verdict") or {}).get("class")
                    or out["verdict_line"].splitlines()[0].replace(
                        "VERDICT:", ""
                    ).strip()
                )
                if clean:
                    paper.mark_verified(
                        label,
                        lean_name=label,
                        lean_statement=str(record.get("main_statement") or ""),
                        kernel_axioms=list(record.get("kernel_axioms") or []),
                        verdict=verdict_class,
                        evidence=(report_obj.get("verdict") or {}).get(
                            "evidence", "kernel"
                        ),
                        lean_code=str(record.get("main_code") or ""),
                        artifacts=saved.get("artifacts") or [],
                    )
                    verified_prior[label] = {
                        "name": label,
                        "statement": str(record.get("main_statement") or ""),
                        "code": str(record.get("main_code") or ""),
                        "artifact": saved.get("main_certificate") or "",
                        "kernel_axioms": list(record.get("kernel_axioms") or []),
                    }
                else:
                    paper.mark_failed(
                        label,
                        verdict_class,
                        note=(report_obj.get("verdict") or {}).get(
                            "reason", ""
                        ),
                        evidence=(report_obj.get("verdict") or {}).get(
                            "evidence", ""
                        ),
                    )
                row = {"name": fx.name,
                       "verdict": verdict_class,
                       "status": "verified" if clean else "failed",
                       "cost_usd": out.get("cost_usd"),
                       "clean": clean,
                       "statement": fx.statement,
                       "artifacts": saved.get("artifacts") or [],
                       "report_obj": report_obj,
                       "record": record,
                       "lean_code": str(record.get("main_code") or ""),
                       "evidence": (report_obj.get("verdict") or {}).get("evidence"),
                       "reason": (report_obj.get("verdict") or {}).get("reason")}
                rows.append(row)
                if out.get("state_dir"):
                    completed_states.append(str(out["state_dir"]))
            for label in omitted:
                component = paper.components[label]
                rows.append({
                    "name": label,
                    "verdict": component.verdict,
                    "status": component.status,
                    "reason": component.note,
                    "evidence": "workflow cap",
                    "statement": component.statement,
                    "cost_usd": None,
                    "artifacts": [],
                })

            main_rows = [
                row for row in rows
                if row.get("name") in paper.components
                and paper.components[row["name"]].is_main
                and row.get("record")
            ]
            if main_rows:
                main_record = main_rows[-1]["record"]
                paper.metadata["paper_sketch"] = {
                    "status": (
                        "PASS" if main_record.get("sketch_verified")
                        else "FAIL"
                    ),
                    "expected_blocks": list(
                        main_record.get("sketch_expected_blocks") or []
                    ),
                    "evidence": (
                        "main component's prior-aware, kernel-compiled "
                        "full-process sketch"
                    ),
                }
            paper.metadata["assembly"] = _assemble_paper_final(
                paper, rows, Path(args.out)
            )
            paper_record = paper.record()
            paper_record_path = (
                Path(args.out) / f"{paper_name}-paper-record.json"
            )
            paper_record_path.parent.mkdir(parents=True, exist_ok=True)
            import json
            paper_record_path.write_text(
                json.dumps(paper_record, indent=2, ensure_ascii=False) + "\n"
            )
            print("\n" + _render_paper_terminal(
                paper_name, rows, paper_record
            ))
            paper_source, paper_notes = _fixture_source(fixtures[0]) if fixtures else (None, [])
            report_path = _write_paper_report(args, paper_name, rows,
                                              paper_record,
                                              source=paper_source,
                                              source_notes=paper_notes)
            if report_path:
                print(f"  report       {_c('→', '2')}  {report_path}")
            print(f"  paper record {_c('→', '2')}  {os.path.relpath(paper_record_path)}")
            if not getattr(args, "keep_intermediates", False):
                for state in completed_states:
                    _cleanup_finished_run(state, args.out)
                for fixture in fixtures:
                    _cleanup_materialized_fixture(fixture.path)
            return 0 if rows and all(r.get("clean") for r in rows) else 1

        try:
            fixture = ingest_to_fixture(
                args.target,
                theorem=args.theorem,
                call_model=get_backend(args.backend, model=model,
                                       timeout=args.gate_timeout,
                                       reasoning_effort=reasoning_effort,
                                       service_tier=service_tier),
            )
        except Exception as e:
            _die(str(e))
        print(f"  fixture written to {fixture.path}")
        print(f"  rerun with: python3 -m harness verify {fixture.path}")
        formal_units = [_unit_from_fixture(fixture)]
        _print_cost_estimate(args, formal_units, model, reasoning_effort,
                             agent_timeout_s)
        formal_estimate_printed = True
        if args.dry_run:
            return 0
        if sys.stdin.isatty():
            print("  Ctrl-C now to review/edit the fixture before verification.")
            time.sleep(3)
        name = args.name or fixture.name
        statement, proof, claim = fixture.statement, fixture.proof, fixture.claim
        report_source, report_notes = _fixture_source(fixture)
        generated_fixture_path = fixture.path
    elif not args.resume:
        name, statement, proof, claim = _resolve_inputs(args)
        formal_units = [_unit_from_parts(name, statement, proof, claim)]
        report_source, report_notes = _source_from_fixture_dir(args.target)

    if args.dry_run:
        print(f"  dry-run: resolved input '{name}'")
        print(f"  statement: {len(statement)} chars")
        print(f"  proof:     {len(proof)} chars")
        if claim:
            print(f"  claim:     {len(claim)} chars")
        if formal_units is not None:
            _print_cost_estimate(args, formal_units, model, reasoning_effort,
                                 agent_timeout_s)
        print("  no agent launched; no tokens spent")
        return 0

    _resolve_sandbox(args)

    if formal_units is not None and not formal_estimate_printed:
        _print_cost_estimate(args, formal_units, model, reasoning_effort,
                             agent_timeout_s)

    print(f"\n{_c('Verifying', '1')}: {statement[:100]}{'…' if len(statement) > 100 else ''}")
    _warn(f"this spends tokens on your '{args.backend}' account "
          "(driving agent + sealed gate calls).")
    _warn("actual cost can differ from the estimate if the agent retries or stalls.")

    # Spend confirmation (T22): the run costs real money and can take many
    # minutes. On a TTY, confirm first unless -y/--yes; non-interactive (CI)
    # proceeds after the warning above.
    if not _confirm_spend(args):
        return 130

    try:
        state_dir = default_state_dir(name, args.out)
        out = run_verification(
            name, statement=statement, proof=proof, nl_claim=claim,
            call_model=get_backend(args.backend, model=model,
                                   timeout=args.gate_timeout,
                                   reasoning_effort=reasoning_effort,
                                   service_tier=service_tier),    # sealed grader
            agent_drive=launch_agent(backend=args.backend, model=model,
                                     timeout=args.budget,
                                     quiet=args.quiet,
                                     reasoning_effort=reasoning_effort,
                                     service_tier=service_tier),  # your agent drives
            agent_context=agent_context,
            state_dir=state_dir, resume=bool(args.resume),
            continue_structural=args.continue_structural,
            continue_unresolved=args.continue_unresolved,
            source_meta=({"source": report_source, "notes": report_notes}
                         if report_source or report_notes else None),
        )
    except AgentBudgetExceeded as e:
        print(_c(f"  ✗ {e}", "31"), file=sys.stderr)
        print(f"  state kept at {state_dir}", file=sys.stderr)
        print(f"  resume with: python3 -m harness verify --resume {name}",
              file=sys.stderr)
        return 1
    except RuntimeError as e:  # auth/launch failure is raised loudly by the runner
        _die(str(e))

    out_dir = Path(args.out)
    saved = _save_artifacts(out, out_dir)
    cert = saved["main_certificate"]
    written = _write_markdown_report(args, name, out, saved,
                                     original_claim=(claim or statement),
                                     source=report_source, source_notes=report_notes)
    report_path = written[0] if written is not None else None
    report_obj = (
        written[1] if written is not None
        else _final_report_object(out, saved)
    )
    cleaned = False
    if (
        not getattr(args, "keep_intermediates", False)
        and not out.get("paused")
        and out.get("verdict_line")
    ):
        cleaned = _cleanup_finished_run(out.get("state_dir"), args.out)
        if generated_fixture_path is not None:
            _cleanup_materialized_fixture(generated_fixture_path)
        if cleaned:
            out["state_dir"] = None
    out["intermediates_cleaned"] = cleaned

    if args.json:
        import json
        structured_verdict = report_obj.get("verdict") or {}
        # surface only the user-facing fields — drop the internal temp corpus
        # path and rename the journal key to the user's --name.
        print(json.dumps({"name": out["fixture"], "verdict_line": out["verdict_line"],
                          "verdict": structured_verdict,
                          "paused": bool(out.get("paused")),
                          "decision_required": bool(out.get("decision_required")),
                          "preflight": out.get("preflight"),
                          "triage_suspects": out.get("triage_suspects"),
                          "certificate": cert, "cost_usd": out.get("cost_usd"),
                          "wall_s": out.get("wall_s"),
                          "phase_telemetry": out.get("phase_telemetry"),
                          "state_dir": out.get("state_dir"),
                          "intermediates_cleaned": cleaned,
                          "structural": out.get("structural"),
                          "artifacts": saved.get("artifacts"),
                          "integrity_manifest": saved.get("integrity_manifest"),
                          "input": saved.get("input"),
                          "report": report_path}, indent=2))
    else:
        print_result(
            out,
            cert=cert,
            artifacts=saved.get("artifacts"),
            report=report_obj,
        )
        if out.get("paused"):
            if (out.get("preflight") or {}).get("status") in {
                "CONFIRMED_THEOREM_REFUTATION",
                "CONFIRMED_PROOF_STEP_FAILURE",
                "CONFIRMED_WELL_DEFINEDNESS_GAP",
            }:
                options = (
                    f"stop, or resume with `python3 -m harness verify --resume "
                    f"{name} --continue-structural`"
                )
            else:
                options = (
                    f"stop; resume full with `python3 -m harness verify "
                    f"--resume {name} --continue-unresolved`; or salvage with "
                    f"`python3 -m harness verify --resume {name} "
                    "--continue-structural`"
                )
            print(_c(f"  decision required: {options}", "33"))
        if report_path:
            print(f"  report       {_c('→', '2')}  {report_path}")
        if cleaned:
            print("  intermediates →  removed; final report/evidence bundle retained")
        print(_c("  verdict glossary: VERIFIED=kernel-clean proof · UNVERIFIED/WRONG="
                 "main theorem refuted · UNVERIFIED/PROOF_INVALID=submitted proof "
                 "step refuted · UNVERIFIED/HYPOTHESIS_VIOLATION=restatement needed · "
                 "UNVERIFIED/UNGATED=compiled but a gate didn't run · "
                 "HAS GAPS=agent didn't finish", "2"))

    # Three-code scheme so CI and "confirming a flaw" both read correctly:
    #   0 = clean VERIFIED (the proof passed)
    #   1 = a real verdict that isn't a clean pass (WRONG / INCOMPLETE / UNGATED /
    #       MODULO-AXIOMS / HAS GAPS — the tool worked, the proof didn't verify)
    #   2 = tool/usage/auth error (handled earlier via sys.exit, which exits 2)
    line = out["verdict_line"]
    return 0 if _is_clean_verdict(line) else 1


def _cmd_doctor(args) -> int:
    script = ROOT / "harness" / "setup.sh"
    if not script.exists():
        _die(f"{script} not found")
    bash = shutil.which("bash")
    if not bash:
        _die(f"bash not found on PATH — run the script directly: {script}")
    env = dict(os.environ)
    if args.check_auth:
        env["CHECK_AUTH"] = "1"
    if args.skip_build:
        env["SKIP_BUILD"] = "1"
    env["HARNESS_BACKEND"] = args.backend
    os.execve(bash, [bash, str(script)], env)  # replaces this process


def _reasoning_effort_for_backend(args) -> str | None:
    if getattr(args, "backend", None) == "codex":
        return getattr(args, "reasoning_effort", None)
    return None


def _cmd_triage(args) -> int:
    from harness.backends import get_backend
    from harness.triage import sealed_triage
    from harness.report import render_triage_card

    model = args.model
    if args.backend != "claude" and model == "opus":
        model = None
    reasoning_effort = _reasoning_effort_for_backend(args)
    service_tier = getattr(args, "service_tier", None)
    try:
        call_model = get_backend(args.backend, model=model,
                                 timeout=args.gate_timeout,
                                 reasoning_effort=reasoning_effort,
                                 service_tier=service_tier)
    except Exception as e:
        _die(str(e))
    _name, statement, proof = _resolve_advisory_input(args, call_model=call_model)
    result = sealed_triage(f"{statement}\n\n{proof}", call_model)
    if args.json:
        import json
        print(json.dumps(result, indent=2))
    else:
        print(render_triage_card(result))
    return 2 if result.get("error") else 0


def _cmd_audit(args) -> int:
    from harness.backends import get_backend
    from harness.hypothesis_audit import sealed_hypothesis_audit
    from harness.report import render_audit_card
    from harness.runner import DEFAULT_CORPUS, _make_corpus_lookup

    model = args.model
    if args.backend != "claude" and model == "opus":
        model = None
    reasoning_effort = _reasoning_effort_for_backend(args)
    service_tier = getattr(args, "service_tier", None)
    try:
        call_model = get_backend(args.backend, model=model,
                                 timeout=args.gate_timeout,
                                 reasoning_effort=reasoning_effort,
                                 service_tier=service_tier)
    except Exception as e:
        _die(str(e))
    _name, statement, proof = _resolve_advisory_input(args, call_model=call_model)
    result = sealed_hypothesis_audit(
        statement, proof, call_model,
        lookup=_make_corpus_lookup(str(DEFAULT_CORPUS)),
    )
    if args.json:
        import json
        print(json.dumps(result, indent=2))
    else:
        print(render_audit_card(result))
    return 2 if result.get("overall") == "ERROR" else 0


def _cmd_falsify(args) -> int:
    from rlverify.falsify import FalsifyReport
    from rlverify.falsify_run import SamplerError, load_sampler, run_sampler
    from harness.report import render_falsify_card

    sampler_path: Path | None = None
    generated_code: str | None = None
    generated_block = ""
    generated_claim = ""
    if args.sampler:
        sampler_path = Path(args.sampler)
    elif _is_sampler_path(args.target):
        sampler_path = Path(args.target)

    if sampler_path is None:
        if not (args.target or args.statement or args.proof or args.claim):
            _die("provide a claim, a sampler .py file, '-', a folder, or -s/--statement")
        if not _confirm_sampler_execution(args):
            return 130
        from harness.backends import get_backend
        from harness.falsify import generate_sampler_spec, write_generated_sampler

        model = args.model
        if args.backend != "claude" and model == "opus":
            model = None
        reasoning_effort = _reasoning_effort_for_backend(args)
        service_tier = getattr(args, "service_tier", None)
        try:
            call_model = get_backend(args.backend, model=model,
                                     timeout=args.gate_timeout,
                                     reasoning_effort=reasoning_effort,
                                     service_tier=service_tier)
        except Exception as e:
            _die(str(e))
        name, claim_text = _resolve_falsify_claim(args, call_model=call_model)
        try:
            spec = generate_sampler_spec(
                claim_text, call_model, block=args.block or name,
                n=args.n, tol=args.tol,
            )
            generated_code = spec.sampler_code
            generated_block = spec.block
            generated_claim = spec.claim or claim_text
            sampler_path = write_generated_sampler(spec, path=args.save_sampler)
        except Exception as e:
            _die(str(e))
    elif not _confirm_sampler_execution(args):
        return 130

    if generated_code is not None:
        # Model-generated Python is never imported into the host interpreter.
        # The one execution path is the confined runner; unsupported platforms
        # fail closed instead of falling back to --trust-samplers.
        from verify_app.confined_python import (
            ConfinedPythonUnavailable,
            UnsafeSampler,
            run_confined_sampler,
        )
        try:
            confined = run_confined_sampler(
                generated_code,
                n=args.n or 200_000,
                seed=args.seed,
                tolerance=args.tol or 1e-9,
            )
        except (ConfinedPythonUnavailable, UnsafeSampler, ValueError) as e:
            _die(f"generated sampler was not executed: {e}")
        verdict = (
            "PASSED" if confined.verdict == "NO_COUNTEREXAMPLE"
            else confined.verdict
        )
        report = FalsifyReport(
            block=args.block or generated_block,
            verdict=verdict,
            claim=generated_claim,
            instances=confined.instances,
            hyp_satisfied=confined.hyp_satisfied,
            violations=confined.violations,
            max_violation=confined.max_violation,
            tolerance=args.tol or 1e-9,
            certificate=confined.certificate,
            # The search was confined and harness-executed, but its formulas
            # and optional recheck were authored by the same model. It remains
            # audit evidence, never an independent certificate.
            reason=(
                "dep|confined|agent-authored formula; independent checker absent"
                if verdict == "REFUTED" else ""
            ),
            executed_by="harness",
        )
    else:
        try:
            mod = load_sampler(sampler_path)
            if args.block:
                setattr(mod, "BLOCK", args.block)
            report = run_sampler(mod, n=args.n, seed=args.seed, tol=args.tol)
        except (FileNotFoundError, ImportError, AttributeError) as e:
            _die(f"could not load sampler: {e}")
        except SamplerError as e:
            _die(f"sampler error: {e}")

    if args.json:
        import json
        data = report.to_dict()
        data["seed"] = args.seed
        data["sampler"] = str(sampler_path)
        print(json.dumps(data, indent=2))
    else:
        print(render_falsify_card(report, seed=args.seed,
                                  sampler_path=str(sampler_path)))
    return 1 if report.verdict == "REFUTED" else 0


# --------------------------------------------------------------------------

def _default_backend() -> str:
    return os.environ.get("HARNESS_BACKEND", "claude")


def build_parser() -> argparse.ArgumentParser:
    default_backend = _default_backend()
    p = argparse.ArgumentParser(
        prog="python3 -m harness",
        description="RLVerify BYO-agent harness — verify a theorem+proof with your "
                    "own agent account; the Lean kernel issues the verdict.")
    sub = p.add_subparsers(dest="cmd", required=True)

    v = sub.add_parser("verify", help="verify a theorem + proof")
    v.add_argument("target", nargs="?",
                   help="folder, .pdf/.tex/.md/.txt, URL/arXiv id, or '-' for stdin")
    v.add_argument("-s", "--statement", help="theorem statement: a file path OR inline text")
    v.add_argument("-p", "--proof", help="proof sketch: a file path OR inline text")
    v.add_argument("-c", "--claim", help="plain-English claim for the back-translation gate "
                                         "(file or inline; defaults to the statement)")
    v.add_argument("-n", "--name", help="run name (default: folder name)")
    v.add_argument("--theorem", help="the theorem label to extract from a paper input")
    v.add_argument("--all-theorems", action="store_true",
                   help="extract and verify every theorem candidate in a paper input")
    v.add_argument("--dry-run", action="store_true",
                   help="resolve/extract input, print the formal-proof estimate, "
                        "and stop before launching the agent")
    v.add_argument("--resume", metavar="NAME",
                   help="resume a stalled/timed-out run from ./rlverify-out/.state/NAME")
    v.add_argument(
        "--continue-structural",
        action="store_true",
        help="after serious preflight findings, verify the remaining proof "
             "modulo explicit named placeholders; can never yield VERIFIED",
    )
    v.add_argument(
        "--continue-unresolved",
        action="store_true",
        help="after targeted confirmation remains unresolved, explicitly "
             "authorize the full Lean verification path",
    )
    v.add_argument("--backend", default=default_backend,
                   help="agent backend (default: HARNESS_BACKEND or claude)")
    v.add_argument("--model", default="opus",
                   help="model (default: opus for claude; codex uses its CLI default when omitted)")
    v.add_argument("--reasoning-effort", choices=["low", "medium", "high", "xhigh"],
                   help="Codex model reasoning effort; overrides Codex config for "
                        "the driving agent and sealed grader")
    v.add_argument("--service-tier", choices=["default", "priority"],
                   help="Codex service tier for the driving agent and sealed grader")
    v.add_argument("--gate-timeout", type=int, default=600,
                   help="seconds for each sealed gate call (default: 600); a "
                        "grader timeout reads as a gate error, not a proof defect")
    v.add_argument("--budget", type=int, default=None,
                   help="seconds for the driving agent (default: 1800; overrides "
                        "RLVERIFY_AGENT_TIMEOUT)")
    v.add_argument("--agent-context",
                   help="file path or short inline context from the foreground "
                        "conversation; advisory only, never a theorem hypothesis")
    v.add_argument("--quiet", action="store_true",
                   help="suppress live per-tool progress from the driving agent")
    v.add_argument("--out", default="rlverify-out", help="where to save the certificate "
                                                        "(default: ./rlverify-out)")
    v.add_argument("--no-sandbox", action="store_true",
                   help="run Lean UNCONFINED (drops the untrusted guarantee; required "
                        "off macOS until the Linux sandbox lands)")
    v.add_argument("--json", action="store_true", help="emit the raw result dict as JSON")
    v.add_argument("--report", nargs="?", const="", default=None,
                   help="write a Markdown report (default path: ./rlverify-out/<name>-report.md; "
                        "pass a path to override)")
    v.add_argument(
        "--keep-intermediates",
        action="store_true",
        help="debugging only: retain resumable state and generated paper fixtures "
             "after a terminal result (default: keep only the final evidence bundle)",
    )
    v.add_argument("-y", "--yes", action="store_true",
                   help="skip the spend-confirmation prompt (implied when non-interactive)")
    v.set_defaults(func=_cmd_verify)

    d = sub.add_parser("doctor", help="provision + health-check (runs harness/setup.sh)")
    d.add_argument("--backend", choices=["claude", "codex"], default=default_backend,
                   help="agent backend CLI to check (default: HARNESS_BACKEND or claude)")
    d.add_argument("--check-auth", action="store_true", help="live-test agent login (spends tokens)")
    d.add_argument("--skip-build", action="store_true", help="skip the heavy Mathlib build")
    d.set_defaults(func=_cmd_doctor)

    t = sub.add_parser("triage", help="run sealed adversarial triage only (advisory)")
    t.add_argument("target", nargs="?", help="folder, paper file/URL, '-' for stdin, or use -s/-p")
    t.add_argument("-s", "--statement", help="statement: file path OR inline text")
    t.add_argument("-p", "--proof", help="proof: file path OR inline text")
    t.add_argument("-c", "--claim", help=argparse.SUPPRESS)
    t.add_argument("-n", "--name", help="input name")
    t.add_argument("--theorem", help="the theorem label to extract from a paper input")
    t.add_argument("--backend", default=default_backend,
                   help="sealed backend (default: HARNESS_BACKEND or claude)")
    t.add_argument("--model", default="opus",
                   help="model (default: opus for claude; codex uses its CLI default when omitted)")
    t.add_argument("--reasoning-effort", choices=["low", "medium", "high", "xhigh"],
                   help="Codex model reasoning effort for the sealed call")
    t.add_argument("--service-tier", choices=["default", "priority"],
                   help="Codex service tier for the sealed call")
    t.add_argument("--gate-timeout", type=int, default=600,
                   help="seconds for the sealed triage call (default: 600)")
    t.add_argument("--json", action="store_true", help="emit JSON")
    t.set_defaults(func=_cmd_triage)

    a = sub.add_parser("audit", help="run sealed hypothesis audit only (advisory)")
    a.add_argument("target", nargs="?", help="folder, paper file/URL, '-' for stdin, or use -s/-p")
    a.add_argument("-s", "--statement", help="statement: file path OR inline text")
    a.add_argument("-p", "--proof", help="proof: file path OR inline text")
    a.add_argument("-c", "--claim", help=argparse.SUPPRESS)
    a.add_argument("-n", "--name", help="input name")
    a.add_argument("--theorem", help="the theorem label to extract from a paper input")
    a.add_argument("--backend", default=default_backend,
                   help="sealed backend (default: HARNESS_BACKEND or claude)")
    a.add_argument("--model", default="opus",
                   help="model (default: opus for claude; codex uses its CLI default when omitted)")
    a.add_argument("--reasoning-effort", choices=["low", "medium", "high", "xhigh"],
                   help="Codex model reasoning effort for sealed calls")
    a.add_argument("--service-tier", choices=["default", "priority"],
                   help="Codex service tier for sealed calls")
    a.add_argument("--gate-timeout", type=int, default=600,
                   help="seconds for the sealed audit calls (default: 600)")
    a.add_argument("--json", action="store_true", help="emit JSON")
    a.set_defaults(func=_cmd_audit)

    f = sub.add_parser("falsify", help="run seeded numeric falsification only")
    f.add_argument("target", nargs="?",
                   help="claim text, sampler .py, folder, paper file/URL, or '-' for stdin")
    f.add_argument("--sampler", help="path to a sampler .py file; skips sampler generation")
    f.add_argument("-s", "--statement", help="statement/context: file path OR inline text")
    f.add_argument("-p", "--proof", help="proof/context: file path OR inline text")
    f.add_argument("-c", "--claim", help="claim to falsify: file path OR inline text")
    f.add_argument("--name", help="input name")
    f.add_argument("--theorem", help="the theorem label to extract from a paper input")
    f.add_argument("--block", default="", help="block/step label for the falsification card")
    f.add_argument("--backend", default=default_backend,
                   help="sealed backend for sampler generation (default: HARNESS_BACKEND or claude)")
    f.add_argument("--model", default="opus",
                   help="model (default: opus for claude; codex uses its CLI default when omitted)")
    f.add_argument("--reasoning-effort", choices=["low", "medium", "high", "xhigh"],
                   help="Codex model reasoning effort for sampler generation")
    f.add_argument("--service-tier", choices=["default", "priority"],
                   help="Codex service tier for sampler generation")
    f.add_argument("--gate-timeout", type=int, default=600,
                   help="seconds for sealed sampler generation (default: 600)")
    f.add_argument("--n", type=int, help="number of samples to draw")
    f.add_argument("--seed", type=int, default=0, help="RNG seed (default: 0)")
    f.add_argument("--tol", type=float, help="relative violation tolerance")
    f.add_argument("--save-sampler",
                   help="where to write a generated sampler (default: rlverify-out/falsify/...)")
    f.add_argument("--trust-samplers", action="store_true",
                   help="allow execution of model-generated Python sampler code")
    f.add_argument("--json", action="store_true", help="emit JSON")
    f.set_defaults(func=_cmd_falsify)
    return p


def main(argv=None) -> int:
    args = build_parser().parse_args(argv)
    try:
        return args.func(args)
    except KeyboardInterrupt:
        # Clean Ctrl-C (T20): no traceback, and terminate the Claude child tree
        # if it was launched in its own process group for streaming cleanup.
        try:
            from harness.runner import terminate_active_agents
            terminate_active_agents()
        except Exception:
            pass
        # Any fixture/certificate already written under ./rlverify-out is kept.
        print(_c("\n  ✗ interrupted — no verdict. Any fixture/certificate already "
                 "written under ./rlverify-out is kept.", "31"), file=sys.stderr)
        return 130


if __name__ == "__main__":
    sys.exit(main())
