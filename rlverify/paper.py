"""Paper-level orchestration for ``/verifyRL-paper``.

This module owns the *cross-component* concerns that a single ``/verify-full-process`` run
structurally cannot see — dependency graph, cycle detection, topological order,
a paper-level sketch (does the main theorem actually follow from its claimed
lemma dependencies?), accumulation of verified components as reusable ``prior``
facts, and a structured paper-level record.

It **composes** the single-proof :class:`rlverify.driver.VerifyDriver` — it only
*calls* the (frozen) driver for the actual Lean work (``compile`` / ``sketch`` /
``formalize`` / ``assemble`` / ``add_novel``). It never modifies the driver or
the verifyRL procedure: per-component verification is still the mature verifyRL
pipeline; this layer is the glue between components.

Typical use from the ``/verifyRL-paper`` skill::

    from rlverify.paper import PaperSession
    p = PaperSession("jin2018_qlearning")
    p.add_component("survival",  stmt_nl, proof_nl, deps=[])
    p.add_component("alpha",     stmt_nl, proof_nl, deps=["survival"], is_main=True)
    p.add_component("azuma", "...", external=True)          # cited result -> library/axiom lane
    cyc = p.detect_cycle()                                  # STOP if not None
    for label in p.topo_order():                            # verify in this order
        ...                                                 # run /verify-full-process on the component
        p.mark_verified(label, lean_name=..., lean_statement=..., kernel_axioms=[...])
    p.save()                                                # runs/papers/<name>.json
"""

from __future__ import annotations

import json
from dataclasses import dataclass, field
from pathlib import Path

try:
    from .driver import VerifyDriver, ROOT
except Exception:  # pragma: no cover - allows standalone import for graph-only use
    VerifyDriver = None  # type: ignore
    ROOT = Path(__file__).resolve().parent.parent

STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


@dataclass
class Component:
    """One theorem/lemma/proposition/corollary/definition from the paper."""

    label: str
    statement: str = ""                # NL or LaTeX statement
    proof: str = ""                    # NL/LaTeX proof text
    kind: str = "lemma"               # lemma|theorem|proposition|corollary|claim|definition
    deps: list[str] = field(default_factory=list)   # labels of OTHER components used
    external: bool = False             # restates a cited result (library/axiom lane)
    is_main: bool = False              # the paper's headline result

    # filled in during verification
    status: str = "pending"           # pending|verified|failed|skipped
    verdict: str = ""                 # per-component verdict (verifyRL Rule 7 vocabulary)
    lean_name: str = ""               # the compiled Lean identifier
    lean_statement: str = ""          # the compiled Lean signature (for prior-reuse / paper sketch)
    library_module: str = ""          # set if added to the library (import path)
    kernel_axioms: list[str] = field(default_factory=list)
    note: str = ""
    evidence: str = ""
    lean_code: str = ""
    artifacts: list[dict] = field(default_factory=list)

    @property
    def verifiable(self) -> bool:
        return not self.external and self.kind != "definition"


class PaperSession:
    def __init__(self, name: str, driver=None, corpus_path: str | None = None):
        self.name = name
        self.components: dict[str, Component] = {}
        self._insertion: list[str] = []          # document order, for deterministic tie-breaks
        self.standing_assumptions: list[str] = []
        self.cycle: list[str] | None = None
        self.metadata: dict = {}
        self._driver = driver
        self._corpus_path = corpus_path

    # -- driver is created lazily so graph-only use needs no Lean toolchain -----
    @property
    def driver(self):
        if self._driver is None:
            if VerifyDriver is None:
                raise RuntimeError("VerifyDriver unavailable; graph-only mode")
            self._driver = VerifyDriver(corpus_path=self._corpus_path)
        return self._driver

    # ------------------------------------------------------------------ build
    def add_component(self, label: str, statement: str = "", proof: str = "",
                      deps: list[str] | None = None, kind: str = "lemma",
                      external: bool = False, is_main: bool = False) -> Component:
        if label in self.components:
            raise ValueError(f"duplicate component label: {label!r}")
        c = Component(label=label, statement=statement, proof=proof, kind=kind,
                      deps=list(deps or []), external=external, is_main=is_main)
        self.components[label] = c
        self._insertion.append(label)
        return c

    def add_standing_assumption(self, text: str) -> None:
        self.standing_assumptions.append(text)

    # ------------------------------------------------------------- graph core
    def dependency_graph(self) -> dict[str, list[str]]:
        """label -> list of *verifiable* component labels it depends on.

        Edges to external/cited components and to definitions are dropped (those
        are context / library-axiom lane, never verified nodes). Unknown deps are
        ignored here and surfaced by :meth:`unknown_deps`.
        """
        g: dict[str, list[str]] = {}
        for label, c in self.components.items():
            if not c.verifiable:
                continue
            edges = []
            for d in c.deps:
                dc = self.components.get(d)
                if dc is not None and dc.verifiable:
                    edges.append(d)
            g[label] = edges
        return g

    def unknown_deps(self) -> dict[str, list[str]]:
        """Components that cite a label not present in the paper (dangling edges)."""
        out: dict[str, list[str]] = {}
        for label, c in self.components.items():
            missing = [d for d in c.deps if d not in self.components]
            if missing:
                out[label] = missing
        return out

    def detect_cycle(self) -> list[str] | None:
        """Return a cycle path (e.g. ['L3','L5','L4','L3']) or None. Sets self.cycle."""
        g = self.dependency_graph()
        WHITE, GRAY, BLACK = 0, 1, 2
        color = {n: WHITE for n in g}
        stack: list[str] = []

        def dfs(u: str) -> list[str] | None:
            color[u] = GRAY
            stack.append(u)
            for v in g.get(u, []):
                if color.get(v, BLACK) == GRAY:        # back-edge -> cycle
                    i = stack.index(v)
                    return stack[i:] + [v]
                if color.get(v, BLACK) == WHITE:
                    r = dfs(v)
                    if r is not None:
                        return r
            stack.pop()
            color[u] = BLACK
            return None

        for n in self._insertion:                      # deterministic start order
            if n in color and color[n] == WHITE:
                r = dfs(n)
                if r is not None:
                    self.cycle = r
                    return r
        self.cycle = None
        return None

    def topo_order(self) -> list[str]:
        """Verifiable components in dependency order (deps before dependents).

        Tie-break rules: definitions are not nodes; lemmas before theorems at the
        same depth; document (insertion) order breaks remaining ties. Raises if a
        cycle exists — call :meth:`detect_cycle` first.
        """
        g = self.dependency_graph()
        if self.detect_cycle() is not None:
            raise ValueError(f"dependency cycle: {' -> '.join(self.cycle)}")
        indeg = {n: 0 for n in g}
        for n in g:
            for m in g[n]:
                indeg[n] += 0  # n depends on m; we want m before n
        # build dependents map: m -> [n that depend on m]
        dependents: dict[str, list[str]] = {n: [] for n in g}
        indeg = {n: len(g[n]) for n in g}
        for n in g:
            for m in g[n]:
                dependents[m].append(n)

        def rank(label: str) -> tuple:
            c = self.components[label]
            kind_rank = 0 if c.kind in ("lemma", "proposition", "claim") else 1
            return (kind_rank, self._insertion.index(label))

        ready = sorted([n for n in g if indeg[n] == 0], key=rank)
        order: list[str] = []
        while ready:
            n = ready.pop(0)
            order.append(n)
            for m in dependents[n]:
                indeg[m] -= 1
                if indeg[m] == 0:
                    ready.append(m)
            ready.sort(key=rank)
        if len(order) != len(g):
            raise ValueError("topological sort failed (residual cycle)")
        return order

    def plan(self) -> str:
        """Human-readable verification plan (graph + order + routing)."""
        lines = [f"Paper: {self.name}", "Dependency graph (verifiable components):"]
        g = self.dependency_graph()
        for n in self._insertion:
            if n in g:
                deps = ", ".join(g[n]) or "(none)"
                main = " [MAIN]" if self.components[n].is_main else ""
                lines.append(f"  {n}{main} -> {deps}")
        ext = [l for l in self._insertion if self.components[l].external]
        if ext:
            lines.append("Cited/external (library-axiom lane, not verified): " + ", ".join(ext))
        defs = [l for l in self._insertion if self.components[l].kind == "definition"]
        if defs:
            lines.append("Definitions (context only): " + ", ".join(defs))
        cyc = self.detect_cycle()
        if cyc:
            lines.append("CIRCULAR: " + " -> ".join(cyc))
        else:
            lines.append("Verification order: " + " -> ".join(self.topo_order()))
        return "\n".join(lines)

    # -------------------------------------------------------- accumulation
    def verified_deps(self, label: str) -> list[Component]:
        """Transitive verified dependencies of *label*, in topo order."""
        seen: set[str] = set()
        out: list[str] = []

        def walk(u: str) -> None:
            for d in self.components.get(u, Component(u)).deps:
                dc = self.components.get(d)
                if dc and dc.verifiable and dc.status == "verified" and d not in seen:
                    seen.add(d)
                    walk(d)
                    out.append(d)
        walk(label)
        order = self.topo_order()
        out.sort(key=lambda x: order.index(x) if x in order else 0)
        return [self.components[d] for d in out]

    def prior_context(self, label: str) -> dict:
        """Imports + stub statements for a component's verified dependencies.

        ``imports`` lists library modules for deps already added via add_novel;
        ``stub_statements`` maps name->Lean signature for the paper-level sketch
        (deps not yet in the library are stubbed with ``sorry``).
        """
        imports, stubs = [], {}
        for dep in self.verified_deps(label):
            if dep.library_module:
                imports.append(dep.library_module)
            elif dep.lean_statement:
                stubs[dep.lean_name or dep.label] = dep.lean_statement
        return {"imports": imports, "stub_statements": stubs}

    # --------------------------------------------------------- paper sketch
    def paper_sketch(self, main_label: str, lean_statement: str, lean_proof: str,
                     imports: list[str] | None = None,
                     opens: str = "Finset BigOperators"):
        """Machine-check that the main theorem follows from its claimed lemma deps.

        Stubs every verified dependency of *main_label* with ``sorry`` and tries
        to compile the main proof against them. Success ⇒ the dependency edges
        really do entail the main result (the paper-level analogue of the
        single-proof ``d.sketch``). Failure with unsolved goals ⇒ a missing edge
        or a genuine gap. Uses only ``driver.compile`` (verifyRL is untouched).
        """
        ctx = self.prior_context(main_label)
        imp = list(imports or ["Mathlib"]) + ctx["imports"]
        import_block = "\n".join(f"import {m}" for m in dict.fromkeys(imp))
        open_block = f"open {opens}\n\n" if opens.strip() else ""
        stub_block = "\n\n".join(f"{sig} := sorry"
                                 for sig in ctx["stub_statements"].values())
        if stub_block:
            stub_block += "\n\n"
        code = f"{import_block}\n\n{open_block}{stub_block}{lean_statement} := by\n  {lean_proof}"
        # Use the driver's sketch: it allows the intentional stub `sorry`s and
        # FAILS if the main proof does not actually use every stubbed dependency
        # (a missing edge / vacuous glue). The stub names are the expected blocks.
        return self.driver.sketch(code, expected_blocks=list(ctx["stub_statements"].keys()))

    # -------------------------------------------------------------- record
    def mark_verified(self, label: str, lean_name: str = "", lean_statement: str = "",
                      library_module: str = "", kernel_axioms: list[str] | None = None,
                      verdict: str = "VERIFIED", evidence: str = "kernel",
                      lean_code: str = "",
                      artifacts: list[dict] | None = None) -> None:
        c = self.components[label]
        c.status = "verified"
        c.verdict = verdict
        c.lean_name = lean_name
        c.lean_statement = lean_statement
        c.library_module = library_module
        c.kernel_axioms = list(kernel_axioms or [])
        c.evidence = evidence
        c.lean_code = lean_code
        c.artifacts = list(artifacts or [])

    def mark_failed(self, label: str, verdict: str, note: str = "",
                    evidence: str = "") -> None:
        c = self.components[label]
        c.status = "failed"
        c.verdict = verdict
        c.note = note
        c.evidence = evidence
        # everything downstream is blocked
        for d in self._downstream(label):
            dc = self.components[d]
            if dc.status == "pending":
                dc.status = "skipped"
                dc.note = f"blocked by {label}"

    def _downstream(self, label: str) -> set[str]:
        g = self.dependency_graph()
        dependents: dict[str, list[str]] = {n: [] for n in g}
        for n in g:
            for m in g[n]:
                dependents[m].append(n)
        out: set[str] = set()
        stack = [label]
        while stack:
            u = stack.pop()
            for v in dependents.get(u, []):
                if v not in out:
                    out.add(v)
                    stack.append(v)
        return out

    def paper_verdict(self) -> str:
        if self.detect_cycle() is not None:
            return "UNVERIFIED/CIRCULAR"
        verifiable = [c for c in self.components.values() if c.verifiable]
        if not verifiable:
            return "UNVERIFIED"
        assembly = self.metadata.get("assembly") or {}
        if assembly.get("status") == "FAILED":
            return (
                "PARTIALLY VERIFIED"
                if any(c.status == "verified" for c in verifiable)
                else "UNVERIFIED"
            )
        statuses = {c.status for c in verifiable}
        if statuses == {"verified"}:
            custom = any(set(c.kernel_axioms) - STANDARD_AXIOMS for c in verifiable)
            return "VERIFIED MODULO AXIOMS" if custom else "VERIFIED"
        if "verified" in statuses:
            return "PARTIALLY VERIFIED"
        return "UNVERIFIED"

    def record(self) -> dict:
        return {
            "name": self.name,
            "verdict": self.paper_verdict(),
            "cycle": self.cycle,
            "standing_assumptions": self.standing_assumptions,
            "metadata": self.metadata,
            "order": (self.topo_order() if self.detect_cycle() is None else []),
            "components": [
                {
                    "label": c.label, "kind": c.kind, "deps": c.deps,
                    "external": c.external, "is_main": c.is_main,
                    "statement": c.statement, "proof": c.proof,
                    "status": c.status, "verdict": c.verdict,
                    "lean_name": c.lean_name,
                    "lean_statement": c.lean_statement,
                    "library_module": c.library_module,
                    "kernel_axioms": c.kernel_axioms, "note": c.note,
                    "evidence": c.evidence,
                    "lean_code": c.lean_code,
                    "artifacts": c.artifacts,
                }
                for c in (self.components[l] for l in self._insertion)
            ],
        }

    def save(self, path: str | None = None) -> Path:
        out = Path(path) if path else (ROOT / "runs" / "papers" / f"{self.name}.json")
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(self.record(), indent=2, ensure_ascii=False) + "\n")
        return out

    @classmethod
    def load(cls, path: str) -> "PaperSession":
        data = json.loads(Path(path).read_text())
        p = cls(data["name"])
        p.standing_assumptions = data.get("standing_assumptions", [])
        p.metadata = dict(data.get("metadata") or {})
        p.cycle = data.get("cycle")
        for cd in data["components"]:
            c = p.add_component(cd["label"],
                                statement=cd.get("statement", ""),
                                proof=cd.get("proof", ""),
                                deps=cd.get("deps", []),
                                kind=cd.get("kind", "lemma"),
                                external=cd.get("external", False),
                                is_main=cd.get("is_main", False))
            c.status = cd.get("status", "pending")
            c.verdict = cd.get("verdict", "")
            c.lean_name = cd.get("lean_name", "")
            c.lean_statement = cd.get("lean_statement", "")
            c.library_module = cd.get("library_module", "")
            c.kernel_axioms = cd.get("kernel_axioms", [])
            c.note = cd.get("note", "")
            c.evidence = cd.get("evidence", "")
            c.lean_code = cd.get("lean_code", "")
            c.artifacts = list(cd.get("artifacts") or [])
        return p
