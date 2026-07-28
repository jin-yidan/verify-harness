"""Static linter for untrusted Lean source (W0, defense-in-depth layer).

This is the SECONDARY control. The primary control is the OS sandbox
(``rlverify.sandbox``). A static blocklist of dangerous Lean syntax is
inherently evadable, so we do NOT rely on it for security — we rely on the
sandbox to contain whatever this misses. This layer exists to (a) shrink the
attack surface and (b) give the agent a clear, fast rejection for the obvious
elaboration-time-IO vectors instead of an opaque sandbox kill.

Why these vectors: Lean executes arbitrary ``IO`` at *elaboration* time, so a
proof file is not inert data. The entry points to elaboration-time IO are a
small set of commands/attributes (``#eval``, ``run_cmd``, ``initialize``,
custom ``elab``/``macro``, ``native_decide`` which invokes the compiler, and
FFI attributes). Ordinary proof terms and standard tactics do not perform
filesystem/network IO, so blocking these entry points plus an import allow-list
covers the static surface.

The scan is intentionally CONSERVATIVE: it matches the raw source (including
comments and strings) with word-boundary patterns. A legitimate proof that
merely mentions ``#eval`` in a comment will be rejected — that is the safe
direction, and such mentions are vanishingly rare in real proof files.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field

# --- Module roots an untrusted file may import. Anything else is rejected. ---
# Proof files in this project import Mathlib / RLGeneralization (+ their deps).
# `Lean`, `System`, and explicit `Init.System.*` give direct IO and are NOT
# allowed. `Init` (bare/auto) is always available without an explicit import.
ALLOWED_IMPORT_ROOTS = frozenset({
    "Mathlib", "RLGeneralization", "SLT",
    "Std", "Batteries", "Aesop", "Qq", "Plausible",
})

# --- Dangerous command / attribute tokens (elaboration-time IO or unsoundness).
# Each entry: (compiled regex, human reason). Word boundaries where meaningful
# so identifiers like `initializeState` or `elaborator` do not false-match.
_BLOCKLIST: list[tuple[re.Pattern, str]] = [
    (re.compile(r"#eval\b"),            "#eval runs IO at elaboration time"),
    (re.compile(r"\brun_cmd\b"),        "run_cmd runs command-elaboration IO"),
    (re.compile(r"\brun_elab\b"),       "run_elab runs elaboration IO"),
    (re.compile(r"\brun_tac\b"),        "run_tac runs TacticM (IO) at elaboration time"),
    (re.compile(r"\b(?:builtin_)?initialize\b"),
                                        "initialize runs IO at module init"),
    (re.compile(r"\belab\b(?!orat)"),   "custom elab can perform IO"),
    (re.compile(r"\belab_rules\b"),     "elab_rules can perform IO"),
    (re.compile(r"\bmacro\b"),          "macro / macro_rules can emit unsafe syntax"),
    (re.compile(r"\bsyntax\b"),         "custom syntax declarations"),
    (re.compile(r"\bunsafe\b"),         "unsafe declarations bypass the kernel"),
    (re.compile(r"\bnative_decide\b"),  "native_decide invokes the compiler (trustCompiler)"),
    (re.compile(r"@\[\s*extern"),       "@[extern] is an FFI escape hatch"),
    (re.compile(r"@\[\s*implemented_by"), "@[implemented_by] replaces a compiled impl"),
    (re.compile(r"@\[\s*export"),       "@[export] exposes a symbol to native code"),
]

_IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z_][\w.]*)", re.MULTILINE)


@dataclass
class LintResult:
    ok: bool
    reasons: list[str] = field(default_factory=list)

    def __bool__(self) -> bool:  # truthy == safe
        return self.ok


def lint_untrusted(code: str) -> LintResult:
    """Return ``LintResult(ok, reasons)`` for an untrusted Lean source string.

    ``ok=False`` means at least one blocklist pattern matched or a disallowed
    import was found; ``reasons`` lists every distinct violation (so the agent
    can fix all at once). ``ok=True`` is NOT a safety guarantee — it only means
    the static surface is clean; the sandbox remains the real boundary.
    """
    reasons: list[str] = []

    for pattern, reason in _BLOCKLIST:
        if pattern.search(code):
            reasons.append(reason)

    for m in _IMPORT_RE.finditer(code):
        module = m.group(1)
        root = module.split(".", 1)[0]
        if root not in ALLOWED_IMPORT_ROOTS:
            reasons.append(f"disallowed import: {module} (root {root!r} not allow-listed)")

    # de-dup while preserving order
    seen: set[str] = set()
    deduped = [r for r in reasons if not (r in seen or seen.add(r))]
    return LintResult(ok=not deduped, reasons=deduped)
