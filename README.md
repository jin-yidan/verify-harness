# Verified Skills

A standalone distribution of Verify: agent routing, mathematical-verification
workflows, the Python harness, and the `RLGeneralization` Lean library.

## Install the plugin

Codex:

```bash
codex plugin marketplace add jin-yidan/verified-skills --ref main
codex plugin add verify@verify
```

Claude Code:

```bash
claude plugin marketplace add https://github.com/jin-yidan/verified-skills.git
claude plugin install verify@verify
```

Restart the agent, then ask naturally:

```text
Try to falsify this theorem first.
Check whether this proof satisfies every hypothesis.
Fully verify this theorem and proof in Lean.
```

The plugin routes the request and installs its bundled engine into isolated
user data after asking permission. It does not fetch code from another Verify
repository. Full Lean checks still download the pinned Lean toolchain and
upstream Mathlib dependencies when they are not already installed.

## Run from a clone

Requirements: Python 3.10 or newer and Lean through `elan`.

```bash
python3 -m venv .venv
.venv/bin/python -m pip install -e ".[pdf]"
lake update SLT
bash scripts/prepare_slt.sh
lake exe cache get
lake build RLGeneralization
(cd tools/repl && lake build repl)
```

Examples:

```bash
.venv/bin/python -m rlverify retrieve "Bellman contraction"
.venv/bin/python -m rlverify falsify --example ucb_mutated
.venv/bin/python -m harness verify path/to/proof --backend codex --report
```

Claude commands are in `.claude/commands/`; standalone Codex skills are in
`codex-skills/`; the installable cross-agent plugin is in `plugins/verify/`.
