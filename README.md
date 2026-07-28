# Verified Skills

Agent skills and Claude Code commands for the
[Verify](https://github.com/jin-yidan/verified-rl) mathematical-verification
engine.

## Install

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

Verify selects the smallest suitable workflow. On first use, it asks before
installing the versioned engine from `verified-rl`; full verification may also
require a separate Lean installation.

## Direct commands

When working from a clone of this repository in Claude Code, the commands in
`.claude/commands/` are available directly, including:

- `/verify-falsify`
- `/verify-hypothesis-audit`
- `/verify-full-process`
- `/verifyRL-paper`
- `/formalize`

Standalone Codex skill sources are in `codex-skills/`. The installable
cross-agent plugin is in `plugins/verify/`.
