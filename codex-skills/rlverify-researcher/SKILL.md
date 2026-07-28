---
name: rlverify-researcher
description: Use the local RLVerify researcher CLI and harness to verify theorem/proof sketches, ingest papers or arXiv links, run sealed triage and hypothesis audit, run numeric falsification, resume verification runs, and interpret RLVerify evidence/outcome cards. Use for requests to check mathematical proofs, verify RL or RL theory claims, audit hidden hypotheses, falsify claims, or run the Verify harness.
---

# RLVerify Researcher

Use the local RLVerify harness as the executable verification engine. Run it
from the current `verify-harness` repository root, which contains
`harness/cli.py` and `rlverify/mcp_server.py`.

## Core Rules

- Verify, do not repair. Never add hypotheses, weaken the claim, invent missing
  proof steps, insert `sorry`, or change the statement to make a proof pass.
- Treat parent-side sealed gates as trusted; do not trust agent-authored gate
  records as load-bearing evidence.
- `VERIFIED` requires kernel closure/certificate evidence plus required gates.
  Compile-only output is not a proof verdict.
- `sorryAx` in the kernel closure means unverified.
- Triage and audit are prioritization-only. `ALL-CLEAR` and `CLEAR` are
  zero-weight signals, not verdicts.
- Falsification `REFUTED` is load-bearing only when a trusted deterministic
  checker independently validates the serialized witness. Confined execution
  and same-author rechecks remain audit-only. `PASSED` is zero-weight.
- Keep exact/weaker/conditional/wrapper/stub/vacuous labels visible. Do not
  overclaim.

## User Interface

This skill is used from the Codex chatbox after the user has logged in to Codex.
Do not tell researchers to run terminal commands. Ask them to paste the paper
link, local PDF/TeX path, or theorem/proof text directly into chat, for example:

```text
Use $rlverify-researcher to verify this paper:
https://arxiv.org/abs/1703.05449
Theorem: Theorem 1
```

```text
Use $rlverify-researcher to verify this local PDF:
/Users/me/papers/ucbvi.pdf
Theorem: Main theorem
```

```text
Use $rlverify-researcher to verify this theorem and proof:
Theorem: ...
Proof: ...
```

The harness CLI is internal engine plumbing for the agent. When this skill runs
that engine, use `--backend codex` by default and optionally pass
`--model <codex-model>` plus `--reasoning-effort <low|medium|high|xhigh>` when
the user is explicitly testing a Codex model. For paper links and PDFs, first
run `python3 -m harness verify ... --dry-run` to materialize a fixture and print
the formal-proof cost estimate. Report the extracted statement/proof fixture and
estimate to the user, then wait for explicit approval before launching the
formal verification run. Only execute generated Python samplers when the user
explicitly approves local sampler execution.

## Output Contract

Report results using the harness card fields:

- `OUTCOME`: closed outcome token, not free prose.
- `EVIDENCE`: one of `kernel`, `certificate`, `compile-only`, `search-hit`,
  `audit-only`, or `none`.
- `WEIGHT`: `load-bearing`, `zero-weight`, `prioritization-only`, or `--`.
- `DETAIL`: concrete evidence, artifact path, gate failure, or failure reason.
- `NEXT`: the next useful action.

Use `harness/OUTPUT.md` for detailed semantics. For the agent-driving procedure,
use `harness/profile/verify-full-process.md`; it is the portable version of the
original Claude verification skill.
