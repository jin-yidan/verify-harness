# Harness demo examples

Three runnable examples of driving the BYO-agent harness via
`run_verification(...)`. Each takes a **paper-style theorem + proof as plain
text** (no Lean) and returns one verdict line.

| File | Needs an agent account? | Outcome it shows | Runtime |
|------|------------------------|------------------|---------|
| `offline_gates_demo.py` | **No** — fully deterministic | enforcement teeth: VERIFIED vs. downgraded UNGATED | ~seconds |
| `live_verified.py` | Yes (`claude`) | a correct **RL** theorem (UCB radius is monotone in the play count) → kernel-closed **VERIFIED** | ~1–2 min |
| `live_wrong.py` | Yes (`claude`) | a flawed **RL** claim (UCB radius *increases* with plays — false) → **UNVERIFIED/WRONG** | ~1–2 min |

> The two live demos use a real reinforcement-learning fact: the UCB1 confidence
> radius √(2 ln t / s) shrinks as an arm is played more (more data ⇒ less
> uncertainty — why UCB converges). `live_verified.py` proves it; `live_wrong.py`
> inverts it into a plausible-sounding false claim and the harness catches it.

## Start here: the offline demo (no account, runs anywhere)

This is the best one to show people first — it needs no login, no network, and
runs the *real* runner / kernel / enforcement with fake stand-ins for the agent
and the model. It runs the same compiling proof twice and shows the harness
**downgrade a VERIFIED to `UNVERIFIED/UNGATED`** when the faithfulness gate says
the Lean statement doesn't match the claim — something a raw "ask the LLM"
workflow cannot do, because the gate runs in trusted harness code.

```bash
RLVERIFY_SANDBOX=0 python harness/examples/offline_gates_demo.py
```

Expected tail:
```
  faithful   → VERDICT: VERIFIED
  unfaithful → VERDICT: UNVERIFIED/UNGATED
```

## The live demos (your own Claude account)

These shell out to *your* authenticated `claude` CLI to actually drive the
formalization — the real BYO path.

Prerequisites:
1. `claude login` — authenticate the CLI with your account (the harness has **no**
   login of its own; it just invokes `claude`).
2. `bash harness/setup.sh` — Lean toolchain, MCP SDK, library build, sandbox check.
3. macOS (`sandbox-exec`). On Linux the untrusted sandbox isn't built — prefix
   with `RLVERIFY_SANDBOX=0` and only run proofs/agents you trust.

```bash
python harness/examples/live_verified.py    # expect VERIFIED
python harness/examples/live_wrong.py       # expect UNVERIFIED/WRONG
```

> Status note: the live agent-launch path is validated end-to-end on small
> fixtures (see `../README.md`) but is still marked LIVE-UNVALIDATED for harder
> proofs and for the `codex` backend. If a live run stalls, the offline demo is
> the reliable fallback for a presentation.

## Writing your own

Copy `live_verified.py` and change three strings:

```python
run_verification(
    "my_fixture",                       # any session name
    statement = "Theorem. ...",         # the claim, paper-style text
    proof     = "Proof. Step 1 ... ∎",  # the argument, paper-style text
    call_model = get_backend("claude", model="opus"),
    agent_drive = launch_agent(backend="claude", model="opus"),
    nl_claim   = "one sentence: what you believe you proved",
)
```

Tip: the more explicitly the proof **names its steps and lemmas**
("Step 3: by Hoeffding…"), the better it decomposes. Vague proofs
("by standard arguments") yield weaker results.
