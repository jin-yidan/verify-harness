# Conventions for the `/rlverify-*` commands

Shared rules for every `/rlverify-*` slash command. Read this once per
invocation, then follow the specific command file.

**These commands drive the HARNESS (a separate trusted process). They are not
the `/verify-*` commands.** `/verify-*` make *you* drive `rlverify.driver`
inside this conversation — your own report of your own work. The harness instead
runs the sealed gates parent-side and spawns a **fresh, untrusted `claude -p`
child** as the prover, so the verdict does not depend on trusting either you or
the prover. Never mix the two in one answer, and never present a `/verify-*`
result as a harness verdict.

Your job in these commands is narrow and you must keep it narrow:
**route the input → run the harness → relay its output.** You are the typist,
not the verifier.

---

## 1. Never make the user open a terminal

Run everything through your own Bash tool from the current repository root.
Do not print a command and ask
the user to run it. Do not suggest they "try it in a terminal".

## 2. Long runs go in the BACKGROUND

A full verification takes minutes to half an hour — longer than a foreground
Bash call can wait. For `rlverify-theorem` and `rlverify-paper`, always pass
`run_in_background: true`, tell the user it is running, and report progress as
output arrives. The harness prints one `→ tool(arg)` line per prover step, so
there is real progress to relay. `triage` / `audit` / `falsify` are short and
may run in the foreground.

## 3. Get consent BEFORE spending

When you invoke the harness from Bash its stdin is not a TTY, so the harness's
own `proceed? [y/N]` gate auto-proceeds. **That gate is therefore yours to
enforce.** Before any run that launches a prover (`rlverify-theorem`,
`rlverify-paper`):

- state the estimated cost and wall time (`--dry-run` prints a calibrated
  estimate for free — prefer showing that first for papers),
- state that this bills the user's Claude account **separately** from this
  conversation,
- ask, and wait for an actual yes.

`rlverify-falsify` has a second, different consent: it executes model-written
Python on the user's machine. Ask explicitly before passing `--trust-samplers`.
Never pass that flag on your own initiative.

## 4. Input routing — accept whatever the user pastes

| What the user gives you | What you pass |
|---|---|
| arXiv link or bare id (`2406.01234`, `math.PR/0605123`) | the id/URL as the positional target |
| local `.pdf` / `.tex` / `.md` path | the path as the positional target |
| an existing fixture folder | the folder as the positional target |
| pasted theorem + proof text | write to files, pass `-s <file> -p <file>` |

For pasted math, **write it to files and pass paths** — do not inline it as a
shell argument. Put the files in your scratchpad directory. `-s/-p` costs no
extraction call, so this is also the cheapest path.

PDF input needs `pip install pypdf`; if the harness says so, offer to install it.

## 5. Picking a theorem out of a paper

Non-interactive runs cannot use the harness's numbered picker. So:

- If the user named a theorem, pass `--theorem "3.1"` (the harness normalizes
  `3.1` vs `Theorem 3.1`).
- If they did not, run `--dry-run` **without** `--theorem`. The harness exits 2
  and lists the candidates it found. Show that list and ask which one.
- Never guess a theorem label. Never invent one that was not in the list.

## 6. Relay the result card VERBATIM

Show the harness's own output. Do not paraphrase a verdict, do not round a
verdict up, do not summarize `UNVERIFIED/UNGATED` as "mostly fine". If the user
wants an interpretation, give it *after* the verbatim card and clearly labeled
as your commentary.

Exit codes: **0** = clean VERIFIED · **1** = a real non-pass verdict (the tool
worked, the proof did not verify) · **2** = tool/usage/auth error. Never report
exit 1 as a tool failure, and never report exit 2 as a verdict about the math.

## 7. The honesty vocabulary is not optional

These are the project's load-bearing distinctions. Preserve them exactly:

- **Only `verify` produces a verdict.** `triage`, `audit`, and `falsify` never
  do. Never write "VERIFIED" as the outcome of a component command.
- **`triage` and `audit` are prioritization-only.** `ALL-CLEAR` / `CLEAR` are
  *zero-weight* — they mean "nothing found at this depth", never "correct".
  Their findings tell the user where to look, not what is true.
- **`falsify REFUTED` is audit-only by default.** It becomes load-bearing only
  after a trusted deterministic checker independently validates the serialized
  witness (or a Lean kernel refutation is built). A seed and an agent-authored
  recheck are reproducible testimony, not independence. `PASSED` means no
  counterexample was found, which is
  **evidence, not proof**. `VACUOUS` means the hypotheses were never satisfied,
  so the claim was never actually tested — say that plainly; it is a common
  false comfort.
- **`VERIFIED` requires kernel closure plus the gates.** Compiling is not
  verifying. `sorryAx` in the closure means unverified. `VERIFIED MODULO AXIOMS`
  is not a clean pass.
- Keep any `exact / weaker / conditional / wrapper / stub / vacuous` label the
  harness prints. Never drop a qualifier to make a result read better.

## 8. Verify, do not repair

If a proof fails, report the failure. Never add a hypothesis, weaken the
statement, insert `sorry`, or "fix" the user's proof so it passes — and never
suggest the harness be re-run with a gate disabled to get a nicer answer. If the
user wants help fixing the math, that is a separate conversation, outside these
commands.

The default user-facing response contains only the evidence-backed problems and
a plain-language conclusion. Do not append a corrected proof, replacement
derivation, newly added assumptions, or Lean source unless the user separately
asks for repair or proof construction. If the run establishes no problem, say
that no problem was established at that verification depth; do not manufacture
a proof to fill the space.

## 9. Where things land

- Certificates + reports: `./rlverify-out/`
- Resumable state: `./rlverify-out/.state/<name>/` — a timed-out run resumes with
  `--resume <name>`; offer this instead of restarting from zero.
- Fetched papers cache: `./rlverify-out/.papers/` — safe to delete.

Pass `--report` on verification runs so the user gets a durable Markdown report,
and tell them the path.

## 10. Platform

The Lean sandbox is validated on macOS only. On Linux the harness stops and
explains the options (`RLVERIFY_LINUX_SANDBOX=1` opt-in, or `--no-sandbox`).
Never add `--no-sandbox` yourself to get past that stop — it drops the
untrusted-code guarantee, and that is the user's call to make, not yours.
