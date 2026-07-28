---
name: verify-output-contract
description: Apply the standard RLVerify result-card vocabulary, evidence weights, and phase-specific reporting contract
user_invocable: true
---

# /verify-* output contract — the standard result card

Every `/verify-*` component ends its run by printing ONE **result card**. The
card is the only thing a reader needs to scan to know *what happened, how
strong the evidence is, and what to do next*. The driver's per-event log lines
(`[phase] glyph status — detail`) still scroll above it; the card is the
summary that does not lie by omission.

## The card

A component ends by printing a **fenced code block** of fixed-label scalar
lines — the code fence *is* the card's border, so the IDE renders it as one
distinct box — immediately followed by the skill's **Markdown table** when it
has one:

```
/verify-<skill> · <target>
OUTCOME   <one token from THIS skill's fixed vocabulary>
EVIDENCE  <tier — see ladder>
WEIGHT    <load-bearing | zero-weight | prioritization-only | —>
DETAIL    <exactly one line of specifics>
NEXT      <the component to run next, or —>
```

| column | column |   ← skill-specific table, ONLY if the skill defines one
|--------|--------|
| …      | …      |

Rules:
- **OUTCOME** is one token from the skill's closed vocabulary (table below) — never free text.
- **EVIDENCE and WEIGHT are mandatory and never blank.** They are what stop a
  PASS / all-clear / compile from being read as proof.
- **DETAIL** is one line. Long content (rendering, goals, search dumps) stays in
  the body above; the card points to it, it does not inline it.
- The card is printed even on failure / early exit.

### Rendering — clear in any IDE / terminal

The layout is chosen so it aligns identically everywhere, with **no reliance on
glyph widths**:

- The fenced block holds only `LABEL␣␣value` lines: labels are ASCII, padded to
  a fixed column per card (≥ the longest label + 1), then the value. **One value
  per line** — never space-align multiple columns *inside* the fence (Unicode
  subscripts/math have ambiguous width and will shift).
- All **structure** (labels, the fence) is ASCII. Math Unicode (Δ, ≤, √, θ, π)
  is allowed only inside the free-text `DETAIL`/value, where nothing aligns to
  it — keep it out of any column you align by.
- The skill's data table is a real **Markdown table** placed right after the
  fence; the IDE renders it aligned regardless of cell content. Never draw a
  table with spaces or box-drawing characters.
- No `━`/box frames — the fence already gives the border. This avoids ragged
  top/bottom rules when a font renders heavy lines with gaps.

### Math notation

Pick the form by **where the math sits**:

- **Inside the fenced card** (`DETAIL`, `REASON`, …) → **safe-Unicode**. The fence
  is monospace and never renders LaTeX, so use real symbols every code font has,
  and LINEARIZE the fragile ones:

  | avoid (poor coverage / breaks width) | use instead |
  |---|---|
  | superscripts `²  ³  ⁻⁴` | `^2  ^3  ^-4` |
  | subscripts `θₖ  Nₜ` | `θ_k  N_t` |
  | norm bars `‖x‖` | `\|\|x\|\|` |
  | hats / overbars `x̄  θ̂` | `x_bar  θ_hat` |
  | ceil / floor `⌈x⌉  ⌊x⌋` | `ceil(x)  floor(x)` |

  Use freely (near-universal, single-width): `≤ ≥ ≠ ≈ → ∞ ± × · √ ∑ ∏ ∫ ∈ ⊆ ∪ ∀ ∃`
  and Greek `Δ Σ Θ α β γ δ ε θ λ μ π σ` and `ℝ ℕ ℤ`. The trap is sub/superscripts
  and combining marks — not Greek or `≤`. Example:
  `gap 0.414 → (√2−1)·Δ at s = ceil(4 ln t / Δ^2)`.

- **In the Markdown table** → **inline LaTeX** `$...$` when the target renders math
  (GitHub, VS Code `Cmd+Shift+V` preview, Obsidian, Jupyter): e.g.
  `$\sum_t 1/t^2 = \pi^2/6$`, `$n = N_{t-1}(a)$`. In a PLAIN terminal `$...$` shows
  literally — fall back to the safe-Unicode form there. The fenced summary already
  carries the scannable result in Unicode, so an unrendered table loses nothing
  critical.

**Compiling / viewing LaTeX locally:**
- `tectonic doc.tex` compiles LaTeX → PDF standalone (installed here); open the PDF.
- `pip install pylatexenc` → `latex2text '...'` (or `unicodeit`) converts LaTeX to
  Unicode text right in the terminal — ideal for generating card `DETAIL` lines.
- VS Code **Cmd+Shift+V** renders the `$...$` table cells as real math.
- The integrated terminal pane shows no images, so the fenced card stays Unicode.

## EVIDENCE ladder (strongest → weakest)

| Tier | Means |
|------|-------|
| `kernel` | a Lean `#print axioms` closure ⊆ {propext, Classical.choice, Quot.sound} backs the claim |
| `certificate` | a serialized counterexample validated by a trusted deterministic checker independent of the sampler author |
| `compile-only` | Lean accepted the code, but no kernel closure was read yet (a block can still be vacuous / import a sorry) |
| `search-hit` | a corpus/`exact?` match was found — necessary, not sufficient |
| `audit-only` | reasoning / a named violated hypothesis — testimony, not machine-checked |
| `none` | nothing was established (a clean falsify PASS, a VACUOUS gate, a `GATED` non-run, a `MAIN-UNFORMALIZABLE` assemble) |

`kernel(skeleton)` is a qualified `kernel`: the skeleton's *glue* is
kernel-checked, but its blocks are still `sorry` — it certifies the
decomposition, never the block statements.

## WEIGHT

- **load-bearing** — this output can decide or support the verdict (a kernel
  closure, an independently validated REFUTED certificate, an independently
  confirmed back-translation mismatch, an
  `add_novel` write).
- **zero-weight** — found nothing / proves nothing on its own (a falsify PASS,
  a compiled-but-vacuity-flagged block, a withheld library write).
- **prioritization-only** — orders later work but is never evidence (triage,
  resolve, hypothesis-audit). A flag here still requires Rule-7 evidence to
  become a verdict.
- **—** (literal dash) — only for a `GATED` non-run: the component did no work,
  so it is neither evidence nor prioritization. `EVIDENCE`/`WEIGHT` are still
  never *blank* — a gated card prints `EVIDENCE none · WEIGHT —`.

## Per-skill vocabulary (the closed OUTCOME sets)

| Skill | OUTCOME ∈ | EVIDENCE | WEIGHT | typical NEXT |
|-------|-----------|----------|--------|--------------|
| `/verify-triage` | `SUSPECTS-FOUND` · `ALL-CLEAR` | audit-only | prioritization-only | resolve + hypothesis-audit (ordered by ranking) |
| `/verify-resolve` | `ALL-LIBRARY` · `HAS-INSTANTIATION` · `HAS-NOVEL` · `HAS-NAMED-RESULT` · `UNRESOLVED-CITATION` | search-hit \| audit-only \| none | prioritization-only | sketch (if non-library remain) else assemble |
| `/verify-hypothesis-audit` | `CLEAR` · `HYPOTHESIS_VIOLATION` · `CIRCULAR` | audit-only | prioritization-only | discharge (to upgrade to kernel refutation) |
| `/verify-falsify` | `REFUTED` · `PASSED` · `VACUOUS` · `SKIPPED` | audit-only (default REFUTED) \| certificate (independently validated REFUTED) \| none | prioritization-only (default REFUTED/SKIPPED) \| load-bearing (independently validated REFUTED) \| zero-weight | independently validate / kernel-refute (if REFUTED); sketch / discharge (if PASSED) |
| `/verify-sketch` | `DECOMPOSITION-OK` · `DECOMPOSITION-GAP` · `GLUE-BUG` | kernel(skeleton) | load-bearing (decomposition) \| zero-weight (proof) | discharge |
| `/verify-discharge` | `COMPILED` · `COMPILED-VACUOUS-RISK` · `DECOMPOSED` · `GAP` · `REFUTED-KERNEL` · `REFUTED-AUDIT-ONLY` | compile-only \| kernel (refute) \| audit-only | load-bearing \| zero-weight (vacuity-flagged) | assemble |
| `/verify-backtranslate` | `MATCH` · `NOTE` · `MISMATCH` (worst category wins) | audit-only | load-bearing | — (MISMATCH blocks the verdict) |
| `/verify-assemble` | `VERIFIED` · `VERIFIED-MODULO-AXIOMS` · `UNVERIFIED-SORRYAX` · `CLOSURE-FAILED` · `MAIN-UNFORMALIZABLE` | kernel \| none (MAIN-UNFORMALIZABLE) | load-bearing \| zero-weight (MAIN-UNFORMALIZABLE → INCOMPLETE) | library (if novel blocks) else — |
| `/verify-library` | `ADDED` · `SKIPPED-REDUNDANT` · `SKIPPED-PAPER-SPECIFIC` · `REJECTED-BY-GATE` · `WITHHELD-NO-WRITE` | search-hit + audit-only | load-bearing (written) \| zero-weight (withheld) | — |

## Universal outcome: GATED (available to every skill)

`GATED` is a cross-cutting OUTCOME token, available to **every** component in
addition to its own closed set. A component prints `GATED` when it is **not run
because a verdict-deciding early exit already fired upstream** — a
kernel-certified CIRCULAR or HYPOTHESIS_VIOLATION, an independently validated
`/verify-falsify` REFUTED, or any gate that fixes the verdict. Audit-only
findings produce SUSPECTED and do not gate later certificate work. The card is still printed (never
left blank):

```
/verify-sketch · sa_ode_gas_circular
OUTCOME   GATED
EVIDENCE  none
WEIGHT    —
DETAIL    upstream CIRCULAR on Lemma 3 (invokes Lemma 2; event E = bounded iterates) — not attempted
NEXT      —
```
(A GATED card has no data table.)

`GATED` never changes the verdict; it records that a phase was correctly skipped.
(The **salvage rule** still applies: a block *independent* of the failed one is
NOT gated — formalize and evaluate it. Only dependents/downstream are GATED.)

## Source of truth

Each skill doc shows its own filled-in card under its `## Output` section. This
file is the single source of truth for the grammar and the vocabulary — if a
skill's card disagrees with this table, this table wins.
