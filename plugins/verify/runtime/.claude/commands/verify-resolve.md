---
name: verify-resolve
description: Standalone resolve phase — decompose a proof into atomic blocks and classify each as library match / instantiation / novel by searching the corpus and running type-directed library_search
user_invocable: true
---

<command-name>verify-resolve</command-name>

# /verify-resolve — is this already in the library?

> A standalone component of **/verify-full-process** (Phases 1–2: extract + resolve). Run
> it to decompose a proof and find out which pieces the library already
> proves, WITHOUT running the gate / sketch / formalize / assemble phases. For
> the full flow, use `/verify-full-process`. Additive — calls `VerifyDriver` search.

## Input

$ARGUMENTS

A proof sketch (to decompose), or a single claim (to look up directly).

## Decompose (if given a multi-step proof)

Break the proof into atomic building blocks. Each must be a single
self-contained fact, stated in **general form** (not tied to this proof's
notation), named in snake_case. Only extract blocks the proof actually
**claims** — never infer steps it doesn't mention. For each block record
`{name, statement, role, depends_on}` and topologically order them.

## Resolve each block against the library

```python
from rlverify.driver import VerifyDriver
d = VerifyDriver()                 # no begin() needed for search

d.grep("keyword")                  # substring match on id/statement (id matches rank first)
d.hybrid_search("natural language description")   # BM25 over id+tags+docstring+statement
d.show("promising_theorem_id")     # full statement of a candidate
```

**Type-directed gate (mandatory before calling a block novel)** — once the
block's Lean statement elaborates:

```python
d.compile_statement(stmt, imports=[...])   # confirm it elaborates first
d.library_search(stmt)                      # compiles `<stmt> := by exact?`, ~15s
```

`found=True` ⇒ a library proof **exists** — the block is library/instantiation;
do not formalize it. `found=False` is weaker than it sounds: `exact?` matches
only up to unification and misses shape variants (n-ary vs binary,
`Finset.range` vs `Fintype`, `<` vs `≤`, ENNReal vs ℝ) — so keep the textual
searches too.

## Classify each block

- **library** — exact match exists → give the qualified name.
- **instantiation** — a more general theorem specializes to this.
- **named-result** — cites a well-known named theorem **absent from the corpus**
  (Picard–Lindelöf, the martingale convergence theorem, the ODE-method /
  asymptotic-pseudotrajectory theorem). NOT novel (we don't formalize it now)
  and NOT library (the corpus doesn't prove it). Record via
  `d.resolve(name, named_result="<name + citation>")` and present it as
  **Kind=named-result** in the report. Two sub-cases: (a) it's in Mathlib under a
  `#check`-able id → it becomes a library import whose hypotheses Phase 3 must
  discharge; (b) the infrastructure is absent (e.g. the ODE method) → it enters
  the **axiom lifecycle** (assemble renders VERIFIED-MODULO-AXIOMS). A corpus
  near-miss like an MDP-specific `mdp_martingale_diff_bounded` is ID-SHAPED for
  the general claim and does NOT downgrade this to library. → OUTCOME
  `HAS-NAMED-RESULT`.
- **novel** — not in library → must be formalized from scratch.

### Disqualifiers (treat the block as novel)

- **ID-SHAPED warning** — a corpus lemma whose conclusion is verbatim one of
  its own hypotheses (`[ID-SHAPED — assumes its conclusion]`) proves nothing.
  Citing it is camouflage. Formalize the real content.
- **External citation must `#check`** — a Mathlib name not in the corpus is
  validated at resolve time; `NOT FOUND by #check` ⇒ fix the citation.
- **`differs:` log-argument scan** — a near-match lemma carrying a different
  log argument (e.g. library needs log(2KT/δ), block claims log(2K/δ)) MUST be
  adjudicated in one sentence. The scan is corroboration, not a gate —
  **silence proves nothing**.

## Output a resolution table

| # | Block Name | Statement (NL) | Kind | Library Match / Notes |
|---|-----------|----------------|------|----------------------|

Then: total blocks N · library X · instantiation Y · novel Z, plus the imports
needed for the library matches. **Report honestly** — a "library match" means
the EXACT mathematical content is proven, not merely related.

**Novel requires DUAL negative evidence** — classify a block novel ONLY when
BOTH (a) every textual search returns zero relevant hits AND (b)
`library_search` returns `found=False` on the elaborated statement. Record both
negatives in the "Found by" column (silence alone proves nothing). A corpus hit
that is `[ID-SHAPED]` or shown vacuous (e.g. the corpus already holds
`ucb_expected_regret_bound`, whose conclusion is an *assumed* decomposition) is
recorded **Kind=novel, EVIDENCE=audit-only**, with the matched id quoted — never
Kind=library. A corpus hit is necessary but not sufficient for "library".

## Output (standard result card)

End with the standard result card (`verify-output-contract.md`). The resolution
table is the card's skill-specific table; `DETAIL` is the exact greppable tally.

Real example (clean UCB1 proof):
```
/verify-resolve · ucb_regret_clean
OUTCOME   HAS-NOVEL
EVIDENCE  search-hit (library blocks) · none (novel blocks, dual-negative)
WEIGHT    prioritization-only
DETAIL    RESOLVE N=4 library=1 instantiation=0 novel=2 unresolved=0 imports=[Concentration.AzumaHoeffding]
NEXT      /verify-sketch (2 novel blocks remain)
```

| # | block | kind | found by | notes |
|---|-------|------|----------|-------|
| 1 | hoeffding_tail | library | grep hoeffding=53 | Concentration.AzumaHoeffding.* |
| 2 | basel_sum $\sum_t 1/t^2$ | novel | grep tsum=0, zeta=0 · library_search=False | $\pi^2/6$ absent |
| 3 | sqrt_threshold_ineq | novel | grep sqrt=191 (no match) · lib_search=False | elementary, formalize |
| 4 | ucb_regret (corpus) | novel | grep regret hit ucb_expected_regret_bound | vacuous — assumed decomp |

## Optional: attach to a live /verify-full-process session

```python
d.resume("fixture_name")
d.resolve("block_name", statement_nl="... explicit constants and log args ...",
          library="Qualified.Lemma.Name")    # or instantiation=/novel
```

`statement_nl` is mandatory in a session `resolve()` and must include the
block's explicit constants and log arguments as written in the paper — that's
what feeds the near-match scan.
