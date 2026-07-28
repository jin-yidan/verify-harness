# RLVerify Benchmark Battery

Planted-flaw and clean-control fixtures for regression-testing the
verification pipeline. **Producing** a run record requires an agent (one
`/verify-full-process` invocation per fixture); **grading** it is fully deterministic
(`score.py`).

## Layout

```
benchmarks/
  README.md                this file (the protocol)
  score.py                 deterministic grader
  results.tsv              append-only result log (date, commit, fixture, ...)
  run_batch.sh             headless batch runner (sequential)
  <fixture>/
    statement.md           the ONLY file the agent under test may see
    reference_run.json     (optional) a graded historical run record
    sealed/
      groundtruth.md       prose explanation of the planted flaws (human)
      expected.json        machine grading key
```

## Protocol (one fixture)

1. **Freeze the corpus** — copy `rlverify/corpus.jsonl` to /tmp and run the
   fixture with `VerifyDriver(corpus_path=<copy>)`. This (a) prevents fixture
   lemmas from polluting the real library (the driver skips source-tree
   writes for non-default corpus paths) and (b) keeps fixture difficulty
   stable across re-runs (salvaged lemmas would otherwise turn novel blocks
   into library matches next time).
2. **Invoke the pipeline** — paste the CONTENT of `statement.md` into a
   `/verify-full-process` invocation. Do not disclose the fixture path; the agent under
   test must never open `benchmarks/*/sealed/` (procedural sealing — the
   threat model is drift, not adversarial agents; see Limitations).
3. **Score** — `python3 benchmarks/score.py benchmarks/<fixture>
   runs/<fixture>_<ts>.json --tsv`.

## What the scorer measures

- **verdict_class** — effective verdict (mirrors the driver's precedence:
  explicit verdict → sorryAx → kernel-backed refutation → REFUTED
  falsification → kernel closure). `verdict_class_any` in expected.json
  accepts a set (used by clean controls).
- **per-flaw detection** — keyword signatures over verdict_reason, block
  statements/notes, falsification claims/certificates, and refutation
  descriptions. An unmatched flaw degrades to NEEDS REVIEW, never a silent
  wrong score (phrasing varies across agent runs).
- **false positives** — REFUTED/violation on blocks the key lists as sound;
  on clean controls, any failure verdict at all.
- **kernel-backed evidence** — library/instantiation + compiled blocks over
  total; refuted-with-certificate and kernel-backed refutation counts;
  verdict_evidence (audit vs kernel).
- **triage anchoring** — flaws found despite NOT being flagged by Phase 0
  triage (proof that gate coverage survived the prose pass); all-clear runs
  that find nothing are a visible signature to scrutinize.

## Fixtures

| fixture | source | expected verdict |
|---|---|---|
| `successive_elimination_hp_regret` | claude_authored_planted (A/B/P experiment) | UNVERIFIED/WRONG |
| `ucb1_hoeffding_at_random_count` | claude_authored_planted (original ucb1 run) | UNVERIFIED/HYPOTHESIS_VIOLATION |
| `ucb_regret_clean` | clean_control (Auer et al. 2002 Thm 1, literature) | VERIFIED-class, zero flaws |
| `ucb_regret_mutated` | mutation (single mechanical 8→4 edit of the clean text) | UNVERIFIED/WRONG |
| `expectation_sum_exchange_erratum` | literature_erratum (Lattimore–Szepesvári Prop 2.6 first printing, author-acknowledged) | UNVERIFIED/WRONG |
| `sa_ode_gas_circular` | user_submitted_organic (SA/ODE-method convergence; the classic Borkar–Meyn stability gap bridged circularly) | UNVERIFIED/CIRCULAR |

Sources are deliberately mixed: two Claude-authored planted fixtures, one
untouched literature control, one mechanical mutation (ground truth exact by
construction), one published author-acknowledged erratum, one organic user
submission (a real input not authored for the battery; its flaw — a
conditional conclusion invoked unconditionally — is invisible to the textual
dependency graph and exercises the only CIRCULAR-class verdict in the suite).
The non-planted fixtures exist because "flaws a Claude plants may be flaws a
Claude finds easily" (A/B/P report caveat).

The mutation recipe generalizes: `tests/proofs/` holds 42 transcribed
literature proofs and `RLGeneralization/` holds kernel-proven lemmas — a
single surgical constant/hypothesis edit of either, with the edit recorded
in groundtruth.md, is a repeatable fixture factory.

## Limitations

- **Sealing is procedural, not cryptographic.** An agent could open
  `sealed/`. Acceptable for a regression suite; pass statement content
  inline and spot-check transcripts.
- **n = 6.** Per-check scores (false positives, kernel-backed fraction,
  evidence class) are informative at this size; cross-version
  detection-rate comparisons need more fixtures before they mean much.
- **Keyword matching is approximate.** `min_keyword_hits` over redundant
  keyword lists plus the NEEDS REVIEW escape hatch keep it honest.
