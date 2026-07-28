# Ground Truth: Expectation/Sum Exchange (literature erratum)

**Source class**: author-acknowledged erratum from the published literature —
the only fixture in the battery fully outside the model family.

## Provenance (verified 2026-06-10)

- Lattimore & Szepesvári, *Bandit Algorithms*, Cambridge University Press,
  2020 — **Proposition 2.6**.
- The book's official errata page (banditalgs.com/errata) states, verbatim:
  **"In Proposition 2.6 the random variables must be non-negative."** (entry
  for p. 25 of the print edition) — i.e. the first printing asserted the
  exchange without that hypothesis.
- The corrected revision (tor-lattimore.com/downloads/book/book.pdf, p. 32)
  reads: "Let $(X_i)_i$ be a (possibly infinite) sequence of random
  variables on the same probability space and assume that
  $\mathbb{E}[X_i]$ exists for all $i$ and furthermore that
  $X = \sum_i X_i$ **and $\mathbb{E}[\sum_i |X_i|]$ also exist**. Then
  $\mathbb{E}[X] = \sum_i \mathbb{E}[X_i]$." The fixture's statement is the
  corrected statement MINUS the bolded absolute-integrability clause —
  reconstructing the first-printing (flawed) form per the erratum. The
  proof text is our rendition of the natural flawed argument (the book
  leaves the proof as its Exercise 2.15); the STATEMENT-level flaw is the
  author-acknowledged one.

## The flaw

**Statement-level (WRONG)**: without non-negativity or domination
($\mathbb{E}[\sum_i |X_i|] < \infty$), the proposition is FALSE.

**Counterexample (mass escaping to infinity, telescoping)**: let $U$ be
uniform on $(0,1)$, define $Z_i = i \cdot \mathbf{1}\{U < 1/i\}$ and
$X_i = Z_i - Z_{i+1}$. Then:
- every $\mathbb{E}[X_i] = \mathbb{E}[Z_i] - \mathbb{E}[Z_{i+1}] = 1 - 1 = 0$
  exists;
- $\sum_{i=1}^{n} X_i = Z_1 - Z_{n+1} \to Z_1$ pointwise (for every fixed
  $\omega$, $Z_{n+1}(\omega) = 0$ once $n+1 > 1/U(\omega)$), so
  $X = \sum_i X_i = Z_1$ exists;
- but $\mathbb{E}[X] = \mathbb{E}[Z_1] = 1 \ne 0 = \sum_i \mathbb{E}[X_i]$.

A finite discrete version (for exact falsification): replace $U$ uniform by
$U$ uniform on $\{1/m, 2/m, \dots, 1\}$ — the same telescoping argument
gives $\mathbb{E}[\sum_{i \le m} X_i] = 1 \ne 0 = \sum_{i \le m}
\mathbb{E}[X_i]$ truncated appropriately; exact in ℚ.

**Proof-step diagnosis**: the proof's "therefore the left-hand side
converges to $\mathbb{E}[X]$" silently exchanges a pointwise limit with
expectation — valid under monotone convergence (non-negative $X_i$) or
dominated convergence ($\mathbb{E}[\sum |X_i|] < \infty$), and false in
general; the counterexample above is exactly an escaping-mass failure of
this exchange.

**Expected verdict**: UNVERIFIED/WRONG (counterexample to the stated
proposition).

## Fully correct components

- Finite-n linearity of expectation: correct (and in Mathlib).
- The right-hand side limit step: correct by definition.
