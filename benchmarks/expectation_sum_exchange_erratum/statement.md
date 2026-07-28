# Exchange of Expectation and Infinite Summation

## Setting

Let $(\Omega, \mathcal{F}, \mathbb{P})$ be a probability space. All random
variables below are real-valued measurable functions on this space. The
expectation $\mathbb{E}[X]$ of a random variable $X$ is its Lebesgue
integral with respect to $\mathbb{P}$, defined whenever it exists. This
exchange result is the workhorse of regret decompositions over infinite
horizons: it lets one write the expectation of an infinite sum of per-round
regret contributions as the sum of per-round expectations, even when the
contributions are dependent.

## Proposition

Let $(X_i)_i$ be a (possibly infinite) sequence of random variables on the
same probability space and assume that $\mathbb{E}[X_i]$ exists for all $i$
and furthermore that $X = \sum_i X_i$ exists. Then
$$\mathbb{E}[X] \;=\; \sum_i \mathbb{E}[X_i].$$

## Proof

By the linearity of expectation, for every finite $n$,
$$\mathbb{E}\Big[ \sum_{i=1}^{n} X_i \Big] \;=\; \sum_{i=1}^{n} \mathbb{E}[X_i].$$
Now let $n \to \infty$. The partial sums $S_n = \sum_{i=1}^n X_i$ converge
to $X$ by the assumption that $X = \sum_i X_i$ exists, and therefore the
left-hand side converges to $\mathbb{E}[X]$. The right-hand side converges
to $\sum_i \mathbb{E}[X_i]$ by definition of an infinite series. Equating
the two limits completes the proof. $\blacksquare$
