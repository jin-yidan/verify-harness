# Ground Truth: Planted Flaws in "A High-Probability Regret Bound for Successive Elimination"

Exactly two flaws are planted. Everything else is correct.

## Flaw 1 — Step 1: union bound misses the quantifier over phases (misuse of a fixed-sample-size concentration bound)

**Location.** Step 1, the final sentence of the concentration argument: "A union bound over the $K$ arms then gives $\mathbb{P}(\mathcal{E}^c) \le K \cdot \delta/K = \delta$, which proves the claim."

**What is wrong.** The event $\mathcal{E}$ requires $|\hat\mu_{i,t} - \mu_i| \le r(t)$ *simultaneously for every phase $t \ge 1$* (up to $T$ phases), not just for a single fixed $t$. Hoeffding's inequality is applied correctly per fixed pair $(i,t)$ — the computation $2\exp(-2t\,r(t)^2) = 2e^{-L} = \delta/K$ is exact — but the union bound is then taken only over the $K$ arms, silently treating the phase index as if it were a single fixed value. The events for different phases $t$ are distinct (and the relevant phase at which an arm's estimate is used, e.g., its elimination phase, is data-dependent), so a valid union bound must also range over $t$, yielding only
$$\mathbb{P}(\mathcal{E}^c) \;\le\; \sum_{i=1}^{K} \sum_{t=1}^{T} \frac{\delta}{K} \;=\; T\,\delta,$$
which is vacuous for $\delta \ge 1/T$. The claim $\mathbb{P}(\mathcal{E}) \ge 1-\delta$ is therefore unjustified, and is false in general: a fixed-width per-phase bound with constant failure probability $\delta/K$ per phase cannot hold uniformly over $T$ phases with total failure probability $\delta$ (by independence of fresh samples across phases, failures accumulate).

**Correct fix.** Take the union bound over both arms and phases: replace $r(t) = \sqrt{\ln(2K/\delta)/(2t)}$ with $r(t) = \sqrt{\ln(2KT/\delta)/(2t)}$ (or use an anytime/peeling bound). Then $\mathbb{P}(|\hat\mu_{i,t}-\mu_i|>r(t)) \le \delta/(KT)$ per pair and $\mathbb{P}(\mathcal{E}^c) \le \delta$ over all $KT$ pairs. This propagates $\ln(2KT/\delta)$ into the final bound.

## Flaw 2 — Step 4: false algebraic equivalence (dropped factor of 2)

**Location.** Step 4, first sentence: "Since $r(t)^2 = L/(2t)$, rearranging shows that the condition $\Delta_i > 4\,r(t)$ holds precisely when $t > 4L/\Delta_i^2$."

**What is wrong.** The correct rearrangement is
$$\Delta_i > 4\,r(t) \iff \Delta_i^2 > 16\,r(t)^2 = \frac{16L}{2t} = \frac{8L}{t} \iff t > \frac{8L}{\Delta_i^2}.$$
The proof states the threshold $4L/\Delta_i^2$ instead of $8L/\Delta_i^2$ — a dropped factor of 2. The stated "only if ⇐" direction is false. (At $t = 4L/\Delta_i^2$ one gets $4r(t) = \sqrt{2}\,\Delta_i > \Delta_i$.)

**Concrete numeric counterexample (verified by computation).** Take $K = 2$, $\delta = 1/2$, $\Delta_i = 1/2$. Then
- $L = \ln(2K/\delta) = \ln 8 = 2.0794415\ldots$
- Flawed threshold: $4L/\Delta_i^2 = 16L = 33.2710\ldots$, so the flawed claim asserts $\Delta_i > 4r(t)$ for every $t \ge 34$. In particular $t_i = \lfloor 16L \rfloor + 1 = 34$.
- At $t = 34$: $r(34) = \sqrt{L/68} = \sqrt{0.0305800\ldots} = 0.1748714\ldots$, hence $4\,r(34) = 0.6994858\ldots$
- But $\Delta_i = 0.5 < 0.6995 = 4\,r(34)$, contradicting the stated equivalence. The claim $\Delta_i > 4r(t_i)$ in Step 4 is false at these values.
- The correct threshold $8L/\Delta_i^2 = 32L = 66.542\ldots$ works: at $t = 67$, $4\,r(67) = 0.49829 < 0.5 = \Delta_i$. ✓

**Correct fix.** Replace the threshold by $t > 8L/\Delta_i^2$ and $t_i := \lfloor 8L/\Delta_i^2 \rfloor + 1$. The final bound's constant then becomes $8$ instead of $4$:
$$R_T \le \sum_{i:\Delta_i>0}\Big(\Delta_i + \frac{8\ln(2K/\delta)}{\Delta_i}\Big),$$
and combined with the fix for Flaw 1, the fully correct theorem is
$$R_T \le \sum_{i:\Delta_i>0}\Big(\Delta_i + \frac{8\ln(2KT/\delta)}{\Delta_i}\Big) \quad \text{w.p. } \ge 1-\delta.$$

**Downstream consequences (not separate flaws).** The definition $t_i = \lfloor 4L/\Delta_i^2 \rfloor + 1$ in Step 4, the bound $N_i(T) \le 4L/\Delta_i^2 + 1$ in Step 5, and the constant $4$ in the theorem statement and Step 6 all inherit Flaw 2; they are internally consistent given the false Step 4 equivalence. Likewise the theorem's probability claim $1-\delta$ inherits Flaw 1.

## Fully correct components

- **Setup/definitions:** all correct. The regret identity $R_T = \sum_i \Delta_i N_i(T)$ is exact for pseudo-regret. The i.i.d. sample-table coupling makes $\hat\mu_{i,t}$ a genuine average of $t$ i.i.d. $[0,1]$ variables for each fixed $(i,t)$.
- **Step 1, per-pair Hoeffding computation:** correct. $2\exp(-2t\,r(t)^2) = 2e^{-L} = \delta/K$ exactly (verified numerically: at $t=34$, $2\exp(-2 \cdot 34 \cdot r(34)^2) = 0.25 = \delta/K$ for $K=2,\delta=1/2$). Only the union-bound scope is flawed.
- **Step 2:** fully correct (induction that arm 1 survives; the chain $\hat\mu_{j,t} \le \mu_j + r(t) \le \mu_1 + r(t) \le \hat\mu_{1,t} + 2r(t)$ holds on $\mathcal{E}$).
- **Step 3:** fully correct ($\Delta_i > 4r(t)$ plus $\mathcal{E}$ implies the strict elimination criterion $> 2r(t)$ is triggered, with arm 1 active by Step 2).
- **Step 4:** flawed only in the algebraic threshold (Flaw 2); the logical structure (eliminate by end of first qualifying completed phase, never active afterwards) is sound.
- **Step 5:** correct given Step 4's $t_i$ (at most one pull per phase through phase $t_i$, none after; partial-phase/budget-expiry case handled correctly; $\lfloor x \rfloor + 1 \le x + 1$).
- **Step 6:** correct algebra given Step 5 ($\Delta_i(4L/\Delta_i^2 + 1) = 4L/\Delta_i + \Delta_i$), and the high-probability conclusion follows correctly from Step 1's (flawed) claim.
