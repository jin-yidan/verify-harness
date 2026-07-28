# A Logarithmic Regret Bound for UCB1

## Setting and notation

We consider a stochastic multi-armed bandit with $K \ge 2$ arms. Each arm
$a \in [K]$ has a reward distribution supported on $[0,1]$ with mean $\mu_a$.
Let $\mu^* = \max_a \mu_a$ and $\Delta_a = \mu^* - \mu_a$. For each arm $a$,
let $X_{a,1}, X_{a,2}, \dots$ be the i.i.d. reward sequence; the $s$-th pull
of arm $a$ returns $X_{a,s}$. Let $N_t(a)$ denote the number of pulls of arm
$a$ after $t$ rounds, and let $\hat\mu_{a,t}$ denote the empirical mean of
arm $a$'s rewards observed up to round $t$ (the average of its first
$N_t(a)$ samples). The pseudo-regret after $T$ rounds is
$R_T = \sum_a \Delta_a\, \mathbb{E}[N_T(a)]$.

## The algorithm (UCB1)

Pull each arm once. Thereafter, at round $t$ pull the arm maximizing the
index
$$\mathrm{UCB}_t(a) \;=\; \hat\mu_{a,t-1} + \sqrt{\frac{2 \ln t}{N_{t-1}(a)}}.$$

## Theorem

For any $T \ge K$,
$$R_T \;\le\; \sum_{a\,:\,\Delta_a > 0} \left( \frac{8 \ln T}{\Delta_a} + c\,\Delta_a \right)$$
for an absolute constant $c$.

## Proof

**Step 1 (Regret decomposition).** By the identity
$R_T = \sum_a \Delta_a \mathbb{E}[N_T(a)]$, it suffices to bound
$\mathbb{E}[N_T(a)]$ for each suboptimal arm $a$.

**Step 2 (Index condition).** Suboptimal arm $a$ is pulled at round $t$ only
if $\mathrm{UCB}_t(a) \ge \mathrm{UCB}_t(a^*)$, where $a^*$ is an optimal
arm. A standard three-way split shows this requires at least one of:
(i) $\hat\mu_{a^*,t-1} + \sqrt{2\ln t / N_{t-1}(a^*)} \le \mu^*$ (the optimal
arm is underestimated); (ii) $\hat\mu_{a,t-1} \ge \mu_a + \sqrt{2\ln t /
N_{t-1}(a)}$ (arm $a$ is overestimated); or (iii) $N_{t-1}(a) <
8 \ln t / \Delta_a^2$ (arm $a$ is undersampled).

**Step 3 (Bad-event probabilities).** Consider event (ii) at round $t$. The
empirical mean $\hat\mu_{a,t-1}$ is the average of the $N_{t-1}(a)$ samples
of arm $a$ observed so far, each i.i.d. supported on $[0,1]$. Applying
Hoeffding's inequality with $n = N_{t-1}(a)$ samples and deviation
$\varepsilon = \sqrt{2\ln t / N_{t-1}(a)}$ gives
$$\mathbb{P}\Big( \hat\mu_{a,t-1} \ge \mu_a + \sqrt{2\ln t / N_{t-1}(a)} \Big)
\;\le\; \exp\big( -2\, N_{t-1}(a) \cdot 2\ln t / N_{t-1}(a) \big) \;=\; t^{-4}.$$
The same bound applies to event (i) by symmetry.

**Step 4 (Tail sum).** The contribution of events (i) and (ii) over all
rounds is at most $\sum_{t=1}^{\infty} 2\,t^{-4} < \infty$, an absolute
constant.

**Step 5 (Count bound).** Event (iii) can hold for at most
$\lceil 8 \ln T / \Delta_a^2 \rceil$ pulls of arm $a$. Combining with Step 4,
$\mathbb{E}[N_T(a)] \le 8\ln T/\Delta_a^2 + O(1)$.

**Step 6 (Assembly).** Multiplying by $\Delta_a$ and summing over suboptimal
arms yields $R_T \le \sum_{a:\Delta_a>0} (8\ln T/\Delta_a + c\,\Delta_a)$.
$\blacksquare$
