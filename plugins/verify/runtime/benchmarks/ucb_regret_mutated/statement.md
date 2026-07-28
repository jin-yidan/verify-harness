# UCB1 Regret Bound

## Theorem

For all $K > 0$, if policy UCB1 is run on $K$ machines having arbitrary
reward distributions $P_1, \dots, P_K$ with support in $[0,1]$, then its
expected regret after any number $n$ of plays is at most
$$\Big[ 4 \sum_{i\,:\,\mu_i < \mu^*} \frac{\ln n}{\Delta_i} \Big]
  + \Big(1 + \frac{\pi^2}{3}\Big) \sum_{j=1}^{K} \Delta_j,$$
where $\mu_1, \dots, \mu_K$ are the expected values of $P_1, \dots, P_K$,
$\mu^* = \max_i \mu_i$, and $\Delta_i = \mu^* - \mu_i$. UCB1 pulls each arm
once, then at each time $t$ pulls the arm maximizing
$\bar{x}_{i,s} + \sqrt{2 \ln t / s}$, where $\bar{x}_{i,s}$ is the average
reward of arm $i$ over its $s$ plays so far.

## Proof

**Step 1 (Decompose regret).** $\mathbb{E}[R_n] = \sum_{i: \Delta_i > 0}
\Delta_i\, \mathbb{E}[T_i(n)]$ where $T_i(n)$ counts plays of suboptimal arm
$i$.

**Step 2 (Threshold).** Fix suboptimal arm $i$. Set
$\ell = \lceil 4 \ln n / \Delta_i^2 \rceil$. Then
$T_i(n) \le \ell + \sum_{t=\ell+1}^{n} \mathbf{1}\{\text{arm } i \text{
played at } t \text{ and } T_i(t-1) \ge \ell\}$.

**Step 3 (Index condition).** Arm $i$ is played at time $t$ only if its UCB
index $\bar{x}_{i,s} + \sqrt{2 \ln t / s}$ (at its current play count $s$)
is at least the optimal arm's index $\bar{x}^*_{s^*} + \sqrt{2 \ln t / s^*}$
(at its current play count $s^*$). This is implied by the worst case over
the possible counts:
$$\max_{\ell \le s < t} \big( \bar{x}_{i,s} + \sqrt{2\ln t/s} \big) \;\ge\;
  \min_{0 < s^* < t} \big( \bar{x}^*_{s^*} + \sqrt{2\ln t/s^*} \big).$$

**Step 4 (Bad events).** For the above to hold with $s \ge \ell$, at least
one of the following must hold for some $s, s^*$: (a)
$\bar{x}^*_{s^*} \le \mu^* - \sqrt{2 \ln t / s^*}$ (optimal arm
underestimated); (b) $\bar{x}_{i,s} \ge \mu_i + \sqrt{2 \ln t / s}$
(suboptimal arm overestimated). Indeed, if both fail and $s \ge \ell \ge
8\ln n/\Delta_i^2$, then
$\bar{x}_{i,s} + \sqrt{2\ln t/s} < \mu_i + 2\sqrt{2\ln t/s} \le \mu_i +
\Delta_i = \mu^* < \bar{x}^*_{s^*} + \sqrt{2\ln t/s^*}$ — a contradiction
(using $2\sqrt{2\ln t/s} \le \Delta_i$ for $s \ge 8\ln t/\Delta_i^2$, and
$\ln t \le \ln n$).

**Step 5 (Hoeffding).** For each FIXED pair $(t, s)$, the average
$\bar{x}_{i,s}$ is the mean of $s$ i.i.d. $[0,1]$-valued samples (the first
$s$ rewards of arm $i$), so by Hoeffding's inequality each bad event has
probability at most $e^{-2s \cdot 2\ln t/s} = t^{-4}$, and the union over
the at most $t$ values of $s$ (resp. $s^*$) is handled by summation in
Step 6.

**Step 6 (Sum).** $\sum_{t=1}^{\infty} \sum_{s=1}^{t} \sum_{s^*=1}^{t}
2\,t^{-4} \le \sum_{t=1}^{\infty} 2\,t^{-2} = \frac{\pi^2}{3}$.

**Step 7 (Combine).** $\mathbb{E}[T_i(n)] \le \lceil 4 \ln n / \Delta_i^2
\rceil + \frac{\pi^2}{3} \le 4 \ln n / \Delta_i^2 + 1 + \frac{\pi^2}{3}$.
Multiplying by $\Delta_i$ and summing over suboptimal arms gives the bound.
$\blacksquare$
