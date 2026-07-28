# A High-Probability Regret Bound for Successive Elimination

## Setting and notation

We consider a stochastic multi-armed bandit with $K \ge 2$ arms. Each arm $i \in [K] := \{1, \dots, K\}$ is associated with a reward distribution $\nu_i$ supported on $[0,1]$ with mean $\mu_i$. We assume arm $1$ is the unique optimal arm, and write
$$\Delta_i := \mu_1 - \mu_i > 0 \quad \text{for } i \ge 2, \qquad \Delta_1 := 0.$$

For each arm $i$, let $X_{i,1}, X_{i,2}, \dots$ be an i.i.d. sequence drawn from $\nu_i$, independent across arms; the $s$-th pull of arm $i$ returns $X_{i,s}$. The empirical mean of arm $i$ after $t$ pulls of that arm is
$$\hat\mu_{i,t} := \frac{1}{t} \sum_{s=1}^{t} X_{i,s}.$$

The learner interacts for a horizon of $T$ rounds, pulling one arm per round. Let $A_t \in [K]$ denote the arm pulled at round $t$, and let $N_i(T) := \sum_{t=1}^{T} \mathbf{1}\{A_t = i\}$ be the number of pulls of arm $i$ within the horizon. The (pseudo-)regret is
$$R_T := T\mu_1 - \sum_{t=1}^{T} \mu_{A_t} = \sum_{i=1}^{K} \Delta_i\, N_i(T),$$
where the second equality is an identity, since each pull of arm $i$ contributes exactly $\Delta_i$ to the left-hand side.

Fix a confidence parameter $\delta \in (0,1)$ and define the confidence radius
$$r(t) := \sqrt{\frac{\ln(2K/\delta)}{2t}}, \qquad t \ge 1.$$

## The algorithm (Successive Elimination)

Maintain an active set $\mathcal{A}$, initialized to $\mathcal{A} = [K]$. The algorithm proceeds in phases $t = 1, 2, \dots$:

1. **Sample.** Pull each arm in $\mathcal{A}$ once. (Thus, at the end of phase $t$, every arm currently in $\mathcal{A}$ has been pulled exactly $t$ times in total.)
2. **Eliminate.** Remove from $\mathcal{A}$ every arm $i \in \mathcal{A}$ such that
$$\max_{j \in \mathcal{A}} \hat\mu_{j,t} - \hat\mu_{i,t} > 2\,r(t).$$

The algorithm halts as soon as the total number of pulls reaches $T$ (possibly in the middle of a phase, in which case the partial phase performs no elimination).

## Theorem

For any $T \ge 1$ and $\delta \in (0,1)$, with probability at least $1 - \delta$, Successive Elimination satisfies
$$R_T \;\le\; \sum_{i\,:\,\Delta_i > 0} \left( \Delta_i + \frac{4 \ln(2K/\delta)}{\Delta_i} \right).$$

## Proof

Throughout, write $L := \ln(2K/\delta)$, so that $r(t) = \sqrt{L/(2t)}$.

**Step 1 (Good event and its probability).** Define the event
$$\mathcal{E} := \Big\{ \, |\hat\mu_{i,t} - \mu_i| \le r(t) \ \text{ for every arm } i \in [K] \text{ and every phase } t \ge 1 \text{ completed by the algorithm} \, \Big\}.$$
We claim $\mathbb{P}(\mathcal{E}) \ge 1 - \delta$. Fix an arm $i \in [K]$ and a phase $t$. The estimate $\hat\mu_{i,t}$ is the average of the $t$ i.i.d. samples $X_{i,1}, \dots, X_{i,t}$, each supported on $[0,1]$, so by Hoeffding's inequality,
$$\mathbb{P}\big( |\hat\mu_{i,t} - \mu_i| > r(t) \big) \;\le\; 2 \exp\big( -2t\, r(t)^2 \big) \;=\; 2 e^{-L} \;=\; \frac{\delta}{K}.$$
A union bound over the $K$ arms then gives $\mathbb{P}(\mathcal{E}^c) \le K \cdot \delta/K = \delta$, which proves the claim. For the remainder of the proof we work on the event $\mathcal{E}$.

**Step 2 (The optimal arm is never eliminated).** We show by induction on the phase index that arm $1$ remains in the active set throughout the run of the algorithm. Arm $1$ is active in phase $1$. Suppose arm $1$ is active during phase $t$. For any arm $j$ active during phase $t$, on $\mathcal{E}$ we have
$$\hat\mu_{j,t} \;\le\; \mu_j + r(t) \;\le\; \mu_1 + r(t) \;\le\; \hat\mu_{1,t} + 2\,r(t),$$
using $\mu_j \le \mu_1$ in the middle inequality. Hence $\max_{j \in \mathcal{A}} \hat\mu_{j,t} - \hat\mu_{1,t} \le 2\,r(t)$, so the elimination criterion is not triggered for arm $1$ at the end of phase $t$, and arm $1$ remains active in phase $t+1$. This completes the induction.

**Step 3 (Elimination criterion for suboptimal arms).** Let $i$ be an arm with $\Delta_i > 0$, and suppose arm $i$ is still active at the end of a completed phase $t$ for which $\Delta_i > 4\,r(t)$. By Step 2, arm $1$ is also active during phase $t$, and on $\mathcal{E}$,
$$\hat\mu_{1,t} - \hat\mu_{i,t} \;\ge\; \big(\mu_1 - r(t)\big) - \big(\mu_i + r(t)\big) \;=\; \Delta_i - 2\,r(t) \;>\; 4\,r(t) - 2\,r(t) \;=\; 2\,r(t).$$
Therefore $\max_{j \in \mathcal{A}} \hat\mu_{j,t} - \hat\mu_{i,t} > 2\,r(t)$, and arm $i$ is eliminated at the end of phase $t$.

**Step 4 (Elimination time).** Since $r(t)^2 = L/(2t)$, rearranging shows that the condition $\Delta_i > 4\,r(t)$ holds precisely when $t > 4L/\Delta_i^2$. Define
$$t_i := \left\lfloor \frac{4L}{\Delta_i^2} \right\rfloor + 1,$$
so that $t_i > 4L/\Delta_i^2$ and hence $\Delta_i > 4\,r(t_i)$. By Step 3, on $\mathcal{E}$ every suboptimal arm $i$ that is still active at the end of phase $t_i$ is eliminated at the end of that phase (if it completes); in particular, arm $i$ is never active in any phase after phase $t_i$.

**Step 5 (Bounding the pull counts).** Fix a suboptimal arm $i$. Arm $i$ is pulled at most once in each of the phases $1, \dots, t_i$ and, by Step 4, never in any later phase. If the budget of $T$ pulls expires during some phase $t \le t_i$, then arm $i$ has been pulled at most $t \le t_i$ times in any case. Hence on $\mathcal{E}$,
$$N_i(T) \;\le\; t_i \;=\; \left\lfloor \frac{4L}{\Delta_i^2} \right\rfloor + 1 \;\le\; \frac{4L}{\Delta_i^2} + 1.$$

**Step 6 (Regret bound).** Using the regret identity $R_T = \sum_{i=1}^{K} \Delta_i N_i(T)$, the fact that $\Delta_1 = 0$, and the bound of Step 5, on $\mathcal{E}$ we obtain
$$R_T \;=\; \sum_{i\,:\,\Delta_i > 0} \Delta_i\, N_i(T) \;\le\; \sum_{i\,:\,\Delta_i > 0} \Delta_i \left( \frac{4L}{\Delta_i^2} + 1 \right) \;=\; \sum_{i\,:\,\Delta_i > 0} \left( \Delta_i + \frac{4 \ln(2K/\delta)}{\Delta_i} \right).$$
Since $\mathbb{P}(\mathcal{E}) \ge 1 - \delta$ by Step 1, the theorem follows. $\blacksquare$
