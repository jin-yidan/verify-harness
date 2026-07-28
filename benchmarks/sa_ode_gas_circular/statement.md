# Almost-Sure Convergence of Stochastic Approximation via the ODE Method

## Setup

A general stochastic-approximation (SA) recursion, the abstraction under
which TD, Q-learning, and actor-critic are all analyzed:

$$\theta_{n+1} = \theta_n + a_n\big(h(\theta_n) + M_{n+1}\big), \qquad \theta_n \in \mathbb{R}^d,$$

where $h(\theta) = \mathbb{E}[\text{update direction} \mid \theta]$ is the
mean field, $M_{n+1}$ is the zero-mean noise (a martingale difference with
respect to the natural filtration $\mathcal{F}_n$), and step sizes obey
Robbins–Monro: $\sum_n a_n = \infty$, $\sum_n a_n^2 < \infty$. The associated
limiting ODE is $\dot\theta = h(\theta)$. In the RL instance,
$h(\theta) = \Phi^\top D(\mathcal{T}_\theta \Phi\theta - \Phi\theta)$ for a
value-based method (or the policy-gradient field for actor-critic), and the
target $\theta^\star$ is the fixed point one wants to reach.

## Theorem

Suppose $h$ is globally Lipschitz, the noise has bounded conditional variance
$\mathbb{E}[\|M_{n+1}\|^2 \mid \mathcal{F}_n] \le C(1 + \|\theta_n\|^2)$, and
the ODE $\dot\theta = h(\theta)$ has a unique globally asymptotically stable
(GAS) equilibrium $\theta^\star$. Then $\theta_n \to \theta^\star$ almost
surely. In particular, any RL algorithm whose mean-field ODE has a unique GAS
equilibrium converges to it.

## Proof

**Lemma 1 (the ODE is well-posed and globally attracting).** Lipschitz $h$
gives existence and uniqueness of solutions (Picard–Lindelöf), and by
hypothesis every solution trajectory $\theta(t)$ converges to $\theta^\star$
from any initial condition. So the ODE has a single global attractor
$\{\theta^\star\}$. $\square$

**Lemma 2 (the noise is asymptotically negligible).** Define the partial sums
$Z_n = \sum_{k=1}^{n} a_k M_{k+1}$. On any event where
$\sup_k \|\theta_k\| < \infty$, the conditional variances are summable:
$\sum_k a_k^2\,\mathbb{E}[\|M_{k+1}\|^2 \mid \mathcal{F}_k] \le C' \sum_k a_k^2 < \infty$.
Hence $(Z_n)$ is an $L^2$-bounded martingale and converges almost surely by
the martingale convergence theorem. The cumulative effect of the noise is
therefore finite, so asymptotically the recursion is a vanishing-perturbation
discretization of the ODE. $\square$

**Lemma 3 (the iterates are bounded).** Since $\theta^\star$ is globally
asymptotically stable (Lemma 1), the mean field $h$ points "inward," driving
any trajectory back toward $\theta^\star$; and by Lemma 2 the accumulated
noise is almost surely finite. A noisy Euler discretization of an ODE all of
whose trajectories converge to a single point, perturbed only by a summable
noise, cannot escape to infinity. Therefore $\sup_n \|\theta_n\| < \infty$
almost surely. $\square$

**Combine.** By Lemma 3 the iterates are bounded, so the standard ODE-method
theorem (Benaïm 1996; Borkar 2008) applies: the linearly interpolated
trajectory of $(\theta_n)$ is an asymptotic pseudotrajectory of
$\dot\theta = h(\theta)$, and a bounded asymptotic pseudotrajectory converges
to the ODE's global attractor. By Lemma 1 that attractor is
$\{\theta^\star\}$, so $\theta_n \to \theta^\star$ almost surely.
$\blacksquare$
