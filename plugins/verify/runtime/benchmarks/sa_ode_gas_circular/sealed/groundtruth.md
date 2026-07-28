# Ground Truth: SA Convergence via the ODE Method (Circular Boundedness)

One flaw, naturally occurring (not planted): the proof bridges the classic
stability gap of the ODE method with circular reasoning. The flaw class is
CIRCULAR — the only fixture in the battery exercising it.

## Flaw — Lemma 2 ↔ Lemma 3: conditional conclusion invoked unconditionally

**Location.** Lemma 3: "by Lemma 2 the accumulated noise is almost surely
finite".

**What is wrong.** Lemma 2 establishes noise convergence ONLY on the event
$\{\sup_k \|\theta_k\| < \infty\}$ — the conditioning is necessary and
explicitly stated there: the variance bound $C(1+\|\theta_n\|^2)$ makes
$\sum_k a_k^2\,\mathbb{E}[\|M_{k+1}\|^2 \mid \mathcal{F}_k]$ summable only if
$\|\theta_k\|$ is bounded. Lemma 3 then invokes Lemma 2's conclusion
UNCONDITIONALLY to prove $\sup_n \|\theta_n\| < \infty$ — i.e., to prove the
very event Lemma 2 is conditioned on. Lemma 3 → Lemma 2 → Lemma 3: a cycle.

The cycle is invisible to a textual `depends_on` graph (Lemma 2 never cites
Lemma 3; the citation arrows are acyclic). It appears only when Lemma 2's
conditioning event is tracked as a hypothesis of every downstream invocation
— conditional-conclusion camouflage (Hypothesis Audit item 4, added to the
pipeline from this very fixture's first run).

**Secondary symptom (same root cause).** Lemma 3's positive argument — GAS
makes $h$ point "inward", so the iterates "cannot escape to infinity" — is
asserted, not proved, and is false in general: global asymptotic stability of
the ODE does not imply boundedness/stability of the noisy discrete iterates.

**Correct fix** (Borkar–Meyn 2000): add a separate stability hypothesis —
the scaled field $h_\infty(\theta) = \lim_{c\to\infty} h(c\theta)/c$ exists
and has the origin as a GAS equilibrium — from which iterate boundedness is
PROVED, and only then apply the martingale argument and the
asymptotic-pseudotrajectory theorem (Benaïm 1996; Borkar 2008). The theorem
as stated omits this hypothesis; adding it would violate Rule 1, so the proof
is not salvageable as written.

**Expected verdict**: UNVERIFIED/CIRCULAR — distinct from
HYPOTHESIS_VIOLATION (the dropped condition is another block's conclusion,
not a library lemma's stated hypothesis) and from INCOMPLETE (no step is
missing — the steps exist but support each other). Audit-only: the flaw is
asymptotic/measure-theoretic with no finite refutation instance, so no
kernel-backed refutation is expected.

## Fully correct components

- Lemma 1 (`ode_wellposed_attractor`): sound in substance (minor: Picard–
  Lindelöf is local; global existence uses linear growth from Lipschitz).
  Formalization would need ODE-flow/attractor infrastructure absent from
  Mathlib — named-result status is the honest outcome.
- Lemma 2 (`conditional_martingale_noise_converges`): sound AS A CONDITIONAL
  statement (standard $L^2$-bounded martingale convergence). A run may
  legitimately attribute the flaw to Lemma 2's unconditional *use* rather
  than to Lemma 3 — which is why this block is NOT listed in
  `sound_block_hints`.
- Combine (`ode_method_convergence`): the Benaïm/Borkar APT theorem is
  correctly cited but takes boundedness as input; blocked by Lemma 3.
- The trailing corollary "any RL algorithm whose mean-field ODE has a unique
  GAS equilibrium converges" is additionally overbroad (asynchronous updates,
  biased non-martingale noise, divergent function-approximation examples),
  but the verdict-deciding flaw is the cycle.

## Provenance

Organic user submission, first verified 2026-06-11
(`runs/sa_ode_method_gas_convergence_20260611_211836.json`, preserved here as
`reference_run.json`). Note: the reference run predates the driver's
`circular` resolve kind, so its verdict-deciding block carries kind
`violation`; later runs should record it via
`d.resolve(..., circular="conditional_martingale_noise_converges", ...)`.
