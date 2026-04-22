# NS BLW-Gradient Chain — Lean 4 Formalization

[![CI](https://github.com/Brsanch/ns-lean-proofs/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/Brsanch/ns-lean-proofs/actions/workflows/lean_action_ci.yml)
[![License: MIT](https://img.shields.io/badge/License-MIT-blue.svg)](./LICENSE)

A Lean 4 + mathlib formalization of the Buaria–Lawson–Wilczek gradient chain
for 3D incompressible Navier–Stokes regularity on the torus $\mathbb{T}^3$
and on $\mathbb{R}^3$.

This repository is the Lean companion to the accompanying paper
(`paper/ns_regularity.md` in the noethersolve project, plus supplementals
`ns_regularity_caveats_formal.md` and `ns_regularity_blw_derivations.md`).
The paper will be added to this repository once the formalization is
complete.

## What is formalized (once complete)

### Unconditional backbone

- **Theorem 1** — if smooth NS data blows up at $T^* < \infty$, the blowup rate
  $\alpha$ (with $M(t) \geq c(T^* - t)^{-\alpha}$) satisfies $\alpha \in (1, 2)$.
- **Theorem 2** — unconditional far-field control:
  $\int_0^{T^*} |\sigma_{>R}|\, dt < \infty$ via Cauchy–Schwarz on the
  Biot–Savart kernel + energy identity.

### The BLW-gradient chain (§12)

- **Theorem 12.2 (gradient bound at argmax).** For smooth $u \in C^\infty(\mathcal{D} \times [0, T^*))$
  with $\nu > 0$ and $\mathcal{D} \in \{\mathbb{T}^3, \mathbb{R}^3\}$, at any
  local maximum $x^*(t)$ of $|\omega|^2$ with $dM/dt(t) \geq 0$:
  $$|\nabla\omega(x^*, t)| \leq M(t)\sqrt{\sigma(x^*, t)/\nu}.$$

- **Proposition 4** — combining Proposition 12.1 (the exact Biot–Savart identity
  at argmax) with Theorem 12.2, the log-absorption ODE, and the Seregin (2012)
  Type-I exclusion, smooth NS extends beyond any candidate $T^*$.

### Five caveats from the companion note

- **C1** Growth-moment coverage. Jordan decomposition.
- **C2** Argmax trajectory smoothness. Closed *unconditionally* via
  Rademacher + Danskin (Lemma C2.5). Optional refinement via Kato (1967)
  time-analyticity (Lemma C2.4, Proposition C2.6).
- **C3** Periodic Biot–Savart corrections. Ewald splitting + Epstein-zeta
  convergence.
- **C4** Implicit-bound uniqueness. Convex analysis + Banach fixed point.
- **C5** Global decomposition. Sub-Type-I rate + Seregin closure.

## Axiomatic footprint

The formalization is written modulo three named classical PDE results:

- `biot_savart_identity_R3` — Proposition 12.1 on $\mathbb{R}^3$.
- `seregin_type_one_exclusion` — Seregin (2012, *CMP* 312, 833–845).
- `NS_time_analyticity` — Kato (1967) / Foias–Temam (1979).

All other content is expected to be machine-verified with **zero `sorry`**.

## Build

**Policy:** CI (`.github/workflows/lean_action_ci.yml`) is the default
verifier. Do **not** run `lake build` or `lake exe cache get` on Apple
Silicon — they trigger apfsd saturation and kernel panics. See
[`DEVELOPMENT.md`](./DEVELOPMENT.md) for the full safe-workflow
protocol, diagnostic tricks, and lessons learned from the sister
project `sqg-lean-proofs`.

For safe local single-file type-checking only (no artifact writes):

```
LEAN_NUM_THREADS=1 lake env lean NSBlwChain/YOUR_FILE.lean
```

For everything else, push and let CI build.

## Status

**v0.3 (2026-04-22 overnight)** — 65 files, ~9500 LOC, all CI-green.

**Machine-verified analytical discharges (items 2-6 fully closed;
item 1 reduced to single residual):**

- **Theorem 12.2 algebraic core** `|∇ω|²(x*) ≤ M²σ/ν` + sqrt form 12.2'.
- **Step (i)** `∂_i|ω|² = 2·M·∂_i ω₃` via mathlib `HasDerivAt.pow`
  (`ScalarProductRule` → `DerivFrameFromProductRule`).
- **Step (ii)** Hessian trace ≤ 0 at local max (`MaxPrinciple`)
  — three `d_i_nonpos` discharged from `IsLocalMax` +
  differentiability via `MaxPrincipleFromLocalMax`
  (`HasDerivAt.tendsto_slope` + `strictMonoOn_of_deriv_pos`).
- **Step (ii.b)** pointwise `(f²)'' = 2(f')² + 2 f · f''` via
  `HasDerivAt.pow` + product rule (`HessianExpansionFromC2`).
- **Step (iii)** Danskin envelope `|ω|²/2` (`EnvelopeIdentity`)
  composed with `d/dt(M²/2) = M·Ṁ` (`ChainRuleMSquared`)
  → `VorticityFrameFromEnvelope`.
- **§12.4 step 5→6** log expansion (`LogAbsorption`).
- **§C1 FTC-for-Lipschitz**
  `GrowthMomentBundle.ofLipschitzAndPointwiseBound` — `hIntegratedBound`
  discharged from `LipschitzWith` via
  `AbsolutelyContinuousOnInterval.integral_deriv_eq_sub`
  (`C1_FTC_Discharge`).
- **§C4 largeness (Banach fixed-point)** closed by elementary
  growth dominance: for `M ≥ M_crit(L, ν, K)`, `1 + log L +
  ½ log(σ/ν) ≤ 4 log M − K/M` (`C4_GrowthDominance`).
- **Angular integrals D.3.1 and D.3.2** from mathlib FTC.
- **Epstein p-series framework** for torus correction.
- **Caveat C2.5 (Danskin envelope)**.
- **End-to-end** `FullDischargePipeline.gradient_bound_from_full_discharge`
  with concrete sanity-check (40 ≤ 400).
- **Seregin threading** `ChainThread.extends_past_T_of_subTypeI`
  + umbrella `ChainHypotheses.proposition_four_of_hypotheses`.
- **NS connection layer** `FromNSEvolution.lean`:
  `MOfVelocityField`, `NSArgmaxInputs`, and
  `argmaxBundle_of_NSEvolutionAxioms` plumb velocity-field data
  through the scalar bundles + gradient bound.

**Partial** (item 1 — ODE integration §12.4 step 7→8):
The algebraic core `integrated_bound_of_substituted_bound` +
constructor `DifferentialInequalityBundle.ofSubstitutedBound` in
`ODEIntegration_Discharge` reduce `(T-t)·M·logM ≤ 1/4` to a single
residual hypothesis

  `hW_lower_bound : ∀ t ∈ (t_start, T), 4·(T-t) ≤ 1/(M(t)·log M(t))`

which remains to be derived from `Ṁ ≤ 4 M² log M` via quotient rule
on `w = 1/(M log M)` + FTC + boundary limit + tail absorption.

See `OPEN.md` for the live roadmap and `DEVELOPMENT.md` for the
build-safety protocol.

## Relationship to the SQG project

This project parallels [`sqg-lean-proofs`](https://github.com/Brsanch/sqg-lean-proofs)
in structure: a conditional regularity roadmap whose analytical chain is
fully formal, with explicitly-named classical PDE results as the only
axiomatic hypotheses. The infrastructure (lattice-zeta bounds, Galerkin
framing, BKM/MMP patterns) will be adapted from the SQG project where
applicable.

## Citation

To be added upon first release. See `CITATION.cff` for the current
software-citation skeleton.

## License

MIT. See [LICENSE](./LICENSE).
