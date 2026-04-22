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

**v0.1.0 (2026-04-22)** — Initial scaffold. Build infrastructure, top-level
module skeleton, and planning documents in place. Formalization content
lands incrementally; see `OPEN.md` for the live roadmap.

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
