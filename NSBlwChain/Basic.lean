-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).
-- Machine-verified formalization of the BLW-gradient chain for 3D
-- Navier–Stokes regularity (see accompanying paper, to be added).

/-!
# NS BLW-Gradient Chain — Lean 4 Formalization

This is the top-level entry module for the formalization of the
Buaria–Lawson–Wilczek gradient chain for 3D Navier–Stokes regularity on
the torus $\mathbb{T}^3$ and on $\mathbb{R}^3$.

## Scope

The formalization targets, following the companion paper:

* **Theorem 1** (unconditional blowup-rate bound, $\alpha \in (1, 2)$).
* **Theorem 2** (unconditional far-field strain control).
* **Theorem 12.2** (gradient bound at argmax):
  $|\nabla\omega|(x^*) \leq M\sqrt{\sigma/\nu}$ under $dM/dt \geq 0$.
* **Proposition 4** (BLW-gradient regularity sketch): structural chain
  combining Proposition 12.1 (exact Biot–Savart identity at argmax),
  Theorem 12.2, the log-absorption ODE, and Seregin (2012).

Together with the five caveats C1–C5 from the companion note
`ns_regularity_caveats_formal.md`:

* **C1** Growth-moment coverage (Jordan decomposition).
* **C2** Argmax trajectory smoothness (Rademacher + Danskin envelope;
  plus optional real-analyticity refinement C2.4 / C2.6).
* **C3** Periodic Biot–Savart corrections (Ewald + Epstein-zeta).
* **C4** Implicit-bound uniqueness (convexity + Banach fixed point).
* **C5** Global decomposition (sub-Type-I rate + Seregin 2012).

## Axiomatic footprint

The formalization is written modulo three explicitly-named classical
PDE results, which are imported from mathlib when possible and declared
as named hypotheses otherwise:

* `biot_savart_identity_R3` — Proposition 12.1 on $\mathbb{R}^3$
  (Biot–Savart identity at argmax, after cylindrical θ-averaging).
* `seregin_type_one_exclusion` — Seregin (2012, CMP 312): if a
  suitable weak solution satisfies $(T^* - t)\|\omega\|_{L^\infty} \to 0$,
  it extends smoothly across $T^*$.
* `NS_time_analyticity` — Kato (1967) / Foias–Temam (1979): smooth
  NS solutions on $[0, T^*)$ extend to a holomorphic map on a
  complex strip $\Sigma$.

All other mathematical content is expected to be machine-verified.

## Repository layout

```
NSBlwChain/
  Basic.lean              -- this file (project entry point)
  Setup/                  -- foundations (vector fields, NS hypothesis, axioms)
  Caveats/                -- elementary caveats C1, C2.5, C4, angular integrals
  BLW/                    -- BLW-gradient chain core (Thm 12.2, log-absorption)
  Torus/                  -- torus Biot–Savart machinery (C3)
  Analyticity/            -- real-analyticity refinement (C2.4, C2.6)
  Unconditional/          -- Theorems 1 and 2
  Capstone.lean           -- end-to-end Proposition 4
```

(Subdirectories created as content lands; this file will import them.)

## Status

Initial scaffold — v0.1.0 (2026-04-22). Work in progress.

The file below contains a placeholder theorem to exercise the build.
It will be replaced as real content lands.
-/

import Mathlib

namespace NSBlwChain

/-- Placeholder lemma to exercise the build during initial setup.
    Will be removed once real content is in place. -/
theorem placeholder_setup_exercises_build : True := trivial

end NSBlwChain
