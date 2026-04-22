# Open items — ns-lean-proofs

Canonical list of everything remaining before the BLW-gradient chain
skeleton is closed. Each item is linked to the tagged release that will
close it (once started).

## Roadmap

The target is a skeleton-formalization of §12 of the companion paper
plus the five caveats C1–C5, matching SQG-project rigor: analytical
chain fully machine-verified, classical PDE inputs stated as named
axioms. Budget: <25,000 LOC.

### Part I — Foundations (~5,000 LOC)

- [ ] **`Setup/VectorFields.lean`** (~1,500 LOC). 3-vector fields on
  $\mathbb{T}^3$ / $\mathbb{R}^3$: divergence, curl, Laplacian, basic
  identities ($\nabla\times\nabla\times = -\Delta + \nabla\nabla\cdot$).
  `irreducible` wrappers to avoid instance-synthesis loops (lesson from
  SQG §10 work).
- [ ] **`Setup/NSHypothesis.lean`** (~500 LOC). `NSEvolutionAxioms`
  bundle: smooth solution + vorticity equation + zero-mean + div-free.
  Analog of SQG's `SqgEvolutionAxioms_strong`.
- [ ] **`Setup/ArgmaxFrame.lean`** (~500 LOC). Local rotation setting
  $\hat\omega(x^*) = \hat e_3$; cylindrical-coordinates conventions
  around $x^*$.
- [ ] **`Setup/LipschitzToAE.lean`** (~300 LOC). Rademacher wrapper:
  Lipschitz → differentiable a.e. pipeline.
- [ ] **`Setup/ClassicalAxioms.lean`** (~2,000 LOC). Three named axioms:
  - `biot_savart_identity_R3` (Proposition 12.1)
  - `seregin_type_one_exclusion` (Seregin 2012)
  - `NS_time_analyticity` (Kato 1967 / Foias–Temam 1979)
- [ ] **`Setup/EnergyEnstrophy.lean`** (~200 LOC). Lemma B + corollaries.

### Part II — Elementary caveats (~3,500 LOC)

- [ ] **`Caveats/C1_GrowthMoment.lean`** (~800 LOC). Jordan decomposition,
  Proposition C1, Corollary C1.1.
- [x] **`Caveats/C2_Envelope.lean`** — **Lemma C2.5 (Danskin envelope)
  core landed in v0.1.1.** Includes `danskin_envelope`,
  `danskin_envelope_consistent` (uniqueness across argmax points), and
  `deriv_sup_eq_deriv_slice_of_argmax`. Still TODO in this file:
  Lemma C2.1 (Lipschitz of $M$) and Proposition C2 (a.e. ODE packaging),
  ~800–1,000 more LOC.
- [ ] **`Caveats/C4_ImplicitBound.lean`** (~1,000 LOC). Convex analysis,
  Proposition C4 ($\sigma \leq 4M\log M$), Banach fixed-point.
- [ ] **`Caveats/AngularIntegrals.lean`** (~500 LOC). D.3.1 ($\int = 2\delta/3$),
  D.3.2 ($\int = (2/3)\log(L/\delta)$) via explicit spherical-coords
  substitution.

### Part III — BLW-gradient chain core (~8,000 LOC)

- [ ] **`BLW/BiotSavartCylindrical.lean`** (~2,000 LOC). Statement of
  Proposition 12.1, derivation on $\mathbb{R}^3$ (cylindrical change of
  variables for vector-valued integrals, $\theta$-averaging).
- [ ] **`BLW/GradientBound.lean`** (~2,500 LOC). **Theorem 12.2 fully
  proven.** Steps (i)–(v) of main paper §12.3: $\nabla|\omega|^2(x^*) = 0$
  ⇒ $\partial_i\omega_3(x^*) = 0$; Hessian trace bound; vorticity-equation
  substitution; combine. ← natural landmark (analog of SQG Duhamel
  keystone).
- [ ] **`BLW/LogAbsorption.lean`** (~2,000 LOC). Steps 1–7 of §12.4 with
  explicit constants (near/far split, C3 absorption, C4 self-consistency,
  C1 ODE integration).
- [ ] **`BLW/SubTypeOneRate.lean`** (~1,500 LOC). Sub-Type-I rate
  (C5.1–C5.3); Seregin closure via axiom.

### Part IV — Torus Biot–Savart machinery (~3,000 LOC)

- [ ] **`Torus/EwaldSplitting.lean`** (~1,000 LOC). $G^{\mathrm{per}}_L
  = G_\infty + H_L$ decomposition; $H_L$ smooth.
- [ ] **`Torus/EpsteinZeta.lean`** (~1,000 LOC).
  $\sum_{n\neq 0}|n|^{-4} \approx 16.533$ bound via 3D p-series.
  Reusable from SQG `HasLatticeZetaBound` infrastructure.
- [ ] **`Torus/Correction.lean`** (~1,000 LOC). Proposition C3,
  Corollary C3.1; $|R_L| \leq C_2 M$.

### Part V — Real-analyticity refinement (~2,500 LOC)

- [ ] **`Analyticity/IdentityTheorem.lean`** (~500 LOC). Wrap mathlib's
  holomorphic-identity theorem for real-analytic functions on an interval.
- [ ] **`Analyticity/ArgmaxAccidental.lean`** (~2,000 LOC). Lemma C2.4
  (accidental multiplicity discrete), Proposition C2.6 (off a discrete
  set, all multiplicity is symmetry-induced).

### Part VI — Unconditional backbone + capstone (~2,000 LOC)

- [ ] **`Unconditional/Theorem1.lean`** (~1,000 LOC). Blowup-rate bound
  $\alpha \in (1, 2)$.
- [ ] **`Unconditional/Theorem2.lean`** (~700 LOC). Far-field control
  via Cauchy–Schwarz + energy identity.
- [ ] **`Capstone.lean`** (~300 LOC). End-to-end:
  `blw_gradient_regularity_of_NSEvolution` combining all of the above.

## Not covered

- Theorem 3 (H1 route of main paper §6) — too open-ended to axiomatize
  cleanly. H1 remains a prose statement in the paper.
- §5 self-strain dichotomy details — could be added if line budget permits
  (~2-3k LOC).
- §11 numerical verification — not Lean material.

## Expected timeline

At ~4,000 LOC/day pace (SQG benchmark), the full scope above is roughly
6 intense days:

| Day | Target |
|---|---|
| 1 | Part I foundations + start Part II C2 envelope |
| 2 | Rest of Part II + start Part III BiotSavartCylindrical |
| 3 | Part III Gradient Bound (Theorem 12.2 landmark) + LogAbsorption |
| 4 | Part III SubTypeOneRate + Part IV Torus machinery |
| 5 | Part V analyticity + Part VI unconditional backbone |
| 6 | Capstone + CI iterations + any overruns |

## Trim fallbacks (if line budget runs tight)

In order of lowest pain:

1. **Drop Part V entirely** (-2,500 LOC). Real-analyticity refinement is
   optional; Lemma C2.5 already closes C2.
2. **Axiomatize Part IV instead of proving** (-2,000 LOC). State the
   torus correction as a fourth named axiom.
3. **Drop `Unconditional/Theorem1.lean` and `Theorem2.lean`** (-1,700 LOC).
   These are classical backbone; the BLW chain is self-contained without them.
