# Changelog

All notable changes to this project will be documented in this file. Releases
will be archived on Zenodo once a publishable milestone is reached.

## v0.2 — 2026-04-22 (late-evening)

**Full §12 BLW-chain skeleton.**  60 files, ~8200 LOC, all CI-green.

**Setup layer:** `VectorFields`, `NSHypothesis`, `ArgmaxFrame`,
`LipschitzToAE` (stub), `EnergyEnstrophy`, `ClassicalAxioms` (three
project axioms).

**Caveats layer:** `AngularIntegrals` (D.3.1 `∫ sin²θ|cos θ|dθ = 2/3` and
D.3.2 `∫ 1/r dr = log(L/δ)` proved), `C1_GrowthMoment`, `C1_FTC`,
`C2_Envelope` (Danskin), `C2_AeOde`, `C4_ImplicitBound`, `C4_Monotonicity`.

**BLW layer (~35 files) organized into:**

- **Theorem 12.2 algebraic core**: `GradientBound` (proves
  `|∇ω|²(x*) ≤ M²σ/ν` from four scalar hypotheses) + `GradientBoundSqrt`
  (12.2' form).
- **Three scalar step-bundles (i/ii/iii)**: `ArgmaxGradient`,
  `HessianAtArgmax`, `VorticityAtArgmax`, unified via `ArgmaxIdentities`.
- **Local-frame wirings**: `ArgmaxGradientFromFrame`,
  `HessianAtArgmaxFromFrame`, `VorticityAtArgmaxFromFrame`.
- **Analytical discharges (mathlib-backed)**: `ScalarProductRule`
  (`∂_i(f²) = 2f·∂_i f` via `HasDerivAt.pow`), `MaxPrinciple` (trace
  non-positive at local max), `EnvelopeIdentity` (Danskin for `|ω|²/2`),
  `HessianExpansionIdentity` (`Δ|ω|² = 2|∇ω|² + 2ω·Δω`),
  `ChainRuleMSquared` (`d/dt(M²/2) = M·Ṁ`), `AdvectionVanishes`,
  `SelfStrainNonneg`, `LogInequalities`.
- **Bundle constructors (discharges → field completion)**:
  `HessianFrameFromMaxPrinciple`, `VorticityFrameFromEnvelope`,
  `DerivFrameFromProductRule`.
- **Composition layers**: `ArgmaxStepsCompose`, `StepsFromFrameCompose`,
  `FullDischargePipeline` (end-to-end theorem
  `gradient_bound_from_full_discharge` with sanity-check `40 ≤ 400`).
- **Axiom threading**: `ClassicalAxiomDischarge`, `AnalyticalToImplicit`,
  `BootstrapDischarge` (bootstrap → C4 largeness), `ChainWiring`,
  `TorusToC4`.
- **Chain capstones**: `Capstone`, `ChainThread`, `ChainHypotheses`
  (umbrella `proposition_four_of_hypotheses`), `PropositionFour` (end-to-end
  skeleton), `ODEIntegration`, `ODEToSeregin`.
- **Support**: `LogAbsorption` (§12.4 step 5→6), `SubTypeOneRate`,
  `GrowthBoundFromStrain`, `LipschitzMScalar` (C2.1), `SanityExamples`.

**Torus/**: `EpsteinZeta`, `EpsteinZetaBounds` (p-series framework).

**Analyticity/**: `IdentityTheorem` (C2.4 codiscrete-set).

**Unconditional/**: `Theorem1` (blowup rate), `Theorem2` (far-field).

**Remaining open items (6 substantive analytical):**
1. ODE integration `Ṁ ≤ 4M²logM → (T-t)·M·logM ≤ 1/4` (§12.4 step 7→8).
2. Banach fixed-point for `ImplicitBoundBundle.hLarge` (§C4).
3. FTC-for-Lipschitz identity (mathlib one-lemma away).
4. Pointwise `Δ(f²) = 2|∇f|² + 2f·Δf` at fderiv-level.
5. 1-D 2nd-derivative test at local max.
6. Wire `NSEvolutionAxioms` → scalar bundles via `M(t) := ‖ω(t,·)‖_∞`.

## v0.1.1 — 2026-04-22

**Lemma C2.5 core content.** First mathematical content landed:
`NSBlwChain/Caveats/C2_Envelope.lean`.

Theorems:

- `danskin_envelope` — the core Danskin envelope identity. Given an
  envelope `M` of `φ(·, t)` and a point `x_star` achieving the envelope
  at `t₀`, the time-derivatives of `M` and of the slice `φ(x_star, ·)`
  at `t₀` coincide. One-page proof via the auxiliary function
  `g(t) := M t - φ(x_star, t)` having a global min at `t₀` (so `g'(t₀) = 0`).
- `danskin_envelope_consistent` — corollary: any two argmax points agree
  on the slice time-derivative at any `t₀` where `M` is differentiable.
- `deriv_sup_eq_deriv_slice_of_argmax` — re-expression as a statement
  about `deriv M t₀`.

This is the lemma that closes caveat C2 (the Lagrangian/Eulerian mismatch)
unconditionally.  The result is abstract: the only structure used is the
pointwise envelope condition and the differentiability hypotheses.  No
Sard-type measure-zero assumption is needed.

## v0.1.0 — 2026-04-22

**Initial scaffold.** Repository initialized, parallel to `sqg-lean-proofs`.

Highlights:

- Build infrastructure: `lakefile.toml`, `lean-toolchain` (`v4.29.0`),
  `.gitignore`, GitHub Actions workflows for CI (`lean_action_ci.yml`),
  dependency updates (`update.yml`), and tag releases (`create-release.yml`).
- Top-level Lean module: `NSBlwChain.lean` imports `NSBlwChain/Basic.lean`.
- `NSBlwChain/Basic.lean` — project entry point with a placeholder theorem
  to exercise the build, plus a doc-comment listing the formalization scope
  and the three named classical axioms.
- `OPEN.md` — live roadmap listing all outstanding items in order (§C1, §C2
  envelope, §C4 convex implicit bound, §D.3 angular integrals, Theorem 12.2,
  and downstream).
- `README.md` — public-facing description of the scope, axiomatic footprint,
  and build instructions.
- `CITATION.cff` — software-citation skeleton (to be populated on first release).

**Mathematical content:** none yet. Build status: expected to compile once
mathlib cache is fetched (CI will verify).
