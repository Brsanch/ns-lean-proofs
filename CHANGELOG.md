# Changelog

All notable changes to this project will be documented in this file. Releases
will be archived on Zenodo once a publishable milestone is reached.

## v0.3 — 2026-04-22 (overnight)

**Analytical discharge pass — five of six OPEN.md items closed,
one reduced to a single residual.** 65 files, ~9500 LOC, all CI-green.

**Item 5 (closed)** — 1-D 2nd-derivative test at local max
(`MaxPrincipleFromLocalMax`).  Constructor
`ScalarLocalMaxSecondDeriv.ofIsLocalMax` discharges all three
`d_i_nonpos` fields from `IsLocalMax g xStar` + slice
differentiability via `HasDerivAt.tendsto_slope` +
`strictMonoOn_of_deriv_pos`.

**Item 4 (closed)** — pointwise `(f²)'' = 2(f')² + 2 f · f''`
(`HessianExpansionFromC2`).  `HasDerivAt.pow` + second product
rule delivers the scalar identity; constructor
`HessianExpansionData.ofScalarIdentities` assembles per-component
identities into the bundle's `sum_scalar_identity` field.

**Item 3 (closed)** — FTC-for-Lipschitz
(`C1_FTC_Discharge.GrowthMomentBundle.ofLipschitzAndPointwiseBound`).
Discharged via mathlib chain `LipschitzWith` →
`LipschitzOnWith.absolutelyContinuousOnInterval` →
`AbsolutelyContinuousOnInterval.integral_deriv_eq_sub`.

**Item 2 (closed)** — §C4 "Banach fixed-point" largeness
(`C4_GrowthDominance`).  The paper's Banach framing turns out to
be structural scaffolding; the mathematical content is elementary
growth dominance (for `M ≥ M_crit(L, ν, K)`, the threshold
inequality holds via `Real.log_le_self` + linear arithmetic).

**Item 6 (closed, structural wiring)** — `NSEvolutionAxioms` →
scalar bundles (`FromNSEvolution`).  `MOfVelocityField` defines
the `L∞` envelope; `NSArgmaxInputs` packages the NS-side
analytical inputs at `(t, xStar)`;
`argmaxBundle_of_NSEvolutionAxioms` plumbs velocity-field data
through to `ArgmaxAnalyticalBundle` + gradient bound.

**Item 1 (partial)** — ODE integration §12.4 step 7→8
(`ODEIntegration_Discharge`).  Algebraic core
`integrated_bound_of_substituted_bound` + constructor
`DifferentialInequalityBundle.ofSubstitutedBound` reduce
`(T-t)·M·logM ≤ 1/4` to a single residual:

  `hW_lower_bound : ∀ t ∈ (t_start, T), 4·(T-t) ≤ 1/(M(t)·log M(t))`

derivable from `Ṁ ≤ 4 M² log M` via quotient rule on
`w = 1/(M log M)` + FTC + boundary limit + tail absorption.

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
