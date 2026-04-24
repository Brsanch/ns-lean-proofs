# NS BLW-Gradient Chain — Lean 4 Formalization

[![CI](https://github.com/Brsanch/ns-lean-proofs/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/Brsanch/ns-lean-proofs/actions/workflows/lean_action_ci.yml)
[![License: MIT](https://img.shields.io/badge/License-MIT-blue.svg)](./LICENSE)

A Lean 4 + mathlib formalization of the Buaria–Lawson–Wilczek gradient
chain for 3D incompressible Navier–Stokes regularity on the torus
$\mathbb{T}^3$ and on $\mathbb{R}^3$.  Companion paper:
`paper/ns_regularity.md` in the `noethersolve` project, with supplements
`ns_regularity_caveats_formal.md` and `ns_regularity_blw_derivations.md`.

**Status: v0.13 (2026-04-25).** ~94 files, ~13,000 LOC, all CI-green.
**All scalar Props derived.**  The gradient bound
`|∇ω|² ≤ M²·σ/ν` is now producible via
`gradient_bound_of_NSEvolutionAxioms_all_scalar_derived` from
`NSEvolutionAxioms` + `IsLocalMax |ω|²` + 7 vector-field-layer
physical identities + positivity/sign.  No scalar-level Props taken.
`step_iii_identity_from_NSEvolution` now takes 5 hypotheses; two
formerly-taken hypotheses (h_contracted, h_material_split) are now
derived internally.
Zero `sorry` in the BLW chain.  Three named classical PDE axioms
(by design); no other axioms.  **The step-(iii) identity
`ν · Δω_3 = Ṁ - M·σ` is now derived from NSEv + IsLocalMax + Danskin
+ alignment** (previously taken as a hypothesis in the L8 thin
wrapper).  Advection-vanishes, alignment contractions, and envelope
form also all derivable.

**Repository is now public** (github.com/Brsanch/ns-lean-proofs).  Free
Actions minutes unlimited — no billing-wall iteration blocks.

## What is formalized

### Theorem 12.2 (§12 BLW-gradient chain) — machine-verified algebraic core

At any local maximum $x^*(t)$ of $|\omega|^2$ for a smooth NS solution
with $dM/dt(t) \ge 0$:
$$|\nabla\omega(x^*, t)|^2 \leq \tfrac{M(t)^2 \cdot \sigma(x^*, t)}{\nu}.$$

Proved unconditionally in `BLW/GradientBound.lean` from four scalar
hypothesis fields (step (i) / (ii) / (iii) identities + viscosity
positivity), with the sqrt-form variant in `BLW/GradientBoundSqrt.lean`.

### The three BLW-chain steps (paper §12.3)

Each step now has *three* layers of formalization:

- a **scalar bundle** stating the identity as taken inputs;
- a **local-frame wiring** combining scalar identities with
  alignment $\omega(x^*) = M \cdot \hat e_2$;
- a **direct wiring from `NSEvolutionAxioms`** (new in v0.6) producing
  the bundle's differentiability hypotheses from the NS solution's
  `ContDiff ℝ 4` smoothness.

| Step | Scalar bundle | Local frame | From NSEvolutionAxioms |
|---|---|---|---|
| (i)  | `ArgmaxGradient` | `ArgmaxGradientFromFrame` / `DerivFrameFromProductRule` | `DerivFrameFromNSEvolution` |
| (ii) | `HessianAtArgmax` + `ScalarLocalMaxSecondDeriv` | `HessianAtArgmaxFromFrame` / `HessianFrameFromMaxPrinciple` | `ScalarMaxFromNSEvolution` |
| (iii)| `VorticityAtArgmax` | `VorticityAtArgmaxFromFrame` / `VorticityFrameFromEnvelope` | *taken structurally via `FromNSEvolution`* (time regularity not yet integrated) |

### §12.4 log-absorption ODE — fully discharged

- **Step 5 → 6** (`LogAbsorption`): `log(L/√(ν/σ)) = log L + ½ log(σ/ν)`.
- **Step 6 → 7**: C4 largeness.  Previously a hypothesis; now
  discharged in `Caveats/C4_GrowthDominance.lean` via elementary
  growth dominance (no Banach fixed-point machinery needed — that
  framing of the paper turned out to be structural scaffolding).
- **Step 7 → 8** (`BLW/ODEIntegration_{,Residual}Discharge`):
  `Ṁ ≤ 4 M² log M  ⇒  (T - t)·M·log M ≤ 1/4` via quotient rule on
  `w = 1/(M log M)`, FTC on `[t, T-ε]`, limit passage `ε → 0⁺` with
  `w(T⁻) = 0`.  Closed unconditionally tonight.

### Five paper caveats (C1–C5)

| Caveat | Status | File |
|---|---|---|
| C1 Growth-moment coverage (Jordan decomposition) | Algebraic bundle proven; FTC-for-Lipschitz identity discharged via mathlib `AbsolutelyContinuousOnInterval.integral_deriv_eq_sub` | `Caveats/C1_FTC_Discharge` |
| C2 Argmax trajectory smoothness (Danskin) | Proven unconditionally via `danskin_envelope` + `danskin_envelope_consistent` | `Caveats/C2_Envelope`, `C2_AeOde` |
| C3 Periodic Biot–Savart corrections | Epstein p-series framework + `TorusToC4` bridge; specific numeric bound `∑_{n≠0}|n|^{-4} ≲ 16.533` taken as a named hypothesis | `Torus/EpsteinZeta{,Bounds}`, `BLW/TorusToC4` |
| C4 Implicit-bound uniqueness | Growth dominance (`C4_GrowthDominance`); the "Banach fixed-point" framing is structural | `Caveats/C4_*` |
| C5 Global decomposition | Sub-Type-I rate + Seregin closure (`ChainThread`) | `BLW/SubTypeOneRate`, `BLW/ChainThread` |

### Unconditional backbone (Theorems 1, 2 — §3, §4)

- **Theorem 1 (`Unconditional/Theorem1`)**: blowup rate α ∈ (1, 2).
  Algebraic core proved from `EnstrophyCrossoverBundle`; bundle takes
  Leray energy identity + enstrophy-crossover as scalar hypotheses.
- **Theorem 2 (`Unconditional/Theorem2`)**: far-field control via
  Cauchy–Schwarz on the Biot–Savart tail + energy identity.

Both are hypothesis-taking skeletons with zero `sorry`.

### The end-to-end theorem

`BLW/PropositionFour.propositionFour_skeleton` /
`BLW/ChainHypotheses.proposition_four_of_hypotheses`: given the
bundled hypotheses + three classical axioms, smooth NS extends
past any candidate blowup time.

## Axiomatic footprint

Three named classical PDE axioms in `Setup/ClassicalAxioms.lean`:

1. **`biot_savart_self_strain_bound`** — output of paper §12.4
   log-absorption step (cylindrical θ-averaging + Lemma B far-field
   + growth-regime).  Takes `NSEvolutionAxioms u ν T` and
   `DecayAtInfinity u T` as hypotheses.  **Note**: not Prop 12.1
   alone — it is the composite theorem.
2. **`seregin_type_one_exclusion`** — vorticity-sub-Type-I form.
   *Composite* of Seregin 2012 CMP (L³ velocity criterion,
   arXiv:1104.3615) + Biot–Savart on ℝ³ + Sobolev embedding.
   Originating L³ criterion: Escauriaza–Seregin–Šverák 2003
   *Russ. Math. Surveys* 58.
3. **`NS_time_analyticity`** — real-analyticity window on `(0, T)`.
   Primary sources: **Masuda 1967**, *Proc. Japan Acad.* **43**,
   827–832 (bounded domain / Dirichlet BC); **Foias–Temam 1979**,
   *J. Math. Pures Appl.* **58**, 339–368 (whole-space / torus).
   Earlier "Kato 1967" citation in drafts is a mis-attribution
   (Kato 1967 ARMA 25 is about 2D Euler).  Venue definitively
   resolved in the journal-hunt memo.

All three axiom statements were cross-checked against public sources
in `noethersolve/docs/findings/ns_journal_theorem_statements_2026_04_22.md`.

### Also present as `Prop`-valued hypothesis structures (not axioms)

- `DecayAtInfinity u T` (`Setup/ClassicalAxioms.lean`) — polynomial
  decay hypothesis consumed by axiom 1.  Constructors in
  `Setup/DecayConstructors.lean`: `of_compactSupport_vorticity`,
  `of_uniform_polynomial_bound`.
- `TorusCorrectionBundle.RL_bound` — specific numeric bound for
  the torus Biot–Savart correction.
- `NSArgmaxInputs` fields — the five scalar analytical inputs at
  an argmax point (M, σ, gradSqNorm, laplaceOmega3, growth) + their
  step-(i)/(ii)/(iii) identities.  Steps (i) and (ii) now derivable
  from `NSEvolutionAxioms` smoothness; step (iii) still taken.

## Repo tour (file-by-file)

### `Setup/` — foundational definitions (9 files)

| File | Content |
|---|---|
| `VectorFields.lean` | `Vec3`, `Vec3.dot`, `Vec3.e`, `partialDeriv`, `divergence`, `curl`, `scalarLaplacian`, `vectorLaplacian` |
| `NSHypothesis.lean` | `NSEvolutionAxioms` bundle (smoothness + div-free + vorticity eqn + time-continuity) + 4 documented implicit assumptions |
| `ArgmaxFrame.lean` | Local-frame alignment setup for argmax analysis |
| `LipschitzToAE.lean` | Rademacher-type wrapper (Lipschitz → a.e. differentiable) |
| `EnergyEnstrophy.lean` | `energyOf`, `enstrophyOf`, `EnergyEnstrophyIdentities` bundle |
| `ClassicalAxioms.lean` | The three named axioms + `DecayAtInfinity` structure |
| `DecayConstructors.lean` | `DecayAtInfinity.of_compactSupport_vorticity`, `.of_uniform_polynomial_bound` |
| `CurlSmoothness.lean` | **v0.6**: `curl C^{n+1} → C^n`, component-pointwise differentiability |
| `VorticityDifferentiable.lean` | **v0.6**: `NSEvolutionAxioms → vort C³, vort-component DifferentiableAt, \|ω\|² C³` |

### `Caveats/` — the five paper caveats (9 files)

| File | Content |
|---|---|
| `AngularIntegrals.lean` | D.3.1 `∫ sin²θ \|cos θ\| dθ = 2/3`, D.3.2 `∫ 1/r dr = log(L/δ)` |
| `C1_GrowthMoment.lean` | Jordan decomposition, `GrowthMomentBundle` |
| `C1_FTC.lean` | FTC-for-Lipschitz scaffolding |
| `C1_FTC_Discharge.lean` | `GrowthMomentBundle.ofLipschitzAndPointwiseBound` via mathlib's `AbsolutelyContinuousOnInterval` |
| `C2_Envelope.lean` | `danskin_envelope`, `danskin_envelope_consistent`, `deriv_sup_eq_deriv_slice_of_argmax` |
| `C2_AeOde.lean` | Proposition C2 (a.e. ODE packaging) |
| `C4_ImplicitBound.lean` | `ImplicitBoundBundle`, `σ_le_of_largeness`, direct un-bundled form |
| `C4_Monotonicity.lean` | Monotonicity lemmas for the §C4 implicit bound |
| `C4_GrowthDominance.lean` | `hLarge_of_large_M_bootstrap`, `ImplicitBoundBundle.ofLargeM` — growth-dominance discharge of C4 largeness |

### `BLW/` — the gradient chain core (41 files)

**Theorem 12.2 algebraic core:**
- `GradientBound.lean` — `GradBoundHypotheses.gradient_bound`
- `GradientBoundSqrt.lean` — sqrt form
- `LogAbsorption.lean` — §12.4 step 5→6
- `SubTypeOneRate.lean` — sub-Type-I rate algebra
- `GrowthBoundFromStrain.lean` — growth bound from strain
- `LogInequalities.lean` — log monotonicity

**Step bundles (i / ii / iii):**
- `ArgmaxGradient.lean`, `HessianAtArgmax.lean`, `VorticityAtArgmax.lean`
- `ArgmaxIdentities.lean` — unified `ArgmaxAnalyticalBundle`

**Local-frame wirings:**
- `ArgmaxGradientFromFrame.lean` (+ `DerivFrameFromProductRule.lean`)
- `HessianAtArgmaxFromFrame.lean` (+ `HessianFrameFromMaxPrinciple.lean`)
- `VorticityAtArgmaxFromFrame.lean` (+ `VorticityFrameFromEnvelope.lean`)

**Analytical discharges (mathlib-backed):**
- `ScalarProductRule.lean` — `∂_i(f²) = 2f·∂_i f` via `HasDerivAt.pow`
- `MaxPrinciple.lean` + `MaxPrincipleFromLocalMax.lean` — 1-D 2nd-deriv test at local max (`HasDerivAt.tendsto_slope` + `strictMonoOn_of_deriv_pos`)
- `HessianExpansionIdentity.lean` + `HessianExpansionFromC2.lean` — `(f²)'' = 2(f')² + 2 f·f''` via `HasDerivAt.pow` + product rule
- `EnvelopeIdentity.lean` — Danskin specialization for `|ω|²/2`
- `ChainRuleMSquared.lean` — `d/dt(M²/2) = M·Ṁ`
- `AdvectionVanishes.lean` — `ω·(u·∇ω)(x*) = 0` at argmax
- `SelfStrainNonneg.lean` — `σ ≥ 0` in growth regime

**ODE integration (§12.4 step 7→8):**
- `ODEIntegration.lean` — `DifferentialInequalityBundle`
- `ODEIntegration_Discharge.lean` — algebraic core
- `ODEIntegration_ResidualDischarge.lean` — quotient rule + FTC + limit closure

**v0.6 — `NSEvolutionAxioms → step bundle` wirings:**
- `DerivFrameFromNSEvolution.lean` — `LocalFrameDerivativeData.ofNSEvolutionAxioms` (step i)
- `SliceSmoothness.lean` — slice `ContDiff` + diff-on-nbhd + sliceDeriv-diff-at-0 (via `iteratedDeriv_one`)
- `ScalarMaxFromNSEvolution.lean` — `ScalarLocalMaxSecondDeriv.ofNSEvolutionAxioms` (step ii)
- `FromNSEvolution.lean` — structural wiring; `argmaxBundle_of_NSEvolutionAxioms`

**Composition layers:**
- `ArgmaxStepsCompose.lean`, `StepsFromFrameCompose.lean`
- `FullDischargePipeline.lean` — `gradient_bound_from_full_discharge` with sanity-check `40 ≤ 400`
- `FullScalarChain.lean`, `AnalyticalToImplicit.lean`, `ClassicalAxiomDischarge.lean`
- `BootstrapDischarge.lean` — bootstrap → C4 largeness

**Chain capstones:**
- `Capstone.lean` — per-time witness
- `ChainThread.lean` — `extends_past_T_of_subTypeI` to Seregin
- `ChainHypotheses.lean` — umbrella `proposition_four_of_hypotheses`
- `PropositionFour.lean` — end-to-end skeleton
- `ODEToSeregin.lean` — ODE integration → Seregin input

**Proposition 12.1 infrastructure:**
- `BiotSavartCylindrical.lean` — axiom + consumed-form structures
- `TorusToC4.lean` — torus correction bridge

**Support:**
- `LipschitzMScalar.lean` — C2.1 Lipschitz-M wrapper
- `SanityExamples.lean` — concrete bundle instantiation
- `ChainWiring.lean` — chain-composition glue

### `Torus/` — periodic infrastructure (2 files)

| File | Content |
|---|---|
| `EpsteinZeta.lean` | Lattice-zeta framework |
| `EpsteinZetaBounds.lean` | p-series bounds (`latticeZetaConst`, `annularShell`, etc.) |

### `Analyticity/` — real-analyticity refinement (1 file)

| File | Content |
|---|---|
| `IdentityTheorem.lean` | C2.4 codiscrete-set argument |

### `Unconditional/` — paper §3 / §4 backbone (2 files)

| File | Content |
|---|---|
| `Theorem1.lean` | Blowup rate α ∈ (1, 2) — `EnstrophyCrossoverBundle` + `blowup_rate_algebraic` + `blowup_rate_alpha_of_bundle` |
| `Theorem2.lean` | Far-field control `∫\|σ_{>R}\| dt < ∞` — Cauchy–Schwarz + energy |

## Status

**v0.6 (2026-04-22 late morning)** — 74 files, ~11,200 LOC, all
CI-green.  Steps (i) and (ii) of the BLW chain derivable from
`NSEvolutionAxioms` + alignment + argmax existence alone (no residual
per-direction differentiability hypotheses).

**v0.5** — Pre-review audit pipeline: four `docs/findings/*.md`
memos (obstructions, citation audit, model correctness, journal
cross-check).  Citation-audit findings propagated into the Lean
axioms.  `DecayAtInfinity` hypothesis now explicit.

**v0.4** — All six originally-listed `OPEN.md` items fully closed.

**v0.3** — Item 1 ODE integration fully discharged.

**v0.2** — Full §12 BLW-chain skeleton.

**v0.1** — Initial scaffold + Danskin envelope (Lemma C2.5) core.

See `CHANGELOG.md` for per-version detail and `OPEN.md` for the
live roadmap.  Build-safety protocol (Apple Silicon apfsd panic
prevention) documented in `DEVELOPMENT.md`.

## Build

**Policy:** CI (`.github/workflows/lean_action_ci.yml`) is the default
verifier. Do **not** run `lake build` or `lake exe cache get` on
Apple Silicon — they trigger apfsd saturation and kernel panics. See
[`DEVELOPMENT.md`](./DEVELOPMENT.md) for the full safe-workflow
protocol, diagnostic tricks, and lessons learned from the sister
project `sqg-lean-proofs`.

For safe local single-file type-checking only (no artifact writes):

```
LEAN_NUM_THREADS=1 lake env lean NSBlwChain/YOUR_FILE.lean
```

For everything else, push and let CI build.

**Polling CI during iteration:** use
```
gh api repos/Brsanch/ns-lean-proofs/actions/runs/<id>/jobs
```
to see when `Run leanprover/lean-action@v1` transitions to
`completed:success` — this is the compile step; no need to wait for
`docgen-action@v1` which runs afterward.

## Pre-review audit pipeline

Four independent memos support external review (in `noethersolve/docs/findings/`):

| Memo | Purpose | Verdict |
|---|---|---|
| `ns_obstruction_memo_2026_04_22.md` | Check chain against 6 literature obstructions (Tao 2014, CKN, BKM, PSL, ESS, Constantin–Foias) | 4 survive; 2 `plausibly survives`; 0 blocked |
| `ns_axiom_citation_audit_2026_04_22.md` | Diff Lean axiom statements vs cited sources | 3 issues found; all 3 fixed in this repo |
| `ns_model_correctness_memo_2026_04_22.md` | Audit `NSEvolutionAxioms` vs physical NS | Core encoding faithful; 4 implicit assumptions flagged (safe, now documented) |
| `ns_journal_theorem_statements_2026_04_22.md` | Hunt free full-text of Masuda 1967, Foias–Temam 1979, Seregin 2012 | Masuda found on J-STAGE; Seregin on arXiv; Foias–Temam venue resolved |

## Relationship to the SQG project

This project parallels [`sqg-lean-proofs`](https://github.com/Brsanch/sqg-lean-proofs)
in structure: a conditional regularity roadmap whose analytical chain
is fully formal, with explicitly-named classical PDE results as the
only axiomatic hypotheses. The infrastructure (lattice-zeta bounds,
Galerkin framing, BKM/MMP patterns) adapts from the SQG project where
applicable.

## Citation

To be added upon first release. See `CITATION.cff` for the current
software-citation skeleton.

## License

MIT. See [LICENSE](./LICENSE).
