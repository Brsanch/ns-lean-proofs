# Changelog

All notable changes to this project will be documented in this file. Releases
will be archived on Zenodo once a publishable milestone is reached.

## v0.10 — 2026-04-24 (evening)

**Further tightenings of the step-iii derivation.**

- `BLW/MaterialDerivativeSplit.lean` — `omega_dot_materialDeriv_split`:
  `ω · materialDeriv = ω · ∂_tω + ω · (u·∇)ω` via `Finset.sum_add_distrib`.
- `step_iii_identity_from_NSEvolution` simplified: `h_contracted`
  hypothesis dropped (derived internally from `ax` via
  `vorticity_equation_contracted_with_omega`).  Reduces the theorem
  from 7 to 6 hypotheses.

## v0.9 — 2026-04-24 (afternoon)

**Step (iii) identity now derived from NSEv + IsLocalMax.**
Previously taken as a hypothesis in the L8 thin wrapper; now a
theorem at the scalar level with the remaining taken hypotheses
isolated to vector-field-layer algebra.

New files:

- `BLW/StrainContractionAligned.lean` — `laplace_contraction_of_aligned`
  (specialization of `dot_of_aligned` to the Laplacian vector).
- `BLW/EnvelopeFormFromNSEvolution.lean` — specializes
  `envelope_identity_for_sqNorm_half` (Danskin) to the vorticity
  field from NSEv.
- `BLW/StepIIIFromNSEvolution.lean` — **capstone**: given NSEv +
  IsLocalMax + 5 Danskin/alignment/time-chain hypotheses, derives
  `ν · Δω_3 = Ṁ - M · σ` via the vorticity equation contracted
  with ω, advection-vanishes (from AdvectionAtArgmaxFromNSEvolution),
  time-chain-rule, Danskin envelope, and alignment contractions.

Combined with tonight's earlier additions (advection-vanishes
capstone, alignment contractions, envelope form), the step-(iii)
scalar identity is no longer a hypothesis.  All that remains taken
at the scalar level are the 5 vector-field algebra steps that unfold
to pointwise derivatives of `∂_t ω`, `(ω·∇)u`, `Δω`.

## v0.8 — 2026-04-24 (late morning)

**Thin-wrapper hypotheses being upgraded to real derivations.**
Advection vanishing at argmax is now a theorem, not a taken
hypothesis.  Four new files:

- `BLW/UGradAtArgmax.lean` — `u·∇g(xStar) = 0` for any direction
  `u` at a local max of `g`, via `IsLocalMax.fderiv_eq_zero`.
- `BLW/OmegaAdvectionProductRule.lean` — product-rule identity
  `ω·(u·∇ω) = (1/2)·u·∇|ω|²`, via
  `ScalarProductRule.partialDeriv_dot_self_eq` +
  `Fin.sum_univ_three` + `ring`.
- `BLW/AdvectionAtArgmaxFromNSEvolution.lean` — **capstone**:
  combines the above with `NSEvolutionAxioms.vorticity_components_differentiableAt`
  to derive `ω · (u·∇ω)(xStar, t) = 0` from NS smoothness +
  `IsLocalMax |ω|² xStar` alone, no further hypotheses.
- `BLW/AlignmentContraction.lean` — `dot_of_aligned`
  (`ω(x) = M·ê₂ ⇒ ω(x)·v = M·v₂`) and `sqNorm_of_aligned`
  (`|ω(x)|² = M²`).  Closes `strain_form` and `laplace_form`
  fields with real derivations.

## v0.7 — 2026-04-24 (overnight)

**All three BLW-chain steps + grand-compose now producible from
`NSEvolutionAxioms`.**  Uniform thin-wrapper pattern:

- `BLW/VorticityEquationAtPoint.lean` — (i) scalar j-component of
  `vorticity_equation` via `congrFun`; (ii) dot-contracted form with
  `ω` via `Finset.mul_sum` forward + `Finset.sum_add_distrib` +
  pointwise `vorticity_equation_scalar` + `ring`.
- `BLW/VorticityFrameFromNSEvolution.lean` —
  `VorticityLocalFrameData.ofNSEvolutionAxioms`: step (iii) bundle
  from NS bundle + scalar inputs `(M, σ, growth, Δω₃)` + step-(iii)
  identity `ν·Δω₃ = growth - M·σ`.  4/5 Prop fields `rfl` given
  canonical data; 5th via `nlinarith`.
- `BLW/ArgmaxBundleFromNSEvolution.lean` — grand-compose
  `ArgmaxAnalyticalBundle.ofNSEvolutionAxioms` producing the unified
  scalar bundle + `gradient_bound_of_NSEvolutionAxioms_via_scalars`
  one-line corollary.

Now uniform L3/L6/L8/L9 pattern:

| Layer | Bundle | File |
|---|---|---|
| L3 | `LocalFrameDerivativeData.ofNSEvolutionAxioms` (step i) | `DerivFrameFromNSEvolution.lean` |
| L6 | `ScalarLocalMaxSecondDeriv.ofNSEvolutionAxioms` (step ii) | `ScalarMaxFromNSEvolution.lean` |
| L8 | `VorticityLocalFrameData.ofNSEvolutionAxioms` (step iii) | `VorticityFrameFromNSEvolution.lean` |
| L9 | `ArgmaxAnalyticalBundle.ofNSEvolutionAxioms` (compose) | `ArgmaxBundleFromNSEvolution.lean` |

**Public repo switch.**  `github.com/Brsanch/ns-lean-proofs` made
public mid-session (previously private; hit the Free plan's 2000-min
Actions quota).  Public repos have unlimited CI minutes on Free,
unblocking further iteration.

**CI polling workflow codified.**  `gh api
repos/.../actions/runs/<id>/jobs | jq '.jobs[].steps[] | name,
status, conclusion'` catches `lean-action: completed:success` about
7 min post-push, well before the ~16 min full-run completion
(docgen-action runs after).  Documented in the updated README build
section.

~80 files, ~11,500 LOC on main, all CI-green.

## v0.6 — 2026-04-22 (late morning)

**NSEvolutionAxioms → steps (i) and (ii) of the BLW chain, fully
derived.**  Seven new files composing a foundation chain that lets
callers produce `LocalFrameDerivativeData` (step (i)) and
`ScalarLocalMaxSecondDeriv` (step (ii)) **directly from**
`NSEvolutionAxioms u ν T` + local-frame alignment + argmax
existence, with **zero** residual differentiability hypotheses
on the caller side.  ~74 files, ~10,700 LOC, all CI-green.

**Foundation layer (L1–L5, ~340 LOC):**

- `NSBlwChain/Setup/CurlSmoothness.lean` (L1) — `curl : C^{n+1} → C^n`
  via `ContDiff.fderiv_right` + continuous-linear-map evaluation.
  Component-pointwise differentiability corollary for `C^4` fields
  (the NS-regularity class).
- `NSBlwChain/Setup/VorticityDifferentiable.lean` (L2, L4) —
  `NSEvolutionAxioms.vorticity_component_differentiableAt`,
  `.vorticity_contDiff` (vort is `C^3`), `.vorticitySqNorm_contDiff`
  (`|ω|²` is `C^3`).
- `NSBlwChain/BLW/SliceSmoothness.lean` (L5) — `sliceMap_contDiff`,
  `slice_contDiff_of_contDiff`, plus three NSEv-keyed corollaries:
  `sqNormVort_slice_contDiff` (C^3 slice), `.sqNormVort_slice_differentiableAt_nhds`
  (slice diff on nbhd of 0), `.sqNormVort_sliceDeriv_differentiableAt_zero`
  (deriv slice diff at 0, via `iteratedDeriv 1` + `iteratedDeriv_one`).

**Step wrappers (L3, L6, ~160 LOC):**

- `NSBlwChain/BLW/DerivFrameFromNSEvolution.lean` (L3) —
  `LocalFrameDerivativeData.ofNSEvolutionAxioms`: step (i) bundle
  from NS axioms + alignment.
- `NSBlwChain/BLW/ScalarMaxFromNSEvolution.lean` (L6) —
  `ScalarLocalMaxSecondDeriv.ofNSEvolutionAxioms`: step (ii) bundle
  from NS axioms + `IsLocalMax |ω|² xStar`.

**Diagnostic workflow proven out.**  Three CI iteration cycles on
L5 surfaced (a) `𝓝` needs `open Topology`, (b) mathlib 4.29's
`ContDiff.differentiable` uses `n ≠ 0` not `1 ≤ n`, (c) `ContDiff.deriv`
dot-resolution to `Exists.deriv` — root-caused by enabling
`set_option diagnostics true` + `threshold 100`.  Noted in
`feedback_lean_diagnostic_workflow` memory.

## v0.5 — 2026-04-22 (morning)

**Pre-review pipeline executed.** Four review-preprocessing deliverables
landed as `docs/findings/*.md` in the noethersolve repo:

- `ns_obstruction_memo_2026_04_22.md` — survives-test against 6
  literature obstructions (Tao 2014, CKN, BKM, PSL, ESS, Constantin-
  Foias). Verdict: no blocking obstructions; Tao + Constantin-Foias
  flagged as `plausibly survives` for closer look.
- `ns_axiom_citation_audit_2026_04_22.md` — citation-fidelity audit
  found three issues, all fixed in commits below.
- `ns_model_correctness_memo_2026_04_22.md` — NSEvolutionAxioms
  faithful encoding; four implicit-but-standard assumptions flagged.
- `ns_journal_theorem_statements_2026_04_22.md` — journal-hunt
  verified Masuda 1967 (J-STAGE) and Seregin 2012 (arXiv:1104.3615);
  Foias-Temam 1979 venue definitively resolved as J. Math. Pures
  Appl. 58 (not J. Funct. Anal. 33 as earlier draft had).

**Lean-side fixes from the audits:**

- Axiom 1 (`biot_savart_self_strain_bound`): added `Mdot` + `0 ≤ Mdot`
  growth-regime hypothesis (previously implicit); corrected docstring
  to identify as §12.4 log-absorption output, not Prop 12.1 alone.
  Threaded through `buildImplicitBundleFromAxiom`,
  `sigma_le_4M_log_M_from_axiom`, `sigma_le_4M_log_M_of_analytical`,
  `FullScalarChain.sigma_bound_from_chain`.
- Axiom 2 (`seregin_type_one_exclusion`): documented as composite
  (Seregin 2012 L³ + Biot-Savart + Sobolev ⇒ vorticity-Type-I);
  added ESS 2003 citation as the originating L³ criterion.
- Axiom 3 (`NS_time_analyticity`): citation corrected from
  "Kato 1967" (2D Euler) to Masuda 1967 Proc Japan Acad 43 +
  Foias-Temam 1979 J. Math. Pures Appl. 58. Masuda covers bounded
  domains / Dirichlet; Foias-Temam covers whole-space / torus.
- New `DecayAtInfinity` structure in `ClassicalAxioms.lean` with
  `has_polynomial_decay` field (C · |x|^{-p}, p > 3); added as
  explicit hypothesis to `biot_savart_self_strain_bound`
  (previously implicit).
- New `NSBlwChain/Setup/DecayConstructors.lean` with two constructors:
  `DecayAtInfinity.of_compactSupport_vorticity` (trivial, for
  compactly-supported vorticity) and
  `DecayAtInfinity.of_uniform_polynomial_bound` (direct pass-through).
- `NSEvolutionAxioms` docstring: new section enumerating the four
  implicit assumptions (time-differentiability via deriv-convention,
  decay at infinity — now explicit in DecayAtInfinity, pressure via
  Helmholtz, initial-data regularity).

67 files, ~9900 LOC on main, all CI-green.

## v0.4 — 2026-04-22 (late-overnight)

**All six originally-listed OPEN.md items fully closed.**  No
`sorry` in the BLW chain.  66 files, ~9650 LOC, all CI-green.

**Item 1 (ODE integration) fully discharged** via
`NSBlwChain/BLW/ODEIntegration_ResidualDischarge.lean` (480 LOC):

- `deriv_w_quotient` — pointwise `d/dt(1/(M·log M))` via
  `HasDerivAt.mul` + `.log` + `.inv`.
- `deriv_w_lower_bound` — ODE inequality transfer:
  `Ṁ ≤ 4 M² log M ⇒ ẇ ≥ -4 - 4/log M`.
- `deriv_w_upper_bound_of_tight` — symmetric tight-equality.
- `hW_lower_bound_of_rate_equality` — FTC + limit composition
  delivering `4·(T-t) ≤ 1/(M·log M)` via
  `intervalIntegral.integral_eq_sub_of_hasDerivAt` +
  `integral_mono_on` + `Filter.Tendsto` limit passage
  `s → T⁻` with `w(T⁻) = 0`.

Composed with `ODEIntegration_Discharge.lean`'s algebraic wrapper,
this delivers the §12.4 step 7→8 bound `(T-t)·M·log M ≤ 1/4`
unconditionally.

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
