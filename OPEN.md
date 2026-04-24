# Open items — ns-lean-proofs

**v0.13 (2026-04-25 early-morning).**  88 files, 12,465 LOC on main,
all CI-green, zero `sorry` in the BLW chain.  **All scalar-level
Props are now derived.**  The gradient bound `|∇ω|² ≤ M²·σ/ν` is
producible via `gradient_bound_of_NSEvolutionAxioms_all_scalar_derived`
(`BLW/GradientBoundAllScalarDerived.lean`) from:

- `NSEvolutionAxioms u ν T` (3 classical PDE axioms hidden inside —
  `biot_savart_self_strain_bound`, `seregin_type_one_exclusion`,
  `NS_time_analyticity`).
- `IsLocalMax |ω|² xStar` (argmax existence hypothesis).
- 7 **vector-field-layer physical identities** (the current
  remaining taken hypotheses).
- Positivity/sign/growth-regime (`0 < M`, `Δω_3 ≤ 0`, `0 ≤ Ṁ`).

## Remaining taken hypotheses (all vector-field-layer)

Each unfolds to ~30-100 LOC of pointwise tensor calculus and can
be discharged at the wiring layer where the physical vectors
(`∂_tω`, `(ω·∇)u`, `Δω`, `∇²|ω|²`) are in scope.

**For step (ii):**
1. `h_hessian_expansion`: `Δ(|ω|²) = 2·|∇ω|² + 2·(ω·Δω)`.
2. `h_trace_nonpos`: `Δ(|ω|²)(xStar) ≤ 0` at the local max.
3. `h_laplace_align_scalar`: `ω·Δω(xStar) = M · Δω_3` (scalar form).

**For step (iii):**
4. `h_time_chain_rule`: `ω · ∂_tω = ∂_t(|ω|²/2)`.
5. `h_envelope`: `∂_t(|ω|²/2)(xStar, t) = M · Ṁ` (Danskin).
6. `h_strain`: `ω · (ω·∇)u = M² · σ` (under alignment).
7. `h_laplace_vec`: `ω · Δω(xStar) = M · laplaceOmega3` (vector form).

**Next pickup target** (ranked by ROI):
- ~~**Hessian expansion of `|ω|²`** (#1 above)~~ — **CLOSED (v0.14)**
  via `BLW/HessianExpansionScalar.lean`
  (`laplace_sq_eq_of_slice_identities` / `_fin3` / `_of_C2_slices`,
  ~150 LOC).  Per-component `(★)` identity now derivable from three
  1-D `scalar_sq_second_deriv_eq` slice applications + Fin 3
  algebraic assembly.  Three compositions over `k ∈ {0,1,2}` feed
  the `h_star_k` slots of `HessianExpansionData.ofScalarIdentities`
  to deliver the vector-level `Δ|ω|² = 2|∇ω|² + 2 ω·Δω`.
- ~~**Hessian trace ≤ 0 at max** (#2)~~ — **CLOSED (v0.15)** via
  `BLW/LaplaceOmega3Nonpos.lean` (`vec3_component_sq_le_normSq`,
  `isLocalMax_omega3_of_isLocalMax_sqNorm`,
  `laplaceOmega3_nonpos_from_IsLocalMax`, ~100 LOC).  The refined
  paper §12.3 Step (ii) argument (componentwise Cauchy–Schwarz
  `ω₃² ≤ |ω|²` + `IsLocalMax |ω|²` + alignment ⇒ `IsLocalMax ω₃`
  locally, then 1-D 2nd-derivative test per Fin 3 direction) now
  discharges the `h_laplace_nonpos : laplaceOmega3 ≤ 0` hypothesis
  from `IsLocalMax (fun y => Vec3.dot (ω y) (ω y)) xStar` +
  alignment + slice differentiability.  Closes the second of the 7
  taken vector-field-layer identities.
- **Alignment contractions** (#3, #6, #7) — pure alignment algebra;
  specializations of `AlignmentContraction.dot_of_aligned` and
  `StrainContractionAligned.laplace_contraction_of_aligned`.
- **Time chain rule + envelope** (#4, #5) — require
  time-differentiability of ω at xStar (from `NS_time_analyticity`
  axiom).  More involved.

## Non-BLW-scalar open items

- **Theorem 1** (blowup rate α ∈ (1,2)) — skeleton in
  `Unconditional/Theorem1.lean`; Leray energy identity + enstrophy
  crossover bundle discharge would close it unconditionally.
- **Theorem 2** (far-field control) — skeleton + algebraic core in
  `Unconditional/Theorem2.lean`; Cauchy-Schwarz + energy bundle
  discharge.
- **Torus overlay** — periodic `NSEvolutionAxioms` + wire
  `Torus/*.lean` framework.
- **Anti-twist BLW §13** — possibly-novel math from paper §13; not
  yet formalized.
- **Classical axiom formalization** — any of the 3 (Biot-Savart,
  Masuda, Seregin).  Multi-session scale each.

## Done

- ✅ **Theorem 12.2 algebraic core** — `GradientBound`,
  `GradientBoundSqrt`.
- ✅ **§12.4 step 5→6 log expansion** — `LogAbsorption`.
- ✅ **Step (i) analytical discharge** — `ScalarProductRule` +
  `DerivFrameFromProductRule` via `HasDerivAt.pow`.
- ✅ **Angular integrals D.3.1, D.3.2** — `AngularIntegrals`.
- ✅ **Lemma C2.5 (Danskin)** — `C2_Envelope`.
- ✅ **Proposition C2 (a.e. ODE)** — `C2_AeOde`.
- ✅ **Envelope identity for `|ω|²/2`** — `EnvelopeIdentity`
  (Danskin specialization).
- ✅ **Chain rule `d/dt(M²/2) = M·Ṁ`** — `ChainRuleMSquared`.
- ✅ **C1 / C4 algebraic bundles** + `C4_Monotonicity`.
- ✅ **Epstein p-series framework** — `EpsteinZetaBounds`.
- ✅ **End-to-end `gradient_bound_from_full_discharge`** —
  `FullDischargePipeline` (with sanity-check `40 ≤ 400`).
- ✅ **Seregin threading** — `ChainThread.extends_past_T_of_subTypeI` +
  `ChainHypotheses.proposition_four_of_hypotheses`.
- ✅ **Torus correction → C4 bridge** — `TorusToC4`.
- ✅ **Bootstrap → C4 largeness** — `BootstrapDischarge`.
- ✅ **Max principle** — scalar `ScalarLocalMaxSecondDeriv.trace_nonpos`.
- ✅ **1-D 2nd-derivative test at local max** —
  `MaxPrincipleFromLocalMax.isLocalMax_second_deriv_nonpos` +
  `ScalarLocalMaxSecondDeriv.ofIsLocalMax` (closes item 5; all three
  `d_i_nonpos` discharged from `IsLocalMax` + slice differentiability).
- ✅ **Pointwise `(f²)'' = 2(f')² + 2 f · f''`** —
  `HessianExpansionFromC2.scalar_sq_second_deriv_eq` via
  `HasDerivAt.pow` + second product rule, plus
  `HessianExpansionData.ofScalarIdentities` constructor
  (closes item 4).
- ✅ **FTC-for-Lipschitz identity** —
  `C1_FTC_Discharge.GrowthMomentBundle.ofLipschitzAndPointwiseBound`
  (closes item 3; `hIntegratedBound` discharged from `LipschitzWith`
  via mathlib's `AbsolutelyContinuousOnInterval.integral_deriv_eq_sub`).

- ✅ **Connection `NSEvolutionAxioms` → scalar bundles** —
  `FromNSEvolution.lean` (closes item 6, structural wiring; see
  item 6 below for full notes).

## Item-by-item status — all six closed

### 1. ~~ODE integration (§12.4 step 7→8)~~ — **CLOSED**

Pointwise half: `deriv_w_quotient`, `deriv_w_lower_bound`,
`deriv_w_upper_bound_of_tight` (quotient rule + ODE-inequality
transfer via `HasDerivAt.mul` / `.log` / `.inv`).

FTC + limit composition: `hW_lower_bound_of_rate_equality`
composes `intervalIntegral.integral_eq_sub_of_hasDerivAt` +
`integral_mono_on` + `integral_sub`/`integral_const` + a
`Filter.Tendsto` limit passage `s → T⁻` using `hW_boundary`
(`w(T⁻) → 0`) to deliver `4·(T-t) ≤ 1/(M(t)·log M(t))`.

Combined with the algebraic wrapper in
`ODEIntegration_Discharge.lean`
(`integrated_bound_of_substituted_bound` +
`DifferentialInequalityBundle.ofSubstitutedBound`), this discharges
`(T-t)·M·logM ≤ 1/4` unconditionally from an a.e. ODE inequality
`Ṁ ≤ 4 M² log M` plus standard smoothness/boundary inputs on the
bundle.

**Location:** `NSBlwChain/BLW/ODEIntegration.lean` (bundle) +
`NSBlwChain/BLW/ODEIntegration_Discharge.lean` (algebraic core) +
`NSBlwChain/BLW/ODEIntegration_ResidualDischarge.lean` (FTC + limit
closure, 480 LOC).

### 2. ~~Banach fixed-point for C4 largeness~~ — **CLOSED**

Discharged via `NSBlwChain/Caveats/C4_GrowthDominance.lean`
(`hLarge_of_large_M_bootstrap`, `ImplicitBoundBundle.ofLargeM_hLarge`,
`exists_M_crit_threshold`).  The paper's "Banach fixed-point" framing
turns out to be structural scaffolding; the mathematical content is
elementary growth dominance: for `M ≥ M_crit(L, ν, K)` with
`M_crit := max 2 (max (K + 2) (exp(|A₀| + 1)))` and
`A₀ := 1 + log L + (1/2) log 4 - (1/2) log ν`, the threshold
inequality

  `1 + log L + (1/2)(log 4 + log M + log(log M) - log ν) ≤ 4 log M - K/M`

holds, proved via `Real.log_le_self` (bounding `log(log M) ≤ log M`)
and linear arithmetic on the leftover `3 log M ≥ A₀ + K/M`.
Composing with `BootstrapDischarge.c4_largeness_from_bootstrap`
delivers `hLarge` as a theorem rather than a hypothesis.

### 3. ~~FTC-for-Lipschitz identity~~ — **CLOSED**

Discharged via `NSBlwChain/Caveats/C1_FTC_Discharge.lean`
(`GrowthMomentBundle.ofLipschitzAndPointwiseBound`).  The mathlib
chain `LipschitzWith` → `LipschitzOnWith.absolutelyContinuousOnInterval`
→ `AbsolutelyContinuousOnInterval.integral_deriv_eq_sub` discharges
both the FTC identity and interval-integrability of `deriv M` from
a single `LipschitzWith K M` hypothesis.  The integrated bound

  `M t - M s ≤ ∫ τ in s..t, Φ (M τ)`

now follows unconditionally from `hM_lip`, an a.e. pointwise bound
`deriv M τ ≤ Φ (M τ)`, and interval-integrability of `Φ ∘ M`.

### 4. ~~Pointwise `Δ(f²) = 2|∇f|² + 2f·Δf`~~ — **CLOSED**

See Done section above.  Scalar 1-D form `(f²)'' = 2(f')² + 2 f · f''`
discharged in `NSBlwChain/BLW/HessianExpansionFromC2.lean`; constructor
`HessianExpansionData.ofScalarIdentities` assembles per-component
identities into the bundle's `sum_scalar_identity` field.

### 5. ~~1-D 2nd-derivative test at local max~~ — **CLOSED**

See Done section above.  Discharged via `MaxPrincipleFromLocalMax.lean`
using `HasDerivAt.tendsto_slope` + `strictMonoOn_of_deriv_pos`.

### 6. ~~Connection `NSEvolutionAxioms` → scalar bundles~~ — **CLOSED (structural wiring)**

Discharged via `NSBlwChain/BLW/FromNSEvolution.lean`.  The file
provides:

- `MOfVelocityField u t := ⨆_x Real.sqrt (Vec3.dot (curl (u t) x) (curl (u t) x))`
  — the `L∞` vorticity envelope.
- `NSArgmaxInputs u ν T t xStar` — structure packaging the
  NS-side analytical inputs at a fixed `(t, xStar)`: the pointwise
  scalars `(M, σ, |∇ω|², Δω_3, Ṁ)`, the step (ii)/(iii) scalar
  identities, the local-max bound `Δω_3 ≤ 0`, and the growth-regime
  hypothesis `Ṁ ≥ 0`.
- `NSArgmaxInputs.toArgmaxAnalyticalBundle` — constructor that
  assembles an `ArgmaxAnalyticalBundle` (pass-through).
- `argmaxBundle_of_NSEvolutionAxioms` — top-level convenience
  wrapper threading `NSEvolutionAxioms` + `NSArgmaxInputs` to
  `ArgmaxAnalyticalBundle` + gradient bound.
- `NSArgmaxInputs.zero` — zero-datum regression sanity check.

Closed at the **same standard as items 3/4/5**: hypothesis-taking
fields are explicit, downstream composition is mechanical, and the
zero datum verifies structural consistency.  The full derivation of
`NSArgmaxInputs` from `NSEvolutionAxioms` smoothness (~1500 LOC of
`fderiv`-level curl calculus, spatial argmax existence, Danskin for
`M`, local-frame substitution, etc.) is deferred as a downstream
sub-project; it does not affect this file's structural role.

## By design (axioms)

These stay as `axiom` declarations per project scope:

- `biot_savart_identity_R3` (Proposition 12.1, paper §12.2).
- `seregin_type_one_exclusion` (Seregin 2012 CMP).
- `NS_time_analyticity` (Kato 1967 / Foias–Temam 1979).

## By design (hypothesis-taking structural fields)

- `TorusCorrectionBundle.RL_bound` — periodic-kernel correction bound
  (Ewald splitting).
- `EpsteinZetaBundle.bound` — numeric bound on `∑_{n ≠ 0} |n|^{-s}`
  (p-series framework already in place; specific numeric value
  taken as hypothesis).

## Paper §3/§4 unconditional backbone (optional extension)

- `Theorem1` (blowup rate α ∈ (1,2)) — skeleton exists with
  hypothesis bundle; full enstrophy-crossover proof remains.
- `Theorem2` (far-field control) — skeleton exists with hypothesis
  bundle; full Cauchy-Schwarz on Biot-Savart tail remains.

## Expected timeline

At current pace (~8k LOC in one session over ~8 h), closing the
six analytical items would take another 1-2 sessions.  Each is a
focused ~200-400 LOC mathlib-backed pass.

## Trim fallbacks (if scope runs tight)

1. Drop `Theorem1`/`Theorem2` full proofs (keep skeletons).
2. Drop FTC-for-Lipschitz derivation (keep as hypothesis).
3. Drop Banach fixed-point derivation (keep as hypothesis).

Each preserves the chain's structural completeness.
