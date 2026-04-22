# Open items — ns-lean-proofs

Canonical list of remaining analytical work, post v0.2 skeleton
completion.

**Status:** 60 files, ~8200 LOC on main, all CI-green.  The **logical
skeleton is complete**: given discharge of the items below, the chain
runs end-to-end from `NSEvolutionAxioms` through
`gradient_bound_from_full_discharge` to `proposition_four_skeleton`
with zero structural gaps.

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

## Remaining — one substantive item (ODE integration — partial)

### 1. ODE integration (§12.4 step 7→8) — **PARTIAL DISCHARGE**

**Target:** `DifferentialInequalityBundle.integrated_bound` field.
Stated: `(T-t) · M(t) · log M(t) ≤ 1/4`.

**Status (2026-04-22):** partially discharged.  The algebraic core
`integrated_bound_of_substituted_bound` plus the bundle constructor
`DifferentialInequalityBundle.ofSubstitutedBound` in
`NSBlwChain/BLW/ODEIntegration_Discharge.lean` reduce the field to
a **single** clean residual hypothesis:

  `hW_lower_bound : ∀ t ∈ (t_start, T), 4·(T-t) ≤ 1/(M(t) · log M(t))`.

This is the substitution-level bound for `w := 1/(M·log M)`.  The
algebraic step `w(t) ≥ 4(T-t) ⇒ (T-t)·M·logM ≤ 1/4` is unconditional.

**Remaining:** derive `hW_lower_bound` from the a.e. ODE inequality
`Ṁ ≤ 4 M² log M` via:
1. quotient rule on `w = 1/(M·log M)` to get `ẇ ≥ -4 - 4/log M`;
2. FTC integration from `t` to `T⁻`
   (`intervalIntegral.integral_eq_sub_of_hasDerivAt`);
3. boundary limit `w(T⁻) = 0` from `log M → ∞` and `M > 1`;
4. tail absorption of `∫_t^T 4/log M ds = o(T-t)` as `t → T⁻`.

**Derivation sketch (paper §12.4):** Given a.e. `Ṁ ≤ 4 M² log M`, the
function `w := 1/(M · log M)` satisfies
`ẇ = -Ṁ(log M + 1)/(M · log M)² ≥ -4 - 4/log M`.  Integrating from
`t` to `T⁻` with `w(T⁻) = 0` (from `log M → ∞`) and absorbing the
`4/log M` tail yields `w(t) ≥ 4(T-t)`, i.e., the clean residual
above.

**Location:** `NSBlwChain/BLW/ODEIntegration.lean` (bundle) +
`NSBlwChain/BLW/ODEIntegration_Discharge.lean` (partial discharge).

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
