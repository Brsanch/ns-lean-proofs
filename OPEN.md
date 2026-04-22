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

## Remaining — six substantive analytical items

### 1. ODE integration (§12.4 step 7→8)

**Target:** `DifferentiableInequalityBundle.integrated_bound` field.
Currently a hypothesis: `(T-t) · M(t) · log M(t) ≤ 1/4`.

**Derivation:** Given a.e. `Ṁ ≤ 4 M² log M` near `T`, let `v = 1/M`.
Then `v̇ = -Ṁ/M² ≥ -4 log M = 4 log v`.  Integration by parts delivers
the integrated bound.

**Location:** `NSBlwChain/BLW/ODEIntegration.lean` (infrastructure
landed, proof remaining).

### 2. Banach fixed-point for C4 largeness

**Target:** `ImplicitBoundBundle.hLarge` field.
Currently a hypothesis: `1 + log L + (1/2) log(σ/ν) ≤ 4 log M - K/M`.

**Derivation:** Convex analysis on `σ ↦ M(1+logL+½log(σ/ν))` showing
a unique fixed point exists and satisfies `σ* ≤ 4 M log M` for `M`
large.  Paper §C4.

**Location:** `NSBlwChain/Caveats/C4_ImplicitBound.lean` or a new
`C4_BanachFixedPoint.lean`.

### 3. FTC-for-Lipschitz identity

**Target:** `GrowthMomentBundle.hIntegratedBound` field.
Currently a hypothesis: `M(t)-M(s) ≤ ∫_s^t Φ(M(τ)) dτ`.

**Derivation:** One mathlib lemma — `LipschitzWith` → absolutely
continuous → FTC `∫ deriv M dτ = M(t)-M(s)`.

**Location:** `NSBlwChain/Caveats/C1_FTC.lean` (scaffolding landed,
identity taken as hypothesis; needs mathlib bridge).

### 4. Pointwise `Δ(f²) = 2|∇f|² + 2f·Δf`

**Target:** `HessianExpansionData.scalar_Δsq_f_identity_k` field.
Currently a hypothesis.

**Derivation:** fderiv-level product rule applied twice, plus
symmetry of mixed partials.

**Location:** `NSBlwChain/BLW/HessianExpansionIdentity.lean` (structural
form landed; identity still hypothesis).

### 5. 1-D 2nd-derivative test at local max

**Target:** `ScalarLocalMaxSecondDeriv.d_i_nonpos` fields.
Currently hypotheses.

**Derivation:** `IsLocalMax.deriv_eq_zero` + sign of second derivative
for scalar functions on ℝ.

**Location:** `NSBlwChain/BLW/MaxPrinciple.lean` (bundle + trace
conclusion landed; per-direction `d_i ≤ 0` still hypothesis).

### 6. Connection `NSEvolutionAxioms` → scalar bundles

**Target:** wire `vorticity u : VelocityField → ...` to the scalar
bundles.  Requires:

- Define `M(t) := ‖vorticity u t · ‖_∞` (supremum over `x : Vec3`).
- Prove Lipschitz-in-`t` of `M`.
- At each growth-regime `t`, extract a `ArgmaxAnalyticalBundle`
  carrying the scalar quantities.

**Location:** new file `NSBlwChain/BLW/FromNSEvolution.lean`.

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
