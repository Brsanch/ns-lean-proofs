-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.BLW.ArgmaxGradientFromFrame
import NSBlwChain.BLW.HessianAtArgmaxFromFrame
import NSBlwChain.BLW.VorticityAtArgmaxFromFrame
import NSBlwChain.BLW.StepsFromFrameCompose
import NSBlwChain.BLW.HessianFrameFromMaxPrinciple
import NSBlwChain.BLW.ScalarProductRule
import NSBlwChain.BLW.MaxPrinciple
import NSBlwChain.BLW.EnvelopeIdentity
import NSBlwChain.BLW.ChainRuleMSquared
import NSBlwChain.BLW.HessianExpansionIdentity
import NSBlwChain.BLW.GradientBound
import NSBlwChain.BLW.ArgmaxIdentities
import NSBlwChain.BLW.SanityExamples
import NSBlwChain.BLW.PropositionFour
import NSBlwChain.BLW.ChainThread

/-!
# Full-discharge pipeline — BLW-gradient chain composition

This file is the **navigational capstone** for the argmax gradient
bound chain of Theorem 12.2 of the companion paper.  It composes
the recently-landed scalar discharges (ScalarProductRule,
MaxPrinciple, EnvelopeIdentity, ChainRuleMSquared,
HessianExpansionIdentity) with the frame-data bundles
(`HessianLocalFrameData`, `VorticityLocalFrameData`,
`LocalFrameDerivativeData`) and the composition layer
(`StepsFromFrameCompose`) into a single named end-to-end theorem,
plus a sanity-check example with concrete numerics.

## Full chain: classical axioms → gradient bound → regularity

```
                        Setup/ClassicalAxioms.lean
                 (three named axioms: BiotSavartSelfStrainBound,
                  SereginTypeOneExclusion, NSTimeAnalyticity)
                                  │
                                  ▼
  ╔═══════════════ §12.3 argmax gradient bound (scalar chain) ═════════════╗
  ║                                                                         ║
  ║  step (i)  — LocalFrameDerivativeData  (ArgmaxGradientFromFrame.lean)   ║
  ║     ↑ discharge: ScalarProductRule.partialDeriv_dot_self_eq             ║
  ║       (ScalarProductRule.lean — paper §12.3 step (i) identity)          ║
  ║                                                                         ║
  ║  step (ii) — HessianLocalFrameData     (HessianAtArgmaxFromFrame.lean)  ║
  ║     ↑ discharge 1: HessianExpansionIdentity.hessian_expansion           ║
  ║       (HessianExpansionIdentity.lean — Δ|ω|² = 2|∇ω|² + 2 ω·Δω)          ║
  ║     ↑ discharge 2: MaxPrinciple.laplace_nonpos_of_localMax              ║
  ║       (MaxPrinciple.lean — L ≤ 0 at local max via trace)                ║
  ║       ↳ combined via HessianFrameFromMaxPrinciple.ofMaxPrinciple        ║
  ║                                                                         ║
  ║  step (iii) — VorticityLocalFrameData  (VorticityAtArgmaxFromFrame.lean) ║
  ║     ↑ discharge 1: EnvelopeIdentity.envelope_identity_for_sqNorm_half   ║
  ║       (EnvelopeIdentity.lean — Danskin specialization ∂_t|ω|² = 2M·Ṁ)   ║
  ║     ↑ discharge 2: ChainRuleMSquared.hasDerivAt_sqHalf_of_hasDerivAt    ║
  ║       (ChainRuleMSquared.lean — d/dt(M²/2) = M·Ṁ)                       ║
  ║                                                                         ║
  ║  ─────────────────────────────────────────────────────────────────────  ║
  ║  composition layer:                                                     ║
  ║                                                                         ║
  ║     FrameCompatibility + ArgmaxAnalyticalBundle.ofFrameData             ║
  ║       (StepsFromFrameCompose.lean — frame data → analytical bundle)     ║
  ║                                                                         ║
  ║     ⇒ gradient_bound_of_frame_data                                      ║
  ║         : |∇ω|²(x*) ≤ M² · σ(x*) / ν    (Theorem 12.2)                  ║
  ╚═════════════════════════════════════════════════════════════════════════╝
                                  │
                                  ▼
  §12.4 log-absorption  (LogAbsorption.lean + BiotSavartCylindrical.lean)
   + caveats C1, C4     (GrowthMomentBundle, ImplicitBoundBundle)
                                  │
                                  ▼
  §12.4 sub-Type-I rate (SubTypeOneRate.subTypeI_rate_of_log_blowup)
                                  │
                                  ▼
  regularity_extension_exists    (ChainThread.lean)
   ↳ consumes seregin_type_one_exclusion axiom
                                  │
                                  ▼
          proposition_four_skeleton      (PropositionFour.lean)
          — end-to-end smooth extension past the first singular time
```

## What this file produces

* **`gradient_bound_from_full_discharge`** — a one-line wrapper
  around `gradient_bound_of_frame_data` that advertises the
  provenance: the frame-data inputs are the outputs of the named
  scalar discharges (ScalarProductRule, MaxPrinciple +
  HessianExpansionIdentity, EnvelopeIdentity + ChainRuleMSquared).

* **`exampleFullDischarge`** — concrete numerical instantiation
  (ν = 1, M = 10, σ = 4, Ṁ = 36, Δω₃ = -4) verifying
  `|∇ω|² ≤ 400 = 10² · 4 / 1`.

## Scope

This file adds **no analytical content**; it is a pure
composition-and-navigation layer.  Every hypothesis field of the
frame-data bundles continues to name a concrete scalar identity
whose pointwise derivation is either (a) already in the named
scalar files (e.g. `hessian_expansion`) or (b) a remaining
discharge consumed via a hypothesis field (e.g. the sum-expansion
identity fed to `MaxPrinciple`).
-/

namespace NSBlwChain.BLW

/-! ## §1. Top-level wiring theorem -/

/-- **Gradient bound from the fully-discharged frame bundles.**

    Given:
    * `frame_data_hessian : HessianLocalFrameData` — assembled from
      `ScalarProductRule` (for the pointwise expansion of
      `∂ᵢ|ω|²`) and from `MaxPrinciple` +
      `HessianExpansionIdentity` (for `hess_trace_nonpos` and
      `hess_expansion`).
    * `frame_data_vorticity : VorticityLocalFrameData` — assembled
      from `EnvelopeIdentity` (for `envelope_form`) and
      `ChainRuleMSquared` (to relate the half-sqNorm time
      derivative to `M · dM/dt`).
    * `hc : FrameCompatibility …` — the two bundles share `M` and
      `laplaceOmega3`.
    * `hg : 0 ≤ frame_data_vorticity.growth` — envelope is
      nondecreasing at the growth-regime time.

    Conclude: the argmax gradient bound
    `|∇ω|²(x*) ≤ M² · σ(x*) / ν` (Theorem 12.2).

    This is a direct re-export of
    `gradient_bound_of_frame_data`; the name advertises that the
    inputs are expected to come from the discharge chain
    documented above. -/
theorem gradient_bound_from_full_discharge
    (frame_data_hessian : HessianLocalFrameData)
    (frame_data_vorticity : VorticityLocalFrameData)
    (hc : FrameCompatibility frame_data_hessian frame_data_vorticity)
    (hg : 0 ≤ frame_data_vorticity.growth) :
    frame_data_hessian.gradSqNorm
      ≤ frame_data_vorticity.M ^ 2 * frame_data_vorticity.sigma
          / frame_data_vorticity.ν :=
  gradient_bound_of_frame_data frame_data_hessian frame_data_vorticity hc hg

/-! ## §2. Sanity-check example

A concrete numerical instantiation with:
  * `ν = 1`, `M = 10`, `σ = 4`, `growth = 36`, `Δω₃ = -4`,
  * `gradSqNorm = 40` (saturating the step-(ii) bound
    `|∇ω|² ≤ M · |Δω₃|` with equality `40 ≤ 10 · 4`).

Checks that `gradient_bound_from_full_discharge` delivers the
arithmetic bound `40 ≤ 400`. -/

/-- Concrete `HessianLocalFrameData` in the local frame where
    `ω(x*) = 10·ê_3`, `∇|ω|²(x*) = 0`, `Δ|ω|²(x*) = 0`,
    `Δω₃(x*) = -4`, `|∇ω|²(x*) = 40`, i.e. saturating step (ii)
    at `40 ≤ 10 · 4`. -/
noncomputable def exampleHessianFrameData : HessianLocalFrameData where
  M                   := 10
  gradSqNorm          := 40
  laplaceSqNorm       := 0
  laplaceOmega3       := -4
  omega_laplace_omega := -40
  omega_0_at_xstar    := 0
  omega_1_at_xstar    := 0
  omega_3_at_xstar    := 10
  laplace_omega_0     := 0
  laplace_omega_1     := 0
  M_nonneg            := by norm_num
  omega_0_zero        := rfl
  omega_1_zero        := rfl
  omega_3_eq_M        := rfl
  dot_expansion       := by norm_num
  hess_expansion      := by norm_num
  hess_trace_nonpos   := by norm_num
  laplace_nonpos      := by norm_num

/-- Concrete `VorticityLocalFrameData` compatible with
    `exampleHessianFrameData`: same `M = 10` and
    `Δω₃ = -4`.  Strain parameters `ν = 1`, `σ = 4`,
    `growth = Ṁ = 36`.  Envelope identity:
    `∂_t(|ω|²/2) = M · Ṁ = 360`; strain form:
    `ω·Sω = M² · σ = 400`; vorticity equation contracted with `ω`:
    `360 = 400 - 0 + 1 · (-40)` ✓. -/
noncomputable def exampleVorticityFrameData : VorticityLocalFrameData where
  ν                   := 1
  M                   := 10
  sigma               := 4
  growth              := 36
  laplaceOmega3       := -4
  omega_S_omega       := 400
  omega_laplace_omega := -40
  time_deriv_half_sqN := 360
  advectionAtArgmax   := 0
  nu_pos                   := by norm_num
  M_pos                    := by norm_num
  vorticity_eq_contracted  := by norm_num
  advection_vanishes       := rfl
  strain_form              := by norm_num
  laplace_form             := by norm_num
  envelope_form            := by norm_num

/-- Compatibility witness: the two bundles agree on `M` and
    `Δω₃`. -/
def exampleFrameCompatibility :
    FrameCompatibility exampleHessianFrameData exampleVorticityFrameData where
  M_eq       := rfl
  laplace_eq := rfl

/-- Growth non-negativity for the example bundle.  Factored out
    because `norm_num` on a raw `exampleVorticityFrameData.growth`
    projection doesn't delta-unfold without help. -/
theorem exampleGrowthNonneg : 0 ≤ exampleVorticityFrameData.growth := by
  show (0 : ℝ) ≤ (36 : ℝ)
  norm_num

/-- **Sanity check — gradient bound on concrete numerics.**
    `exampleHessianFrameData.gradSqNorm = 40`; the right-hand side
    `M² · σ / ν = 10² · 4 / 1 = 400`; so the conclusion is
    `40 ≤ 400` — sensible. -/
example :
    exampleHessianFrameData.gradSqNorm
      ≤ exampleVorticityFrameData.M ^ 2 * exampleVorticityFrameData.sigma
          / exampleVorticityFrameData.ν :=
  gradient_bound_from_full_discharge
    exampleHessianFrameData exampleVorticityFrameData
    exampleFrameCompatibility exampleGrowthNonneg

/-- The numerical RHS evaluates to `400`. -/
example :
    exampleVorticityFrameData.M ^ 2 * exampleVorticityFrameData.sigma
        / exampleVorticityFrameData.ν = 400 := by
  show (10 : ℝ) ^ 2 * (4 : ℝ) / (1 : ℝ) = 400
  norm_num

/-- The numerical LHS is `40`. -/
example : exampleHessianFrameData.gradSqNorm = 40 := rfl

/-! ## §3. Navigational map — file ↔ paper reference

| Lean file                                    | Paper §   | Role                               |
|----------------------------------------------|-----------|------------------------------------|
| `ScalarProductRule.lean`                     | §12.3 (i) | ∂ᵢ(dot ω ω) = 2 Σ_k ω_k ∂ᵢ ω_k    |
| `ArgmaxGradientFromFrame.lean`               | §12.3 (i) | LocalFrameDerivativeData bundle    |
| `HessianExpansionIdentity.lean`              | §12.3 (ii)| Δ|ω|² = 2|∇ω|² + 2 ω·Δω             |
| `MaxPrinciple.lean`                          | §12.3 (ii)| Laplacian ≤ 0 at local max          |
| `HessianAtArgmaxFromFrame.lean`              | §12.3 (ii)| HessianLocalFrameData bundle        |
| `HessianFrameFromMaxPrinciple.lean`          | §12.3 (ii)| MaxPrinciple → HessianLocalFrameData|
| `ChainRuleMSquared.lean`                     | §12.3 (iii)| d/dt(M²/2) = M · Ṁ                 |
| `EnvelopeIdentity.lean`                      | §12.3 (iii)| Danskin envelope specialization    |
| `VorticityAtArgmaxFromFrame.lean`            | §12.3 (iii)| VorticityLocalFrameData bundle     |
| `StepsFromFrameCompose.lean`                 | §12.3     | Frame data → ArgmaxAnalyticalBundle |
| `GradientBound.lean`                         | §12.3     | Analytical bundle → |∇ω|² bound     |
| `FullDischargePipeline.lean` (this file)     | §12.3     | End-to-end composition              |
| `LogAbsorption.lean`                         | §12.4     | σ ≤ M(2 + log L + ½ log(σ/ν))       |
| `BiotSavartCylindrical.lean`                 | §12.2     | Cylindrical BLW identity bound      |
| `SubTypeOneRate.lean`                        | §12.4     | ODE bound → sub-Type-I rate         |
| `ChainThread.lean`                           | §12       | Seregin → extends past T            |
| `PropositionFour.lean`                       | §12       | End-to-end capstone                 |

-/

end NSBlwChain.BLW
