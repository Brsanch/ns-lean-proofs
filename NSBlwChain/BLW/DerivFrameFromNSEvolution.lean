-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Setup.VorticityDifferentiable
import NSBlwChain.BLW.DerivFrameFromProductRule

/-!
# `LocalFrameDerivativeData` from `NSEvolutionAxioms`

This file composes the foundational smoothness result
`NSEvolutionAxioms.vorticity_components_differentiableAt` (from
`Setup/VorticityDifferentiable.lean`) with the step-(i) discharge
`LocalFrameDerivativeData.ofDifferentiableVectorField` (from
`BLW/DerivFrameFromProductRule.lean`) to produce a
`LocalFrameDerivativeData` **directly from** the `NSEvolutionAxioms`
bundle plus local-frame alignment data at the argmax `xStar`.

Before this file, `ofDifferentiableVectorField` took the pointwise
differentiability hypothesis `∀ k, DifferentiableAt ℝ (fun y => ω y k) xStar`
as an input the caller had to supply.  Here that hypothesis is
produced from `NSEvolutionAxioms.smooth_in_space` (which asserts
`ContDiff ℝ 4 (u t)`), via the `curl`-smoothness chain in
`CurlSmoothness.lean`.

## Usage

A caller with a smooth NS solution `ax : NSEvolutionAxioms u ν T`
and a candidate argmax point `xStar` satisfying the local-frame
alignment `ω(xStar) = M · ê₂` can invoke
`LocalFrameDerivativeData.ofNSEvolutionAxioms` to get the step-(i)
bundle directly, with no remaining differentiability hypothesis.

## Scope

This wrapper composes NS smoothness with the step-(i) discharge
only.  The local-frame alignment (`ω(xStar) = M · ê₂`) is still a
taken hypothesis — it corresponds to choosing a coordinate frame
in which the vorticity argmax lies on the third basis axis, which
is a rotation-of-reference-frame, not a derivable fact.  Similarly,
`xStar` being a local argmax of `|ω|²` is a separate existence
claim (requires decay or compactness).
-/

namespace NSBlwChain.BLW

open NSBlwChain

/-- **`LocalFrameDerivativeData` from `NSEvolutionAxioms`.**

    Given:
    * `ax : NSEvolutionAxioms u ν T` — a smooth NS solution bundle.
    * `t : ℝ` with `0 ≤ t < T` — interior time of the evolution.
    * `xStar : Vec3` — candidate argmax point.
    * `i : Fin 3` — direction for the partial derivative.
    * `M : ℝ` — envelope value at `(t, xStar)`.
    * Local-frame alignment hypotheses: `ω(xStar) · ê₀ = 0`,
      `ω(xStar) · ê₁ = 0`, `ω(xStar) · ê₂ = M`.

    Produce a `LocalFrameDerivativeData` with all fields discharged
    (including `sqNorm_deriv_identity` via mathlib product rule),
    and no residual differentiability hypothesis — the latter is
    derived from the NS bundle's `smooth_in_space` + `curl` smoothness. -/
noncomputable def LocalFrameDerivativeData.ofNSEvolutionAxioms
    {u : VelocityField} {ν T : ℝ}
    (ax : NSEvolutionAxioms u ν T)
    (t : ℝ) (ht : 0 ≤ t) (htT : t < T)
    (xStar : Vec3) (i : Fin 3) (M : ℝ)
    (h_ω_0 : vorticity u t xStar 0 = 0)
    (h_ω_1 : vorticity u t xStar 1 = 0)
    (h_ω_2 : vorticity u t xStar 2 = M) :
    LocalFrameDerivativeData :=
  -- Derive pointwise differentiability of each vorticity component
  -- from the NS bundle's `ContDiff ℝ 4 (u t)`.
  let hω : ∀ k : Fin 3, DifferentiableAt ℝ (fun y => vorticity u t y k) xStar :=
    ax.vorticity_components_differentiableAt ht htT xStar
  -- Compose with the step-(i) discharge.
  LocalFrameDerivativeData.ofDifferentiableVectorField
    (vorticity u t) xStar i M hω h_ω_0 h_ω_1 h_ω_2

end NSBlwChain.BLW
