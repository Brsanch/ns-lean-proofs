-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.BLW.SliceSmoothness
import NSBlwChain.BLW.MaxPrincipleFromLocalMax

set_option diagnostics true
set_option diagnostics.threshold 100

/-!
# `ScalarLocalMaxSecondDeriv` from `NSEvolutionAxioms`

This file composes the `NSEvolutionAxioms`-side slice-smoothness results
(from `SliceSmoothness.lean`) with the general constructor
`ScalarLocalMaxSecondDeriv.ofIsLocalMax` (from `MaxPrincipleFromLocalMax.lean`)
to produce a `ScalarLocalMaxSecondDeriv` bundle **directly from** a
smooth NS solution plus only the existence hypothesis
`IsLocalMax |ω|² xStar`.

## Result

`ScalarLocalMaxSecondDeriv.ofNSEvolutionAxioms`: given
`ax : NSEvolutionAxioms u ν T`, a time `t ∈ [0, T)`, a spatial point
`xStar : Vec3`, and a local-max hypothesis `IsLocalMax |ω|² xStar`,
produce a `ScalarLocalMaxSecondDeriv` record — the step-(ii) analog
of `LocalFrameDerivativeData.ofNSEvolutionAxioms` in
`DerivFrameFromNSEvolution.lean`.

## Significance

With this file, the caller no longer needs to supply the per-direction
`DifferentiableAt` hypotheses (`hf_nhd`, `hD`) that
`ofIsLocalMax` previously required.  They are derived from the NS
bundle's C⁴ smoothness of `u`, transported through curl smoothness
to `|ω|²` ContDiff 3, and finally to slice + deriv-slice
differentiability.

Combined with `DerivFrameFromNSEvolution.lean`, both step (i) and
step (ii) of the BLW chain's analytical inputs are now producible
from `NSEvolutionAxioms` + local-frame alignment + argmax existence
alone — the "structural wiring → real derivation" upgrade for items
(i) and (ii) of `NSArgmaxInputs`.
-/

namespace NSBlwChain

open NSBlwChain.BLW

/-- **`ScalarLocalMaxSecondDeriv` from `NSEvolutionAxioms`.**

    Given:
    * `ax : NSEvolutionAxioms u ν T` — smooth NS solution bundle.
    * `t : ℝ` with `0 ≤ t < T` — interior time.
    * `xStar : Vec3` — spatial point where `|ω(t, ·)|²` has a local max.
    * `hmax : IsLocalMax (|ω(t, ·)|²) xStar` — the local-max hypothesis.

    Produce a `ScalarLocalMaxSecondDeriv` record.  The per-direction
    differentiability hypotheses consumed by
    `ScalarLocalMaxSecondDeriv.ofIsLocalMax` are discharged via
    `NSEvolutionAxioms.sqNormVort_slice_differentiableAt_nhds` and
    `NSEvolutionAxioms.sqNormVort_sliceDeriv_differentiableAt_zero`. -/
noncomputable def ScalarLocalMaxSecondDeriv.ofNSEvolutionAxioms
    {u : VelocityField} {ν T : ℝ}
    (ax : NSEvolutionAxioms u ν T)
    (t : ℝ) (ht : 0 ≤ t) (htT : t < T)
    (xStar : Vec3)
    (hmax : IsLocalMax
      (fun y : Vec3 => Vec3.dot (vorticity u t y) (vorticity u t y))
      xStar) :
    ScalarLocalMaxSecondDeriv :=
  ScalarLocalMaxSecondDeriv.ofIsLocalMax
    (fun y : Vec3 => Vec3.dot (vorticity u t y) (vorticity u t y))
    xStar hmax
    (fun i => ax.sqNormVort_slice_differentiableAt_nhds ht htT xStar i)
    (fun i => ax.sqNormVort_sliceDeriv_differentiableAt_zero ht htT xStar i)

end NSBlwChain
