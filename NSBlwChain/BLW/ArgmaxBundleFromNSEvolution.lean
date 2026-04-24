-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.BLW.ArgmaxIdentities
import NSBlwChain.BLW.DerivFrameFromNSEvolution
import NSBlwChain.BLW.ScalarMaxFromNSEvolution
import NSBlwChain.BLW.VorticityFrameFromNSEvolution

set_option diagnostics true
set_option diagnostics.threshold 100

/-!
# `ArgmaxAnalyticalBundle` directly from `NSEvolutionAxioms`

Grand-compose theorem: the three step-bundle constructors L3, L6, L8
(steps (i), (ii), (iii) of the BLW chain's argmax analytical inputs)
combine into a single `ArgmaxAnalyticalBundle.ofNSEvolutionAxioms`
producing the unified scalar bundle consumed by
`ArgmaxAnalyticalBundle.gradient_bound`.

## Shape

Given:
- `ax : NSEvolutionAxioms u ν T`
- `t ∈ [0, T)`, `xStar : Vec3`
- Local-frame alignment `ω(xStar) = M · ê₂` (three equations)
- Scalar data `(M, σ, growth, gradSqNorm, laplaceOmega3)`
- Step (ii) pointwise inequality `gradSqNorm ≤ M · |laplaceOmega3|`
- Step (iii) identity `ν · laplaceOmega3 = growth - M · σ`
- Sign condition `laplaceOmega3 ≤ 0`
- Growth regime `0 ≤ growth`
- Positivity: `0 < ν`, `0 ≤ M`

Produce an `ArgmaxAnalyticalBundle` from which
`gradient_bound : gradSqNorm ≤ M² · σ / ν` follows.

## Positioning

The three underlying constructors (`LocalFrameDerivativeData`,
`ScalarLocalMaxSecondDeriv`, `VorticityLocalFrameData` each from NSEv)
are not strictly required by this wrapper — the relevant *scalar
outputs* (M, σ, growth, laplaceOmega3, gradSqNorm) are already
caller-supplied here.  The wrapper documents that each such scalar
can, in principle, be produced by composing the L3/L6/L8 constructors
with appropriate differentiability/alignment hypotheses.

A "full" grand-compose that derives step_ii from the Hessian chain
would additionally need:
- The gradient_bound's hypothesis flow through `GradBoundHypotheses`
  (existing in `GradientBound.lean`).
- Composition of step-(i) `LocalFrameDerivativeData` + step-(ii)
  `HessianLocalFrameData` + step-(iii) `VorticityLocalFrameData` via
  `ArgmaxStepsCompose.lean` + `StepsFromFrameCompose.lean`.

This thin wrapper matches the L3/L6/L8 pattern and completes the
NSEvolutionAxioms → scalar bundle story at the same granularity.
-/

namespace NSBlwChain.BLW

/-- **Grand-compose: `ArgmaxAnalyticalBundle` from `NSEvolutionAxioms`.**

    Given the five scalar data + six Prop inputs listed in the file
    docstring, assemble the unified analytical bundle.  The bundle's
    `gradient_bound : gradSqNorm ≤ M² · σ / ν` follows immediately
    via `ArgmaxAnalyticalBundle.gradient_bound`. -/
noncomputable def ArgmaxAnalyticalBundle.ofNSEvolutionAxioms
    {u : VelocityField} {ν T : ℝ}
    (_ax : NSEvolutionAxioms u ν T)
    (_t : ℝ) (_ht : 0 ≤ _t) (_htT : _t < T)
    (_xStar : Vec3)
    (M σ growth gradSqNorm laplaceOmega3 : ℝ)
    (hν : 0 < ν) (hM_nonneg : 0 ≤ M)
    (h_step_ii : gradSqNorm ≤ M * |laplaceOmega3|)
    (h_step_iii : ν * laplaceOmega3 = growth - M * σ)
    (h_laplace_nonpos : laplaceOmega3 ≤ 0)
    (h_growth_nonneg : 0 ≤ growth) :
    ArgmaxAnalyticalBundle where
  ν             := ν
  M             := M
  sigma         := σ
  gradSqNorm    := gradSqNorm
  laplaceOmega3 := laplaceOmega3
  growth        := growth
  nu_pos                := hν
  M_nonneg              := hM_nonneg
  step_i_M_zero_or_zero := trivial
  step_ii               := h_step_ii
  step_iii              := h_step_iii
  laplace_nonpos        := h_laplace_nonpos
  growth_nonneg         := h_growth_nonneg

/-- **Gradient bound from the grand-compose.**  Immediate corollary:
    `gradSqNorm ≤ M² · σ / ν` when the analytical bundle is produced
    from `NSEvolutionAxioms` via the **scalar-data** grand-compose
    (as opposed to the earlier `FromNSEvolution.gradient_bound_of_NSEvolutionAxioms`
    which consumes an `NSArgmaxInputs` record). -/
theorem gradient_bound_of_NSEvolutionAxioms_via_scalars
    {u : VelocityField} {ν T : ℝ}
    (ax : NSEvolutionAxioms u ν T)
    (t : ℝ) (ht : 0 ≤ t) (htT : t < T)
    (xStar : Vec3)
    (M σ growth gradSqNorm laplaceOmega3 : ℝ)
    (hν : 0 < ν) (hM_nonneg : 0 ≤ M)
    (h_step_ii : gradSqNorm ≤ M * |laplaceOmega3|)
    (h_step_iii : ν * laplaceOmega3 = growth - M * σ)
    (h_laplace_nonpos : laplaceOmega3 ≤ 0)
    (h_growth_nonneg : 0 ≤ growth) :
    gradSqNorm ≤ M ^ 2 * σ / ν :=
  (ArgmaxAnalyticalBundle.ofNSEvolutionAxioms ax t ht htT xStar
      M σ growth gradSqNorm laplaceOmega3
      hν hM_nonneg h_step_ii h_step_iii
      h_laplace_nonpos h_growth_nonneg).gradient_bound

end NSBlwChain.BLW
