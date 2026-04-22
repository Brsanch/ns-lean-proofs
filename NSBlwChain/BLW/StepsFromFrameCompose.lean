-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.BLW.ArgmaxGradientFromFrame
import NSBlwChain.BLW.HessianAtArgmaxFromFrame
import NSBlwChain.BLW.VorticityAtArgmaxFromFrame
import NSBlwChain.BLW.ArgmaxStepsCompose
import NSBlwChain.BLW.GradientBound
import NSBlwChain.BLW.ArgmaxIdentities

/-!
# Local-frame composition — three steps → gradient bound

This file composes the three "local-frame data" bundles
(`HessianLocalFrameData`, `VorticityLocalFrameData`, and optionally
`LocalFrameDerivativeData` for step (i) consistency) into the
unified gradient bound of Theorem 12.2:

  `|∇ω|²(x*) ≤ M² · σ(x*) / ν`.

## Chain

1. `HessianLocalFrameData.toHessianAtArgmaxInputs` — delivers step (ii).
2. `VorticityLocalFrameData.toVorticityAtArgmaxInputs` — delivers
   step (iii).
3. `ArgmaxAnalyticalBundle.ofSteps` (from `ArgmaxStepsCompose.lean`)
   composes (ii) + (iii) with the growth hypothesis into the unified
   `ArgmaxAnalyticalBundle`.
4. `ArgmaxAnalyticalBundle.gradient_bound` delivers the conclusion.

All four steps are already machine-verified; this file is a
one-line composition layer.
-/

namespace NSBlwChain.BLW

/-- Compatibility between the step (ii) and step (iii) local-frame
    bundles: they must agree on `M` and `laplaceOmega3`. -/
structure FrameCompatibility
    (h₂ : HessianLocalFrameData) (h₃ : VorticityLocalFrameData) : Prop where
  M_eq : h₂.M = h₃.M
  laplace_eq : h₂.laplaceOmega3 = h₃.laplaceOmega3

/-- **Compose frame data into `ArgmaxAnalyticalBundle`.** -/
def ArgmaxAnalyticalBundle.ofFrameData
    (h₂ : HessianLocalFrameData) (h₃ : VorticityLocalFrameData)
    (hc : FrameCompatibility h₂ h₃)
    (hg : 0 ≤ h₃.growth) : ArgmaxAnalyticalBundle :=
  ArgmaxAnalyticalBundle.ofSteps
    h₂.toHessianAtArgmaxInputs
    h₃.toVorticityAtArgmaxInputs
    { M_eq := hc.M_eq, laplace_eq := hc.laplace_eq }
    hg

/-- **End-to-end: gradient bound from frame data.** -/
theorem gradient_bound_of_frame_data
    (h₂ : HessianLocalFrameData) (h₃ : VorticityLocalFrameData)
    (hc : FrameCompatibility h₂ h₃)
    (hg : 0 ≤ h₃.growth) :
    h₂.gradSqNorm ≤ h₃.M ^ 2 * h₃.sigma / h₃.ν :=
  (ArgmaxAnalyticalBundle.ofFrameData h₂ h₃ hc hg).gradient_bound

end NSBlwChain.BLW
