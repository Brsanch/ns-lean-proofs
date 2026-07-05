-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import FourierAnalysis.ArgmaxFromDecay
import NSBlwChain.Setup.VectorFields
import NSBlwChain.Setup.NSHypothesis

/-!
# Spatial argmax existence from decay-at-infinity (consumes shared package)

The domain-polymorphic compactness-via-decay lemma now lives once in the shared
`fourier_analysis` package (`FourierAnalysis.exists_argmax_of_continuous_tendsto_zero`,
proved for any `[TopologicalSpace X]`), which both `ns-lean-proofs` and
`sqg-lean-proofs` `require`. This file **consumes** it:

* re-exports it into the `NSBlwChain.BLW` namespace (so the existing call sites —
  `PerTimeInstantConstructor`, `DecayToCocompact`, `SpatialArgmaxFromDecay`,
  `PeriodicArgmaxExistence` — are unchanged), and
* provides the `Vec3 = Fin 3 → ℝ` specialization for `|ω|²` that the BLW chain
  needs at every `τ ∈ (0, T)`.

The relocation is the shared-infra half of the SQG↔NS link: the argmax primitive
is proved once and imported by both programs rather than duplicated per repo.
-/

namespace NSBlwChain.BLW

open Filter Topology NSBlwChain

/-- **Spatial argmax from decay at infinity** — re-export of the shared
`FourierAnalysis.exists_argmax_of_continuous_tendsto_zero` (proved once in the
`fourier_analysis` package for any `[TopologicalSpace X]`). Kept under the
`NSBlwChain.BLW` name so downstream call sites are unaffected. -/
alias exists_argmax_of_continuous_tendsto_zero :=
  FourierAnalysis.exists_argmax_of_continuous_tendsto_zero

/-- **Spatial argmax for `|ω|²` over `Vec3` from polynomial decay.**

    Specialization to the squared-vorticity field that the BLW chain needs.
    Assumes:
    * `(t, y) ↦ |ω(t, y)|²` is continuous in `y` at fixed `t`,
    * the field decays at infinity (encoded as `Tendsto ... (𝓝 0)`),
    * `|ω(t, ·)|²` is strictly positive at some witness point.

    Conclusion: there exists `xStar` at which `|ω(t, xStar)|²` is the maximum.
    This is the operational form of the classical "smooth NS solution on `ℝ³`
    with vorticity decay achieves its `L^∞` max", obtained by instantiating the
    shared compactness-via-decay primitive at `X := Vec3`. -/
theorem exists_vorticity_argmax_of_decay
    {u : VelocityField} {t : ℝ}
    (h_cont : Continuous (fun y =>
      Vec3.dot (vorticity u t y) (vorticity u t y)))
    (h_decay : Tendsto
      (fun y => Vec3.dot (vorticity u t y) (vorticity u t y))
      (cocompact Vec3) (𝓝 0))
    {y₀ : Vec3} (hy₀_pos :
      0 < Vec3.dot (vorticity u t y₀) (vorticity u t y₀)) :
    ∃ xStar : Vec3,
      ∀ y : Vec3,
        Vec3.dot (vorticity u t y) (vorticity u t y)
          ≤ Vec3.dot (vorticity u t xStar) (vorticity u t xStar) :=
  FourierAnalysis.exists_argmax_of_continuous_tendsto_zero h_cont h_decay hy₀_pos

end NSBlwChain.BLW
