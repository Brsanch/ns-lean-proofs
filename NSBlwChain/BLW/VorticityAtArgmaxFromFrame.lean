-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.BLW.VorticityAtArgmax

/-!
# Step (iii) — local-frame scalar wiring

This file provides a **scalar-level wiring** from local-frame
calculus identities to `VorticityAtArgmaxInputs` in
`BLW/VorticityAtArgmax.lean`.

## The identities

Step (iii) of Theorem 12.2 uses:

1. **Half-sqNorm time-derivative** via dot with `ω`:
   `ω · ∂_t ω = (1/2) · ∂_t |ω|²`.
2. **Strain projection.**  `ω · S ω = M² · σ` where
   `σ := ω̂ · S ω̂`.
3. **Laplacian projection (local frame).**  `ω · Δω = M · Δω_3`.
4. **Advection vanishes at argmax.**
   `ω · (u · ∇ω) = (1/2) · u · ∇|ω|² = 0` when `∇|ω|²(x*) = 0`.
5. **Envelope identity (Danskin).**
   `∂_t |ω|² (x*, t) = 2 · M · dM/dt`.
6. **Vorticity equation at `x*`.**
   `∂_t ω = S ω - u · ∇ω + ν Δω`.

Combining these scalars via `VorticityAtArgmaxInputs.step_iii`
yields `ν · Δω_3 = Ṁ - M · σ`.

The **multivariable-calculus derivations** of (1), (4), (5) are
open discharges.

## Contents

* `VorticityLocalFrameData` — scalar bundle packaging the inputs.
* `toVorticityAtArgmaxInputs` — produces the downstream bundle.
-/

namespace NSBlwChain.BLW

/-- Scalar data for the step-(iii) local-frame computation at `x*`.

    The fields correspond to:
    * `ν, M, sigma, growth, laplaceOmega3` — primary scalars.
    * `omega_S_omega` — `ω·Sω(x*)`.
    * `omega_laplace_omega` — `ω·Δω(x*)`.
    * `time_deriv_half_sqN` — `∂_t (|ω|²/2)(x*)`.
    * `advectionAtArgmax` — `ω·(u·∇ω)(x*)`.

    Hypothesis fields mirror identities (1)–(6) above. -/
structure VorticityLocalFrameData where
  ν                   : ℝ
  M                   : ℝ
  sigma               : ℝ
  growth              : ℝ
  laplaceOmega3       : ℝ
  omega_S_omega       : ℝ
  omega_laplace_omega : ℝ
  time_deriv_half_sqN : ℝ
  advectionAtArgmax   : ℝ
  nu_pos : 0 < ν
  M_pos  : 0 < M
  /-- (6) Vorticity equation contracted with `ω`. -/
  vorticity_eq_contracted :
    time_deriv_half_sqN
      = omega_S_omega - advectionAtArgmax + ν * omega_laplace_omega
  /-- (4) Advection vanishes. -/
  advection_vanishes : advectionAtArgmax = 0
  /-- (2) Strain projection. -/
  strain_form : omega_S_omega = M ^ 2 * sigma
  /-- (3) Laplace projection (local frame). -/
  laplace_form : omega_laplace_omega = M * laplaceOmega3
  /-- (5) Envelope identity. -/
  envelope_form : time_deriv_half_sqN = M * growth

namespace VorticityLocalFrameData

variable (d : VorticityLocalFrameData)

/-- **Wiring.**  Produce the downstream `VorticityAtArgmaxInputs`
    bundle. -/
def toVorticityAtArgmaxInputs : VorticityAtArgmaxInputs where
  ν                   := d.ν
  M                   := d.M
  sigma               := d.sigma
  growth              := d.growth
  laplaceOmega3       := d.laplaceOmega3
  omega_S_omega       := d.omega_S_omega
  omega_laplace_omega := d.omega_laplace_omega
  time_deriv_half_sqN := d.time_deriv_half_sqN
  advectionAtArgmax   := d.advectionAtArgmax
  nu_pos := d.nu_pos
  M_pos  := d.M_pos
  vorticity_eq_contracted := d.vorticity_eq_contracted
  advection_vanishes := d.advection_vanishes
  strain_form := d.strain_form
  laplace_form := d.laplace_form
  envelope_form := d.envelope_form

/-- **Step (iii) conclusion** applied to the local-frame data. -/
theorem step_iii_local_frame :
    d.ν * d.laplaceOmega3 = d.growth - d.M * d.sigma :=
  d.toVorticityAtArgmaxInputs.step_iii

end VorticityLocalFrameData

end NSBlwChain.BLW
