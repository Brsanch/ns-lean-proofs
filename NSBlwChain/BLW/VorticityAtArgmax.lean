-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Setup.VectorFields
import NSBlwChain.Setup.NSHypothesis

/-!
# Step (iii) of Theorem 12.2 — vorticity equation contracted at `x*`

This file factors **step (iii)** of the proof of Theorem 12.2 in
§12.3 of the companion paper into a clean scalar-algebra lemma.
The conclusion is:

  `ν · Δω_3(x*) = dM/dt - M · σ(x*)`.

## The chain at `x*`

In the local frame where `ω(x*) = M · ê_3`:

1. **Vorticity equation contracted with `ω`.**
   `∂_t(|ω|²/2)(x*) = ω · S ω(x*) - ω · (u · ∇ω)(x*) + ν · ω · Δω(x*)`.

2. **Advection vanishes.**  `ω · (u · ∇ω) = (1/2) · u · ∇|ω|²`, which
   vanishes at `x*` because `∇|ω|²(x*) = 0`.

3. **Strain form.**  `ω · S ω = M² · σ` by definition of
   `σ(x*) = hat ω · S hat ω`.

4. **Laplace form.**  `ω · Δω = M · Δω_3` in the local frame
   (`ω = M ê_3`).

5. **Envelope identity (Danskin).**  `∂_t(|ω|²/2)(x*) = M · dM/dt`
   at any point where `M` is differentiable (a consequence of
   `C2_Envelope.danskin_envelope` applied to `|ω|²`).

Combining (1)-(5) and dividing by `M > 0`:
  `ν · Δω_3(x*) = dM/dt - M · σ(x*)`.

## What is verified here

The **scalar combination** of the five identities into the step (iii)
conclusion is machine-verified below.  The individual identities (1)-(5)
are taken as inputs, since they each require local-frame calculus
(Rademacher, Hessian, vorticity equation with advection) best
handled in separate files.

This factoring is useful because it isolates the exact hypotheses
that a downstream analytical pass needs to discharge in order to
populate `ArgmaxAnalyticalBundle.step_iii` in
`BLW/ArgmaxIdentities.lean`.
-/

namespace NSBlwChain.BLW

/-- **Step (iii) scalar hypothesis bundle.**

    Packages the five scalar identities at `(x*, t)` that feed the
    conclusion `ν · Δω_3 = dM/dt - M · σ`.

    Fields:
    * `ν, M, sigma, growth, laplaceOmega3` — the scalars of interest.
    * `omega_S_omega, omega_laplace_omega, time_deriv_half_sqN,
      advectionAtArgmax` — intermediate scalars, each identified with
      an analytical quantity by a named hypothesis field.
    * Hypothesis fields (1)-(5) mirror the enumeration above.

    All analytical content is isolated in the hypothesis fields; the
    conclusion below is pure algebra. -/
structure VorticityAtArgmaxInputs where
  ν : ℝ
  M : ℝ
  sigma : ℝ
  growth : ℝ
  laplaceOmega3 : ℝ
  omega_S_omega : ℝ
  omega_laplace_omega : ℝ
  time_deriv_half_sqN : ℝ
  advectionAtArgmax : ℝ
  nu_pos : 0 < ν
  M_pos : 0 < M
  /-- (1) Vorticity equation contracted with `ω`. -/
  vorticity_eq_contracted :
    time_deriv_half_sqN
      = omega_S_omega - advectionAtArgmax + ν * omega_laplace_omega
  /-- (2) Advection term vanishes at the argmax. -/
  advection_vanishes : advectionAtArgmax = 0
  /-- (3) Strain form `ω · S ω = M² · σ`. -/
  strain_form : omega_S_omega = M ^ 2 * sigma
  /-- (4) Laplace form `ω · Δω = M · Δω_3` in the local frame. -/
  laplace_form : omega_laplace_omega = M * laplaceOmega3
  /-- (5) Danskin envelope: `∂_t (|ω|²/2)(x*) = M · dM/dt`. -/
  envelope_form : time_deriv_half_sqN = M * growth

namespace VorticityAtArgmaxInputs

variable (h : VorticityAtArgmaxInputs)

/-- **Step (iii) conclusion.**

    From the five scalar hypotheses, `ν · Δω_3 = dM/dt - M · σ`.

    Proof: substitute (2)-(5) into (1), solve for `ν · M · Δω_3`,
    and divide by `M > 0`. -/
theorem step_iii : h.ν * h.laplaceOmega3 = h.growth - h.M * h.sigma := by
  have h1 := h.vorticity_eq_contracted
  have h2 := h.advection_vanishes
  have h3 := h.strain_form
  have h4 := h.laplace_form
  have h5 := h.envelope_form
  -- substitute into h1 to reduce to an equation in the primary scalars.
  -- From (1) + (2): time_deriv_half_sqN = omega_S_omega + ν * omega_laplace_omega
  -- Then (3), (4): = M² σ + ν * M * laplaceOmega3
  -- Then (5): M * growth = M² σ + ν * M * laplaceOmega3
  -- Hence M * (growth - M * σ - ν * laplaceOmega3) = 0.
  have hM_ne : h.M ≠ 0 := ne_of_gt h.M_pos
  have key :
      h.M * (h.growth - h.M * h.sigma - h.ν * h.laplaceOmega3) = 0 := by
    have expand :
        h.M * h.growth
          = h.M ^ 2 * h.sigma + h.ν * (h.M * h.laplaceOmega3) := by
      calc h.M * h.growth
          = h.time_deriv_half_sqN := by rw [h5]
        _ = h.omega_S_omega - h.advectionAtArgmax
              + h.ν * h.omega_laplace_omega := h1
        _ = h.omega_S_omega - 0
              + h.ν * h.omega_laplace_omega := by rw [h2]
        _ = h.omega_S_omega + h.ν * h.omega_laplace_omega := by ring
        _ = h.M ^ 2 * h.sigma + h.ν * (h.M * h.laplaceOmega3) := by
              rw [h3, h4]
    -- Rearrange: M * (growth - M σ - ν Δω_3) = M · growth - M²σ - ν M Δω_3
    -- = 0 by `expand`.
    have : h.M * (h.growth - h.M * h.sigma - h.ν * h.laplaceOmega3)
            = h.M * h.growth - h.M ^ 2 * h.sigma
              - h.ν * (h.M * h.laplaceOmega3) := by ring
    rw [this, expand]
    ring
  -- Since M ≠ 0, divide through.
  have h_zero : h.growth - h.M * h.sigma - h.ν * h.laplaceOmega3 = 0 :=
    (mul_eq_zero.mp key).resolve_left hM_ne
  linarith

end VorticityAtArgmaxInputs

end NSBlwChain.BLW
