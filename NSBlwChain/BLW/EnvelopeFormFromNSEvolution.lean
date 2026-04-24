-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Setup.NSHypothesis
import NSBlwChain.BLW.EnvelopeIdentity

/-!
# `envelope_form` from `NSEvolutionAxioms` + Danskin

Specialization of `EnvelopeIdentity.envelope_identity_for_sqNorm_half`
to the vorticity envelope `M(t) := ‖ω(t,·)‖_∞`.  Discharges the
`envelope_form : time_deriv_half_sqN = M · growth` field of
`VorticityLocalFrameData` from Danskin-level hypotheses.

## Statement

Given:
- `ax : NSEvolutionAxioms u ν T`,
- a time `t ∈ [0, T)` and argmax point `xStar : Vec3`,
- an envelope function `M : ℝ → ℝ` with the property
  `Vec3.dot (vorticity u t' x) (vorticity u t' x) / 2 ≤ M t' ^ 2 / 2`
  (pointwise envelope),
- the argmax condition at `(xStar, t)` (slice hits the envelope),
- derivative hypotheses `HasDerivAt (fun τ => (M τ)²/2) (M t · Ṁ) t`
  and `HasDerivAt (fun τ => |ω(xStar, τ)|²/2) slice_deriv t`,

Conclude `slice_deriv = M(t) · Ṁ(t)`.

## Note

Most of the "work" here is packaging.  The mathematical content
is `envelope_identity_for_sqNorm_half` (Danskin + chain rule), which
is already proved in `EnvelopeIdentity.lean`.  The specialization
simply threads `NSEvolutionAxioms` and the vorticity field through.
-/

namespace NSBlwChain.BLW

/-- **Envelope form for the BLW chain's step (iii)**, specialized to
    the NS vorticity field.

    Given `NSEvolutionAxioms u ν T` and Danskin-level hypotheses
    (envelope inequality, argmax, derivatives), conclude that the
    slice derivative `slice_deriv = ∂_t(|ω(xStar, ·)|²/2)(t)` equals
    `M(t) · deriv M t`.  This is the `envelope_form` field of
    `VorticityLocalFrameData` when `growth := deriv M t`. -/
theorem envelope_form_of_NSEvolutionAxioms
    {u : VelocityField} {ν T : ℝ} (_ax : NSEvolutionAxioms u ν T)
    (M : ℝ → ℝ) (xStar : Vec3) (t : ℝ) (ht : 0 ≤ t) (htT : t < T)
    (M_deriv slice_deriv : ℝ)
    (h_env :
      ∀ x t', Vec3.dot (vorticity u t' x) (vorticity u t' x) / 2
                ≤ (M t') ^ 2 / 2)
    (h_hit :
      Vec3.dot (vorticity u t xStar) (vorticity u t xStar) / 2
        = (M t) ^ 2 / 2)
    (h_M2_deriv : HasDerivAt (fun τ => (M τ) ^ 2 / 2) M_deriv t)
    (h_slice :
      HasDerivAt
        (fun τ => Vec3.dot (vorticity u τ xStar) (vorticity u τ xStar) / 2)
        slice_deriv t)
    (h_connect : M_deriv = M t * deriv M t) :
    slice_deriv = M t * deriv M t := by
  -- Apply the general Danskin envelope identity with
  --   phi := fun x t' => Vec3.dot (ω t' x) (ω t' x) / 2.
  exact envelope_identity_for_sqNorm_half
    (fun x t' => Vec3.dot (vorticity u t' x) (vorticity u t' x) / 2)
    M xStar t M_deriv slice_deriv h_env h_hit h_M2_deriv h_slice h_connect

end NSBlwChain.BLW
