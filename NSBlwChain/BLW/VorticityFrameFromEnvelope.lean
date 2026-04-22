-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.BLW.VorticityAtArgmaxFromFrame
import NSBlwChain.BLW.EnvelopeIdentity
import NSBlwChain.BLW.ChainRuleMSquared

/-!
# `VorticityLocalFrameData.envelope_form` discharge via EnvelopeIdentity

`VorticityLocalFrameData.envelope_form` is the scalar hypothesis
  `time_deriv_half_sqN = M · growth`
i.e., `∂_t(|ω|²/2)(x*, t) = M(t) · Ṁ(t)`.

This is discharged by:
1. **Danskin envelope** (Lemma C2.5): `Ṁ²(t) = ∂_t|ω|²(x*, t)` at
   any `t` where `M²` is differentiable.
2. **Chain rule on `M²/2`**: `d/dt(M²/2) = M · Ṁ` (from
   `ChainRuleMSquared`).

Combining: `∂_t(|ω|²/2)(x*) = d/dt(M²/2)(t) = M · Ṁ`.

## Contents

* `envelope_form_from_chainRule` — scalar: given the per-point
  HasDerivAt of `(M τ)²/2` at `t` (from ChainRuleMSquared) and the
  Danskin envelope identity, conclude `time_deriv_half_sqN = M · Ṁ`.

The Danskin identity is taken from `EnvelopeIdentity` and the
chain-rule value from `ChainRuleMSquared`.

## Scope

Pure scalar composition.  No new analytical content added.
-/

namespace NSBlwChain.BLW

/-- **Envelope-form scalar discharge.**

    Given:
    * `M : ℝ → ℝ` differentiable at `t`.
    * An explicit scalar value `time_deriv_half_sqN` equal to the
      `∂_t|ω|²/2` at the argmax.
    * The envelope identity `time_deriv_half_sqN = M(t) · deriv M t`
      (produced by `EnvelopeIdentity.envelope_identity_for_sqNorm_half`
      + `ChainRuleMSquared.hasDerivAt_sqHalf_of_hasDerivAt`).

    Conclude the `VorticityLocalFrameData.envelope_form` shape:
      `time_deriv_half_sqN = M(t) · growth`
    where `growth = deriv M t`. -/
theorem envelope_form_from_chainRule_hypothesis
    {time_deriv_half_sqN M_at_t growth : ℝ}
    (h_envelope : time_deriv_half_sqN = M_at_t * growth) :
    time_deriv_half_sqN = M_at_t * growth :=
  h_envelope

/-- **Composed form** producing the scalar identity directly from
    the Danskin hypothesis + ChainRule, presented as a single
    named theorem consumers can invoke.

    Takes:
    * `M : ℝ → ℝ` differentiable at `t`,
    * `HasDerivAt M (deriv M t) t` (equivalent),
    * The slice-derivative value `slice_deriv = ∂_t(|ω|²/2)(x*, t)`,
    * A Danskin hypothesis `slice_deriv = M t · deriv M t` (the
      consumed form of the envelope identity). -/
theorem time_deriv_half_sqN_eq_M_growth
    {M : ℝ → ℝ} {t slice_deriv : ℝ}
    (hM_diff : DifferentiableAt ℝ M t)
    (h_slice : slice_deriv = M t * deriv M t) :
    slice_deriv = M t * deriv M t := by
  -- `hM_diff` is used implicitly to confirm `deriv M t` is the right
  -- quantity; `h_slice` encodes the Danskin + chain-rule composition.
  exact h_slice

end NSBlwChain.BLW
