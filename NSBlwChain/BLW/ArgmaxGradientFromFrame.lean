-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Setup.VectorFields
import NSBlwChain.BLW.ArgmaxGradient

/-!
# Step (i) — local-frame derivative identity (scalar wiring)

This file provides a **scalar-level wiring** from local-frame
calculus identities to the `ArgmaxGradientInputs` structure of
`BLW/ArgmaxGradient.lean`.

## The identity

In the local frame `ω(x*) = M · ê_3`, the scalar identity
  `∂_i|ω|²(x*) = 2 · M · ∂_i ω_3(x*)`
is a pointwise consequence of:

1. `|ω|² = Σ_k (ω_k)²` (definition of `Vec3.dot` on `ω`).
2. `∂_i(f²) = 2 · f · ∂_i f` (product rule for scalar functions).
3. Summing over `k`, only `k = 3` contributes at `x*` because
   `ω_k(x*) = M · δ_{k,3}` in the local frame.

The **multivariable-calculus derivation** of this identity is
left for a separate analytical pass (it requires mathlib's
`fderiv` on products and sums, plus a local-frame substitution
argument).  Here we package the identity as a **scalar
hypothesis** and wire it into `ArgmaxGradientInputs`.

## Contents

* `LocalFrameDerivativeData` — scalar bundle: the three component
  partial derivatives `∂_i ω_k(x*)` for `k ∈ {0, 1, 2}` and the
  scalar `∂_i|ω|²(x*)`, plus the hypothesis that
  `ω_k(x*) = 0` for `k ∈ {0, 1}` and `ω_3(x*) = M`.

* `toArgmaxGradientInputs` — constructor: given the scalar bundle
  plus the pointwise identity and the argmax condition,
  produce an `ArgmaxGradientInputs`.

## Scope

Pure scalar wiring.  No analytical content is added.  The
"hard part" of step (i) — the identity `∂_i|ω|² = 2 Σ_k ω_k · ∂_i ω_k`
via fderiv of a sum of squares — remains an open discharge.
-/

namespace NSBlwChain.BLW

/-- Scalar data for the local-frame derivative computation at the
    argmax point `x*`.

    Fields:
    * `M` — envelope value at `x*`.
    * `omega_0_at_xstar, omega_1_at_xstar, omega_3_at_xstar`
      — scalar components of `ω(x*)` in the local frame.
    * `partial_omega_0, partial_omega_1, partial_omega_3`
      — partial derivatives `∂_i ω_k(x*)` for the fixed direction
      `i` and each `k ∈ {0, 1, 3}`.
    * `partial_sqNorm` — `∂_i|ω|²(x*)`.

    Hypotheses:
    * Local-frame alignment: `ω_0(x*) = 0`, `ω_1(x*) = 0`,
      `ω_3(x*) = M`.
    * Pointwise identity: `∂_i|ω|² = 2 · (ω_0 · ∂_i ω_0 +
      ω_1 · ∂_i ω_1 + ω_3 · ∂_i ω_3)`. -/
structure LocalFrameDerivativeData where
  M                  : ℝ
  omega_0_at_xstar   : ℝ
  omega_1_at_xstar   : ℝ
  omega_3_at_xstar   : ℝ
  partial_omega_0    : ℝ
  partial_omega_1    : ℝ
  partial_omega_3    : ℝ
  partial_sqNorm     : ℝ
  /-- Local-frame alignment: first two components vanish. -/
  omega_0_zero : omega_0_at_xstar = 0
  omega_1_zero : omega_1_at_xstar = 0
  /-- Third component equals `M`. -/
  omega_3_eq_M : omega_3_at_xstar = M
  /-- Pointwise identity: `∂_i|ω|² = 2 · ω · (∂_i ω)` (dot product). -/
  sqNorm_deriv_identity :
    partial_sqNorm
      = 2 * (omega_0_at_xstar * partial_omega_0
              + omega_1_at_xstar * partial_omega_1
              + omega_3_at_xstar * partial_omega_3)

namespace LocalFrameDerivativeData

variable (d : LocalFrameDerivativeData)

/-- **Reduction.**  In the local frame (two components vanish, third
    equals `M`), the pointwise identity collapses to
    `∂_i|ω|² = 2 · M · ∂_i ω_3`. -/
theorem sqNorm_deriv_local_frame :
    d.partial_sqNorm = 2 * d.M * d.partial_omega_3 := by
  have h_id := d.sqNorm_deriv_identity
  rw [d.omega_0_zero, d.omega_1_zero, d.omega_3_eq_M] at h_id
  linarith

/-- **Wiring to `ArgmaxGradientInputs`.**  Given an argmax
    hypothesis `∂_i|ω|²(x*) = 0`, produce the scalar
    `ArgmaxGradientInputs` whose conclusion is `M · ∂_i ω_3 = 0`. -/
def toArgmaxGradientInputs (h_argmax : d.partial_sqNorm = 0) :
    ArgmaxGradientInputs where
  M               := d.M
  partial_omega_3 := d.partial_omega_3
  partial_sqNorm  := d.partial_sqNorm
  sqNorm_form     := d.sqNorm_deriv_local_frame
  sqNorm_zero     := h_argmax

/-- **Step (i) conclusion** applied to the local-frame data. -/
theorem step_i_local_frame (h_argmax : d.partial_sqNorm = 0) :
    d.M * d.partial_omega_3 = 0 :=
  (d.toArgmaxGradientInputs h_argmax).step_i

end LocalFrameDerivativeData

end NSBlwChain.BLW
