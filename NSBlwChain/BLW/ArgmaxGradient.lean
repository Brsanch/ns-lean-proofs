-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib

/-!
# Step (i) of Theorem 12.2 — argmax gradient identity

This file formalizes **step (i)** of the proof of Theorem 12.2 in
§12.3 of the companion paper.  The conclusion is:

  In the local frame where `ω(x*) = M · ê_3`,
  `∇|ω|²(x*) = 0` ⇒ `∂_i ω_3(x*) = 0` for every `i`.

## The chain at `x*`

At any point,
  `∂_i |ω|²(x) = 2 · ∑_k ω_k(x) · ∂_i ω_k(x)`.

In the local frame at `x*`, `ω(x*) = M · ê_3`, so `ω_k(x*) = 0` for
`k ≠ 3` and `ω_3(x*) = M`.  Hence

  `∂_i |ω|²(x*) = 2 · M · ∂_i ω_3(x*)`.

The argmax identity `∂_i |ω|²(x*) = 0` then gives

  `M · ∂_i ω_3(x*) = 0`,

which is step (i).  If in addition `M > 0`, we conclude
`∂_i ω_3(x*) = 0`.

## What is verified here

Pure scalar algebra from the two hypothesis inputs.  The analytical
derivations of `∂_i |ω|² = 2 M · ∂_i ω_3` in the local frame and of
`∂_i |ω|²(x*) = 0` from the argmax condition are taken as the
structure fields.
-/

namespace NSBlwChain.BLW

/-- **Step (i) scalar hypothesis bundle.**

    Fields:
    * `M` — vorticity magnitude at `x*`.
    * `partial_omega_3` — `∂_i ω_3(x*)` for the fixed direction `i`.
    * `partial_sqNorm` — `∂_i |ω|²(x*)`.

    Hypotheses:
    * `sqNorm_form` — in the local frame, `∂_i |ω|² = 2 M · ∂_i ω_3`.
    * `sqNorm_zero` — argmax: `∂_i |ω|²(x*) = 0`.

    Conclusion (below): `M · ∂_i ω_3 = 0`. -/
structure ArgmaxGradientInputs where
  M : ℝ
  partial_omega_3 : ℝ
  partial_sqNorm : ℝ
  /-- Local-frame form: `∂_i |ω|² = 2 M · ∂_i ω_3`. -/
  sqNorm_form : partial_sqNorm = 2 * M * partial_omega_3
  /-- Argmax: `∂_i |ω|²(x*) = 0`. -/
  sqNorm_zero : partial_sqNorm = 0

namespace ArgmaxGradientInputs

variable (h : ArgmaxGradientInputs)

/-- **Step (i) conclusion.**  `M · ∂_i ω_3 = 0`. -/
theorem step_i : h.M * h.partial_omega_3 = 0 := by
  have h1 := h.sqNorm_form
  have h2 := h.sqNorm_zero
  linarith

/-- **Step (i) corollary.**  If `M ≠ 0`, then `∂_i ω_3(x*) = 0`. -/
theorem partial_omega_3_zero_of_M_ne_zero (hM : h.M ≠ 0) :
    h.partial_omega_3 = 0 := by
  have hprod : h.M * h.partial_omega_3 = 0 := h.step_i
  exact (mul_eq_zero.mp hprod).resolve_left hM

end ArgmaxGradientInputs

end NSBlwChain.BLW
