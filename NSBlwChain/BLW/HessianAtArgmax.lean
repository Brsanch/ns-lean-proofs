-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Setup.VectorFields

/-!
# Step (ii) of Theorem 12.2 — Hessian trace bound at `x*`

This file factors **step (ii)** of the proof of Theorem 12.2 in
§12.3 of the companion paper into a clean scalar-algebra lemma.
The conclusion is:

  `|∇ω|²(x*) ≤ M · |Δω_3(x*)|`.

## The chain at `x*`

In the local frame where `ω(x*) = M · ê_3`:

1. **Argmax identity (step (i)).**  `∇|ω|²(x*) = 0` gives
   `∂_i ω_3(x*) = 0` for every `i` (once `M ≠ 0`).

2. **Hessian trace non-positivity.**  Because `|ω|²` has a local
   maximum at `x*`, the trace of its Hessian is non-positive:
   `Δ|ω|²(x*) ≤ 0`.

3. **Expansion of `Δ|ω|²`.**
   `Δ|ω|²(x*) = 2 · |∇ω|²(x*) + 2 · ω · Δω(x*)`.

4. **Local-frame substitution.**  In the frame `ω(x*) = M · ê_3`,
   `ω · Δω = M · Δω_3`.

5. **Combine.**  From (2)-(4),
   `2 |∇ω|²(x*) + 2 M Δω_3(x*) ≤ 0`,
   i.e. `|∇ω|²(x*) ≤ - M · Δω_3(x*) = M · |Δω_3(x*)|` using
   `Δω_3(x*) ≤ 0` (the scalar `ω_3` attains a local max at `x*`).

## What is verified here

The **scalar combination** of the four identities into the step (ii)
conclusion is machine-verified.  The individual identities (1)-(4) +
the sign constraint `Δω_3(x*) ≤ 0` are taken as inputs.

This factoring populates `ArgmaxAnalyticalBundle.step_ii` once the
analytical discharges are supplied.
-/

namespace NSBlwChain.BLW

/-- **Step (ii) scalar hypothesis bundle.**

    Packages the four scalar identities at `(x*, t)` (local frame)
    that feed `|∇ω|²(x*) ≤ M · |Δω_3(x*)|`.

    Note the `laplace_nonpos` sign: `ω_3` attains a local max at `x*`
    (in the frame where `ω(x*) = M ê_3`, so `ω_3(x*) = M`; in a
    neighborhood of `x*` we have `|ω|² ≤ M² = ω_3(x*)²`, and combined
    with `∂_i ω_3(x*) = 0` this forces `ω_3` itself to be locally
    extremal at `x*`). -/
structure HessianAtArgmaxInputs where
  M : ℝ
  gradSqNorm : ℝ
  laplaceSqNorm : ℝ
  laplaceOmega3 : ℝ
  omega_laplace_omega : ℝ
  M_nonneg : 0 ≤ M
  /-- Step (2): trace of Hessian non-positive. -/
  hess_trace_nonpos : laplaceSqNorm ≤ 0
  /-- Step (3): pointwise expansion `Δ|ω|² = 2 |∇ω|² + 2 ω · Δω`. -/
  laplace_sqNorm_expansion :
    laplaceSqNorm = 2 * gradSqNorm + 2 * omega_laplace_omega
  /-- Step (4): `ω · Δω = M · Δω_3` in the local frame. -/
  laplace_form : omega_laplace_omega = M * laplaceOmega3
  /-- `Δω_3(x*) ≤ 0`:  `ω_3` attains a local max at `x*`. -/
  laplace_nonpos : laplaceOmega3 ≤ 0

namespace HessianAtArgmaxInputs

variable (h : HessianAtArgmaxInputs)

/-- **Step (ii) conclusion.**

    From the four scalar hypotheses, `|∇ω|²(x*) ≤ M · |Δω_3(x*)|`. -/
theorem step_ii : h.gradSqNorm ≤ h.M * |h.laplaceOmega3| := by
  have h_expand := h.laplace_sqNorm_expansion
  have h_form := h.laplace_form
  have h_nonpos := h.hess_trace_nonpos
  have h_lap := h.laplace_nonpos
  have habs : |h.laplaceOmega3| = - h.laplaceOmega3 :=
    abs_of_nonpos h_lap
  -- From h_expand + h_form + h_nonpos:
  --   2 gradSqNorm + 2 M · Δω_3 ≤ 0, i.e. gradSqNorm ≤ - M · Δω_3.
  have combine : 2 * h.gradSqNorm + 2 * (h.M * h.laplaceOmega3) ≤ 0 := by
    calc 2 * h.gradSqNorm + 2 * (h.M * h.laplaceOmega3)
        = 2 * h.gradSqNorm + 2 * h.omega_laplace_omega := by rw [h_form]
      _ = h.laplaceSqNorm := by rw [h_expand]
      _ ≤ 0 := h_nonpos
  have key : h.gradSqNorm ≤ - (h.M * h.laplaceOmega3) := by linarith
  -- Conclude using `|Δω_3| = - Δω_3`.
  calc h.gradSqNorm
      ≤ - (h.M * h.laplaceOmega3) := key
    _ = h.M * (- h.laplaceOmega3) := by ring
    _ = h.M * |h.laplaceOmega3| := by rw [habs]

end HessianAtArgmaxInputs

end NSBlwChain.BLW
