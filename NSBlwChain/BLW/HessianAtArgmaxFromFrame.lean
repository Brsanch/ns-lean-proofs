-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.BLW.HessianAtArgmax

/-!
# Step (ii) — local-frame scalar wiring

This file provides a **scalar-level wiring** from local-frame
calculus identities to `HessianAtArgmaxInputs` in
`BLW/HessianAtArgmax.lean`.

## The identities

Step (ii) of Theorem 12.2 uses:

1. **Hessian expansion.**  For any `C²` vector field `ω`,
   `Δ|ω|²(x) = 2 · |∇ω|²(x) + 2 · ω(x) · Δω(x)`.
2. **Local-frame alignment.**  In the frame where `ω(x*) = M · ê_3`:
   `ω(x*) · Δω(x*) = M · Δω_3(x*)`.
3. **Hessian trace non-positive at a local maximum.**  Because
   `|ω|²` attains a local max at `x*`, `Δ|ω|²(x*) ≤ 0`.
4. **Δω_3 non-positive.**  Because `ω_3(x*) = M = |ω(x*)|` and
   `|ω(x*)| = |ω(x*)|_∞`, the scalar `ω_3` itself attains a local
   max at `x*`, forcing `Δω_3(x*) ≤ 0`.

The **multivariable-calculus derivation** of (1), (3), (4) is left
for a separate analytical pass.  This file wires scalar hypotheses
in place of that derivation.

## Contents

* `HessianLocalFrameData` — scalar bundle packaging the inputs.
* `toHessianAtArgmaxInputs` — produce the downstream
  `HessianAtArgmaxInputs` bundle.
-/

namespace NSBlwChain.BLW

/-- Scalar data for the local-frame Hessian computation at `x*`.

    Fields:
    * `M` — envelope value.
    * `gradSqNorm` — `|∇ω|²(x*)`.
    * `laplaceSqNorm` — `Δ|ω|²(x*)`.
    * `laplaceOmega3` — `Δω_3(x*)`.
    * `omega_laplace_omega` — `ω(x*) · Δω(x*)`.
    * `omega_0_at_xstar, omega_1_at_xstar, omega_3_at_xstar` — the
      components of `ω(x*)`.

    Hypotheses:
    * Local-frame alignment: `ω_0(x*) = 0`, `ω_1(x*) = 0`,
      `ω_3(x*) = M`.
    * Dot-product expansion: `ω · Δω = Σ_k ω_k · Δω_k`.
    * Hessian expansion: `Δ|ω|² = 2 · |∇ω|² + 2 · ω · Δω`.
    * Hessian trace non-positive (local max of `|ω|²`).
    * `Δω_3 ≤ 0` (local max of `ω_3` in the local frame). -/
structure HessianLocalFrameData where
  M                   : ℝ
  gradSqNorm          : ℝ
  laplaceSqNorm       : ℝ
  laplaceOmega3       : ℝ
  omega_laplace_omega : ℝ
  omega_0_at_xstar    : ℝ
  omega_1_at_xstar    : ℝ
  omega_3_at_xstar    : ℝ
  laplace_omega_0     : ℝ
  laplace_omega_1     : ℝ
  M_nonneg            : 0 ≤ M
  /-- Local-frame alignment. -/
  omega_0_zero : omega_0_at_xstar = 0
  omega_1_zero : omega_1_at_xstar = 0
  omega_3_eq_M : omega_3_at_xstar = M
  /-- Dot-product expansion `ω · Δω = Σ_k ω_k · Δω_k`. -/
  dot_expansion :
    omega_laplace_omega
      = omega_0_at_xstar * laplace_omega_0
        + omega_1_at_xstar * laplace_omega_1
        + omega_3_at_xstar * laplaceOmega3
  /-- Hessian expansion `Δ|ω|² = 2 · |∇ω|² + 2 · ω · Δω`. -/
  hess_expansion :
    laplaceSqNorm = 2 * gradSqNorm + 2 * omega_laplace_omega
  /-- Local max of `|ω|²` → Hessian trace non-positive. -/
  hess_trace_nonpos : laplaceSqNorm ≤ 0
  /-- Local max of `ω_3` (in the local frame) → `Δω_3 ≤ 0`. -/
  laplace_nonpos : laplaceOmega3 ≤ 0

namespace HessianLocalFrameData

variable (d : HessianLocalFrameData)

/-- In the local frame, the dot-product expansion reduces to
    `ω · Δω(x*) = M · Δω_3(x*)`. -/
theorem omega_laplace_local_frame :
    d.omega_laplace_omega = d.M * d.laplaceOmega3 := by
  have h := d.dot_expansion
  rw [d.omega_0_zero, d.omega_1_zero, d.omega_3_eq_M] at h
  linarith

/-- **Wiring to `HessianAtArgmaxInputs`.**  Produces the downstream
    bundle whose `step_ii` conclusion is
    `|∇ω|²(x*) ≤ M · |Δω_3(x*)|`. -/
def toHessianAtArgmaxInputs : HessianAtArgmaxInputs where
  M                   := d.M
  gradSqNorm          := d.gradSqNorm
  laplaceSqNorm       := d.laplaceSqNorm
  laplaceOmega3       := d.laplaceOmega3
  omega_laplace_omega := d.omega_laplace_omega
  M_nonneg            := d.M_nonneg
  hess_trace_nonpos   := d.hess_trace_nonpos
  laplace_sqNorm_expansion := d.hess_expansion
  laplace_form        := d.omega_laplace_local_frame
  laplace_nonpos      := d.laplace_nonpos

/-- **Step (ii) conclusion** applied to the local-frame data. -/
theorem step_ii_local_frame :
    d.gradSqNorm ≤ d.M * |d.laplaceOmega3| :=
  d.toHessianAtArgmaxInputs.step_ii

end HessianLocalFrameData

end NSBlwChain.BLW
