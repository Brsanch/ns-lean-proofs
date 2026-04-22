-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.BLW.HessianAtArgmaxFromFrame
import NSBlwChain.BLW.MaxPrinciple

/-!
# `HessianLocalFrameData.hess_trace_nonpos` discharge via `MaxPrinciple`

`HessianLocalFrameData` (from `BLW/HessianAtArgmaxFromFrame.lean`)
takes `hess_trace_nonpos : laplaceSqNorm ≤ 0` as a field hypothesis.
`MaxPrinciple.laplace_nonpos_of_localMax` delivers exactly this
conclusion from a `ScalarLocalMaxSecondDeriv` bundle + a
sum-expansion identity.

This file provides the one-line composition: given the scalar
local-max data + the sum-expansion hypothesis, produce a
`HessianLocalFrameData` field-filled.

## Contents

* `HessianLocalFrameData.ofMaxPrinciple` — constructor taking the
  MaxPrinciple bundle + the expansion identity + the remaining
  scalar hypotheses for `HessianLocalFrameData`, and discharging
  `hess_trace_nonpos` automatically.
-/

namespace NSBlwChain.BLW

/-- **`HessianLocalFrameData` from scalar MaxPrinciple data.**

    The `hess_trace_nonpos` field is discharged from
    `laplace_nonpos_of_localMax` applied to the MaxPrinciple bundle.
    All other fields are passed through as arguments.

    Convention: `s` is the MaxPrinciple bundle whose three second
    derivatives sum to `laplaceSqNorm`.  The sum hypothesis is
    `h_sum_form`. -/
def HessianLocalFrameData.ofMaxPrinciple
    (M gradSqNorm laplaceSqNorm laplaceOmega3 omega_laplace_omega : ℝ)
    (omega_0_at_xstar omega_1_at_xstar omega_3_at_xstar : ℝ)
    (laplace_omega_0 laplace_omega_1 : ℝ)
    (M_nonneg : 0 ≤ M)
    (s : ScalarLocalMaxSecondDeriv)
    (h_sum_form : ScalarLaplacianSumFormHyp laplaceSqNorm s.d0 s.d1 s.d2)
    (hess_expansion :
      laplaceSqNorm = 2 * gradSqNorm + 2 * omega_laplace_omega)
    (omega_0_zero : omega_0_at_xstar = 0)
    (omega_1_zero : omega_1_at_xstar = 0)
    (omega_3_eq_M : omega_3_at_xstar = M)
    (dot_expansion :
      omega_laplace_omega
        = omega_0_at_xstar * laplace_omega_0
          + omega_1_at_xstar * laplace_omega_1
          + omega_3_at_xstar * laplaceOmega3)
    (laplace_nonpos : laplaceOmega3 ≤ 0) :
    HessianLocalFrameData where
  M                    := M
  gradSqNorm           := gradSqNorm
  laplaceSqNorm        := laplaceSqNorm
  laplaceOmega3        := laplaceOmega3
  omega_laplace_omega  := omega_laplace_omega
  omega_0_at_xstar     := omega_0_at_xstar
  omega_1_at_xstar     := omega_1_at_xstar
  omega_3_at_xstar     := omega_3_at_xstar
  laplace_omega_0      := laplace_omega_0
  laplace_omega_1      := laplace_omega_1
  M_nonneg             := M_nonneg
  omega_0_zero         := omega_0_zero
  omega_1_zero         := omega_1_zero
  omega_3_eq_M         := omega_3_eq_M
  dot_expansion        := dot_expansion
  hess_expansion       := hess_expansion
  hess_trace_nonpos    := laplace_nonpos_of_localMax s h_sum_form
  laplace_nonpos       := laplace_nonpos

end NSBlwChain.BLW
