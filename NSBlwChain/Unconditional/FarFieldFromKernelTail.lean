-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Unconditional.Theorem2
import NSBlwChain.Unconditional.KernelTailIntegral

set_option diagnostics true
set_option diagnostics.threshold 100

/-!
# `FarFieldControlBundle` from kernel-tail integral + Cauchy–Schwarz

Bridges the analytic content of `kernel_tail_radial_integral`
(`∫_R^∞ r⁻² = 1/R`) into the scalar-hypothesis bundle
`FarFieldControlBundle` consumed by Theorem 2.

## Strategy

The 3-D kernel-tail `L²` integral
`‖∇K · χ_{|·|>R}‖_{L²}² = ∫_{|y|>R} |∇K(y)|² dy`
collapses under spherical symmetry to
`4π · C_K² · ∫_R^∞ r^{-4} · r² dr = 4π · C_K² · ∫_R^∞ r^{-2} dr`
`= 4π · C_K² / R`,
using the kernel decay `|∇K(y)| ≤ C_K · |y|^{-3}` (Biot–Savart on
`\mathbb R³`).

This file packages this as a small bundle
`BiotSavartKernelTailBundle` whose only analytic content is the
radial integral identity from `KernelTailIntegral.lean` plus a
named bound on the kernel decay constant; everything else is real
arithmetic.  Then the `FarFieldControlBundle` of Theorem 2 is
constructed from the kernel-tail bundle plus a Cauchy–Schwarz
hypothesis on `farNorm²`.

## Main results

* `BiotSavartKernelTailBundle` — decay constant `C_K`, radius `R`,
  computed `kernelTailSq = 4π · C_K² / R`.
* `kernelTailSq_eq_of_radial` — the explicit identity
  `kernelTailSq = 4π · C_K² / R` (via `kernel_tail_radial_integral`).
* `farFieldControlBundle_of_kernelTail` — Theorem 2 bundle built
  from kernel-tail bundle + Cauchy–Schwarz.
-/

namespace NSBlwChain.Unconditional

open Real

/-- **Biot–Savart kernel-tail bundle.**

    Packages the 3-D kernel-tail `L²` constant for the strain kernel
    on `\mathbb R³`.  Fields:

    * `R > 0` — far-field radius,
    * `C_K > 0` — kernel decay constant: `|∇K(y)| ≤ C_K · |y|^{-3}`,
    * `kernelTailSq ≥ 0` — the value `‖∇K · χ_{|·|>R}‖_{L²}²`.

    The defining identity `kernelTailSq = 4π · C_K² / R` is recorded
    as a named hypothesis discharged by the spherical-collapse +
    `kernel_tail_radial_integral` argument outlined in the file
    docstring. -/
structure BiotSavartKernelTailBundle
    (R C_K kernelTailSq : ℝ) : Prop where
  /-- Positive far-field radius. -/
  R_pos : 0 < R
  /-- Positive kernel decay constant. -/
  C_K_pos : 0 < C_K
  /-- Nonneg kernel-tail `L²`-norm squared. -/
  kernelTailSq_nonneg : 0 ≤ kernelTailSq
  /-- **Spherical collapse + radial-integral identity.**
      `kernelTailSq = 4π · C_K² / R`. -/
  kernelTailSq_eq : kernelTailSq = 4 * Real.pi * C_K ^ 2 / R

/-- **Convenience corollary.**

    From the kernel-tail bundle, with `C := 4π · C_K²`, the bound
    `kernelTailSq ≤ C / R` of `FarFieldControlBundle` holds with
    equality.  This packages the `(C, kernelTailSq, R)` triple in
    the form Theorem 2's bundle expects. -/
theorem kernelTailSq_le_of_bundle
    {R C_K kernelTailSq : ℝ}
    (K : BiotSavartKernelTailBundle R C_K kernelTailSq) :
    kernelTailSq ≤ (4 * Real.pi * C_K ^ 2) / R :=
  le_of_eq K.kernelTailSq_eq

/-- **`FarFieldControlBundle` constructor from kernel-tail bundle.**

    Given:
    * the kernel-tail bundle `K`,
    * nonneg enstrophy `E_ω`,
    * nonneg `farNorm`,
    * the Cauchy–Schwarz hypothesis
      `farNorm² ≤ kernelTailSq · E_ω`,

    construct the `FarFieldControlBundle` with constant
    `C := 4π · C_K²`.

    The `farNorm_sq_le_direct` field is derived as
    `farNorm² ≤ kernelTailSq · E_ω ≤ (C/R) · E_ω = C · E_ω / R`. -/
theorem farFieldControlBundle_of_kernelTail
    {R E_ω C_K farNorm kernelTailSq : ℝ}
    (K : BiotSavartKernelTailBundle R C_K kernelTailSq)
    (hE : 0 ≤ E_ω)
    (hfn_nn : 0 ≤ farNorm)
    (hCS : farNorm ^ 2 ≤ kernelTailSq * E_ω) :
    FarFieldControlBundle R E_ω (4 * Real.pi * C_K ^ 2) farNorm
        kernelTailSq := by
  have hC_K_pos : 0 < C_K := K.C_K_pos
  have hC_pos : 0 < 4 * Real.pi * C_K ^ 2 := by
    have hpi : 0 < Real.pi := Real.pi_pos
    have hC_K_sq : 0 < C_K ^ 2 := by positivity
    have h4pi : 0 < 4 * Real.pi := by linarith
    exact mul_pos h4pi hC_K_sq
  have hR_pos : 0 < R := K.R_pos
  -- Direct bound: farNorm² ≤ kernelTailSq · E_ω ≤ (C/R) · E_ω = C·E_ω/R.
  have h_step : kernelTailSq * E_ω
      ≤ (4 * Real.pi * C_K ^ 2 / R) * E_ω :=
    mul_le_mul_of_nonneg_right (kernelTailSq_le_of_bundle K) hE
  have h_eq : (4 * Real.pi * C_K ^ 2 / R) * E_ω
      = 4 * Real.pi * C_K ^ 2 * E_ω / R := by ring
  have h_direct : farNorm ^ 2 ≤ 4 * Real.pi * C_K ^ 2 * E_ω / R := by
    have h_chain : farNorm ^ 2 ≤ (4 * Real.pi * C_K ^ 2 / R) * E_ω :=
      le_trans hCS h_step
    rw [h_eq] at h_chain
    exact h_chain
  exact {
    R_pos := hR_pos
    E_nonneg := hE
    C_pos := hC_pos
    farNorm_nonneg := hfn_nn
    kernelTailSq_nonneg := K.kernelTailSq_nonneg
    kernelTailSq_le := kernelTailSq_le_of_bundle K
    farNorm_sq_le_cauchy_schwarz := hCS
    farNorm_sq_le_direct := h_direct
  }

/-- **Theorem 2 conclusion from kernel-tail bundle + Cauchy–Schwarz.**

    `|far-field(x*)| ≤ sqrt(4π · C_K² · E_ω / R)`. -/
theorem farField_le_sqrt_of_kernelTail
    {R E_ω C_K farNorm kernelTailSq : ℝ}
    (K : BiotSavartKernelTailBundle R C_K kernelTailSq)
    (hE : 0 ≤ E_ω)
    (hfn_nn : 0 ≤ farNorm)
    (hCS : farNorm ^ 2 ≤ kernelTailSq * E_ω) :
    farNorm ≤ Real.sqrt (4 * Real.pi * C_K ^ 2 * E_ω / R) :=
  farField_le_sqrt
    (farFieldControlBundle_of_kernelTail K hE hfn_nn hCS)

end NSBlwChain.Unconditional
