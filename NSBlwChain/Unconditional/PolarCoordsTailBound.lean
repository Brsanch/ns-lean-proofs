-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Unconditional.KernelTailIntegral
import NSBlwChain.Unconditional.FarFieldFromKernelTail

set_option diagnostics true
set_option diagnostics.threshold 100

/-!
# Polar-coordinates collapse for the kernel-tail integral

Reduces `BiotSavartKernelTailBundle.kernelTailSq_eq` to **one named
structural identity** plus the **already-proven**
`kernel_tail_radial_integral` (`∫_R^∞ r⁻² = 1/R`).

## Strategy

The 3-D Lebesgue integral of the radially-symmetric function
`y ↦ C_K² · |y|⁻⁴` over `{y : |y| > R}` collapses, by the
polar-coords change of variables on ℝ³, to

  `4π · ∫_R^∞ C_K² · r⁻⁴ · r² dr = 4π · C_K² · ∫_R^∞ r⁻² dr
                                  = 4π · C_K² / R`.

The polar-coords step (the cube‐to‐radial collapse) is the only
analytical content not yet in the build chain.  This file isolates
it as a **single named hypothesis** `KernelTailRadialIdentity`
whose statement is exactly the equality

  `kernelTailSq = 4π · C_K² · ∫_R^∞ r⁻² dr`.

The composition with `kernel_tail_radial_integral` (this session,
proved) then gives the closed-form `4π · C_K² / R` consumed by
`BiotSavartKernelTailBundle.kernelTailSq_eq` — fully discharged
from the named radial identity, no further analytic input required.

This refactors the structural status of `kernelTailSq_eq` into:

  *one* named radial identity (cleanly stated, future-discharge target)
  *one* fully-verified mathlib lemma (`integral_Ioi_rpow_of_lt`).

The radial identity itself is a one-step polar-coords application
that requires routing `Vec3 = Fin 3 → ℝ` through
`EuclideanSpace ℝ (Fin 3)` to apply mathlib's
`MeasureTheory.integral_fun_norm_addHaar` family — a multi-session
cross-instance project bracketed out here.

## Main result

* `kernelTail_value_via_radial_identity` — closed-form value for
  `kernelTailSq` from the named radial identity + the proven
  `kernel_tail_radial_integral`.
* `BiotSavartKernelTailBundle.ofRadialIdentity` — discharge
  constructor: builds the bundle from a radial-identity witness
  plus positivity hypotheses.
-/

namespace NSBlwChain.Unconditional

open Real

/-- **Named radial identity for the kernel-tail integral.**

    For positive `R`, `C_K`, `kernelTailSq`, asserts the polar-coords
    collapse identity

      `kernelTailSq = 4π · C_K² · ∫_R^∞ r⁻² dr`.

    Discharged via the standard `Vec3` → `EuclideanSpace ℝ (Fin 3)`
    polar coords on ℝ³ (a multi-session mathlib hookup); taken here
    as a named hypothesis. -/
def KernelTailRadialIdentity (R C_K kernelTailSq : ℝ) : Prop :=
  kernelTailSq = 4 * Real.pi * C_K ^ 2 * ∫ r in Set.Ioi R, r ^ (-(2 : ℝ))

/-- **Closed-form value for the kernel-tail integral.**

    From the named radial identity (`KernelTailRadialIdentity`) and
    the proven `kernel_tail_radial_integral`
    (`∫_R^∞ r⁻² dr = 1/R`), conclude
    `kernelTailSq = 4π · C_K² / R`. -/
theorem kernelTail_value_via_radial_identity
    {R C_K kernelTailSq : ℝ} (hR_pos : 0 < R)
    (h_radial : KernelTailRadialIdentity R C_K kernelTailSq) :
    kernelTailSq = 4 * Real.pi * C_K ^ 2 / R := by
  unfold KernelTailRadialIdentity at h_radial
  rw [kernel_tail_radial_integral hR_pos] at h_radial
  -- h_radial : kernelTailSq = 4 * π * C_K² * (1/R)
  rw [h_radial]
  field_simp

/-- **`BiotSavartKernelTailBundle` constructor from the radial identity.**

    Given:
    * positive `R, C_K`,
    * non-neg `kernelTailSq`,
    * the named radial identity `KernelTailRadialIdentity R C_K kernelTailSq`,

    discharge the bundle's `kernelTailSq_eq` field automatically. -/
theorem BiotSavartKernelTailBundle.ofRadialIdentity
    {R C_K kernelTailSq : ℝ} (hR_pos : 0 < R) (hCK_pos : 0 < C_K)
    (hKtail_nn : 0 ≤ kernelTailSq)
    (h_radial : KernelTailRadialIdentity R C_K kernelTailSq) :
    BiotSavartKernelTailBundle R C_K kernelTailSq :=
  { R_pos := hR_pos
    C_K_pos := hCK_pos
    kernelTailSq_nonneg := hKtail_nn
    kernelTailSq_eq :=
      kernelTail_value_via_radial_identity hR_pos h_radial }

end NSBlwChain.Unconditional
