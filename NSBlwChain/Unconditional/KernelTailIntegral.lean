-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib

set_option diagnostics true
set_option diagnostics.threshold 100

/-!
# Biot–Savart kernel-tail radial integral

Self-contained analytic content for Theorem 2's discharge from
`NSEvolutionAxioms`: the 1-D radial integral

  `∫_R^∞ r^{-2} dr = 1/R`     (R > 0)

is the spherical-symmetry collapse of the 3-D `‖∇K · χ_{|·|>R}‖_{L²}²`
integral after `|∇K(y)| ≤ C_K · |y|^{-3}` is fed in (`r^{-6} · r^2 =
r^{-4}` ... wait, in this normalization the strain kernel gives
`r^{-4} · r^2 = r^{-2}` after the Jacobian-volume factor; see
`paper/ns_regularity.md` §4.1).  This file proves the radial part as
a real equality consumed downstream.

## Main result

* `kernel_tail_radial_integral` — `∫ r in (R, ∞), r^{-2} = 1/R`.
-/

namespace NSBlwChain.Unconditional

open MeasureTheory Set Real

/-- **Kernel-tail radial integral.**

    For `R > 0`, the radial integral of `r ↦ r^{-2}` over `(R, ∞)` is
    exactly `1/R`. -/
theorem kernel_tail_radial_integral
    {R : ℝ} (hR : 0 < R) :
    ∫ r in Set.Ioi R, r ^ (-2 : ℝ) = 1 / R := by
  have h_exp : (-2 : ℝ) < -1 := by norm_num
  rw [integral_Ioi_rpow_of_lt h_exp hR]
  -- Goal: -R ^ (-2 + 1) / (-2 + 1) = 1 / R
  have h_sum : (-2 + 1 : ℝ) = -1 := by norm_num
  rw [h_sum]
  -- Goal: -R ^ (-1 : ℝ) / -1 = 1 / R
  have hR_nn : 0 ≤ R := le_of_lt hR
  rw [show (-1 : ℝ) = -(1 : ℝ) from rfl, Real.rpow_neg hR_nn, Real.rpow_one]
  -- Goal: -R⁻¹ / -1 = 1 / R
  field_simp

end NSBlwChain.Unconditional
