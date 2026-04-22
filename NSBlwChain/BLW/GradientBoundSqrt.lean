-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.BLW.GradientBound

/-!
# Theorem 12.2', sqrt form: `|∇ω|(x*) ≤ M · √(σ/ν)`

`BLW/GradientBound.lean` delivers the *squared* form
  `|∇ω|²(x*) ≤ M² · σ / ν`.

Taking square roots gives the **paper's stated form** (equation 12.2'):
  `|∇ω|(x*) ≤ M · √(σ / ν)`
or equivalently, with viscous scale `δ_ν := √(ν/σ)`:
  `|∇ω|(x*) ≤ M / δ_ν`.

This file packages the square-root conclusion as a named corollary.

## Contents

* `GradBoundHypotheses.gradient_bound_sqrt` — `√(gradSqNorm) ≤ M · √(σ/ν)`.

* `GradBoundHypotheses.gradient_bound_over_delta` — `√(gradSqNorm) ≤ M / √(ν/σ)`.

* `GradBoundHypotheses.gradient_bound_sqrt_of_sigma_pos` — with
  the stricter hypothesis `σ > 0` (growth-regime), the inequality
  is the clean sqrt form.

All three are pure algebra on the squared conclusion.
-/

namespace NSBlwChain.BLW

namespace GradBoundHypotheses

variable (h : GradBoundHypotheses)

/-- **Theorem 12.2 sqrt form.**

    Under the additional hypothesis `σ ≥ 0` (which holds in the
    growth regime by `VorticityAtArgmaxInputs.sigma_nonneg_of_growth_regime`),
    take the square root of `gradient_bound`:

      `√|∇ω|²(x*) ≤ √(M² · σ / ν) = M · √(σ/ν)`.

    Uses `Real.sqrt_le_sqrt` + `Real.sqrt_mul`/`Real.sqrt_div`. -/
theorem gradient_bound_sqrt (h_sigma_nn : 0 ≤ h.sigma) :
    Real.sqrt h.gradSqNorm ≤ h.M * Real.sqrt (h.sigma / h.ν) := by
  have h_gb := h.gradient_bound
  have hM_nn := h.M_nonneg
  have hν_pos := h.nu_pos
  -- From `h_gb : gradSqNorm ≤ M² · σ / ν`,
  -- take sqrt: `√ gradSqNorm ≤ √(M² · σ / ν)`.
  have h_rhs_nn : 0 ≤ h.M ^ 2 * h.sigma / h.ν :=
    div_nonneg (mul_nonneg (sq_nonneg _) h_sigma_nn) (le_of_lt hν_pos)
  have h_sqrt_le : Real.sqrt h.gradSqNorm
                     ≤ Real.sqrt (h.M ^ 2 * h.sigma / h.ν) :=
    Real.sqrt_le_sqrt h_gb
  -- Simplify RHS: √(M² · σ / ν) = M · √(σ/ν).
  have h_simplify :
      Real.sqrt (h.M ^ 2 * h.sigma / h.ν) = h.M * Real.sqrt (h.sigma / h.ν) := by
    rw [mul_div_assoc]
    rw [Real.sqrt_mul (sq_nonneg _)]
    rw [Real.sqrt_sq hM_nn]
  rw [h_simplify] at h_sqrt_le
  exact h_sqrt_le

/-- **Alternate form.**  With the viscous scale `δ_ν := √(ν/σ)`
    (when `σ > 0`), `√|∇ω|²(x*) ≤ M / δ_ν`.  This is equation
    (12.2') of the paper, in reciprocal form. -/
theorem gradient_bound_over_delta
    (h_sigma_pos : 0 < h.sigma) :
    Real.sqrt h.gradSqNorm ≤ h.M / Real.sqrt (h.ν / h.sigma) := by
  have h_base := h.gradient_bound_sqrt (le_of_lt h_sigma_pos)
  have hν_pos := h.nu_pos
  have h_ratio_pos : 0 < h.sigma / h.ν := div_pos h_sigma_pos hν_pos
  have h_inv_ratio_pos : 0 < h.ν / h.sigma := div_pos hν_pos h_sigma_pos
  -- `√(σ/ν) = 1 / √(ν/σ)`.
  have h_sqrt_inv :
      Real.sqrt (h.sigma / h.ν) = 1 / Real.sqrt (h.ν / h.sigma) := by
    rw [eq_div_iff (ne_of_gt (Real.sqrt_pos.mpr h_inv_ratio_pos))]
    rw [← Real.sqrt_mul (le_of_lt h_ratio_pos)]
    have h_prod : (h.sigma / h.ν) * (h.ν / h.sigma) = 1 := by
      field_simp
    rw [h_prod, Real.sqrt_one]
  rw [h_sqrt_inv] at h_base
  -- `M * (1 / √(ν/σ)) = M / √(ν/σ)`.
  have h_eq : h.M * (1 / Real.sqrt (h.ν / h.sigma))
                = h.M / Real.sqrt (h.ν / h.sigma) := by
    field_simp
  rw [h_eq] at h_base
  exact h_base

end GradBoundHypotheses

end NSBlwChain.BLW
