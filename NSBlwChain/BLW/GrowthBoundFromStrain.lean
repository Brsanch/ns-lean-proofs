-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.BLW.VorticityAtArgmax

/-!
# Scalar wiring — from step (iii) + strain bound to `Ṁ ≤ 4 M² log M`

This file provides the scalar bridge from:

* `VorticityAtArgmaxInputs` (step (iii) of Theorem 12.2) — giving
  `ν · Δω_3 = Ṁ - M σ` with `Δω_3 ≤ 0`,
* a bound `σ ≤ 4 M log M` (from C4),

to the a.e. ODE ingredient consumed by the sub-Type-I rate
derivation:

  `Ṁ ≤ 4 · M² · log M`.

The derivation is pure scalar algebra:
  `Δω_3 ≤ 0` and `ν > 0` ⇒ `ν · Δω_3 ≤ 0`
  ⇒ `Ṁ - M σ ≤ 0`  (by step (iii))
  ⇒ `Ṁ ≤ M σ`      (the "pointwise Ṁ ≤ M σ" bound of §2).
  Combined with `σ ≤ 4 M log M`  ⇒  `Ṁ ≤ 4 M² log M`.

## Contents

* `growth_le_M_sigma` — pointwise `Ṁ ≤ M σ` from step (iii).
* `growth_bound_from_strain` — `Ṁ ≤ 4 M² log M` given the strain
  bound.

Both are pure algebra.  No analytical content is added.
-/

namespace NSBlwChain.BLW

/-- **Pointwise `Ṁ ≤ M σ` from step (iii).**

    Given `VorticityAtArgmaxInputs` (which carries `ν · Δω_3 = Ṁ - M σ`
    and `Δω_3 ≤ 0`), conclude `Ṁ ≤ M σ`.

    This is the scalar form of the paper's Lemma 2.1 statement
    "at a spatial maximum `x*` of `|ω|`, `Ṁ ≤ σ(x*) · M`". -/
theorem VorticityAtArgmaxInputs.growth_le_M_sigma
    (h : VorticityAtArgmaxInputs) (h_lap : h.laplaceOmega3 ≤ 0) :
    h.growth ≤ h.M * h.sigma := by
  have h_eq := h.step_iii
  -- h_eq : h.ν * h.laplaceOmega3 = h.growth - h.M * h.sigma
  -- h.ν > 0 and h.laplaceOmega3 ≤ 0 → h.ν * h.laplaceOmega3 ≤ 0.
  have h_prod_nonpos : h.ν * h.laplaceOmega3 ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (le_of_lt h.nu_pos) h_lap
  -- So h.growth - h.M * h.sigma ≤ 0.
  linarith [h_eq, h_prod_nonpos]

/-- **`Ṁ ≤ 4 M² log M` from the strain bound.**

    Given `VorticityAtArgmaxInputs` and an external strain bound
    `σ ≤ 4 · M · log M` with `M ≥ 0`, conclude `Ṁ ≤ 4 M² log M`.

    This is the pointwise precursor to §12.4 step 7 of the paper
    (the a.e. ODE `Ṁ ≤ 4 M² log M` consumed by the sub-Type-I
    integration). -/
theorem VorticityAtArgmaxInputs.growth_bound_from_strain
    (h : VorticityAtArgmaxInputs) (h_lap : h.laplaceOmega3 ≤ 0)
    (h_strain : h.sigma ≤ 4 * h.M * Real.log h.M) :
    h.growth ≤ 4 * h.M ^ 2 * Real.log h.M := by
  -- Step 1: Ṁ ≤ M σ (pointwise).
  have h1 := h.growth_le_M_sigma h_lap
  -- Step 2: multiply strain bound by M ≥ 0 to get M σ ≤ 4 M² log M.
  have hM_nn : 0 ≤ h.M := le_of_lt h.M_pos
  have h_Mσ : h.M * h.sigma ≤ h.M * (4 * h.M * Real.log h.M) :=
    mul_le_mul_of_nonneg_left h_strain hM_nn
  have h_rhs_eq :
      h.M * (4 * h.M * Real.log h.M) = 4 * h.M ^ 2 * Real.log h.M := by ring
  linarith [h1, h_Mσ, h_rhs_eq.le, h_rhs_eq.ge]

end NSBlwChain.BLW
