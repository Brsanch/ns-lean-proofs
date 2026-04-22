-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.BLW.VorticityAtArgmax

/-!
# Self-strain non-negativity in the growth regime

Step (iii) of Theorem 12.2 (`VorticityAtArgmaxInputs.step_iii`)
gives `ν · Δω_3(x*) = Ṁ - M · σ(x*)`.  Under the growth-regime
hypothesis `Ṁ ≥ 0` and the laplacian-non-positivity hypothesis
`Δω_3(x*) ≤ 0`, this implies `σ(x*) ≥ 0` when `M > 0`.

This is the "growth-regime sign observation" of paper §2.1 /
§12.3: at any argmax where the envelope is growing, the aligned
self-strain is non-negative.

## Contents

* `sigma_nonneg_of_growth_regime` — given
  `VorticityAtArgmaxInputs` plus `Δω_3 ≤ 0` and `Ṁ ≥ 0`, conclude
  `σ ≥ 0`.

The scalar argument: from `ν Δω_3 = Ṁ - Mσ`, `ν > 0`, `Δω_3 ≤ 0`:
  `0 ≥ ν Δω_3 = Ṁ - Mσ`, so `Mσ ≥ Ṁ ≥ 0`.  Divide by `M > 0`.
-/

namespace NSBlwChain.BLW

/-- **Self-strain non-negativity in the growth regime.**

    At any growth-regime argmax with `Δω_3 ≤ 0` and `Ṁ ≥ 0`,
    `σ(x*) ≥ 0`. -/
theorem VorticityAtArgmaxInputs.sigma_nonneg_of_growth_regime
    (h : VorticityAtArgmaxInputs)
    (h_lap : h.laplaceOmega3 ≤ 0) (h_growth : 0 ≤ h.growth) :
    0 ≤ h.sigma := by
  have h_eq := h.step_iii
  -- h_eq : h.ν * h.laplaceOmega3 = h.growth - h.M * h.sigma
  have h_prod_nonpos : h.ν * h.laplaceOmega3 ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (le_of_lt h.nu_pos) h_lap
  -- So `growth - M σ ≤ 0`, i.e. `M σ ≥ growth ≥ 0`.
  have h_Mσ_nonneg : 0 ≤ h.M * h.sigma := by linarith
  -- Divide by M > 0.
  have hM_pos := h.M_pos
  have : h.sigma = h.M * h.sigma / h.M := by
    field_simp
  rw [this]
  exact div_nonneg h_Mσ_nonneg (le_of_lt hM_pos)

end NSBlwChain.BLW
