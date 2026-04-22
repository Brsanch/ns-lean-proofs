-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Setup.ClassicalAxioms
import NSBlwChain.Caveats.C4_ImplicitBound
import NSBlwChain.BLW.ArgmaxIdentities
import NSBlwChain.BLW.GradientBound
import NSBlwChain.BLW.ClassicalAxiomDischarge

/-!
# `ArgmaxAnalyticalBundle` → `ImplicitBoundBundle` via the Biot-Savart axiom

This file wires an `ArgmaxAnalyticalBundle` (the unified bundle from
`BLW/ArgmaxIdentities.lean` packaging steps (ii), (iii), and the
growth-regime hypothesis) together with the `BiotSavartSelfStrainBound`
axiom into a `σ ≤ 4 M log M` conclusion, modulo the C4 largeness
hypothesis.

## Shape

`ArgmaxAnalyticalBundle` guarantees:
  `|∇ω|²(x*) ≤ M² · σ / ν`     (via `gradient_bound`).

`BiotSavartSelfStrainBound u ν T` guarantees (for every `(M, σ)`):
  `σ ≤ M · (1 + C_L + log(L / √(ν/σ)))`.

Discharging the Biot-Savart axiom output at the analytical-bundle's
`(M, σ)` via `sigma_le_4M_log_M_from_axiom` delivers `σ ≤ 4 M log M`.

## Contents

* `sigma_le_4M_log_M_of_analytical` — end-to-end: given the bundle,
  the axiom, and the C4 largeness hypothesis, deliver
  `σ ≤ 4 · M · log M`.
-/

namespace NSBlwChain.BLW

open NSBlwChain NSBlwChain.Caveats

/-- **End-to-end.**  From the analytical bundle + Biot-Savart axiom +
    C4 largeness hypothesis, conclude `σ ≤ 4 · M · log M`.

    This is a one-line re-export of `sigma_le_4M_log_M_from_axiom`
    with the scalars supplied from the analytical bundle. -/
theorem sigma_le_4M_log_M_of_analytical
    {u : VelocityField} {ν T : ℝ}
    (a : ArgmaxAnalyticalBundle) (hν_agree : a.ν = ν)
    (bs : BiotSavartSelfStrainBound u ν T)
    (hM_ge_one : 1 ≤ a.M) (hσ_pos : 0 < a.sigma)
    (hLarge :
      1 + Real.log (bs.L * Real.exp bs.C_L)
        + (1 / 2) * Real.log (a.sigma / ν)
          ≤ 4 * Real.log a.M - 0 / a.M) :
    a.sigma ≤ 4 * a.M * Real.log a.M := by
  have hν_pos : 0 < ν := by rw [← hν_agree]; exact a.nu_pos
  exact sigma_le_4M_log_M_from_axiom bs a.M a.sigma hM_ge_one hσ_pos hν_pos hLarge

end NSBlwChain.BLW
