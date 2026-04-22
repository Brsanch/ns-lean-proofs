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
axiom into a ready-to-consume `ImplicitBoundBundle` for the
self-consistency analysis of C4.

## Shape

`ArgmaxAnalyticalBundle` guarantees:
  `|∇ω|²(x*) ≤ M² · σ / ν`     (via `gradient_bound`).

`BiotSavartSelfStrainBound u ν T` guarantees (for every `(M, σ)`):
  `σ ≤ M · (1 + C_L + log(L / √(ν/σ)))`.

Discharging the Biot-Savart axiom output at the analytical-bundle's
`(M, σ)`, plus the log-expansion identity, delivers an
`ImplicitBoundBundle` with `L_eff := L · exp(C_L)` and `K := 0`.

## Contents

* `ArgmaxAnalyticalBundle.toImplicitBoundBundle_viaAxiom` — the
  one-step composition: given the analytical bundle + Biot-Savart
  axiom + `M ≥ 1` hypothesis, produce the C4 bundle.

* `sigma_le_4M_log_M_of_analytical` — end-to-end: given the bundle,
  the axiom, and the C4 largeness hypothesis, deliver
  `σ ≤ 4 · M · log M`.
-/

namespace NSBlwChain.BLW

open NSBlwChain NSBlwChain.Caveats

/-- **ArgmaxAnalyticalBundle → ImplicitBoundBundle** via the axiom.

    Discharges the implicit inequality at the scalars `(a.M, a.sigma,
    a.ν)`, requiring `M ≥ 1` and `σ > 0` as the additional hypotheses
    consumed by C4. -/
noncomputable def ArgmaxAnalyticalBundle.toImplicitBoundBundle_viaAxiom
    {u : VelocityField} {ν T : ℝ}
    (a : ArgmaxAnalyticalBundle) (hν_agree : a.ν = ν)
    (bs : BiotSavartSelfStrainBound u ν T)
    (hM_ge_one : 1 ≤ a.M) (hσ_pos : 0 < a.sigma) :
    ImplicitBoundBundle :=
  buildImplicitBundleFromAxiom (ν := ν)
    bs a.M a.sigma hM_ge_one hσ_pos
    (by rw [← hν_agree]; exact a.nu_pos)

/-- **End-to-end.**  From the analytical bundle + Biot-Savart axiom +
    C4 largeness hypothesis, conclude `σ ≤ 4 · M · log M`. -/
theorem sigma_le_4M_log_M_of_analytical
    {u : VelocityField} {ν T : ℝ}
    (a : ArgmaxAnalyticalBundle) (hν_agree : a.ν = ν)
    (bs : BiotSavartSelfStrainBound u ν T)
    (hM_ge_one : 1 ≤ a.M) (hσ_pos : 0 < a.sigma)
    (hLarge :
      1 + Real.log (bs.L * Real.exp bs.C_L)
        + (1 / 2) * Real.log (a.sigma / a.ν)
          ≤ 4 * Real.log a.M - 0 / a.M) :
    a.sigma ≤ 4 * a.M * Real.log a.M := by
  have bundle :=
    a.toImplicitBoundBundle_viaAxiom hν_agree bs hM_ge_one hσ_pos
  -- The bundle's fields are a.ν, a.M, a.sigma, etc.
  -- Apply `σ_le_of_largeness` on the constructed bundle.
  -- Note: the bundle's L is bs.L * Real.exp bs.C_L, matches hLarge.
  exact bundle.σ_le_of_largeness (by
    -- bundle.ν = ν, bundle.σ = a.sigma, bundle.L = bs.L * exp bs.C_L.
    -- Goal: 1 + log (bundle.L) + (1/2) log (bundle.σ / bundle.ν)
    --         ≤ 4 log bundle.M - bundle.K / bundle.M.
    -- Substituting: 1 + log (bs.L · exp bs.C_L) + (1/2) log (a.sigma / ν)
    --         ≤ 4 log a.M - 0 / a.M.
    -- We have hLarge in terms of a.ν; convert to ν via hν_agree.
    have : a.sigma / a.ν = a.sigma / ν := by rw [hν_agree]
    rw [this] at hLarge
    exact hLarge)

end NSBlwChain.BLW
