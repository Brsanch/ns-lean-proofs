-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Setup.ClassicalAxioms
import NSBlwChain.Caveats.C4_ImplicitBound
import NSBlwChain.BLW.GradientBound
import NSBlwChain.BLW.ArgmaxIdentities
import NSBlwChain.BLW.HessianAtArgmax
import NSBlwChain.BLW.VorticityAtArgmax
import NSBlwChain.BLW.ArgmaxStepsCompose
import NSBlwChain.BLW.ClassicalAxiomDischarge
import NSBlwChain.BLW.GrowthBoundFromStrain

/-!
# Full scalar chain — from steps (i)-(iii) + axioms to `Ṁ ≤ 4 M² log M`

This file composes all the scalar-algebra pieces of the BLW chain
into a single named theorem:

  from the step (ii) and step (iii) hypothesis bundles +
       the `BiotSavartSelfStrainBound` axiom +
       the C4 largeness hypothesis,
  conclude the pointwise bound `Ṁ(t) ≤ 4 · M(t)² · log M(t)`,
  which is the ODE precursor consumed by `SubTypeOneRate`.

## Chain

1. `ArgmaxAnalyticalBundle.ofSteps` — composes step (ii), step (iii),
   and growth-regime hypothesis into `ArgmaxAnalyticalBundle`.
2. `ArgmaxAnalyticalBundle.gradient_bound` — delivers
   `|∇ω|²(x*) ≤ M² · σ / ν`.
3. `sigma_le_4M_log_M_from_axiom` — combines the Biot–Savart axiom
   output with the implicit-bound largeness to deliver
   `σ(x*) ≤ 4 · M · log M`.
4. `VorticityAtArgmaxInputs.growth_bound_from_strain` — combines
   step (iii) with the strain bound to deliver
   `Ṁ ≤ 4 · M² · log M`.

All four pieces are already machine-verified; this file is a
one-line composition.
-/

namespace NSBlwChain.BLW

open NSBlwChain NSBlwChain.Caveats

/-- **Full scalar chain.**

    Given:
    * Step (ii) bundle `h₂` and step (iii) bundle `h₃` with shared
      scalars (compatibility `hc`) and growth-regime hypothesis `hg`.
    * The `BiotSavartSelfStrainBound` axiom output `bs`.
    * The C4 largeness hypothesis `hLarge` for the relevant `(M, σ, ν)`.
    * `M ≥ 1`, `σ > 0` (the scalars agree across bundles).

    Conclude: `Ṁ ≤ 4 · M² · log M`. -/
theorem full_scalar_chain
    {u : VelocityField} {ν T : ℝ}
    (h₂ : HessianAtArgmaxInputs) (h₃ : VorticityAtArgmaxInputs)
    (hc : StepsCompatibility h₂ h₃)
    (hg : 0 ≤ h₃.growth)
    (bs : BiotSavartSelfStrainBound u ν T)
    (hν_agree : h₃.ν = ν)
    (hM_ge_one : 1 ≤ h₃.M)
    (hσ_pos : 0 < h₃.sigma)
    (hLarge :
      1 + Real.log (bs.L * Real.exp bs.C_L)
        + (1 / 2) * Real.log (h₃.sigma / h₃.ν)
          ≤ 4 * Real.log h₃.M - 0 / h₃.M) :
    h₃.growth ≤ 4 * h₃.M ^ 2 * Real.log h₃.M := by
  -- Step 3: invoke the axiom discharge for σ ≤ 4 M log M.
  have hν_pos : 0 < ν := by rw [← hν_agree]; exact h₃.nu_pos
  have h_strain :
      h₃.sigma ≤ 4 * h₃.M * Real.log h₃.M := by
    have h_rewrite :
        (1 + Real.log (bs.L * Real.exp bs.C_L)
          + (1 / 2) * Real.log (h₃.sigma / ν))
        = (1 + Real.log (bs.L * Real.exp bs.C_L)
            + (1 / 2) * Real.log (h₃.sigma / h₃.ν)) := by
      rw [hν_agree]
    have hLarge' :
        1 + Real.log (bs.L * Real.exp bs.C_L)
          + (1 / 2) * Real.log (h₃.sigma / ν)
            ≤ 4 * Real.log h₃.M - 0 / h₃.M := by
      rw [h_rewrite]; exact hLarge
    have := sigma_le_4M_log_M_from_axiom bs h₃.M h₃.sigma h₃.growth
      hM_ge_one hσ_pos hν_pos hg hLarge'
    -- this : h₃.sigma ≤ 4 * h₃.M * Real.log h₃.M
    exact this
  -- Step 4: combine step (iii) with strain bound.
  have h_lap := by
    -- Δω_3 ≤ 0 comes from h₂.laplace_nonpos + hc.laplace_eq.
    have := h₂.laplace_nonpos
    rw [hc.laplace_eq] at this
    exact this
  exact h₃.growth_bound_from_strain h_lap h_strain

end NSBlwChain.BLW
