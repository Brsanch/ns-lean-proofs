-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Setup.VectorFields
import NSBlwChain.Setup.NSHypothesis
import NSBlwChain.Setup.ClassicalAxioms
import NSBlwChain.Caveats.C4_ImplicitBound
import NSBlwChain.BLW.LogAbsorption

/-!
# Discharge: `BiotSavartSelfStrainBound` → `ImplicitBoundBundle`

This file provides the direct bridge from the classical axiom
`biot_savart_self_strain_bound`'s output `BiotSavartSelfStrainBound`
to an `ImplicitBoundBundle` for specific `(M, σ, ν)`.

## Shape

`BiotSavartSelfStrainBound u ν T` provides:
  `∀ M σ, 0 ≤ M → 0 < σ → 0 < ν → σ ≤ M · (1 + C_L + log(L/√(ν/σ)))`,

which after log-expansion via `log_L_over_sqrt_delta` becomes:
  `σ ≤ M · (1 + C_L + log L + (1/2) · log(σ/ν))`,
i.e.,
  `σ ≤ M · (1 + log L + (1/2) · log(σ/ν)) + M · C_L`.

This has the C4 shape `σ ≤ M · (1 + log L + (1/2) log(σ/ν)) + K`
with `K = M · C_L`.

For the C4 bundle to apply cleanly, we need `K` to be a constant
independent of `M` — which is *not* what `M · C_L` is.  The standard
workaround is to absorb the constant into an effective `L`:
`L_eff := L · exp(C_L)`, since
  `log(L_eff) = log L + C_L`,
and then `K_eff = 0`.

## Contents

* `buildImplicitBundleFromAxiom` — given the axiom output, an
  ArgmaxAnalyticalBundle (providing `M`, `σ`), and the positivity
  hypotheses, produce an `ImplicitBoundBundle` with `L_eff = L · e^{C_L}`
  and `K_eff = 0`.
-/

namespace NSBlwChain.BLW

open NSBlwChain NSBlwChain.Caveats

/-- **Axiom → ImplicitBoundBundle bridge.**

    Takes the raw output of `biot_savart_self_strain_bound` (a
    `BiotSavartSelfStrainBound`) and a specific `(M, σ, ν)` triple
    plus positivity / largeness hypotheses, and produces the
    corresponding `ImplicitBoundBundle`.

    Effective torus side: `L_eff = L · exp(C_L)`, so that
    `1 + log(L_eff) = 1 + log L + C_L`, matching the axiom's
    `(1 + C_L + log L + (1/2) log(σ/ν))` form with `K = 0`. -/
noncomputable def buildImplicitBundleFromAxiom
    {u : VelocityField} {ν T : ℝ}
    (bs : BiotSavartSelfStrainBound u ν T)
    (M σ : ℝ) (hM : 1 ≤ M) (hσ : 0 < σ) (hν : 0 < ν) :
    ImplicitBoundBundle where
  ν := ν
  L := bs.L * Real.exp bs.C_L
  M := M
  σ := σ
  K := 0
  hν_pos := hν
  hL_pos := by
    have h_pos : 0 < Real.exp bs.C_L := Real.exp_pos _
    exact mul_pos bs.L_pos h_pos
  hM_ge_one := hM
  hσ_pos := hσ
  hK_nonneg := le_refl 0
  hImplicit := by
    -- Step 1: invoke the axiom bound for this specific (M, σ).
    have h_ax := bs.bound M σ (le_trans zero_le_one hM) hσ hν
    -- h_ax : σ ≤ M · (1 + C_L + log(L/√(ν/σ)))
    -- Step 2: log-expand via log_L_over_sqrt_delta.
    have h_log : Real.log (bs.L / Real.sqrt (ν / σ))
                   = Real.log bs.L + (1 / 2) * Real.log (σ / ν) :=
      log_L_over_sqrt_delta bs.L_pos hν hσ
    rw [h_log] at h_ax
    -- h_ax : σ ≤ M · (1 + C_L + log L + (1/2) log(σ/ν))
    -- Target: σ ≤ M · (1 + log(L · e^{C_L}) + (1/2) log(σ/ν)) + 0.
    have h_log_eff :
        Real.log (bs.L * Real.exp bs.C_L) = Real.log bs.L + bs.C_L := by
      have hL_ne : bs.L ≠ 0 := ne_of_gt bs.L_pos
      have he_ne : Real.exp bs.C_L ≠ 0 := Real.exp_ne_zero _
      rw [Real.log_mul hL_ne he_ne, Real.log_exp]
    rw [h_log_eff]
    linarith [h_ax]

/-- **Axiom → σ ≤ 4 M log M.**

    End-to-end: from `BiotSavartSelfStrainBound` + positivity +
    a largeness hypothesis, conclude `σ ≤ 4 M log M`. -/
theorem sigma_le_4M_log_M_from_axiom
    {u : VelocityField} {ν T : ℝ}
    (bs : BiotSavartSelfStrainBound u ν T)
    (M σ : ℝ) (hM : 1 ≤ M) (hσ : 0 < σ) (hν : 0 < ν)
    (hLarge :
      1 + Real.log (bs.L * Real.exp bs.C_L) + (1 / 2) * Real.log (σ / ν)
        ≤ 4 * Real.log M - 0 / M) :
    σ ≤ 4 * M * Real.log M :=
  (buildImplicitBundleFromAxiom bs M σ hM hσ hν).σ_le_of_largeness hLarge

end NSBlwChain.BLW
