-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Torus.EpsteinZeta
import NSBlwChain.Caveats.C4_ImplicitBound
import NSBlwChain.BLW.LogAbsorption

/-!
# Torus correction → `ImplicitBoundBundle` bridge

This file wires the `TorusCorrectionBundle` output of
`NSBlwChain/Torus/EpsteinZeta.lean` into the C4 `ImplicitBoundBundle`.

## Shape

`TorusCorrectionBundle.torus_corrected_bound` delivers
  `σ ≤ M · (1 + C_2 + log(L/δ_ν))`.

Expanding `log(L/δ_ν) = log L + (1/2) log(σ/ν)` (via
`log_L_over_sqrt_delta`) and absorbing `C_2` into an effective
`L_eff := L · exp(C_2)` converts this to the C4 implicit form
  `σ ≤ M · (1 + log L_eff + (1/2) log(σ/ν)) + 0`.

This exactly populates an `ImplicitBoundBundle` with `K = 0`.

## Contents

* `TorusCorrectionBundle.buildImplicitBundle` — the bridge, given
  `M ≥ 1`, `σ > 0`, and the decomposition / near-far bound hypotheses.
-/

namespace NSBlwChain.BLW

open NSBlwChain NSBlwChain.Torus NSBlwChain.Caveats

/-- **Torus correction → ImplicitBoundBundle.**

    Given a `TorusCorrectionBundle` (providing `|R_L| ≤ C_2 M`), a
    near/far-field bound `σ_near_far ≤ M·(1 + log(L/δ_ν))`, the
    decomposition `σ = σ_near_far + R_L`, and `M ≥ 1` + `σ > 0`:
    produce the `ImplicitBoundBundle` with effective
    `L_eff := L · exp(C_2)` and `K := 0`.

    With `σ = σ_near_far + R_L` and `δ_ν := √(ν/σ)`, this bundle
    exactly encodes the §12.4 step 5 → step 6 self-consistency
    inequality. -/
noncomputable def TorusCorrectionBundle.buildImplicitBundle
    (b : TorusCorrectionBundle)
    (σ σ_near_far : ℝ)
    (hM_ge_one : 1 ≤ b.M) (hσ_pos : 0 < σ)
    (h_decompose : σ = σ_near_far + b.RL)
    (h_near_far :
      σ_near_far ≤ b.M * (1 + Real.log (b.L / Real.sqrt (b.ν / σ)))) :
    ImplicitBoundBundle where
  ν := b.ν
  L := b.L * Real.exp b.C_2
  M := b.M
  σ := σ
  K := 0
  hν_pos := b.ν_pos
  hL_pos :=
    mul_pos b.L_pos (Real.exp_pos _)
  hM_ge_one := hM_ge_one
  hσ_pos := hσ_pos
  hK_nonneg := le_refl 0
  hImplicit := by
    -- Step 1: σ ≤ M · (1 + C_2 + log(L / δ_ν))  via torus_corrected_bound.
    have h_torus :=
      torus_corrected_bound b σ σ_near_far (Real.sqrt (b.ν / σ))
        h_decompose h_near_far
    -- h_torus : σ ≤ b.M * (1 + b.C_2 + Real.log (b.L / Real.sqrt (b.ν / σ)))
    -- Step 2: log(L/√(ν/σ)) = log L + (1/2) log(σ/ν).
    have h_log := log_L_over_sqrt_delta b.L_pos b.ν_pos hσ_pos
    rw [h_log] at h_torus
    -- h_torus : σ ≤ b.M * (1 + b.C_2 + (log b.L + (1/2) log (σ / b.ν)))
    -- Step 3: log(L · exp C_2) = log L + C_2.
    have h_log_eff :
        Real.log (b.L * Real.exp b.C_2) = Real.log b.L + b.C_2 := by
      have hL_ne : b.L ≠ 0 := ne_of_gt b.L_pos
      have he_ne : Real.exp b.C_2 ≠ 0 := Real.exp_ne_zero _
      rw [Real.log_mul hL_ne he_ne, Real.log_exp]
    rw [h_log_eff]
    linarith [h_torus]

end NSBlwChain.BLW
