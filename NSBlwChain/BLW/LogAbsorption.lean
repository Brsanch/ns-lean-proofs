-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Setup.VectorFields
import NSBlwChain.Setup.NSHypothesis

/-!
# Log-absorption chain (§12.4 algebraic pieces)

This file formalizes the *algebraic* portions of §12.4's log-absorption
argument.  The full chain combines these with the three named classical
axioms (Biot–Savart identity, Seregin exclusion, Kato analyticity);
this file contains only the parts that are pure real-analysis algebra
on scalars.

## What lives here

* **`log_L_over_sqrt_delta`** — step 5→6 algebraic expansion:
  `log(L / √(ν/σ)) = log L + (1/2) · log(σ/ν)`.  Converts the
  geometric-mean splitting scale `δ_ν = √(ν/σ)` into a log-additive form.

* **`sigma_le_log_selfConsistent_of_linear_bound`** — step 5 → 6
  repackaging: from `σ ≤ M · (1 + C + log(L/δ_ν))` with
  `δ_ν = √(ν/σ)`, conclude `σ ≤ M · (1 + C + log L + (1/2) · log(σ/ν))`.

The full Banach fixed-point step (C4) and the ODE integration (C1) are
handled in the respective caveat files.
-/

namespace NSBlwChain.BLW

open Real

/-- Step 5→6 algebraic expansion.  With `δ_ν := √(ν/σ)`,
    `log(L / δ_ν) = log L + (1/2) log(σ/ν)`.  All inputs strictly
    positive. -/
lemma log_L_over_sqrt_delta
    {L ν σ : ℝ} (hL : 0 < L) (hν : 0 < ν) (hσ : 0 < σ) :
    Real.log (L / Real.sqrt (ν / σ))
      = Real.log L + (1 / 2) * Real.log (σ / ν) := by
  have hνσ_pos : 0 < ν / σ := div_pos hν hσ
  have hsqrt_pos : 0 < Real.sqrt (ν / σ) := Real.sqrt_pos.mpr hνσ_pos
  have hsqrt_ne : Real.sqrt (ν / σ) ≠ 0 := ne_of_gt hsqrt_pos
  have hL_ne : L ≠ 0 := ne_of_gt hL
  have hσν_pos : 0 < σ / ν := div_pos hσ hν
  -- log(L / √(ν/σ)) = log L - log (√(ν/σ))
  --                = log L - (1/2) · log(ν/σ)
  --                = log L + (1/2) · log(σ/ν).
  have h_div : Real.log (L / Real.sqrt (ν / σ))
                 = Real.log L - Real.log (Real.sqrt (ν / σ)) :=
    Real.log_div hL_ne hsqrt_ne
  have h_sqrt : Real.log (Real.sqrt (ν / σ)) = Real.log (ν / σ) / 2 :=
    Real.log_sqrt (le_of_lt hνσ_pos)
  have h_inv : Real.log (ν / σ) = - Real.log (σ / ν) := by
    have hνσ_ne : ν / σ ≠ 0 := ne_of_gt hνσ_pos
    have hσν_ne : σ / ν ≠ 0 := ne_of_gt hσν_pos
    -- ν/σ = (σ/ν)⁻¹
    have hinv : ν / σ = (σ / ν)⁻¹ := by
      rw [inv_div]
    rw [hinv, Real.log_inv]
  rw [h_div, h_sqrt, h_inv]
  ring

/-- Step 5 → 6 repackaging.

    From the near/far-split + torus-correction combined bound
    (paper §12.4 step 5)
      `σ ≤ M · (1 + C + log(L / δ_ν))`,
    with `δ_ν := √(ν/σ)`, conclude
      `σ ≤ M · (1 + C + log L + (1/2) · log(σ/ν))`.

    All inputs strictly positive. -/
lemma sigma_le_log_selfConsistent_of_linear_bound
    {M σ ν L C : ℝ}
    (hM_nn : 0 ≤ M) (hν : 0 < ν) (hσ : 0 < σ) (hL : 0 < L)
    (h_bound : σ ≤ M * (1 + C + Real.log (L / Real.sqrt (ν / σ)))) :
    σ ≤ M * (1 + C + Real.log L + (1 / 2) * Real.log (σ / ν)) := by
  have h_eq : Real.log (L / Real.sqrt (ν / σ))
                = Real.log L + (1 / 2) * Real.log (σ / ν) :=
    log_L_over_sqrt_delta hL hν hσ
  calc σ
      ≤ M * (1 + C + Real.log (L / Real.sqrt (ν / σ))) := h_bound
    _ = M * (1 + C + Real.log L + (1 / 2) * Real.log (σ / ν)) := by
        rw [h_eq]; ring

end NSBlwChain.BLW
