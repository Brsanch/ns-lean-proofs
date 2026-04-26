-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Unconditional.Theorem1FromLeray
import NSBlwChain.Unconditional.RunningSupOn

set_option diagnostics true
set_option diagnostics.threshold 100

/-!
# `EnstrophyCrossoverRegularity` from `runningSupOn`

Discharges the routine fields of
`EnstrophyCrossoverRegularity` (`M_nonneg`, `M_mono`) for the
canonical choice `M := runningSupOn f`, where `f` is meant to be
`t ↦ ‖ω(·, t)‖_∞`.  The third field `Z_nonneg` follows from any
non-negativity hypothesis on `Z`.

This removes `M_mono` and `M_nonneg` from the *primitive* hypothesis
list for Theorem 1's discharge: a downstream consumer needs only

* a non-negative `f` (vorticity max envelope per time),
* a uniform image-boundedness hypothesis (always true on a smooth
  finite-time NS solution),
* a non-negative `Z`,

to obtain the regularity bundle.

## Main result

* `enstrophyCrossoverRegularity_of_runningSup` —
  `EnstrophyCrossoverRegularity (runningSupOn f) Z Tstar` from
  the three structural hypotheses above.
-/

namespace NSBlwChain.Unconditional

open Set

/-- **`EnstrophyCrossoverRegularity` from `runningSupOn`.**

    For non-negative `f, Z` with `f` bounded on `[0, T]` for every
    `T`, the running supremum `runningSupOn f` is non-decreasing and
    non-negative on `[0, Tstar]`, discharging the regularity bundle. -/
theorem enstrophyCrossoverRegularity_of_runningSup
    {f Z : ℝ → ℝ} {Tstar : ℝ}
    (hf_bdd : ∀ T : ℝ, BddAbove (f '' Icc 0 T))
    (hf_nn : ∀ s : ℝ, 0 ≤ s → 0 ≤ f s)
    (hZ_nn : ∀ t : ℝ, 0 ≤ t → t ≤ Tstar → 0 ≤ Z t) :
    EnstrophyCrossoverRegularity (runningSupOn f) Z Tstar :=
  { M_nonneg := fun t ht_nn _ =>
      runningSupOn_nonneg f hf_bdd hf_nn ht_nn
    M_mono := fun {s t} hs_nn hst _ =>
      runningSupOn_mono f hf_bdd hs_nn hst
    Z_nonneg := hZ_nn }

end NSBlwChain.Unconditional
