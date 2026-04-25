-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.BLW.DecayThresholdBridge

/-!
# Concrete `Real.rpow` threshold-finder for decay-to-cocompact

Constructs `R_of_ε ε := max R ((C^2 / ε + 1)^(1 / (2*p)))` and proves
the rpow inequality `C^2 / ε + 1 ≤ (R_of_ε ε)^(2*p)` consumed by
`decay_threshold_property_from_explicit_constants`.

## Strategy

Key identity: `(y^(1/k))^k = y` when `y ≥ 0` and `k > 0` (real).
Concretely:

  `(C^2/ε + 1)^(1/(2p)) ^ (2*p) = (C^2/ε + 1) ^ ((1/(2p)) * (2*p))`
  via `Real.rpow_mul` (with positivity), then `(1/(2p)) * (2p) = 1`,
  giving `(C^2/ε + 1)^1 = C^2/ε + 1`.

Plus `max`-monotonicity to lift to the `max R (...)` form.

## Main result

* `rpow_threshold_bound` — concrete construction of `R_of_ε` plus
  the verified rpow inequality.
-/

namespace NSBlwChain.BLW

open Real
open scoped BigOperators

/-- **Concrete threshold-finder satisfying the rpow margin.**

    Given `R > 0`, `C ≥ 0`, `p > 0`, define
    `R_of_ε ε := max R ((C^2 / ε + 1)^(1 / (2*p)))`.

    Then for every `ε > 0`:
    * `0 < R_of_ε ε`,
    * `R ≤ R_of_ε ε`,
    * `C^2 / ε + 1 ≤ (R_of_ε ε)^(2*p)`.

    The third inequality is the rpow margin consumed by
    `decay_threshold_property_from_explicit_constants`. -/
theorem rpow_threshold_bound
    {R C p : ℝ} (hR_pos : 0 < R) (hC_nn : 0 ≤ C) (hp_pos : 0 < p)
    (ε : ℝ) (hε : 0 < ε) :
    let R_of_ε := max R ((C ^ 2 / ε + 1) ^ (1 / (2 * p)))
    0 < R_of_ε ∧ R ≤ R_of_ε ∧
      C ^ 2 / ε + 1 ≤ R_of_ε ^ (2 * p) := by
  set y : ℝ := C ^ 2 / ε + 1 with hy_def
  set yPow : ℝ := y ^ (1 / (2 * p)) with hyPow_def
  set R_of_ε : ℝ := max R yPow with hRofε_def
  -- Step 1: y ≥ 1 (since C²/ε ≥ 0).
  have hy_ge_one : 1 ≤ y := by
    have h_ratio_nn : 0 ≤ C ^ 2 / ε :=
      div_nonneg (sq_nonneg C) (le_of_lt hε)
    show 1 ≤ C ^ 2 / ε + 1; linarith
  have hy_pos : 0 < y := lt_of_lt_of_le zero_lt_one hy_ge_one
  -- Step 2: yPow > 0 (rpow of positive base is positive).
  have hyPow_pos : 0 < yPow := Real.rpow_pos_of_pos hy_pos _
  -- Step 3: R_of_ε > 0 (max of positives).
  have hRofε_pos : 0 < R_of_ε := lt_max_of_lt_left hR_pos
  -- Step 4: R ≤ R_of_ε (immediate from max).
  have hRofε_ge_R : R ≤ R_of_ε := le_max_left _ _
  -- Step 5: yPow ≤ R_of_ε (other side of max).
  have hRofε_ge_yPow : yPow ≤ R_of_ε := le_max_right _ _
  -- Step 6: yPow ^ (2*p) = y.
  -- Use Real.rpow_natCast / Real.rpow_mul.  Since `2 * p > 0` and
  -- `yPow > 0`, we can use `Real.rpow_mul` and then
  -- `1/(2p) * (2p) = 1`.
  have h2p_pos : 0 < 2 * p := by linarith
  have h2p_ne : (2 * p) ≠ 0 := ne_of_gt h2p_pos
  have h_inv_mul : (1 / (2 * p)) * (2 * p) = 1 := by
    field_simp
  have h_yPow_pow : yPow ^ (2 * p) = y := by
    rw [hyPow_def]
    rw [← Real.rpow_natCast y 1] at *
    -- Use Real.rpow_mul: y^(a*b) = (y^a)^b for y ≥ 0 (or > 0).
    rw [← Real.rpow_mul (le_of_lt hy_pos)]
    rw [h_inv_mul]
    exact Real.rpow_one y
  -- Step 7: R_of_ε ^ (2*p) ≥ yPow ^ (2*p) by rpow monotonicity in
  -- the base (since yPow ≤ R_of_ε and 2*p ≥ 0).
  have h_pow_mono : yPow ^ (2 * p) ≤ R_of_ε ^ (2 * p) :=
    Real.rpow_le_rpow (le_of_lt hyPow_pos) hRofε_ge_yPow (le_of_lt h2p_pos)
  -- Step 8: chain.
  have h_main : y ≤ R_of_ε ^ (2 * p) := by
    rw [← h_yPow_pow]; exact h_pow_mono
  exact ⟨hRofε_pos, hRofε_ge_R, h_main⟩

end NSBlwChain.BLW
