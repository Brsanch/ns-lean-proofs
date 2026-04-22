-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib

/-!
# Log inequalities for the BLW chain

Small algebraic helpers on `Real.log` used throughout the chain.
These are pure scalar inequalities; no PDE content.

## Contents

* `log_sigma_over_nu_le_of_sigma_bound` — given `σ ≤ 4 · M · log M`
  and positivity, `log(σ / ν) ≤ log(4 · M · log M / ν)`.

* `log_four_M_logM_expand` — algebraic expansion
  `log(4 · M · log M / ν) = log 4 + log M + log (log M) - log ν`
  (for `M > 1`, `ν > 0`).

Both are trivial from `Real.log_le_log` and `Real.log_mul / log_div`.
-/

namespace NSBlwChain.BLW

/-- Monotonicity of `log(σ/ν)` under the bootstrap `σ ≤ 4 M log M`. -/
theorem log_sigma_over_nu_le_of_sigma_bound
    {σ M ν : ℝ} (hσ_pos : 0 < σ) (hν_pos : 0 < ν) (hM_pos : 0 < M)
    (h_logM_pos : 0 < Real.log M)
    (h_bound : σ ≤ 4 * M * Real.log M) :
    Real.log (σ / ν) ≤ Real.log (4 * M * Real.log M / ν) := by
  have h_rhs_pos : 0 < 4 * M * Real.log M := by positivity
  have h_rhs_div_pos : 0 < 4 * M * Real.log M / ν := div_pos h_rhs_pos hν_pos
  have h_div_le : σ / ν ≤ 4 * M * Real.log M / ν :=
    div_le_div_of_nonneg_right h_bound (le_of_lt hν_pos) |>.trans
      (by linarith [div_le_div_of_nonneg_right h_bound (le_of_lt hν_pos)])
  -- Actually simpler: just div_le_div_of_nonneg_right.
  have h_div_le' : σ / ν ≤ 4 * M * Real.log M / ν :=
    div_le_div_of_nonneg_right h_bound (le_of_lt hν_pos)
  exact Real.log_le_log (div_pos hσ_pos hν_pos) h_div_le'

/-- Algebraic expansion `log(4 · M · log M / ν) = log 4 + log M + log(log M) - log ν`
    under positivity hypotheses. -/
theorem log_four_M_logM_expand
    {M ν : ℝ} (hM : 1 < M) (hν : 0 < ν) :
    Real.log (4 * M * Real.log M / ν)
      = Real.log 4 + Real.log M + Real.log (Real.log M) - Real.log ν := by
  have h4_pos : (0 : ℝ) < 4 := by norm_num
  have hM_pos : 0 < M := lt_trans zero_lt_one hM
  have h_logM_pos : 0 < Real.log M := Real.log_pos hM
  have h_prod : 4 * M * Real.log M = (4 * M) * Real.log M := by ring
  have h_4M_pos : 0 < 4 * M := mul_pos h4_pos hM_pos
  have h_4M_ne : (4 * M) ≠ 0 := ne_of_gt h_4M_pos
  have h_logM_ne : Real.log M ≠ 0 := ne_of_gt h_logM_pos
  have h_ν_ne : ν ≠ 0 := ne_of_gt hν
  have h4_ne : (4 : ℝ) ≠ 0 := by norm_num
  have hM_ne : M ≠ 0 := ne_of_gt hM_pos
  have h_num_ne : 4 * M * Real.log M ≠ 0 := by
    rw [h_prod]
    exact mul_ne_zero h_4M_ne h_logM_ne
  calc Real.log (4 * M * Real.log M / ν)
      = Real.log (4 * M * Real.log M) - Real.log ν :=
        Real.log_div h_num_ne h_ν_ne
    _ = Real.log ((4 * M) * Real.log M) - Real.log ν := by rw [h_prod]
    _ = Real.log (4 * M) + Real.log (Real.log M) - Real.log ν := by
        rw [Real.log_mul h_4M_ne h_logM_ne]
    _ = (Real.log 4 + Real.log M) + Real.log (Real.log M) - Real.log ν := by
        rw [Real.log_mul h4_ne hM_ne]
    _ = Real.log 4 + Real.log M + Real.log (Real.log M) - Real.log ν := by ring

end NSBlwChain.BLW
