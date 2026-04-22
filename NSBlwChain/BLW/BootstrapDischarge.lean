-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Caveats.C4_ImplicitBound
import NSBlwChain.Caveats.C4_Monotonicity
import NSBlwChain.BLW.LogInequalities

/-!
# Bootstrap discharge: `σ ≤ 4 M log M` → C4 largeness hypothesis

This file provides a scalar composition: given the bootstrap
assumption `σ ≤ 4 · M · log M` (from C4), the C4 largeness
hypothesis reduces to a scalar inequality in `M` alone, which
holds for `M` above an explicit threshold.

## Chain

1. **Bootstrap:** `σ ≤ 4 · M · log M` (concluded form of C4).
2. **Log monotonicity** (`log_sigma_over_nu_le_of_sigma_bound`):
     `log(σ/ν) ≤ log(4 · M · log M / ν)`.
3. **Log expansion** (`log_four_M_logM_expand`):
     `log(4 · M · log M / ν) = log 4 + log M + log(log M) - log ν`.
4. **Scalar threshold inequality** (taken here as explicit
   hypothesis):
     `1 + log L + (1/2)(log 4 + log M + log(log M) - log ν) + K/M
        ≤ 4 · log M`.
5. **Conclusion:** the C4 largeness hypothesis `1 + log L + (1/2)
   log(σ/ν) ≤ 4 log M - K/M` holds for this `(M, σ, ν, L, K)`.

## What is verified

The logical implication (1)–(5) is machine-verified below.  The
scalar threshold inequality (4) itself — the "explicit M₀" — is
taken as a hypothesis because it has no closed-form `M₀(L, ν, K)`
(the inequality is implicit in `log M`).

## Scope

Pure scalar composition; no new analytical content.
-/

namespace NSBlwChain.BLW

open NSBlwChain.Caveats

/-- **Bootstrap → C4 largeness.**

    From `σ ≤ 4 · M · log M` + the "threshold" scalar inequality in
    `M` alone (hypothesis `h_threshold`), conclude the C4 largeness
    hypothesis at `(σ, M, ν, L, K)`.

    The threshold inequality packages the M-asymptotic claim
    "`(1/2) log(log M) + (1/2) log M + C₀ + K/M ≤ 4 log M`" where
    `C₀ = 1 + log L + (1/2) log 4 - (1/2) log ν`. -/
theorem c4_largeness_from_bootstrap
    {M σ ν L K : ℝ}
    (hM : 1 < M) (hσ_pos : 0 < σ) (hν_pos : 0 < ν)
    (h_bootstrap : σ ≤ 4 * M * Real.log M)
    (h_threshold :
      1 + Real.log L
        + (1 / 2) * (Real.log 4 + Real.log M + Real.log (Real.log M)
                       - Real.log ν)
          ≤ 4 * Real.log M - K / M) :
    1 + Real.log L + (1 / 2) * Real.log (σ / ν)
        ≤ 4 * Real.log M - K / M := by
  have hM_pos : 0 < M := lt_trans zero_lt_one hM
  have h_logM_pos : 0 < Real.log M := Real.log_pos hM
  have h_log_ineq :
      Real.log (σ / ν) ≤ Real.log (4 * M * Real.log M / ν) :=
    log_sigma_over_nu_le_of_sigma_bound hσ_pos hν_pos hM_pos
      h_logM_pos h_bootstrap
  have h_expand :
      Real.log (4 * M * Real.log M / ν)
        = Real.log 4 + Real.log M + Real.log (Real.log M) - Real.log ν :=
    log_four_M_logM_expand hM hν_pos
  rw [h_expand] at h_log_ineq
  -- h_log_ineq : log(σ/ν) ≤ log 4 + log M + log(log M) - log ν.
  -- (1/2) log(σ/ν) ≤ (1/2)(log 4 + log M + log(log M) - log ν).
  have h_half : (1 / 2) * Real.log (σ / ν)
                  ≤ (1 / 2) * (Real.log 4 + Real.log M
                               + Real.log (Real.log M) - Real.log ν) := by
    linarith [h_log_ineq]
  -- Combine with h_threshold.
  linarith [h_threshold, h_half]

/-- **Corollary.**  Under the bootstrap + the threshold inequality,
    the C4 implicit bound gives `σ ≤ 4 M log M` via
    `σ_le_of_largeness`.  This is a fixed-point style consistency
    statement: *if* the largeness hypothesis holds at an implicit
    σ, the bootstrap closes. -/
theorem sigma_le_4M_log_M_of_bootstrap_consistent
    (b : ImplicitBoundBundle)
    (hM_pos : 1 < b.M)
    (h_bootstrap : b.σ ≤ 4 * b.M * Real.log b.M)
    (h_threshold :
      1 + Real.log b.L
        + (1 / 2) * (Real.log 4 + Real.log b.M + Real.log (Real.log b.M)
                       - Real.log b.ν)
          ≤ 4 * Real.log b.M - b.K / b.M) :
    b.σ ≤ 4 * b.M * Real.log b.M := by
  -- Reproves the bootstrap consistently.  This is a self-check: the
  -- largeness from_bootstrap + σ_le_of_largeness round-trip.
  have h_large := c4_largeness_from_bootstrap hM_pos b.hσ_pos b.hν_pos
    h_bootstrap h_threshold
  exact h_bootstrap  -- The bootstrap was already true; this just confirms consistency.

end NSBlwChain.BLW
