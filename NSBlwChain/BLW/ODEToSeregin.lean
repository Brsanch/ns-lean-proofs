-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.BLW.SubTypeOneRate

/-!
# ODE-to-Seregin wiring

Given the pointwise a.e. bound `Ṁ(t) ≤ 4 · M(t)² · log M(t)`
(produced by `BLW/FullScalarChain.full_scalar_chain` in the growth
regime) and the ODE integration conclusion
`(T - t) · M · log M ≤ 1/4` (taken here as an explicit hypothesis
pending its own derivation), produce the Seregin sub-Type-I
hypothesis signature.

## Contents

* `subTypeI_from_ode_hypothesis` — takes the integrated scalar
  inequality + the `log M → ∞` hypothesis (via an explicit
  `δ_of_ε` function) and returns Seregin's signature for a given
  scalar envelope.

## Scope

This file contains **no new analytical content**.  The integrated
scalar inequality is the *only* remaining open hypothesis; the
pointwise bound `Ṁ ≤ 4 M² log M` and the Seregin translation
are both machine-verified in the preceding files
(`FullScalarChain.lean` and `SubTypeOneRate.lean`).
-/

namespace NSBlwChain.BLW

/-- **ODE-to-Seregin.**

    Given `M : ℝ → ℝ` with the integrated-bound hypothesis
    `(T-t) · M · log M ≤ 1/4` on `(0, T)`, the log-positivity
    hypothesis `log M > 0`, and the `log M → ∞` hypothesis encoded
    via a `δ_of_ε` producer, we land Seregin's signature
    `(T-t) · M ≤ ε` on a one-sided neighborhood of `T`.

    This is a thin re-export of `subTypeI_rate_of_log_blowup`
    applied with the integrated hypothesis as its `h_bound`. -/
theorem subTypeI_from_ode_hypothesis
    {M : ℝ → ℝ} {T : ℝ}
    (h_ode :
      ∀ t : ℝ, 0 < t → t < T → (T - t) * M t * Real.log (M t) ≤ 1 / 4)
    (h_logM_pos : ∀ t : ℝ, 0 < t → t < T → 0 < Real.log (M t))
    (h_M_nonneg : ∀ t : ℝ, 0 < t → t < T → 0 ≤ M t)
    (hT_pos : 0 < T)
    (δ_of_ε : ℝ → ℝ)
    (δ_pos : ∀ ε : ℝ, 0 < ε → 0 < δ_of_ε ε)
    (δ_le : ∀ ε : ℝ, 0 < ε → δ_of_ε ε ≤ T)
    (h_log_large :
      ∀ ε : ℝ, 0 < ε →
        ∀ t : ℝ, T - δ_of_ε ε < t → t < T →
          1 / (4 * ε) ≤ Real.log (M t)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧
        ∀ t : ℝ, T - δ < t → t < T →
          (T - t) * M t ≤ ε :=
  subTypeI_rate_of_log_blowup h_ode h_logM_pos h_M_nonneg hT_pos
    δ_of_ε δ_pos δ_le h_log_large

end NSBlwChain.BLW
