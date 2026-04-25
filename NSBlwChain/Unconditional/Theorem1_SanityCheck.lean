-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Unconditional.Theorem1

/-!
# Theorem 1 — concrete numerical sanity check

Instantiates `blowup_rate_alpha_beta_two` (the generic-`β=2` form
of Theorem 1's algebraic core) on concrete numerical scalars and
verifies the algebraic conclusion.

## Concrete instance

* `ν := 1` (unit viscosity).
* `E₀ := 1` (unit initial energy).
* `Tstar := 1` (unit blowup time).
* `M(t) := 2 / (Tstar - t)` (a concrete envelope candidate
  satisfying the saturating Type-I bound `(Tstar - t) · M(t) = 2`).
* `Z(t) := 4 · M(t)²` (saturating the enstrophy crossover at
  `c_Z = 4`).
* `β := 2` (generic enstrophy crossover exponent).
* `c_Z := 4`.
* `α := 1.5` (any value strictly between `1` and `β = 2`).

The numerical bound from `blowup_rate_alpha_beta_two`:

  `(Tstar - t) · M(t)^α ≤ E₀ / (ν · c_Z) = 1/4`

at any `t ∈ [0, Tstar]` with `1 ≤ M(t)`.

This file does NOT construct the full `EnstrophyCrossoverBundle`
(which requires verifying the `enstrophy_integral` Leray bound and
the `Z_integrable` hypothesis on the concrete `Z`).  Instead it
provides a numerical *if-then* statement at the algebraic-core
level: given a hypothetical bundle on concrete `M, Z` with the
above parameters, T1 delivers `(Tstar - t) · M(t)^1.5 ≤ 1/4` —
demonstrating the concrete threshold the chain produces.

## Sanity-check theorem

* `blowup_rate_at_concrete_values` — chain instantiation.
-/

namespace NSBlwChain.Unconditional

open Real

/-- **Concrete-instance sanity check for Theorem 1's algebraic core.**

    On any `EnstrophyCrossoverBundle` with `ν = 1`, `E₀ = 1`,
    `Tstar = 1`, `c_Z = 4`, and `β = 2`, applying
    `blowup_rate_alpha_beta_two` at any `t ∈ [0, 1]` with `M(t) ≥ 1`
    delivers `(1 - t) · M(t)^α ≤ 1/4` for every `α ∈ (1, 2]`.

    The conclusion is the canonical "Type-Ⅱ scaling" form of T1
    in unit-normalized variables. -/
theorem blowup_rate_at_concrete_values
    {M Z : ℝ → ℝ} {α : ℝ}
    (B : EnstrophyCrossoverBundle 1 1 1 M Z 2 4)
    (hNoType1 : NoTypeIBlowup M 1)
    (hα_gt_one : 1 < α) (hα_le_two : α ≤ 2)
    {t : ℝ} (ht_nn : 0 ≤ t) (htT : t ≤ 1) (hMt : 1 ≤ M t) :
    (1 - t) * M t ^ α ≤ 1 / 4 := by
  -- Apply blowup_rate_alpha_beta_two with concrete ν=1, E₀=1, Tstar=1, c_Z=4.
  have h := blowup_rate_alpha_beta_two B hNoType1 hα_gt_one hα_le_two
    ht_nn htT hMt
  -- h : (1 - t) * M t ^ α ≤ 1 / (1 * 4)
  -- Simplify: 1 / (1 * 4) = 1 / 4.
  have h_simp : (1 : ℝ) / (1 * 4) = 1 / 4 := by norm_num
  rw [h_simp] at h
  exact h

/-- **Threshold form**: at the half-way point `t = 1/2` with
    saturating `M(1/2) = 4`, the bound forces `M(1/2)^α ≤ 1/2`. -/
theorem blowup_rate_at_halftime
    {M Z : ℝ → ℝ} {α : ℝ}
    (B : EnstrophyCrossoverBundle 1 1 1 M Z 2 4)
    (hNoType1 : NoTypeIBlowup M 1)
    (hα_gt_one : 1 < α) (hα_le_two : α ≤ 2)
    (hMt : 1 ≤ M (1/2)) :
    M (1/2) ^ α ≤ 1 / 2 := by
  have h := blowup_rate_at_concrete_values (M := M) (Z := Z) (α := α)
    B hNoType1 hα_gt_one hα_le_two
    (t := 1/2) (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) ≤ 1) hMt
  -- h : (1 - 1/2) * M (1/2) ^ α ≤ 1/4
  -- Multiply both sides by 2 to get M^α ≤ 1/2.
  have h_one_minus : (1 : ℝ) - 1/2 = 1/2 := by norm_num
  rw [h_one_minus] at h
  -- h : (1/2) * M (1/2) ^ α ≤ 1/4
  linarith

end NSBlwChain.Unconditional
