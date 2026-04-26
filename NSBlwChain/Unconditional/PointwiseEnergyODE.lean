-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Unconditional.LerayEnergyEquality

set_option diagnostics true
set_option diagnostics.threshold 100

/-!
# Pointwise energy ODE → integrated Leray balance

Derives `LerayEnergyEquality.energy_balance`
(`E(0) - E(Tstar) = ν · ∫₀^{Tstar} Z(t) dt`) from the **pointwise**
energy identity

  `dE/dt(t) = -ν · Z(t)`           (a.e. or everywhere on `[0, Tstar]`)

via mathlib's fundamental theorem of calculus
(`intervalIntegral.integral_eq_sub_of_hasDerivAt`).

The pointwise form is the natural output of the energy method on
sufficiently regular NS solutions (e.g., on a smooth solution
extending classically; mathlib stores the FTC under
`HasDerivAt`-form hypotheses).  This file collapses
"pointwise ODE + continuity" → "integrated balance" → the
`LerayEnergyEquality` bundle, closing one structural step
toward full discharge of Theorem 1 from `NSEvolutionAxioms`.

## Main results

* `LerayEnergyPointwise` — pointwise hypothesis bundle.
* `lerayEnergyEquality_of_pointwise` — full bundle from pointwise +
  routine integrability/positivity.
-/

namespace NSBlwChain.Unconditional

open MeasureTheory intervalIntegral
open scoped BigOperators

/-- **Pointwise Leray energy ODE on `[0, Tstar]`.**

    Packages the pointwise content of the energy identity:

    * `nu_pos`              — positive viscosity,
    * `Tstar_pos`           — positive interval endpoint,
    * `E_nonneg_at_T`       — terminal energy `E(Tstar) ≥ 0`,
    * `E_hasDerivAt`        — `(d/dt) E(t) = -ν · Z(t)` everywhere on
                              `[0, Tstar]`,
    * `negνZ_intervalInt`   — `t ↦ -ν · Z(t)` is `IntervalIntegrable`
                              on `[0, Tstar]`. -/
structure LerayEnergyPointwise
    (E Z : ℝ → ℝ) (ν Tstar : ℝ) : Prop where
  /-- Positive viscosity. -/
  nu_pos : 0 < ν
  /-- Positive interval endpoint. -/
  Tstar_pos : 0 < Tstar
  /-- Terminal energy non-negative. -/
  E_nonneg_at_T : 0 ≤ E Tstar
  /-- **Pointwise energy ODE.**  `dE/dt(t) = -ν · Z(t)` on `[0, Tstar]`. -/
  E_hasDerivAt :
    ∀ t ∈ Set.Icc (0 : ℝ) Tstar, HasDerivAt E (-(ν * Z t)) t
  /-- `t ↦ -ν · Z(t)` is `IntervalIntegrable` on `[0, Tstar]`. -/
  negνZ_intervalInt :
    IntervalIntegrable (fun t => -(ν * Z t)) volume 0 Tstar
  /-- `Z` is `IntervalIntegrable` on `[0, Tstar]`. -/
  Z_intervalInt : IntervalIntegrable Z volume 0 Tstar

/-- **Integrated balance from pointwise ODE via FTC.**

    `E(Tstar) - E(0) = ∫₀^{Tstar} -ν · Z(t) dt = -ν · ∫₀^{Tstar} Z(t) dt`,
    which rearranges to `E(0) - E(Tstar) = ν · ∫₀^{Tstar} Z(t) dt`. -/
theorem energy_balance_of_pointwise
    {E Z : ℝ → ℝ} {ν Tstar : ℝ}
    (P : LerayEnergyPointwise E Z ν Tstar) :
    E 0 - E Tstar = ν * ∫ t in (0 : ℝ)..Tstar, Z t := by
  have h0T : (0 : ℝ) ≤ Tstar := le_of_lt P.Tstar_pos
  -- FTC on `[0, Tstar]`: ∫₀^Tstar (dE/dt) dt = E(Tstar) - E(0).
  have h_ftc :
      (∫ t in (0 : ℝ)..Tstar, -(ν * Z t)) = E Tstar - E 0 := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt ?_ ?_
    · -- HasDerivAt on uIcc 0 Tstar.
      intro t ht
      rw [Set.uIcc_of_le h0T] at ht
      exact P.E_hasDerivAt t ht
    · exact P.negνZ_intervalInt
  -- ∫₀^Tstar -ν·Z = -ν · ∫₀^Tstar Z.
  have h_neg :
      (∫ t in (0 : ℝ)..Tstar, -(ν * Z t))
        = -(ν * ∫ t in (0 : ℝ)..Tstar, Z t) := by
    -- Pull out the constant -ν.
    have h_pull :
        (∫ t in (0 : ℝ)..Tstar, -(ν * Z t))
          = -ν * ∫ t in (0 : ℝ)..Tstar, Z t := by
      have h1 :
          (∫ t in (0 : ℝ)..Tstar, -(ν * Z t))
            = (∫ t in (0 : ℝ)..Tstar, (-ν) * Z t) := by
        apply intervalIntegral.integral_congr
        intro t _
        ring
      rw [h1, intervalIntegral.integral_const_mul]
    rw [h_pull]
    ring
  -- Combine: -ν · ∫ Z = E(Tstar) - E(0), i.e. ν · ∫ Z = E(0) - E(Tstar).
  have h_chain : -(ν * ∫ t in (0 : ℝ)..Tstar, Z t) = E Tstar - E 0 := by
    rw [← h_neg]; exact h_ftc
  linarith [h_chain]

/-- **`LerayEnergyEquality` bundle constructor from pointwise ODE.** -/
theorem lerayEnergyEquality_of_pointwise
    {E Z : ℝ → ℝ} {ν Tstar : ℝ}
    (P : LerayEnergyPointwise E Z ν Tstar) :
    LerayEnergyEquality E Z ν Tstar :=
  { nu_pos := P.nu_pos
    Tstar_pos := P.Tstar_pos
    E_nonneg_at_T := P.E_nonneg_at_T
    Z_integrable := P.Z_intervalInt
    energy_balance := energy_balance_of_pointwise P }

end NSBlwChain.Unconditional
