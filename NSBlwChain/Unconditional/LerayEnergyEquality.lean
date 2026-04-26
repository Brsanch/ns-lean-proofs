-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Setup.EnergyEnstrophy

set_option diagnostics true
set_option diagnostics.threshold 100

/-!
# Leray energy equality + integrated enstrophy bound

Real analytic content for the discharge of
`EnstrophyCrossoverBundle.enstrophy_integral`
(in `Unconditional/Theorem1.lean`):

  `∫₀^{Tstar} Z(t) dt ≤ E₀ / ν`

The standard route, on a smooth NS solution on `[0, T)`:

  `dE/dt(t) = -ν · Z(t)`              (energy *equality*; Leray on `\mathbb R³`)
  `⇒ E(T) - E(0) = -ν · ∫₀^T Z(t) dt`  (integrate)
  `⇒ ν · ∫₀^T Z(t) dt = E(0) - E(T) ≤ E(0)`     (since `E(T) ≥ 0`)
  `⇒ ∫₀^T Z(t) dt ≤ E(0) / ν`         (divide by `ν > 0`).

The first step is the **Leray energy identity** (Lemma B in the
companion paper `paper/ns_regularity.md`), a classical result on
sufficiently regular NS solutions.  It is taken here as a named
hypothesis bundle `LerayEnergyEquality`, mirroring the design of
`Setup/EnergyEnstrophy.lean` (which packages the *inequality* form
`energy_decreasing`).  Discharging it from `NSEvolutionAxioms` would
require the weighted-cutoff energy-balance argument on `\mathbb R³`,
a substantial classical exercise outside the BLW-chain scope.

## Main results

* `LerayEnergyEquality` — bundle: `dE/dt = -ν · Z(t)` plus
  integrability hypotheses.
* `enstrophy_integral_bound` — the algebraic core
  `∫₀^T Z(t) dt ≤ E(0) / ν` from the bundle.
-/

namespace NSBlwChain.Unconditional

open MeasureTheory Set
open scoped BigOperators

/-- **Leray energy-equality bundle on `[0, T)`.**

    Packages the analytical content of the energy identity
    `dE/dt(t) = -ν · Z(t)` plus the regularity required to integrate
    it over `[0, T]`.

    Fields:

    * `nu_pos` — positive viscosity,
    * `Tstar_pos` — positive interval endpoint,
    * `E_nonneg_at_T` — terminal energy `E(T) ≥ 0` (immediate from
      `(1/2) · ∫|u|²`, recorded explicitly to avoid re-deriving),
    * `Z_integrable` — `Z` is `IntervalIntegrable` on `[0, T]`,
    * `energy_balance` — the integrated energy identity
      `E(0) - E(T) = ν · ∫₀^T Z(t) dt`. -/
structure LerayEnergyEquality
    (E Z : ℝ → ℝ) (ν Tstar : ℝ) : Prop where
  /-- Positive viscosity. -/
  nu_pos : 0 < ν
  /-- Positive interval endpoint. -/
  Tstar_pos : 0 < Tstar
  /-- Terminal energy non-negative.  (`E := (1/2) ∫ |u(T,·)|²` — but
      we record this explicitly because the discharge happens at the
      scalar level and `E` is just a real-valued function here.) -/
  E_nonneg_at_T : 0 ≤ E Tstar
  /-- `Z` is `IntervalIntegrable` on `[0, Tstar]`. -/
  Z_integrable : IntervalIntegrable Z volume 0 Tstar
  /-- **Integrated Leray energy equality.**
      `E(0) - E(Tstar) = ν · ∫₀^{Tstar} Z(t) dt`. -/
  energy_balance :
    E 0 - E Tstar = ν * ∫ t in (0 : ℝ)..Tstar, Z t

/-- **Algebraic core: integrated enstrophy bound from Leray equality.**

    From the Leray energy equality on `[0, Tstar]`,
    `∫₀^{Tstar} Z(t) dt ≤ E(0) / ν`.

    Proof: `ν · ∫ Z = E(0) - E(Tstar) ≤ E(0)` (since `E(Tstar) ≥ 0`),
    then divide by `ν > 0`. -/
theorem enstrophy_integral_bound
    {E Z : ℝ → ℝ} {ν Tstar : ℝ}
    (L : LerayEnergyEquality E Z ν Tstar) :
    (∫ t in (0 : ℝ)..Tstar, Z t) ≤ E 0 / ν := by
  -- ν · ∫ Z = E(0) - E(Tstar).
  have h_balance : E 0 - E Tstar = ν * ∫ t in (0 : ℝ)..Tstar, Z t :=
    L.energy_balance
  have h_E_T_nn : 0 ≤ E Tstar := L.E_nonneg_at_T
  have hν_pos : 0 < ν := L.nu_pos
  -- E(0) - E(Tstar) ≤ E(0).
  have h_diff_le : E 0 - E Tstar ≤ E 0 := by linarith
  -- So ν · ∫ Z ≤ E(0).
  have h_νZ_le : ν * (∫ t in (0 : ℝ)..Tstar, Z t) ≤ E 0 := by linarith
  -- Divide by ν > 0.
  have h_div : (∫ t in (0 : ℝ)..Tstar, Z t) ≤ E 0 / ν :=
    (le_div_iff₀ hν_pos).mpr (by linarith [h_νZ_le])
  exact h_div

end NSBlwChain.Unconditional
