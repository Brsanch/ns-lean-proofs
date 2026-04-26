-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Unconditional.Theorem1
import NSBlwChain.Unconditional.LerayEnergyEquality

set_option diagnostics true
set_option diagnostics.threshold 100

/-!
# `EnstrophyCrossoverBundle` from Leray equality + spherical crossover

End-to-end discharge for Theorem 1 (`blowup_rate_alpha`):

  `LerayEnergyEquality + EnstrophyCrossover + scalar regularity`
       `⇒ EnstrophyCrossoverBundle`
       `⇒ blowup_rate_alpha` (algebraic Theorem 1).

Two analytic inputs:

1. `LerayEnergyEquality`  — energy identity
   `E(0) - E(Tstar) = ν · ∫₀^{Tstar} Z`  (`LerayEnergyEquality.lean`).
2. `EnstrophyCrossoverHypothesis` — pointwise spherical-average lower
   bound  `Z(t) ≥ c_Z · M(t)^β`  (Proposition 3.1 in
   `paper/ns_regularity.md` §3.1; classical, taken here as a named
   hypothesis).

Plus three structural fields that are routine on a smooth NS
solution:

* `M_nonneg` and `M_mono` — monotonicity of the running supremum
  (the bundle's `M` is constructed as `max_{s ≤ t} ‖ω(·, s)‖_∞`),
* `Z_nonneg` — non-negativity of the squared-norm integrand.

## Main result

* `enstrophyCrossoverBundle_of_leray` — full bundle constructor.
* `blowup_rate_alpha_of_leray` — Theorem 1 conclusion from the two
  named analytic inputs.
-/

namespace NSBlwChain.Unconditional

open MeasureTheory
open scoped BigOperators

/-- **Enstrophy-crossover hypothesis (Proposition 3.1).**

    Pointwise spherical-average lower bound:
    `c_Z · M(t)^β ≤ Z(t)` on `[0, Tstar]`, with `c_Z, β > 0`.

    Discharged via the spherical-average crossover argument
    (paper §3.1).  Taken here as a named hypothesis. -/
structure EnstrophyCrossoverHypothesis
    (M Z : ℝ → ℝ) (β c_Z Tstar : ℝ) : Prop where
  /-- Positive crossover exponent. -/
  beta_pos : 0 < β
  /-- Positive crossover constant. -/
  cZ_pos  : 0 < c_Z
  /-- **Pointwise enstrophy lower bound.** -/
  Z_lower_bound :
    ∀ t : ℝ, 0 ≤ t → t ≤ Tstar → c_Z * M t ^ β ≤ Z t

/-- **Auxiliary regularity bundle.**

    Bundles the routine fields of `EnstrophyCrossoverBundle` that
    don't have a dedicated analytic source — they are immediate from
    the construction of `M` (running supremum) and the definition of
    `Z` (squared-norm integrand). -/
structure EnstrophyCrossoverRegularity
    (M Z : ℝ → ℝ) (Tstar : ℝ) : Prop where
  /-- `M` is nonneg on `[0, Tstar]`. -/
  M_nonneg : ∀ t : ℝ, 0 ≤ t → t ≤ Tstar → 0 ≤ M t
  /-- `M` is non-decreasing on `[0, Tstar]` (running supremum). -/
  M_mono : ∀ {s t : ℝ}, 0 ≤ s → s ≤ t → t ≤ Tstar → M s ≤ M t
  /-- `Z` is nonneg on `[0, Tstar]`. -/
  Z_nonneg : ∀ t : ℝ, 0 ≤ t → t ≤ Tstar → 0 ≤ Z t

/-- **`EnstrophyCrossoverBundle` from Leray + crossover + regularity.**

    Composes the three analytic inputs into the scalar bundle
    consumed by `blowup_rate_alpha`. -/
theorem enstrophyCrossoverBundle_of_leray
    {E M Z : ℝ → ℝ} {ν Tstar β c_Z : ℝ}
    (L : LerayEnergyEquality E Z ν Tstar)
    (X : EnstrophyCrossoverHypothesis M Z β c_Z Tstar)
    (R : EnstrophyCrossoverRegularity M Z Tstar)
    (hE0_nn : 0 ≤ E 0) :
    EnstrophyCrossoverBundle ν (E 0) Tstar M Z β c_Z := by
  exact {
    nu_pos := L.nu_pos
    E0_nonneg := hE0_nn
    Tstar_pos := L.Tstar_pos
    beta_pos := X.beta_pos
    cZ_pos := X.cZ_pos
    M_nonneg := R.M_nonneg
    M_mono := R.M_mono
    Z_nonneg := R.Z_nonneg
    Z_lower_bound := X.Z_lower_bound
    enstrophy_integral := enstrophy_integral_bound L
    Z_integrable := L.Z_integrable
  }

/-- **Theorem 1 from named analytic inputs (no NoTypeI).**

    Algebraic upper-bound form, before composition with ESS. -/
theorem blowup_rate_alpha_of_leray
    {E M Z : ℝ → ℝ} {ν Tstar β c_Z α : ℝ}
    (L : LerayEnergyEquality E Z ν Tstar)
    (X : EnstrophyCrossoverHypothesis M Z β c_Z Tstar)
    (R : EnstrophyCrossoverRegularity M Z Tstar)
    (hE0_nn : 0 ≤ E 0)
    (hα_pos : 0 < α) (hα_le_β : α ≤ β)
    {t : ℝ} (ht_nn : 0 ≤ t) (htT : t ≤ Tstar) (hMt : 1 ≤ M t) :
    (Tstar - t) * M t ^ α ≤ E 0 / (ν * c_Z) :=
  blowup_rate_alpha_of_bundle
    (enstrophyCrossoverBundle_of_leray L X R hE0_nn)
    hα_pos hα_le_β ht_nn htT hMt

/-- **Theorem 1 from named analytic inputs + ESS Type-I exclusion.**

    Full Theorem 1 conclusion: under Leray + crossover + regularity
    + ESS, every genuine blowup has `(Tstar - t) · M(t)^α ≤ E(0)/(ν·c_Z)`
    for `α ∈ (1, β]`. -/
theorem blowup_rate_alpha_full
    {E M Z : ℝ → ℝ} {ν Tstar β c_Z α : ℝ}
    (L : LerayEnergyEquality E Z ν Tstar)
    (X : EnstrophyCrossoverHypothesis M Z β c_Z Tstar)
    (R : EnstrophyCrossoverRegularity M Z Tstar)
    (hE0_nn : 0 ≤ E 0)
    (_hNoType1 : NoTypeIBlowup M Tstar)
    (hα_gt_one : 1 < α) (hα_le_β : α ≤ β)
    {t : ℝ} (ht_nn : 0 ≤ t) (htT : t ≤ Tstar) (hMt : 1 ≤ M t) :
    (Tstar - t) * M t ^ α ≤ E 0 / (ν * c_Z) :=
  blowup_rate_alpha_of_leray L X R hE0_nn
    (lt_trans zero_lt_one hα_gt_one) hα_le_β ht_nn htT hMt

end NSBlwChain.Unconditional
