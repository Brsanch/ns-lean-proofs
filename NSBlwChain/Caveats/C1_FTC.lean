-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Caveats.C1_GrowthMoment

/-!
# Caveat C1 — FTC wrapper for the integrated bound

This file provides the **FTC (fundamental theorem of calculus) bridge**
that feeds `hIntegratedBound` in `GrowthMomentBundle`
(`C1_GrowthMoment.lean`).

## Mathematical content

Let `M : ℝ → ℝ` be Lipschitz (hence absolutely continuous).  Then by
the FTC for absolutely continuous functions,

  `M(t) - M(s) = ∫_s^t M'(τ) dτ`   for all `s ≤ t`.

If furthermore `M'(τ) ≤ Φ(M(τ))` for a.e. `τ` in `[0, T)` and
`τ ↦ Φ(M(τ))` is interval-integrable, then integrating the a.e.
inequality and using FTC yields

  `M(t) - M(s) ≤ ∫_s^t Φ(M(τ)) dτ`   for all `0 ≤ s ≤ t < T`.

This is the exact form consumed as `hIntegratedBound` in the
growth-moment bundle.

## Status of the FTC identity

Mathlib 4.29's direct FTC-for-Lipschitz route
(`LipschitzWith → AbsolutelyContinuous → integral_eq_sub_of_hasDerivAt`)
has several small typeclass / argument-shape hurdles when specialized
to the `ℝ → ℝ` case we need.  To keep this file surgical and CI-safe,
we take the FTC identity

  `M(t) - M(s) = ∫_s^t deriv M τ dτ`

as an **explicit hypothesis** of the main theorem.  This is the exact
content of FTC applied to `M` on `[s, t]`, and is a standard classical
fact — discharging it from `LipschitzWith` alone is pure mathlib
plumbing deferred to a later pass.

Taking it as a hypothesis still delivers a useful downstream lemma:
once the FTC identity is established (by the caller or by a future
mathlib-only sub-lemma), the integrated bound follows automatically.

## References

* Evans, *PDE* 2nd ed., §5.8: Lipschitz → absolutely continuous → FTC.
* Companion note `paper/ns_regularity_caveats_formal.md`, §C1.
-/

namespace NSBlwChain.Caveats

open MeasureTheory Set Filter intervalIntegral
open scoped Topology

/-- **FTC wrapper: integrated bound from a.e. derivative bound.**

    Given:
    * `M : ℝ → ℝ` Lipschitz (hence abs. continuous, hence a.e.
      differentiable);
    * An a.e. pointwise bound `deriv M τ ≤ Φ (M τ)` on `[0, T)`;
    * Interval-integrability of `τ ↦ Φ(M τ)` and `τ ↦ deriv M τ` on
      `[s, t]`;
    * The **FTC identity** `M t - M s = ∫ τ in s..t, deriv M τ` (taken
      as a hypothesis — see file doc).

    Conclude the integrated bound

      `M t - M s ≤ ∫ τ in s..t, Φ (M τ)`   for `0 ≤ s ≤ t < T`.

    Proof strategy: interval-integral monotonicity of the integrand
    on `[s, t]`, then chain with the FTC identity. -/
theorem integratedBound_of_ftc_identity
    {M Φ : ℝ → ℝ} {T : ℝ}
    (hDerivInt : ∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t < T →
      IntervalIntegrable (fun τ => deriv M τ) MeasureTheory.volume s t)
    (hPhiInt : ∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t < T →
      IntervalIntegrable (fun τ => Φ (M τ)) MeasureTheory.volume s t)
    (hAeBound : ∀ᵐ τ : ℝ,
      (0 ≤ τ ∧ τ < T) → deriv M τ ≤ Φ (M τ))
    (hFTC : ∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t < T →
      M t - M s = ∫ τ in s..t, deriv M τ) :
    ∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t < T →
      M t - M s ≤ ∫ τ in s..t, Φ (M τ) := by
  intro s t h0s hst htT
  -- Step 1: integral monotonicity from the a.e. bound on [s, t].
  have h_ae_Icc :
      ∀ᵐ τ ∂(MeasureTheory.volume.restrict (Icc s t)),
        deriv M τ ≤ Φ (M τ) := by
    refine (ae_restrict_iff' measurableSet_Icc).mpr ?_
    filter_upwards [hAeBound] with τ hτ hτIcc
    have h0τ : 0 ≤ τ := le_trans h0s hτIcc.1
    have hτT : τ < T := lt_of_le_of_lt hτIcc.2 htT
    exact hτ ⟨h0τ, hτT⟩
  have h_mono :
      ∫ τ in s..t, deriv M τ ≤ ∫ τ in s..t, Φ (M τ) :=
    intervalIntegral.integral_mono_ae_restrict hst
      (hDerivInt h0s hst htT) (hPhiInt h0s hst htT) h_ae_Icc
  -- Step 2: chain with the FTC identity.
  have hEq : M t - M s = ∫ τ in s..t, deriv M τ := hFTC h0s hst htT
  linarith

/-- **GrowthMomentBundle constructor from an FTC-identity hypothesis.**

    Produces a `GrowthMomentBundle` from:
    * `M` Lipschitz with constant `K`;
    * Integrability of `Φ ∘ M` on every sub-interval;
    * Integrability of `deriv M` on every sub-interval;
    * An a.e. bound `deriv M τ ≤ Φ(M τ)` on `[0, T)`;
    * The FTC identity `M t - M s = ∫ τ in s..t, deriv M τ` on
      sub-intervals of `[0, T)`.

    The `hIntegratedBound` field is discharged via
    `integratedBound_of_ftc_identity`.  All other fields are direct
    hypotheses. -/
noncomputable def GrowthMomentBundle.ofFTCIdentity
    {M Φ : ℝ → ℝ} {T : ℝ} {K : NNReal}
    (hTpos : 0 < T)
    (hM_lip : LipschitzWith K M)
    (hPhiInt : ∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t < T →
      IntervalIntegrable (fun τ => Φ (M τ)) MeasureTheory.volume s t)
    (hDerivInt : ∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t < T →
      IntervalIntegrable (fun τ => deriv M τ) MeasureTheory.volume s t)
    (hAeBound : ∀ᵐ τ : ℝ,
      (0 ≤ τ ∧ τ < T) → deriv M τ ≤ Φ (M τ))
    (hFTC : ∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t < T →
      M t - M s = ∫ τ in s..t, deriv M τ) :
    GrowthMomentBundle where
  M := M
  Φ := Φ
  T := T
  hTpos := hTpos
  K := K
  hM_lip := hM_lip
  hInt_loc := hPhiInt
  hIntegratedBound :=
    integratedBound_of_ftc_identity hDerivInt hPhiInt hAeBound hFTC

/-! ## Variant: a.e. bound indexed to `[0, T)` via filter_upwards

For convenience, some downstream callers have the a.e. bound in a
"restricted on `[0, T)`" form

  `∀ᵐ τ, 0 ≤ τ → τ < T → deriv M τ ≤ Φ(M τ)`

(uncurried into an implication inside the a.e. quantifier).  The
following adapter converts it to the conjunction form used above. -/

/-- Adapter: curried-implication form of the a.e. bound is
    equivalent to the conjunction form. -/
lemma ae_bound_curried_iff_conj
    {M Φ : ℝ → ℝ} {T : ℝ} :
    (∀ᵐ τ : ℝ, 0 ≤ τ → τ < T → deriv M τ ≤ Φ (M τ)) ↔
    (∀ᵐ τ : ℝ, (0 ≤ τ ∧ τ < T) → deriv M τ ≤ Φ (M τ)) := by
  constructor
  · intro h
    filter_upwards [h] with τ hτ hc
    exact hτ hc.1 hc.2
  · intro h
    filter_upwards [h] with τ hτ h1 h2
    exact hτ ⟨h1, h2⟩

/-- **Curried-hypothesis variant.**  Same conclusion as
    `integratedBound_of_ftc_identity`, but with the a.e. bound in the
    uncurried/chained-implication form that most downstream callers
    already have. -/
theorem integratedBound_of_ftc_identity_curried
    {M Φ : ℝ → ℝ} {T : ℝ}
    (hDerivInt : ∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t < T →
      IntervalIntegrable (fun τ => deriv M τ) MeasureTheory.volume s t)
    (hPhiInt : ∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t < T →
      IntervalIntegrable (fun τ => Φ (M τ)) MeasureTheory.volume s t)
    (hAeBound : ∀ᵐ τ : ℝ, 0 ≤ τ → τ < T → deriv M τ ≤ Φ (M τ))
    (hFTC : ∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t < T →
      M t - M s = ∫ τ in s..t, deriv M τ) :
    ∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t < T →
      M t - M s ≤ ∫ τ in s..t, Φ (M τ) :=
  integratedBound_of_ftc_identity hDerivInt hPhiInt
    ((ae_bound_curried_iff_conj).mp hAeBound) hFTC

/-! ## Sanity check

Constant `M ≡ c` with `Φ ≡ 0`: `deriv M ≡ 0`, a.e. bound is trivial,
FTC identity reduces to `c - c = 0`, and the integrated bound is
`0 ≤ 0`.  Exercises the wiring. -/

example (c : ℝ) (T : ℝ) (_hT : 0 < T) :
    let M : ℝ → ℝ := fun _ => c
    let Φ : ℝ → ℝ := fun _ => 0
    ∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t < T →
      M t - M s ≤ ∫ τ in s..t, Φ (M τ) := by
  intro M Φ s t h0s hst _
  -- Both sides are 0.
  simp [M, Φ]

end NSBlwChain.Caveats
