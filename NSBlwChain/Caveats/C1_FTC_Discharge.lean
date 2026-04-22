-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Caveats.C1_GrowthMoment
import NSBlwChain.Caveats.C1_FTC

/-!
# Caveat C1 — FTC-for-Lipschitz discharge (unconditional bridge)

This file closes **OPEN.md item 3**: the `hIntegratedBound` field of
`GrowthMomentBundle` is discharged directly from a global Lipschitz
hypothesis on `M` plus an a.e. pointwise bound on `deriv M`, via the
mathlib FTC-for-absolutely-continuous-functions route.

## Mathematical content

Let `M : ℝ → ℝ` be Lipschitz (`LipschitzWith K M`).  Then on every
compact interval `[s, t]` (with `s ≤ t`):

1.  `M` is absolutely continuous on `uIcc s t = [s, t]`
    (`LipschitzOnWith.absolutelyContinuousOnInterval`).
2.  `deriv M` is interval-integrable on `s..t`
    (`AbsolutelyContinuousOnInterval.intervalIntegrable_deriv`).
3.  FTC:
    `∫ τ in s..t, deriv M τ = M t - M s`
    (`AbsolutelyContinuousOnInterval.integral_deriv_eq_sub`).

Given an a.e. pointwise bound `deriv M τ ≤ Φ (M τ)` on `[0, T)` and
interval-integrability of `τ ↦ Φ (M τ)`, step 3 combined with
interval-integral monotonicity yields the integrated bound

  `M t - M s ≤ ∫ τ in s..t, Φ (M τ)`   for all `0 ≤ s ≤ t < T`.

This is the exact field `hIntegratedBound` of `GrowthMomentBundle`.

## Relationship to `C1_FTC.lean`

`C1_FTC.lean` produced the integrated bound assuming the FTC identity
`M t - M s = ∫ τ in s..t, deriv M τ` as a hypothesis.  This file
**discharges** that hypothesis from mathlib, eliminating the gap.

The downstream constructor `GrowthMomentBundle.ofLipschitzAndPointwiseBound`
is now parameterized only by:

* `hM_lip : LipschitzWith K M`   (globally Lipschitz envelope);
* `hAeBound : ∀ᵐ τ, (0 ≤ τ ∧ τ < T) → deriv M τ ≤ Φ (M τ)`;
* `hPhiInt : ∀ 0 ≤ s ≤ t < T, IntervalIntegrable (Φ ∘ M) volume s t`.

Both `hDerivInt` and `hFTC` are now *derived* from `hM_lip`, not taken
as hypotheses.

## References

* Mathlib `Mathlib/MeasureTheory/Function/AbsolutelyContinuous.lean`:
  `LipschitzOnWith.absolutelyContinuousOnInterval`.
* Mathlib `Mathlib/MeasureTheory/Integral/IntervalIntegral/AbsolutelyContinuousFun.lean`:
  `AbsolutelyContinuousOnInterval.integral_deriv_eq_sub`.
* Mathlib `Mathlib/MeasureTheory/Integral/IntervalIntegral/DerivIntegrable.lean`:
  `AbsolutelyContinuousOnInterval.intervalIntegrable_deriv`.
* Evans, *PDE* 2nd ed., §5.8.
-/

namespace NSBlwChain.Caveats

open MeasureTheory Set Filter intervalIntegral
open scoped Topology

/-- **FTC identity on `[s, t]` for globally Lipschitz `M`.**

    The core mathlib bridge, isolated for readability.  If
    `M : ℝ → ℝ` is Lipschitz and `s ≤ t`, then

      `M t - M s = ∫ τ in s..t, deriv M τ`.

    Proof: `LipschitzWith` restricts to `LipschitzOnWith` on `uIcc s t`,
    which implies `AbsolutelyContinuousOnInterval`, whose FTC identity
    reads `∫ x in s..t, deriv M x = M t - M s`.  Rearrange. -/
theorem ftc_identity_of_lipschitz
    {M : ℝ → ℝ} {K : NNReal} (hLip : LipschitzWith K M)
    {s t : ℝ} (hst : s ≤ t) :
    M t - M s = ∫ τ in s..t, deriv M τ := by
  -- Step 1: restrict global Lipschitz to the interval.
  have hLipOn : LipschitzOnWith K M (uIcc s t) := hLip.lipschitzOnWith _
  -- Step 2: Lipschitz-on-interval ⟹ absolutely continuous on interval.
  have hAC : AbsolutelyContinuousOnInterval M s t :=
    hLipOn.absolutelyContinuousOnInterval
  -- Step 3: FTC for AC functions.
  have hFTC : ∫ τ in s..t, deriv M τ = M t - M s :=
    hAC.integral_deriv_eq_sub
  linarith

/-- **Interval-integrability of `deriv M` from a global Lipschitz
    hypothesis.**  Direct corollary of Lipschitz → AC →
    `intervalIntegrable_deriv`. -/
theorem intervalIntegrable_deriv_of_lipschitz
    {M : ℝ → ℝ} {K : NNReal} (hLip : LipschitzWith K M)
    (s t : ℝ) :
    IntervalIntegrable (fun τ => deriv M τ) MeasureTheory.volume s t := by
  have hLipOn : LipschitzOnWith K M (uIcc s t) := hLip.lipschitzOnWith _
  have hAC : AbsolutelyContinuousOnInterval M s t :=
    hLipOn.absolutelyContinuousOnInterval
  exact hAC.intervalIntegrable_deriv

/-- **Integrated bound discharge from Lipschitz + a.e. pointwise
    bound.**  Given:

    * `M : ℝ → ℝ` globally Lipschitz;
    * An a.e. pointwise bound `deriv M τ ≤ Φ (M τ)` on `[0, T)`;
    * Interval-integrability of `τ ↦ Φ (M τ)` on every sub-interval
      of `[0, T)`;

    conclude the integrated bound

      `M t - M s ≤ ∫ τ in s..t, Φ (M τ)`   for `0 ≤ s ≤ t < T`.

    Unlike the FTC-hypothesis version in `C1_FTC.lean`, this version
    has no `hFTC` or `hDerivInt` hypothesis — both are discharged from
    `hLip` using mathlib's AC-FTC pipeline. -/
theorem integratedBound_of_lipschitz
    {M Φ : ℝ → ℝ} {T : ℝ} {K : NNReal}
    (hLip : LipschitzWith K M)
    (hPhiInt : ∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t < T →
      IntervalIntegrable (fun τ => Φ (M τ)) MeasureTheory.volume s t)
    (hAeBound : ∀ᵐ τ : ℝ,
      (0 ≤ τ ∧ τ < T) → deriv M τ ≤ Φ (M τ)) :
    ∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t < T →
      M t - M s ≤ ∫ τ in s..t, Φ (M τ) := by
  -- Assemble the three ingredients that `integratedBound_of_ftc_identity`
  -- needs, now discharging `hDerivInt` and `hFTC` from `hLip`.
  have hDerivInt : ∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t < T →
      IntervalIntegrable (fun τ => deriv M τ) MeasureTheory.volume s t :=
    fun s t _ _ _ => intervalIntegrable_deriv_of_lipschitz hLip s t
  have hFTC : ∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t < T →
      M t - M s = ∫ τ in s..t, deriv M τ :=
    fun _ _ _ hst _ => ftc_identity_of_lipschitz hLip hst
  -- Delegate the monotonicity + chaining argument to the existing
  -- hypothesis-form lemma in `C1_FTC.lean`.
  exact integratedBound_of_ftc_identity hDerivInt hPhiInt hAeBound hFTC

/-- **Curried-hypothesis variant.**  Same conclusion as
    `integratedBound_of_lipschitz`, but with the a.e. bound in the
    chained-implication form `0 ≤ τ → τ < T → deriv M τ ≤ Φ (M τ)`. -/
theorem integratedBound_of_lipschitz_curried
    {M Φ : ℝ → ℝ} {T : ℝ} {K : NNReal}
    (hLip : LipschitzWith K M)
    (hPhiInt : ∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t < T →
      IntervalIntegrable (fun τ => Φ (M τ)) MeasureTheory.volume s t)
    (hAeBound : ∀ᵐ τ : ℝ, 0 ≤ τ → τ < T → deriv M τ ≤ Φ (M τ)) :
    ∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t < T →
      M t - M s ≤ ∫ τ in s..t, Φ (M τ) :=
  integratedBound_of_lipschitz hLip hPhiInt
    ((ae_bound_curried_iff_conj).mp hAeBound)

/-- **Unconditional `GrowthMomentBundle` constructor.**

    Produces a `GrowthMomentBundle` from exactly the data mathematically
    needed:

    * `hTpos : 0 < T`;
    * `hM_lip : LipschitzWith K M` — global Lipschitz regularity of `M`;
    * `hPhiInt : ∀ 0 ≤ s ≤ t < T, IntervalIntegrable (Φ ∘ M) volume s t`;
    * `hAeBound : ∀ᵐ τ, (0 ≤ τ ∧ τ < T) → deriv M τ ≤ Φ (M τ)`.

    The `hIntegratedBound` field is discharged by
    `integratedBound_of_lipschitz`.  No FTC or derivative-integrability
    hypothesis is needed from the caller — both follow from `hM_lip`
    via mathlib's AC-FTC pipeline.

    This closes **OPEN.md item 3** (FTC-for-Lipschitz identity). -/
noncomputable def GrowthMomentBundle.ofLipschitzAndPointwiseBound
    {M Φ : ℝ → ℝ} {T : ℝ} {K : NNReal}
    (hTpos : 0 < T)
    (hM_lip : LipschitzWith K M)
    (hPhiInt : ∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t < T →
      IntervalIntegrable (fun τ => Φ (M τ)) MeasureTheory.volume s t)
    (hAeBound : ∀ᵐ τ : ℝ,
      (0 ≤ τ ∧ τ < T) → deriv M τ ≤ Φ (M τ)) :
    GrowthMomentBundle where
  M := M
  Φ := Φ
  T := T
  hTpos := hTpos
  K := K
  hM_lip := hM_lip
  hInt_loc := hPhiInt
  hIntegratedBound :=
    integratedBound_of_lipschitz hM_lip hPhiInt hAeBound

/-- **Curried-hypothesis form of the bundle constructor.**  Same as
    `GrowthMomentBundle.ofLipschitzAndPointwiseBound` but with the
    chained-implication form of the a.e. bound. -/
noncomputable def GrowthMomentBundle.ofLipschitzAndPointwiseBound_curried
    {M Φ : ℝ → ℝ} {T : ℝ} {K : NNReal}
    (hTpos : 0 < T)
    (hM_lip : LipschitzWith K M)
    (hPhiInt : ∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t < T →
      IntervalIntegrable (fun τ => Φ (M τ)) MeasureTheory.volume s t)
    (hAeBound : ∀ᵐ τ : ℝ, 0 ≤ τ → τ < T → deriv M τ ≤ Φ (M τ)) :
    GrowthMomentBundle :=
  GrowthMomentBundle.ofLipschitzAndPointwiseBound hTpos hM_lip hPhiInt
    ((ae_bound_curried_iff_conj).mp hAeBound)

/-! ## Sanity checks

Constant `M ≡ c` with `Φ ≡ 0` exercises the full discharge pipeline:
`LipschitzWith 0 M` is trivial, `deriv M ≡ 0` a.e., and the integrated
bound reduces to `0 ≤ 0`. -/

example (c : ℝ) (T : ℝ) (hT : 0 < T) :
    ∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t < T →
      (fun _ : ℝ => c) t - (fun _ : ℝ => c) s ≤
        ∫ τ in s..t, (fun _ : ℝ => (0 : ℝ)) ((fun _ : ℝ => c) τ) := by
  -- Constant function is `LipschitzWith 0`.
  have hLip : LipschitzWith 0 (fun _ : ℝ => c) := LipschitzWith.const c
  -- The a.e. bound is trivial (both sides computationally 0).
  have hAe : ∀ᵐ τ : ℝ, (0 ≤ τ ∧ τ < T) →
      deriv (fun _ : ℝ => c) τ ≤ (fun _ : ℝ => (0 : ℝ)) ((fun _ : ℝ => c) τ) := by
    refine Filter.Eventually.of_forall ?_
    intro τ _
    simp
  -- Integrability is trivial — constant function.
  have hPhiInt : ∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t < T →
      IntervalIntegrable
        (fun τ => (fun _ : ℝ => (0 : ℝ)) ((fun _ : ℝ => c) τ))
        MeasureTheory.volume s t := by
    intro s t _ _ _
    simpa using (intervalIntegrable_const : IntervalIntegrable
      (fun _ : ℝ => (0 : ℝ)) MeasureTheory.volume s t)
  exact integratedBound_of_lipschitz hLip hPhiInt hAe

/-- **Demonstration** that the new constructor produces a well-typed
    `GrowthMomentBundle` in the trivial constant-function case. -/
noncomputable example (c : ℝ) (T : ℝ) (hT : 0 < T) : GrowthMomentBundle :=
  GrowthMomentBundle.ofLipschitzAndPointwiseBound
    (M := fun _ => c) (Φ := fun _ => 0) (T := T) (K := 0)
    hT (LipschitzWith.const c)
    (by
      intro s t _ _ _
      simpa using (intervalIntegrable_const :
        IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) MeasureTheory.volume s t))
    (by
      refine Filter.Eventually.of_forall ?_
      intro τ _
      simp)

end NSBlwChain.Caveats
