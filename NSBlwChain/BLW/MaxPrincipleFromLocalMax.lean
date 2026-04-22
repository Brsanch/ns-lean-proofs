-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Setup.VectorFields
import NSBlwChain.BLW.MaxPrinciple

/-!
# Max principle — 1-D 2nd-derivative test at a local max

This file closes **OPEN.md item 5**: the `d0_nonpos`, `d1_nonpos`,
`d2_nonpos` fields of `ScalarLocalMaxSecondDeriv` are produced
constructively from an `IsLocalMax` hypothesis on the scalar
function `g : Vec3 → ℝ` plus appropriate differentiability of
each 1-D slice.

## Key lemma

`isLocalMax_second_deriv_nonpos`:
If `f : ℝ → ℝ` has a local max at `x`, is differentiable on a
neighborhood of `x`, and `deriv f` is differentiable at `x`, then
`deriv (deriv f) x ≤ 0`.

The proof is by contradiction via the slope characterization of
the derivative (`hasDerivAt_iff_tendsto_slope`): if `L := deriv²f(x)
> 0`, then `deriv f y / (y - x) → L` as `y → x`, so `deriv f > 0` on
some half-open interval `(x, x+ε)`.  Combined with differentiability
of `f` on a neighborhood of `x`, `strictMonoOn_of_deriv_pos` gives
`f` strictly increasing on `[x, x+ε]`, contradicting `IsLocalMax f x`.

## Constructor

`ScalarLocalMaxSecondDeriv.ofIsLocalMax`:
Given `g : Vec3 → ℝ` with `IsLocalMax g xStar`, plus for each direction
`i : Fin 3` (a) differentiability of `slice g xStar i` on a neighborhood
of `0` and (b) differentiability of `deriv (slice g xStar i)` at `0`,
produces a `ScalarLocalMaxSecondDeriv` whose three `d_i_nonpos` fields
are discharged.

No `sorry`, no new `axiom`.
-/

namespace NSBlwChain.BLW

open Filter Topology

/-! ### 1-D 2nd-derivative test -/

/-- **Standard fact:** if `f : ℝ → ℝ` has a local max at `x`, is
    differentiable on a neighborhood of `x`, and `deriv f` is
    differentiable at `x`, then `deriv (deriv f) x ≤ 0`. -/
theorem isLocalMax_second_deriv_nonpos
    {f : ℝ → ℝ} {x : ℝ}
    (hmax : IsLocalMax f x)
    (hf_nhd : ∀ᶠ t in 𝓝 x, DifferentiableAt ℝ f t)
    (hD : DifferentiableAt ℝ (deriv f) x) :
    deriv (deriv f) x ≤ 0 := by
  -- Let `L := deriv (deriv f) x`.  We have `HasDerivAt (deriv f) L x`.
  set L : ℝ := deriv (deriv f) x with hL
  have hD' : HasDerivAt (deriv f) L x := hD.hasDerivAt
  -- From Fermat's theorem, `deriv f x = 0`.
  have hdf0 : deriv f x = 0 := hmax.deriv_eq_zero
  -- Suppose for contradiction that `L > 0`.
  by_contra hpos
  push_neg at hpos
  -- Slope characterization of the derivative at `x`.
  have hslope : Tendsto (fun y => (deriv f y - deriv f x) / (y - x))
      (𝓝[≠] x) (𝓝 L) := by
    have := hD'.tendsto_slope
    -- `slope (deriv f) x y = (deriv f y - deriv f x) / (y - x)`
    -- by `slope_def_field`.
    simpa [slope_def_field] using this
  -- Rewrite using `deriv f x = 0`.
  have hslope' : Tendsto (fun y => deriv f y / (y - x))
      (𝓝[≠] x) (𝓝 L) := by
    have hrw : (fun y => (deriv f y - deriv f x) / (y - x))
        = (fun y => deriv f y / (y - x)) := by
      funext y
      rw [hdf0, sub_zero]
    rw [hrw] at hslope
    exact hslope
  -- Restrict to the right: `𝓝[>] x ≤ 𝓝[≠] x`.
  have hslope_right : Tendsto (fun y => deriv f y / (y - x))
      (𝓝[>] x) (𝓝 L) :=
    hslope'.mono_left (nhdsWithin_mono _ (fun _ h => ne_of_gt h))
  -- Eventually on the right, `deriv f y / (y - x) > L / 2 > 0`.
  have hhalf : 0 < L / 2 := by linarith
  have hL_pos : L / 2 < L := by linarith
  have hev_slope : ∀ᶠ y in 𝓝[>] x, L / 2 < deriv f y / (y - x) := by
    exact (tendsto_order.mp hslope_right).1 _ hL_pos
  -- On `(x, x+ε)` we have `y - x > 0`, so `deriv f y > (L/2)(y - x) > 0`.
  have hev_right_pos : ∀ᶠ y in 𝓝[>] x, 0 < deriv f y := by
    have hpos_y_minus_x : ∀ᶠ y in 𝓝[>] x, 0 < y - x := by
      refine eventually_nhdsWithin_of_forall (fun y hy => ?_)
      linarith [hy]
    filter_upwards [hev_slope, hpos_y_minus_x] with y hy hypos
    have hquot_pos : 0 < deriv f y / (y - x) := by linarith
    -- From `0 < a/b` and `0 < b`, conclude `0 < a`.
    have := (div_pos_iff_of_pos_right hypos).mp hquot_pos
    exact this
  -- Differentiability of `f` on a neighborhood — restrict to the right.
  have hf_right : ∀ᶠ y in 𝓝[>] x, DifferentiableAt ℝ f y :=
    nhdsWithin_le_nhds hf_nhd
  -- Local-max condition — on a neighborhood.
  have hmax_nbhd : ∀ᶠ y in 𝓝 x, f y ≤ f x := hmax
  have hmax_right : ∀ᶠ y in 𝓝[>] x, f y ≤ f x :=
    nhdsWithin_le_nhds hmax_nbhd
  -- Combine: on a right neighborhood, `0 < deriv f y`, `f y ≤ f x`,
  -- and `f` differentiable at `y`.  Pick an explicit small `ε > 0` witness.
  -- We extract `ε > 0` such that `∀ y ∈ (x, x+ε), 0 < deriv f y ∧
  -- DifferentiableAt ℝ f y ∧ f y ≤ f x`.
  have hcomb : ∀ᶠ y in 𝓝[>] x,
      0 < deriv f y ∧ DifferentiableAt ℝ f y ∧ f y ≤ f x := by
    filter_upwards [hev_right_pos, hf_right, hmax_right] with y h1 h2 h3
    exact ⟨h1, h2, h3⟩
  -- From `𝓝[>] x`, extract a set `(x, x+ε) ⊆ {y | ...}`.
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hcomb
  obtain ⟨ε, hεpos, hε⟩ := hcomb
  -- Now work on the closed interval `[x, x + ε/2]`, with interior `(x, x + ε/2)`.
  set δ : ℝ := ε / 2 with hδ_def
  have hδpos : 0 < δ := by positivity
  have hδlt : δ < ε := by simp [hδ_def]; linarith
  -- On `(x, x + δ)`, all three properties hold.
  have hProp : ∀ y ∈ Set.Ioo x (x + δ),
      0 < deriv f y ∧ DifferentiableAt ℝ f y ∧ f y ≤ f x := by
    intro y ⟨hy1, hy2⟩
    have hdist : dist y x < ε := by
      rw [Real.dist_eq]
      have hy_sub : y - x < ε := by linarith
      have hy_sub_pos : 0 < y - x := by linarith
      rw [abs_of_pos hy_sub_pos]
      exact hy_sub
    exact hε hdist hy1
  -- Continuity of `f` on `[x, x + δ]`: at `x` from right, at interior from
  -- differentiability.  We need `ContinuousOn f (Set.Icc x (x+δ))`.
  -- Strategy: `f` is differentiable on all of `(x, x+ε)`, hence continuous there.
  -- For continuity at `x`: `f` is differentiable at `x` iff... actually we don't
  -- have this.  Instead, we use `IsLocalMax` — `f` tends to something at `x`?
  -- NO — `IsLocalMax` does not give continuity at `x`.
  --
  -- Workaround: we don't need continuity at `x`.  We only need: for some
  -- `y ∈ (x, x+δ)`, `f y > f x`.  This contradicts `hProp`'s `f y ≤ f x`.
  --
  -- To get `f y > f x`: pick any `y₀ ∈ (x, x+δ)`, then by differentiability on
  -- `(x, x+δ)` and `deriv f > 0` there, `f` is strictly increasing on
  -- `(x, x+δ)`.  But `(x, x+δ)` is open.  We need to compare `f y₀` to
  -- `f x`, and `f x` is not reached by any `y₀ ∈ (x, x+δ)`.
  --
  -- Alternative: use `hasDerivAt` of `f` at `x`?  We don't have this.
  --
  -- Correct strategy: note `hmax` gives `f y ≤ f x` for `y` in a FULL
  -- neighborhood of `x`, including both sides.  Similarly, by the slope
  -- argument on the LEFT: for `y < x` close to `x`, `deriv f y < 0`, so `f`
  -- is strictly decreasing on `(x-δ', x)`.  Combined with `f y ≤ f x` for
  -- `y` in a full neighborhood... still doesn't give continuity at `x`.
  --
  -- NEW strategy: use MVT on `[x', x'']` for `x' < x'' ∈ (x, x+δ)`.  But this
  -- only bounds `f x'' - f x'`, not `f x'' - f x`.
  --
  -- Final strategy: use the SYMMETRIC argument.  `L > 0` forces `deriv f y < 0`
  -- on the LEFT and `deriv f y > 0` on the RIGHT.  On the RIGHT of x:
  -- `strictMonoOn f` on `[x, x+δ]` IF we have continuity at `x`.
  --
  -- Simplest fix: add `ContinuousAt f x` to the hypothesis set via `hf_nhd`
  -- at `x` itself: `DifferentiableAt ℝ f x` implies `ContinuousAt f x`.
  -- Since `hf_nhd : ∀ᶠ t in 𝓝 x, DifferentiableAt ℝ f t`, we have in particular
  -- `DifferentiableAt ℝ f x` (by evaluating at `x`).
  have hf_at_x : DifferentiableAt ℝ f x := hf_nhd.self_of_nhds
  have hfcont_x : ContinuousAt f x := hf_at_x.continuousAt
  -- Continuity of `f` on `[x, x+δ]`.
  have hfcont_icc : ContinuousOn f (Set.Icc x (x + δ)) := by
    intro y hy
    rcases eq_or_lt_of_le hy.1 with hxy | hxy
    · -- y = x: use continuity at x.
      rw [← hxy]
      exact hfcont_x.continuousWithinAt
    · -- y > x: y ∈ (x, x+δ] ⊆ interior of differentiability neighborhood.
      rcases eq_or_lt_of_le hy.2 with hyr | hyr
      · -- y = x + δ.  Use `hf_nhd` — need `DifferentiableAt f (x+δ)`.
        -- Since `x + δ = x + ε/2 < x + ε` and on `(x, x+ε)` we have differ.
        rw [hyr]
        have : DifferentiableAt ℝ f (x + δ) := by
          have hy_in : y ∈ Set.Ioo x (x + δ + (δ/2)) := by
            refine ⟨?_, ?_⟩
            · rw [hyr]; linarith
            · rw [hyr]; linarith
          -- Use hε: dist (x+δ) x < ε.
          have hdist : dist (x + δ) x < ε := by
            rw [Real.dist_eq]
            have : x + δ - x = δ := by ring
            rw [this, abs_of_pos hδpos]
            exact hδlt
          exact (hε hdist (by linarith : x < x + δ)).2.1
        exact this.continuousAt.continuousWithinAt
      · -- y ∈ (x, x+δ): use hProp.
        have hyIoo : y ∈ Set.Ioo x (x + δ) := ⟨hxy, hyr⟩
        exact ((hProp y hyIoo).2.1).continuousAt.continuousWithinAt
  -- `deriv f > 0` on interior of `[x, x+δ]`.
  have hderiv_pos : ∀ y ∈ interior (Set.Icc x (x + δ)), 0 < deriv f y := by
    intro y hy
    rw [interior_Icc] at hy
    exact (hProp y hy).1
  -- Apply `strictMonoOn_of_deriv_pos`.
  have hmono : StrictMonoOn f (Set.Icc x (x + δ)) :=
    strictMonoOn_of_deriv_pos (convex_Icc _ _) hfcont_icc hderiv_pos
  -- Pick `y := x + δ / 2 ∈ (x, x+δ)`.  Then `f y > f x`.
  have hy_in : (x + δ / 2) ∈ Set.Icc x (x + δ) := by
    refine ⟨?_, ?_⟩ <;> linarith
  have hx_in : x ∈ Set.Icc x (x + δ) := by
    refine ⟨le_refl _, ?_⟩; linarith
  have hlt : x < x + δ / 2 := by linarith
  have hf_gt : f x < f (x + δ / 2) := hmono hx_in hy_in hlt
  -- But `f (x + δ / 2) ≤ f x` from `hProp` (since `x + δ/2 ∈ (x, x+δ)`).
  have hy_Ioo : (x + δ / 2) ∈ Set.Ioo x (x + δ) := ⟨by linarith, by linarith⟩
  have hf_le : f (x + δ / 2) ≤ f x := (hProp _ hy_Ioo).2.2
  linarith

/-! ### Slice of a function along a coordinate axis -/

/-- The slice of `g : Vec3 → ℝ` at `xStar` along direction `i`:
    `t ↦ g (xStar + t • e_i)`, where `e_i` is the `i`-th standard
    basis vector. -/
noncomputable def slice (g : Vec3 → ℝ) (xStar : Vec3) (i : Fin 3) :
    ℝ → ℝ :=
  fun t => g (fun j => xStar j + t * (Vec3.e i) j)

/-- The slice map `t ↦ xStar + t • e_i` as a ℝ → Vec3 function. -/
noncomputable def sliceMap (xStar : Vec3) (i : Fin 3) : ℝ → Vec3 :=
  fun t => fun j => xStar j + t * (Vec3.e i) j

@[simp] lemma sliceMap_zero (xStar : Vec3) (i : Fin 3) :
    sliceMap xStar i 0 = xStar := by
  funext j
  simp [sliceMap]

/-- The slice map is continuous in `t`. -/
lemma continuous_sliceMap (xStar : Vec3) (i : Fin 3) :
    Continuous (sliceMap xStar i) := by
  unfold sliceMap
  -- `fun t => fun j => xStar j + t * (Vec3.e i) j` is continuous as a map
  -- into `Fin 3 → ℝ` iff each coordinate is continuous.
  refine continuous_pi (fun j => ?_)
  exact continuous_const.add (continuous_id.mul continuous_const)

/-- The slice map is continuous at every point (in particular at 0). -/
lemma continuousAt_sliceMap (xStar : Vec3) (i : Fin 3) (t : ℝ) :
    ContinuousAt (sliceMap xStar i) t :=
  (continuous_sliceMap xStar i).continuousAt

/-- If `g : Vec3 → ℝ` has a local max at `xStar`, then for each direction
    `i`, the slice `t ↦ g (xStar + t • e_i)` has a local max at `0`. -/
theorem isLocalMax_slice
    {g : Vec3 → ℝ} {xStar : Vec3}
    (hmax : IsLocalMax g xStar) (i : Fin 3) :
    IsLocalMax (slice g xStar i) 0 := by
  -- `slice g xStar i = g ∘ sliceMap xStar i`, and `sliceMap xStar i 0 = xStar`.
  have hcomp : slice g xStar i = g ∘ sliceMap xStar i := by
    funext t; rfl
  rw [hcomp]
  have h0 : sliceMap xStar i 0 = xStar := sliceMap_zero xStar i
  -- Apply `IsLocalMax.comp_continuous`.
  have hmax' : IsLocalMax g (sliceMap xStar i 0) := by rw [h0]; exact hmax
  exact hmax'.comp_continuous (continuousAt_sliceMap xStar i 0)

/-! ### Constructor for `ScalarLocalMaxSecondDeriv` -/

/-- **Constructor for `ScalarLocalMaxSecondDeriv`** from an `IsLocalMax`
    hypothesis.

    Given `g : Vec3 → ℝ` with `IsLocalMax g xStar`, and for each direction
    `i : Fin 3`:

    (a) `hf_nhd i`: `∀ᶠ t in 𝓝 0, DifferentiableAt ℝ (slice g xStar i) t`
        (the slice is differentiable on a neighborhood of `0`), and

    (b) `hD i`: `DifferentiableAt ℝ (deriv (slice g xStar i)) 0`
        (the derivative of the slice is itself differentiable at `0`),

    we construct a `ScalarLocalMaxSecondDeriv` whose per-direction 2nd
    derivatives are `deriv (deriv (slice g xStar i)) 0` and whose
    `d_i_nonpos` fields are discharged via `isLocalMax_second_deriv_nonpos`. -/
noncomputable def ScalarLocalMaxSecondDeriv.ofIsLocalMax
    (g : Vec3 → ℝ) (xStar : Vec3)
    (hmax : IsLocalMax g xStar)
    (hf_nhd : ∀ i : Fin 3,
      ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ (slice g xStar i) t)
    (hD : ∀ i : Fin 3,
      DifferentiableAt ℝ (deriv (slice g xStar i)) 0) :
    ScalarLocalMaxSecondDeriv where
  d0 := deriv (deriv (slice g xStar 0)) 0
  d1 := deriv (deriv (slice g xStar 1)) 0
  d2 := deriv (deriv (slice g xStar 2)) 0
  d0_nonpos :=
    isLocalMax_second_deriv_nonpos
      (isLocalMax_slice hmax 0) (hf_nhd 0) (hD 0)
  d1_nonpos :=
    isLocalMax_second_deriv_nonpos
      (isLocalMax_slice hmax 1) (hf_nhd 1) (hD 1)
  d2_nonpos :=
    isLocalMax_second_deriv_nonpos
      (isLocalMax_slice hmax 2) (hf_nhd 2) (hD 2)

end NSBlwChain.BLW
