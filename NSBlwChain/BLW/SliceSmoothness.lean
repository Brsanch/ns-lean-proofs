-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Setup.VorticityDifferentiable
import NSBlwChain.BLW.MaxPrincipleFromLocalMax

/-!
# Smoothness of scalar slices

This file proves that the coordinate-axis slice `slice g xStar i`
(from `BLW/MaxPrincipleFromLocalMax.lean`) inherits the smoothness
of `g`.  Together with
`NSEvolutionAxioms.vorticitySqNorm_contDiff`, this delivers step
(ii) of the BLW chain's analytical inputs from `NSEvolutionAxioms`.

## Results

* `sliceMap_contDiff` — the affine map `t ↦ xStar + t · e_i` is
  `ContDiff ℝ ∞`.
* `slice_contDiff_of_contDiff` — if `g : Vec3 → ℝ` is `ContDiff ℝ n`,
  then `slice g xStar i` is `ContDiff ℝ n` for every `xStar, i`.
* `NSEvolutionAxioms.sqNormVort_slice_contDiff` — the `|ω|²` slice at
  `xStar` in direction `i` is `ContDiff ℝ 3`, derived from the NS
  bundle's `C^4` smoothness of `u`.

The downstream consumer `ScalarLocalMaxSecondDeriv.ofIsLocalMax` takes
two hypotheses per direction:
- `hf_nhd i : ∀ᶠ t in 𝓝 0, DifferentiableAt ℝ (slice g xStar i) t`
- `hD i : DifferentiableAt ℝ (deriv (slice g xStar i)) 0`

Both follow from `slice` being `ContDiff ℝ 3`: (a) `ContDiff 3 →
Differentiable` gives `DifferentiableAt` at every point; (b)
`ContDiff 3 → ContDiff 2 (deriv)` gives `Differentiable (deriv)`,
hence `DifferentiableAt (deriv) 0`.
-/

namespace NSBlwChain.BLW

open NSBlwChain

/-- **Smoothness of `sliceMap`.**  The affine map `t ↦ xStar + t · e_i`
    from `ℝ` to `Vec3` is `ContDiff ℝ ∞` (any order of smoothness). -/
theorem sliceMap_contDiff (xStar : Vec3) (i : Fin 3) (n : ℕ∞) :
    ContDiff ℝ n (sliceMap xStar i) := by
  unfold sliceMap
  -- `fun t => fun j => xStar j + t * (Vec3.e i) j`
  -- Componentwise: `fun t => xStar j + t * c_j` is linear-affine, ContDiff ∞.
  refine contDiff_pi.mpr (fun j => ?_)
  -- Goal: `ContDiff ℝ n (fun t : ℝ => xStar j + t * Vec3.e i j)`.
  fun_prop

/-- **Slice of a `ContDiff ℝ n` function is `ContDiff ℝ n`.**

    `slice g xStar i = g ∘ sliceMap xStar i`, and composition of
    `ContDiff n` with `ContDiff ∞` (the affine `sliceMap`) preserves
    `ContDiff n`. -/
theorem slice_contDiff_of_contDiff
    {g : Vec3 → ℝ} {n : ℕ∞} (hg : ContDiff ℝ n g)
    (xStar : Vec3) (i : Fin 3) :
    ContDiff ℝ n (slice g xStar i) := by
  have h_map : ContDiff ℝ n (sliceMap xStar i) := sliceMap_contDiff xStar i n
  -- `slice g xStar i = g ∘ sliceMap xStar i` (definitionally).
  show ContDiff ℝ n (g ∘ sliceMap xStar i)
  exact hg.comp h_map

end NSBlwChain.BLW

namespace NSBlwChain

open NSBlwChain.BLW Topology Filter

/-- **`|ω|² slice smoothness from `NSEvolutionAxioms`.**

    The slice of `|ω(t, ·)|²` at `xStar` in direction `e_i` is
    `ContDiff ℝ 3` for every `t ∈ [0, T)` and every `i : Fin 3`.
    Derived from `NSEvolutionAxioms.vorticitySqNorm_contDiff` +
    `slice_contDiff_of_contDiff`. -/
theorem NSEvolutionAxioms.sqNormVort_slice_contDiff
    {u : VelocityField} {ν T : ℝ} (ax : NSEvolutionAxioms u ν T)
    {t : ℝ} (ht : 0 ≤ t) (htT : t < T)
    (xStar : Vec3) (i : Fin 3) :
    ContDiff ℝ 3
      (slice (fun y : Vec3 => Vec3.dot (vorticity u t y) (vorticity u t y))
        xStar i) :=
  slice_contDiff_of_contDiff (ax.vorticitySqNorm_contDiff ht htT) xStar i

/-- **Slice-differentiable-on-neighborhood from `NSEvolutionAxioms`.**

    Every point is a neighborhood-of-differentiability for the
    `|ω|²` slice.  Consumed by `ScalarLocalMaxSecondDeriv.ofIsLocalMax`'s
    `hf_nhd` field. -/
theorem NSEvolutionAxioms.sqNormVort_slice_differentiableAt_nhds
    {u : VelocityField} {ν T : ℝ} (ax : NSEvolutionAxioms u ν T)
    {t : ℝ} (ht : 0 ≤ t) (htT : t < T)
    (xStar : Vec3) (i : Fin 3) :
    ∀ᶠ s in 𝓝 (0 : ℝ),
      DifferentiableAt ℝ
        (slice (fun y : Vec3 => Vec3.dot (vorticity u t y) (vorticity u t y))
          xStar i) s := by
  have h_slice := ax.sqNormVort_slice_contDiff ht htT xStar i
  refine Filter.Eventually.of_forall (fun s => ?_)
  -- `fun_prop` handles `ContDiff n f, n > 0 → DifferentiableAt f s`
  -- with the coercion between `ℕ∞` and `WithTop ℕ∞` implicit.
  exact h_slice.differentiable (by norm_num) s

/- Note: the slice-derivative-differentiable-at-0 corollary requires
   `ContDiff.deriv : ContDiff n f → ContDiff (n-1) (deriv f)` in
   mathlib 4.29, which resolves `h_slice.deriv` to `Exists.deriv` in
   this elaboration context (ContDiff unfolded to `∃ p, HasFTaylorSeriesUpTo`
   before the dot-notation lookup succeeded).  Deferred until a
   clean `ContDiff.deriv` invocation via explicit application is tested.
   Consumers can currently derive it inline via `iteratedDeriv`. -/

end NSBlwChain
