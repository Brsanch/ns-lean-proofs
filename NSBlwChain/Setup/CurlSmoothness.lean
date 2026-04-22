-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Setup.VectorFields

/-!
# Smoothness of `curl` (foundation for `NSArgmaxInputs` derivation)

This file proves that the curl of a `C^{n+1}` vector field on
`ℝ^3` is `C^n`, via `ContDiff.fderiv_right` (smoothness of the
Fréchet derivative) and continuous-linear-map evaluation.

## Main result

`curl_contDiff` — if `F : Vec3 → Vec3` is `ContDiff ℝ (n+1)`, then
`curl F` is `ContDiff ℝ n`.  Specializing to `n = 3` (paper §12.3
regularity requirement on `u`), the vorticity `ω = curl u` is
`C^3`, which is enough to make the local-frame derivative and
second-derivative arguments of `NSArgmaxInputs` well-defined
pointwise.

## Usage

The downstream consumer
`LocalFrameDerivativeData.ofDifferentiableVectorField` requires
`DifferentiableAt ℝ (fun y => ω y k) xStar` for each `k : Fin 3`.
This follows from `curl_contDiff` via
`ContDiff.differentiable` and component projection.
-/

namespace NSBlwChain

open scoped BigOperators

/-- **Smoothness of a single component of `partialDerivVec`.**

    Component `j` of `partialDerivVec F i` at `x` equals
    `fderiv ℝ F x (Vec3.e i) j`.  This is obtained by composing:
    - `fderiv ℝ F : Vec3 → (Vec3 →L[ℝ] Vec3)` — `ContDiff ℝ n`
      by `ContDiff.fderiv_right`;
    - evaluation at the constant `Vec3.e i`, which is a
      continuous-linear map (`ContinuousLinearMap.apply`);
    - projection to component `j : Fin 3`, also a continuous-linear
      map (`ContinuousLinearMap.proj`).

    All three compose to a `ContDiff ℝ n` function. -/
theorem partialDerivVec_component_contDiff
    {F : Vec3 → Vec3} {n : ℕ∞} (i j : Fin 3)
    (hF : ContDiff ℝ (n + 1) F) :
    ContDiff ℝ n (fun x => partialDerivVec F i x j) := by
  -- Unfold the definition.
  unfold partialDerivVec
  -- Goal: ContDiff ℝ n (fun x => fderiv ℝ F x (Vec3.e i) j)
  -- `fderiv ℝ F` is ContDiff ℝ n.
  have h_fderiv : ContDiff ℝ n (fun x => fderiv ℝ F x) :=
    hF.fderiv_right (le_refl _)
  -- Evaluate at the constant `Vec3.e i`: the map
  -- `L ↦ L v` (with `v` fixed) is linear, so composition preserves ContDiff.
  -- Finally project to component `j`: linear in `Vec3 = Fin 3 → ℝ`, so ContDiff.
  fun_prop

/-- **Smoothness of `partialDerivVec` (vector form).**

    `partialDerivVec F i : Vec3 → Vec3` is `ContDiff ℝ n` whenever
    `F` is `ContDiff ℝ (n+1)`.  Follows from the component-wise
    lemma plus `contDiff_pi`. -/
theorem partialDerivVec_contDiff
    {F : Vec3 → Vec3} {n : ℕ∞} (i : Fin 3)
    (hF : ContDiff ℝ (n + 1) F) :
    ContDiff ℝ n (fun x => partialDerivVec F i x) := by
  rw [contDiff_pi]
  intro j
  exact partialDerivVec_component_contDiff i j hF

/-- **Smoothness of `curl`.**

    If `F : Vec3 → Vec3` is `ContDiff ℝ (n+1)`, then
    `curl F : Vec3 → Vec3` is `ContDiff ℝ n`.

    Each component of `curl F` is a difference of two components of
    `partialDerivVec F i`, so the result follows componentwise. -/
theorem curl_contDiff
    {F : Vec3 → Vec3} {n : ℕ∞}
    (hF : ContDiff ℝ (n + 1) F) :
    ContDiff ℝ n (fun x => curl F x) := by
  rw [contDiff_pi]
  intro k
  -- Expand curl's k-th component via the `if`-chain.
  unfold curl
  -- For each k ∈ Fin 3, the component is a difference of two
  -- partialDerivVec component evaluations.
  fin_cases k
  · -- k = 0: curl F x 0 = partialDerivVec F 1 x 2 - partialDerivVec F 2 x 1
    simp only [Fin.mk_zero, ite_true, if_pos rfl]
    exact (partialDerivVec_component_contDiff 1 2 hF).sub
            (partialDerivVec_component_contDiff 2 1 hF)
  · -- k = 1: curl F x 1 = partialDerivVec F 2 x 0 - partialDerivVec F 0 x 2
    simp only [Fin.mk_one, ite_false, if_neg (by decide : (1 : Fin 3) ≠ 0),
               if_pos rfl]
    exact (partialDerivVec_component_contDiff 2 0 hF).sub
            (partialDerivVec_component_contDiff 0 2 hF)
  · -- k = 2: curl F x 2 = partialDerivVec F 0 x 1 - partialDerivVec F 1 x 0
    simp only [if_neg (by decide : (2 : Fin 3) ≠ 0),
               if_neg (by decide : (2 : Fin 3) ≠ 1)]
    exact (partialDerivVec_component_contDiff 0 1 hF).sub
            (partialDerivVec_component_contDiff 1 0 hF)

/-- **Corollary: pointwise differentiability of `curl F` components.**

    For `F : Vec3 → Vec3` in `ContDiff ℝ 4` (the NS solution's
    regularity class), each component `fun y => curl F y k` is
    `DifferentiableAt ℝ` at every point.  This is the exact
    hypothesis consumed by
    `LocalFrameDerivativeData.ofDifferentiableVectorField`. -/
theorem curl_component_differentiableAt_of_ContDiff4
    {F : Vec3 → Vec3}
    (hF : ContDiff ℝ 4 F) (x : Vec3) (k : Fin 3) :
    DifferentiableAt ℝ (fun y => curl F y k) x := by
  have h_curl : ContDiff ℝ 3 (fun y => curl F y) :=
    curl_contDiff (n := 3) (by
      -- 3 + 1 = 4, so hF : ContDiff ℝ 4 F matches.
      exact hF)
  have h_comp : ContDiff ℝ 3 (fun y => curl F y k) := by
    rw [contDiff_pi] at h_curl
    exact h_curl k
  -- ContDiff 3 → Differentiable (since 1 ≤ 3).
  exact h_comp.differentiable (by norm_num) x

end NSBlwChain
