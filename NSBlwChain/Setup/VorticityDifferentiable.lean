-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Setup.VectorFields
import NSBlwChain.Setup.NSHypothesis
import NSBlwChain.Setup.CurlSmoothness

/-!
# Differentiability of vorticity components from `NSEvolutionAxioms`

This file packages the curl-smoothness results of `CurlSmoothness.lean`
into the **exact form** consumed by
`LocalFrameDerivativeData.ofDifferentiableVectorField` downstream in
`BLW/DerivFrameFromProductRule.lean`.

## What this gives

Given `NSEvolutionAxioms u ν T` and a time `t ∈ [0, T)`, each
component `fun y => vorticity u t y k` is `DifferentiableAt` at
every spatial point.  This lets step (i) of the BLW chain's local-
frame derivative setup (`LocalFrameDerivativeData`) be produced
directly from the NS bundle without taking the differentiability
hypothesis as an extra input.

## Why this matters

In `FromNSEvolution.lean`'s top-level wiring, the `NSArgmaxInputs`
bundle takes scalar field values as given.  Deriving those scalars
from the NS bundle's actual smoothness is the "structural wiring →
real derivation" upgrade for item 6.  This file provides one of the
required building blocks (pointwise differentiability of each
vorticity component).
-/

namespace NSBlwChain

/-- **Vorticity-component differentiability from `NSEvolutionAxioms`.**

    Given a smooth NS solution bundle, each component of the
    vorticity `ω = curl u` is `DifferentiableAt ℝ` at every spatial
    point `xStar`, for every time `t ∈ [0, T)`.

    The proof: `NSEvolutionAxioms.smooth_in_space` delivers
    `ContDiff ℝ 4 (u t)`, then `curl_component_differentiableAt_of_ContDiff4`
    (from `CurlSmoothness.lean`) produces the pointwise
    differentiability. -/
theorem NSEvolutionAxioms.vorticity_component_differentiableAt
    {u : VelocityField} {ν T : ℝ} (ax : NSEvolutionAxioms u ν T)
    {t : ℝ} (ht : 0 ≤ t) (htT : t < T)
    (xStar : Vec3) (k : Fin 3) :
    DifferentiableAt ℝ (fun y => vorticity u t y k) xStar := by
  have h_smooth : ContDiff ℝ 4 (u t) := ax.smooth_in_space t ht htT
  -- Unfold `vorticity` to expose the curl.
  unfold vorticity
  exact curl_component_differentiableAt_of_ContDiff4 h_smooth xStar k

/-- **All three vorticity components differentiable.**

    Pointwise form: every component of the vorticity is
    differentiable at `xStar`.  Used by consumers that need
    `∀ k : Fin 3, DifferentiableAt ℝ (fun y => vorticity u t y k) xStar`
    as a single hypothesis (e.g.,
    `LocalFrameDerivativeData.ofDifferentiableVectorField`). -/
theorem NSEvolutionAxioms.vorticity_components_differentiableAt
    {u : VelocityField} {ν T : ℝ} (ax : NSEvolutionAxioms u ν T)
    {t : ℝ} (ht : 0 ≤ t) (htT : t < T)
    (xStar : Vec3) :
    ∀ k : Fin 3, DifferentiableAt ℝ (fun y => vorticity u t y k) xStar :=
  fun k => ax.vorticity_component_differentiableAt ht htT xStar k

/-- **Smoothness of vorticity, packaged form.**

    `vorticity u t : Vec3 → Vec3` is `ContDiff ℝ 3` at every
    `t ∈ [0, T)`.  This is the direct consequence of curl taking
    `C^{n+1}` to `C^n` applied to the `C^4` smoothness of `u`. -/
theorem NSEvolutionAxioms.vorticity_contDiff
    {u : VelocityField} {ν T : ℝ} (ax : NSEvolutionAxioms u ν T)
    {t : ℝ} (ht : 0 ≤ t) (htT : t < T) :
    ContDiff ℝ 3 (fun y => vorticity u t y) := by
  have h_smooth : ContDiff ℝ 4 (u t) := ax.smooth_in_space t ht htT
  unfold vorticity
  exact curl_contDiff (n := 3) h_smooth

/-- **Smoothness of `|ω|²`.**

    The scalar field `|ω(t, ·)|² = ∑_k (ω(t, ·) k)²` is `ContDiff ℝ 3`
    for every `t ∈ [0, T)`, as a sum of squares of `ContDiff 3`
    component functions.  Consumed by step (ii) of the BLW chain
    (Hessian / max-principle analysis on `|ω|²`). -/
theorem NSEvolutionAxioms.vorticitySqNorm_contDiff
    {u : VelocityField} {ν T : ℝ} (ax : NSEvolutionAxioms u ν T)
    {t : ℝ} (ht : 0 ≤ t) (htT : t < T) :
    ContDiff ℝ 3
      (fun y : Vec3 => Vec3.dot (vorticity u t y) (vorticity u t y)) := by
  have h_vort : ContDiff ℝ 3 (fun y => vorticity u t y) :=
    ax.vorticity_contDiff ht htT
  -- Each component `fun y => vorticity u t y k` is ContDiff 3 (via contDiff_pi).
  have h_comp : ∀ k : Fin 3, ContDiff ℝ 3 (fun y => vorticity u t y k) := by
    intro k
    rw [contDiff_pi] at h_vort
    exact h_vort k
  -- `Vec3.dot v v = ∑ i, v i * v i`.
  unfold Vec3.dot
  -- Goal: ContDiff 3 (fun y => ∑ i, (vorticity u t y i) * (vorticity u t y i))
  -- Each summand is a product of two ContDiff 3 functions.
  apply ContDiff.sum
  intro k _
  exact (h_comp k).mul (h_comp k)

end NSBlwChain
