-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Setup.NSHypothesis

/-!
# Component-wise extraction of the vorticity equation at a point

`NSEvolutionAxioms.vorticity_equation` asserts a **vector-valued**
pointwise equality between `materialDerivative u ω` and
`(ω·∇)u + ν·Δω`.  For the BLW chain's step (iii) at the argmax, we
need the **scalar-valued** equation in the `j`-th component.

This file provides that extraction as a small utility lemma.

## Usage

Step (iii)'s `vorticity_eq_contracted` identity contracts the
j-th component equation with `ω_j` and sums.  Before that
contraction, we need the scalar j-th equation.  This is a pure
algebraic consequence of the bundle's `vorticity_equation` field,
not new analysis.

## Main result

`NSEvolutionAxioms.vorticity_equation_scalar`: for any time
`t ∈ [0, T)`, spatial point `x : Vec3`, and component `j : Fin 3`,

  `(materialDerivative u ω t x) j = vortexStretching u ω t x j + ν · vectorLaplacian (ω t) x j`,

where `ω = vorticity u`.  This is simply the j-th component of the
bundle's vector-valued `vorticity_equation`.
-/

set_option diagnostics true
set_option diagnostics.threshold 100

namespace NSBlwChain

open scoped BigOperators

/-- **Scalar j-component of the vorticity equation.**  The bundle's
    `vorticity_equation` field asserts a pointwise equality between
    two vector-valued functions; applying both sides at index `j`
    gives the scalar equation.  This is pure unfolding. -/
theorem NSEvolutionAxioms.vorticity_equation_scalar
    {u : VelocityField} {ν T : ℝ} (ax : NSEvolutionAxioms u ν T)
    {t : ℝ} (ht : 0 ≤ t) (htT : t < T) (x : Vec3) (j : Fin 3) :
    materialDerivative u (vorticity u) t x j =
      vortexStretching u (vorticity u) t x j
        + ν * vectorLaplacian (vorticity u t) x j := by
  have h := ax.vorticity_equation t ht htT x
  -- `h` is a vector equality; apply both sides at `j`.
  have hj := congrFun h j
  -- Left side of `h` is `materialDerivative u (vorticity u) t x`
  -- (already a function `Fin 3 → ℝ`).  Applied at `j` gives the
  -- scalar.  Right side is `fun j => vortexStretching ... j + ν *
  -- vectorLaplacian ... j`; applied at `j` gives exactly the RHS.
  exact hj

/-- **Contracted vorticity equation.**  Dot-product the vector
    vorticity equation with the vorticity `ω` itself at the point
    `x`, and sum over components:

      `ω · D_t ω = ω · ((ω·∇) u) + ν · ω · Δω`.

    This is the scalar-valued form consumed by the BLW chain's step
    (iii) `vorticity_eq_contracted` field (after rearrangement using
    `ω · ∂_t ω = ∂_t (|ω|²/2)` and the advection-vanishes-at-argmax
    identity).  Proof: sum the scalar j-component equations weighted
    by `ω_j(x)`. -/
theorem NSEvolutionAxioms.vorticity_equation_contracted_with_omega
    {u : VelocityField} {ν T : ℝ} (ax : NSEvolutionAxioms u ν T)
    {t : ℝ} (ht : 0 ≤ t) (htT : t < T) (x : Vec3) :
    Vec3.dot (vorticity u t x)
             (materialDerivative u (vorticity u) t x) =
      Vec3.dot (vorticity u t x)
               (vortexStretching u (vorticity u) t x)
        + ν * Vec3.dot (vorticity u t x)
                       (fun j => vectorLaplacian (vorticity u t) x j) := by
  -- Unfold Vec3.dot to expose the Fin 3 sums on both sides.
  unfold Vec3.dot
  -- Goal:
  --   ∑ j, ω_j · MD_j = ∑ j, ω_j · VS_j + ν · ∑ j, ω_j · VL_j
  -- Distribute ν inside the second sum (Finset.mul_sum forward).
  rw [Finset.mul_sum]
  -- Goal:
  --   ∑ j, ω_j · MD_j = ∑ j, ω_j · VS_j + ∑ j, ν · (ω_j · VL_j)
  -- Combine the two sums on RHS.
  rw [← Finset.sum_add_distrib]
  -- Goal: ∑ j, ω_j · MD_j = ∑ j, (ω_j · VS_j + ν · (ω_j · VL_j))
  apply Finset.sum_congr rfl
  intro j _
  -- Goal: ω_j · MD_j = ω_j · VS_j + ν · (ω_j · VL_j)
  have hj := ax.vorticity_equation_scalar ht htT x j
  -- hj: MD_j = VS_j + ν · VL_j
  rw [hj]
  ring

end NSBlwChain
