-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Setup.NSHypothesis

set_option diagnostics true
set_option diagnostics.threshold 100

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

namespace NSBlwChain

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

end NSBlwChain
