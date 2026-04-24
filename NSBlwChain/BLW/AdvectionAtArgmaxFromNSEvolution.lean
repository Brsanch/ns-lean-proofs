-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Setup.VorticityDifferentiable
import NSBlwChain.BLW.UGradAtArgmax
import NSBlwChain.BLW.OmegaAdvectionProductRule

set_option diagnostics true
set_option diagnostics.threshold 100

/-!
# Advection vanishes at argmax of `|ω|²` — from `NSEvolutionAxioms`

Combines the two derivations landed tonight into the final
theorem: given a smooth NS solution bundle and a local max `xStar`
of `|ω(t,·)|²`, the ω-contracted advection
`ω · (u·∇ω)(xStar, t) = 0`.

## Proof

- `OmegaAdvectionProductRule.omega_dot_u_grad_omega_eq_half_u_grad_sqNorm`:
  `ω · (u·∇ω)(x) = (1/2) · u · ∇|ω|²(x)`
  (product-rule identity, needs componentwise differentiability).
- `UGradAtArgmax.u_dot_grad_eq_zero_at_localMax`:
  `u · ∇|ω|²(xStar) = 0` at a local max.
- Componentwise differentiability: from `NSEvolutionAxioms`' C^4
  smoothness via `vorticity_components_differentiableAt`.

Substitute and simplify: `ω · (u·∇ω)(xStar) = 0`.

## Consumed by

`VorticityLocalFrameData.advection_vanishes` field.  In the thin
wrapper
`BLW/VorticityFrameFromNSEvolution.VorticityLocalFrameData.ofNSEvolutionAxioms`,
`advectionAtArgmax` was defined to `0` and `advection_vanishes` was
`rfl`.  The present theorem shows that the *actual* advection scalar
at the argmax is also `0` — so the definitional `0` is mathematically
correct, not just a convenient choice.
-/

namespace NSBlwChain.BLW

open scoped BigOperators

/-- **Advection vanishes at the argmax of `|ω|²`.**

    Given `NSEvolutionAxioms u ν T`, a time `t ∈ [0, T)`, and a
    spatial local max `xStar` of `|ω(t,·)|²`, the vorticity-
    contracted advection
    `ω(xStar, t) · (u(xStar, t) · ∇) ω(·, t)|_{xStar} = 0`.

    Expressed in pointwise scalar form using the project's
    `partialDeriv` conventions. -/
theorem advection_vanishes_at_argmax_from_NSEvolution
    {u : VelocityField} {ν T : ℝ} (ax : NSEvolutionAxioms u ν T)
    {t : ℝ} (ht : 0 ≤ t) (htT : t < T)
    (xStar : Vec3)
    (hmax : IsLocalMax
      (fun y : Vec3 => Vec3.dot (vorticity u t y) (vorticity u t y))
      xStar) :
    (∑ j : Fin 3, vorticity u t xStar j *
      (∑ i : Fin 3, u t xStar i *
        partialDeriv (fun y => vorticity u t y j) i xStar)) = 0 := by
  -- Step 1: vorticity components are differentiable at xStar (from NSEv C^4).
  have hω : ∀ k : Fin 3,
      DifferentiableAt ℝ (fun y => vorticity u t y k) xStar :=
    ax.vorticity_components_differentiableAt ht htT xStar
  -- Step 2: apply the product-rule identity at the direction `u t xStar`.
  have h_prod := omega_dot_u_grad_omega_eq_half_u_grad_sqNorm
    (ω := fun y => vorticity u t y) (x := xStar) hω (u t xStar)
  rw [h_prod]
  -- Goal: (1/2) * (∑ i, (u t xStar) i * ∂ᵢ|ω|²(xStar)) = 0.
  -- Step 3: at a local max of |ω|², the directional derivative vanishes.
  have h_zero :
      (∑ i : Fin 3, u t xStar i *
        partialDeriv (fun y => Vec3.dot (vorticity u t y) (vorticity u t y))
          i xStar) = 0 :=
    u_dot_grad_eq_zero_at_localMax (g := fun y => Vec3.dot (vorticity u t y)
      (vorticity u t y)) hmax (u t xStar)
  rw [h_zero]
  ring

end NSBlwChain.BLW
