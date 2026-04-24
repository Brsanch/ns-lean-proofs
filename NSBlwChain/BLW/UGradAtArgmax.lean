-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Setup.VectorFields

/-!
# Directional derivative at a local maximum vanishes

At a local maximum `xStar` of a differentiable scalar function
`g : Vec3 → ℝ`, the directional derivative in any direction `u`
vanishes.  In particular, for `g = |ω|²` this gives the argmax
hypothesis `u·∇|ω|²(xStar) = 0` that `AdvectionVanishes.lean`
consumes.

## Main result

`u_dot_grad_eq_zero_at_localMax` — for differentiable `g` with
`IsLocalMax g xStar` and any `u : Vec3`,
`Σᵢ uᵢ · partialDerivᵢ g xStar = 0`.

Consumed by the argmax-half of step-(iii) wiring: the scalar
`u_dot_grad_sqNorm := u · ∇|ω|²(xStar)` that appears as a
hypothesis of `advection_vanishes_at_argmax` in
`AdvectionVanishes.lean` is exactly 0 at a local max of `|ω|²`.
-/

namespace NSBlwChain.BLW

open scoped BigOperators

/-- **Directional derivative vanishes at a local max.**

    For a differentiable scalar `g : Vec3 → ℝ` attaining a local max
    at `xStar`, the sum `Σᵢ uᵢ · ∂ᵢg(xStar) = fderiv g xStar u = 0`
    for any direction `u : Vec3`.

    Consequence: if `g := |ω|²`, then `u · ∇|ω|²(xStar) = 0`.
    Consumed by `AdvectionVanishes.advection_vanishes_at_argmax`'s
    `h_argmax` hypothesis. -/
theorem u_dot_grad_eq_zero_at_localMax
    {g : Vec3 → ℝ} {xStar : Vec3}
    (hmax : IsLocalMax g xStar)
    (u : Vec3) :
    (∑ i : Fin 3, u i * partialDeriv g i xStar) = 0 := by
  -- Step 1: fderiv g xStar = 0 at the local max (mathlib's
  -- `IsLocalMax.fderiv_eq_zero` — no differentiability hypothesis
  -- needed; returns 0 by `deriv = 0` convention if non-differentiable).
  have h_fderiv_zero : fderiv ℝ g xStar = 0 := hmax.fderiv_eq_zero
  -- Step 2: partialDeriv g i xStar = (fderiv g xStar) (Vec3.e i).
  -- When fderiv g xStar = 0 as a continuous-linear map, evaluating
  -- at any vector gives 0.
  have h_partial_zero : ∀ i : Fin 3, partialDeriv g i xStar = 0 := by
    intro i
    unfold partialDeriv
    rw [h_fderiv_zero]
    rfl
  -- Step 3: the sum is a sum of zeros.
  simp [h_partial_zero]

end NSBlwChain.BLW
