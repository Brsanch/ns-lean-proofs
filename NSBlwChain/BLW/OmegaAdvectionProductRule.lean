-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.BLW.ScalarProductRule
import NSBlwChain.BLW.UGradAtArgmax

set_option diagnostics true
set_option diagnostics.threshold 100

/-!
# Product rule: `ω · (u · ∇ω) = (1/2) u · ∇|ω|²`

Closes the remaining hypothesis of
`AdvectionVanishes.advection_vanishes_at_argmax`: the product-rule
identity that expresses the vorticity-weighted advection
`ω · (u · ∇ω)(x)` as half of the directional derivative of `|ω|²`
along `u`.

Combined with `UGradAtArgmax.u_dot_grad_eq_zero_at_localMax` applied
to `g := |ω|²`, both hypotheses of `advection_vanishes_at_argmax` are
now derived from first principles:

- **Product rule** (this file): `ω · (u · ∇ω) = (1/2) u · ∇|ω|²`.
- **Argmax** (`UGradAtArgmax`): `u · ∇|ω|²(xStar) = 0` at a local
  max of `|ω|²`.

Together: `ω · (u · ∇ω)(xStar) = 0` at the argmax of `|ω|²`.  The
step-(iii) `advection_vanishes` field of `VorticityLocalFrameData`
is now a theorem, not a taken hypothesis.

## Proof

`∂ᵢ(|ω|²) = 2 · Σₖ ωₖ · ∂ᵢωₖ` (by `partialDeriv_dot_self_eq`).
Multiply by `uᵢ`, sum over `i`:

  `u · ∇|ω|² = Σᵢ uᵢ · ∂ᵢ(|ω|²)
              = 2 · Σᵢ Σₖ uᵢ · ωₖ · ∂ᵢωₖ
              = 2 · Σₖ ωₖ · (Σᵢ uᵢ · ∂ᵢωₖ)
              = 2 · ω · (u · ∇ω)`.

So `ω · (u · ∇ω) = (1/2) · u · ∇|ω|²`.
-/

namespace NSBlwChain.BLW

open scoped BigOperators

/-- **Product-rule identity for `ω · (u · ∇ω)`.**

    For a vector field `ω : Vec3 → Vec3` differentiable
    componentwise at `x`, any direction `u : Vec3`:

      `Σⱼ ωⱼ(x) · Σᵢ uᵢ · ∂ᵢωⱼ(x) = (1/2) · Σᵢ uᵢ · ∂ᵢ(|ω|²)(x)`.

    Combined with `u_dot_grad_eq_zero_at_localMax` (from
    `UGradAtArgmax.lean`) applied to `|ω|²`, this discharges the
    `omega_dot_u_grad_omega = 0` identity at a local max of `|ω|²`. -/
theorem omega_dot_u_grad_omega_eq_half_u_grad_sqNorm
    {ω : Vec3 → Vec3} {x : Vec3}
    (hω : ∀ k : Fin 3, DifferentiableAt ℝ (fun y => ω y k) x)
    (u : Vec3) :
    (∑ j : Fin 3,
      ω x j * (∑ i : Fin 3, u i * partialDeriv (fun y => ω y j) i x))
    = (1 / 2) *
      (∑ i : Fin 3,
        u i * partialDeriv (fun y => Vec3.dot (ω y) (ω y)) i x) := by
  -- Rewrite ∂ᵢ(|ω|²) using the scalar product rule.
  have hpd : ∀ i : Fin 3,
      partialDeriv (fun y => Vec3.dot (ω y) (ω y)) i x
        = 2 * ∑ k : Fin 3, ω x k * partialDeriv (fun y => ω y k) i x :=
    fun i => partialDeriv_dot_self_eq hω i
  -- Expand all Fin 3 sums explicitly via Fin.sum_univ_three,
  -- rewrite each ∂ᵢ(|ω|²) via hpd (also expanded), then ring-close
  -- on concrete polynomial arithmetic.
  simp only [Fin.sum_univ_three, hpd]
  ring

end NSBlwChain.BLW
