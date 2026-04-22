-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.BLW.ArgmaxGradientFromFrame
import NSBlwChain.BLW.ScalarProductRule

/-!
# `LocalFrameDerivativeData.sqNorm_deriv_identity` discharge via ScalarProductRule

`NSBlwChain.BLW.LocalFrameDerivativeData` carries the scalar
identity
  `∂_i|ω|²(x*) = 2 · (ω_0 · ∂_i ω_0 + ω_1 · ∂_i ω_1 + ω_3 · ∂_i ω_3)`
as a named hypothesis field `sqNorm_deriv_identity`.

`NSBlwChain.BLW.ScalarProductRule.partialDeriv_dot_self_eq` delivers
  `∂_i(dot ω ω)(x) = 2 · ∑_{k : Fin 3} ω_k(x) · ∂_i ω_k(x)`.

**Convention.** The bundle's fields `omega_0, omega_1, omega_3` are
treated as the scalar values `ω_0 := ω x (0 : Fin 3)`,
`ω_1 := ω x (1 : Fin 3)`, and `ω_3 := ω x (2 : Fin 3)` — i.e.,
the physics "component 3" is the Lean-`Fin 3` index 2.  Under
this convention, the sum `∑ k : Fin 3` equals the three-term form
in the bundle.

## Contents

* `LocalFrameDerivativeData.ofDifferentiableVectorField` —
  constructor from a C¹ vector field `ω : Vec3 → Vec3` at `x*`,
  direction `i : Fin 3`, and local-frame alignment
  `ω(x*) = M · ê_2` (i.e., second basis vector, which is "third"
  in physics 1-indexing), discharging `sqNorm_deriv_identity`
  automatically via `partialDeriv_dot_self_eq`.
-/

namespace NSBlwChain.BLW

/-- **Constructor for `LocalFrameDerivativeData`.**

    Given:
    * a vector field `ω : Vec3 → Vec3`,
    * a point `x* : Vec3` and a direction `i : Fin 3`,
    * differentiability at `x*` of each component `y ↦ ω y k` (k : Fin 3),
    * local-frame alignment: `ω x* (0 : Fin 3) = 0`,
      `ω x* (1 : Fin 3) = 0`, `ω x* (2 : Fin 3) = M`,
    * an argmax hypothesis: `∂_i|ω|²(x*) = 0`,

    produce a `LocalFrameDerivativeData` with `partial_sqNorm`
    discharged via `partialDeriv_dot_self_eq`, the alignment
    fields populated, and step (i) conclusion
    `M · ∂_i ω_3(x*) = 0` available as a downstream corollary. -/
noncomputable def LocalFrameDerivativeData.ofDifferentiableVectorField
    (ω : Vec3 → Vec3) (x_star : Vec3) (i : Fin 3) (M : ℝ)
    (hω : ∀ k : Fin 3, DifferentiableAt ℝ (fun y => ω y k) x_star)
    (h_ω_0 : ω x_star 0 = 0)
    (h_ω_1 : ω x_star 1 = 0)
    (h_ω_2 : ω x_star 2 = M) :
    LocalFrameDerivativeData where
  M                  := M
  omega_0_at_xstar   := ω x_star 0
  omega_1_at_xstar   := ω x_star 1
  omega_3_at_xstar   := ω x_star 2
  partial_omega_0    := partialDeriv (fun y => ω y 0) i x_star
  partial_omega_1    := partialDeriv (fun y => ω y 1) i x_star
  partial_omega_3    := partialDeriv (fun y => ω y 2) i x_star
  partial_sqNorm     := partialDeriv (fun y => Vec3.dot (ω y) (ω y)) i x_star
  omega_0_zero := h_ω_0
  omega_1_zero := h_ω_1
  omega_3_eq_M := h_ω_2
  sqNorm_deriv_identity := by
    -- `partialDeriv_dot_self_eq hω i` gives:
    --   `partialDeriv (dot ω ω) i x_star
    --      = 2 * ∑ k : Fin 3, ω x_star k * partialDeriv (ω y k) i x_star`.
    -- Expand the sum over `Fin 3 = {0, 1, 2}` and reshape.
    have h := partialDeriv_dot_self_eq hω i
    -- After `rw [h, Fin.sum_univ_three]`, the goal closes by `rfl`
    -- (the 3-term sum equals the concrete field-access form
    -- `ω x_star 0 * ∂ω_0 + ω x_star 1 * ∂ω_1 + ω x_star 2 * ∂ω_2`
    -- by definition of `Fin.sum_univ_three`).
    simpa [Fin.sum_univ_three] using h

end NSBlwChain.BLW
