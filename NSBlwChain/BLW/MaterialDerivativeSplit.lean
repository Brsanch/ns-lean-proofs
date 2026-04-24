-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Setup.NSHypothesis

/-!
# Splitting the ω-contracted material derivative

`materialDerivative u V t x j = ∂_t V(·, x, j) + Σᵢ uᵢ·∂ᵢVⱼ(x)`
(from `NSHypothesis.lean`).  Contracting with `ω(t, x)` and summing
over `j`, the two terms split additively:

  `ω · materialDeriv = ω · ∂_t ω + ω · (u·∇) ω`.

This is pure unfolding + `Finset.sum_add_distrib`.  It discharges
the `h_material_split` hypothesis of
`step_iii_identity_from_NSEvolution` as a theorem.

## Result

`omega_dot_materialDeriv_split`: the scalar split identity.
-/

namespace NSBlwChain.BLW

open scoped BigOperators

/-- **Material-derivative split under ω-contraction.**

    `Σⱼ ωⱼ · materialDerivative_j = ω · ∂_tω + ω · (u·∇)ω`
    at any point `(t, x)`.  Pure unfolding + `Finset.sum_add_distrib`. -/
theorem omega_dot_materialDeriv_split
    (u : VelocityField) (V : ℝ → Vec3 → Vec3) (t : ℝ) (x : Vec3)
    (ω : Vec3) :
    (∑ j : Fin 3, ω j * materialDerivative u V t x j)
      = (∑ j : Fin 3, ω j * deriv (fun τ => V τ x j) t)
        + (∑ j : Fin 3,
            ω j * (∑ i : Fin 3, u t x i *
              partialDeriv (fun y => V t y j) i x)) := by
  -- Unfold materialDerivative: material_j = ∂_tV_j + Σᵢ uᵢ · ∂ᵢV_j.
  unfold materialDerivative
  -- Goal: Σⱼ ωⱼ · (∂_tV_j + Σᵢ uᵢ·∂ᵢV_j) = Σⱼ ωⱼ·∂_tV_j + Σⱼ ωⱼ·(Σᵢ uᵢ·∂ᵢV_j)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

end NSBlwChain.BLW
