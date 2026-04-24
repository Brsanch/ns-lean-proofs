-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Setup.VectorFields

/-!
# Dot-product with an aligned vorticity

Algebraic helpers for the BLW chain's local-frame argmax analysis.
When `ω(xStar) = M·ê₂` (alignment), contractions `ω · v` simplify
to `M · v_2`.  This closes the `strain_form` and `laplace_form`
fields of `VorticityLocalFrameData` with real derivations instead
of definitional `rfl`.

## Results

- `dot_of_aligned`: if `ω(x) = (0, 0, M)`, then `ω(x) · v = M · v 2`
  for any `v : Vec3`.

## Consumed by

- `VorticityLocalFrameData.strain_form` via the specialization
  `ω · (ω·∇u)(x) = M · ((ω·∇u)(x)) 2`, which combined with alignment
  again on the `(ω·∇u)` computation gives `M² · (∂_2 u_2)(x)`.
- `VorticityLocalFrameData.laplace_form` via the specialization
  `ω · Δω(x) = M · (Δω)(x) 2`.
-/

namespace NSBlwChain.BLW

open scoped BigOperators

/-- **Dot-product with an aligned vector.**  If `ω(x) = (0, 0, M)`
    (local-frame alignment), then `ω(x) · v = M · v 2` for every
    `v : Vec3`. -/
theorem dot_of_aligned
    {ω : Vec3 → Vec3} {x : Vec3} {M : ℝ}
    (h_0 : ω x 0 = 0) (h_1 : ω x 1 = 0) (h_2 : ω x 2 = M)
    (v : Vec3) :
    Vec3.dot (ω x) v = M * v 2 := by
  unfold Vec3.dot
  simp [Fin.sum_univ_three, h_0, h_1, h_2]

/-- **Squared-magnitude under alignment.**  If `ω(x) = (0, 0, M)`,
    then `|ω(x)|² = M²`. -/
theorem sqNorm_of_aligned
    {ω : Vec3 → Vec3} {x : Vec3} {M : ℝ}
    (h_0 : ω x 0 = 0) (h_1 : ω x 1 = 0) (h_2 : ω x 2 = M) :
    Vec3.dot (ω x) (ω x) = M ^ 2 := by
  rw [dot_of_aligned h_0 h_1 h_2 (ω x), h_2]
  ring

end NSBlwChain.BLW
