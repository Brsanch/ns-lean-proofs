-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.BLW.AlignmentContraction

/-!
# Laplacian contraction under local-frame alignment

Specialization of `AlignmentContraction.dot_of_aligned` to the
vorticity Laplacian: at a point `x` where `ω(x) = M·ê₂`,

  `ω(x) · Δω(x) = M · (Δω)(x) 2`.

This is the mathematical content behind `VorticityLocalFrameData`'s
`laplace_form` field.

(The analogous strain contraction `ω(x) · (ω·∇u)(x) = M² · (∂₂ u₂)(x)`
requires two applications of `dot_of_aligned` AND knowledge that the
velocity-gradient contraction `(ω·∇u) j = Σᵢ ωᵢ · ∂ᵢuⱼ` with the
second alignment used on the inner `ωᵢ`.  That full derivation lives
most naturally at the wiring layer where the physical `(ω·∇u)` vector
is in scope; it is not a pure-algebra lemma.)
-/

namespace NSBlwChain.BLW

open scoped BigOperators

/-- **Laplacian contraction under alignment.**  When `ω(x) = M·ê₂`,
    `ω(x) · Δω(x) = M · (Δω)(x) 2`.  Direct application of
    `dot_of_aligned` to the Laplacian vector. -/
theorem laplace_contraction_of_aligned
    {ω : Vec3 → Vec3} {lap_omega : Vec3 → Vec3} {x : Vec3} {M : ℝ}
    (h_0 : ω x 0 = 0) (h_1 : ω x 1 = 0) (h_2 : ω x 2 = M) :
    Vec3.dot (ω x) (lap_omega x) = M * (lap_omega x) 2 :=
  dot_of_aligned h_0 h_1 h_2 (lap_omega x)

end NSBlwChain.BLW
