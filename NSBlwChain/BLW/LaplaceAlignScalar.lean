-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.BLW.AlignmentContraction

/-!
# `ω · Δω(x*) = M · Δω₃(x*)` under alignment — scalar & vector forms

Discharges two of the seven remaining vector-field-layer physical
identities from the alignment hypothesis `ω(x*) = (0, 0, M)`:

* **Scalar form** (OPEN.md step (ii) item 3, `h_laplace_align_scalar`):
  `omega_laplace_omega = M · laplaceOmega3`, where
  `omega_laplace_omega` is the abstract scalar for `ω·Δω(x*)` and
  `laplaceOmega3` is the abstract scalar for `(Δω(x*))_3`.

* **Vector form** (OPEN.md step (iii) item 7, `h_laplace_vec`):
  `Vec3.dot ω(x*) (Δω)(x*) = M · laplaceOmega3`.

Both reduce to a single application of the Vec3-direct alignment
contraction `dot_of_aligned_direct`, plus substitution of the
scalar definitions.  Pure alignment algebra, ~70 LOC.

## Main results

* `dot_of_aligned_direct` — `Vec3`-direct variant of
  `AlignmentContraction.dot_of_aligned` taking `a b : Vec3` (rather
  than a vector field + point of evaluation).

* `laplace_align_scalar_of_aligned` — scalar identity `#3` from
  alignment + definitions.

* `laplace_vec_of_aligned` — vector identity `#7` from alignment +
  scalar definition.

## Consumed by

- `GradientBoundAllScalarDerived.gradient_bound_of_NSEvolutionAxioms_all_scalar_derived`
  via its `h_laplace_align_scalar` and `h_laplace_vec` slots.
-/

namespace NSBlwChain.BLW

open scoped BigOperators

/-- **Alignment dot-product on `Vec3` values.**  If `a : Vec3`
    satisfies `a 0 = 0`, `a 1 = 0`, `a 2 = M`, then for every
    `b : Vec3`, `Vec3.dot a b = M · b 2`.

    This is the `Vec3`-direct analogue of
    `AlignmentContraction.dot_of_aligned`, which takes a vector
    field `ω : Vec3 → Vec3` and a point of evaluation.  Here we
    deal directly with the vector value. -/
theorem dot_of_aligned_direct
    {a : Vec3} {M : ℝ}
    (h_0 : a 0 = 0) (h_1 : a 1 = 0) (h_2 : a 2 = M)
    (b : Vec3) :
    Vec3.dot a b = M * b 2 := by
  unfold Vec3.dot
  simp [Fin.sum_univ_three, h_0, h_1, h_2]

/-- **Scalar identity #3** (`h_laplace_align_scalar`).

    Given abstract scalars `omega_laplace_omega`, `laplaceOmega3`
    satisfying the definitional equations `omega_laplace_omega =
    Vec3.dot omegaVec laplaceVec` and `laplaceOmega3 = laplaceVec 2`,
    plus alignment `omegaVec = (0, 0, M)`, the identity
    `omega_laplace_omega = M · laplaceOmega3` holds. -/
theorem laplace_align_scalar_of_aligned
    (omegaVec laplaceVec : Vec3)
    {omega_laplace_omega laplaceOmega3 M : ℝ}
    (h_omega_lap_def :
      omega_laplace_omega = Vec3.dot omegaVec laplaceVec)
    (h_laplace3_def :
      laplaceOmega3 = laplaceVec 2)
    (h_0 : omegaVec 0 = 0)
    (h_1 : omegaVec 1 = 0)
    (h_2 : omegaVec 2 = M) :
    omega_laplace_omega = M * laplaceOmega3 := by
  rw [h_omega_lap_def, dot_of_aligned_direct h_0 h_1 h_2,
      h_laplace3_def]

/-- **Vector identity #7** (`h_laplace_vec`).

    Under alignment `omegaVec = (0, 0, M)`, the dot product
    `Vec3.dot omegaVec laplaceVec` equals `M · laplaceOmega3`,
    where `laplaceOmega3 := laplaceVec 2` is the scalar 3rd
    component of the vector Laplacian at the argmax. -/
theorem laplace_vec_of_aligned
    (omegaVec laplaceVec : Vec3)
    {laplaceOmega3 M : ℝ}
    (h_laplace3_def : laplaceOmega3 = laplaceVec 2)
    (h_0 : omegaVec 0 = 0)
    (h_1 : omegaVec 1 = 0)
    (h_2 : omegaVec 2 = M) :
    Vec3.dot omegaVec laplaceVec = M * laplaceOmega3 := by
  rw [dot_of_aligned_direct h_0 h_1 h_2, h_laplace3_def]

end NSBlwChain.BLW
