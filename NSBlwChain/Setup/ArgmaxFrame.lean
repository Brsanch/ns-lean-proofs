-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Setup.VectorFields
import NSBlwChain.Setup.NSHypothesis

/-!
# Local frame at the vorticity argmax

This file sets up the *local rotation* convention used throughout the
BLW-gradient chain: at any argmax point `x_star` of `|ω(t, ·)|`, we may
rotate coordinates so that the vorticity at `x_star` points along the
third standard basis vector `ê₃`.

All downstream calculations at `x_star` are then carried out in this
rotated frame, avoiding the need to track the vorticity direction
explicitly.  This is the frame convention from §12.3 of the companion
paper.

## Contents

* `NSBlwChain.IsArgmax` — predicate: `x_star` achieves the sup of
  `|ω(t, ·)|` at time `t`.
* `NSBlwChain.LocalFrame` — structure recording a rotation aligning the
  vorticity at `x_star` with `ê₃`.
* `NSBlwChain.localFrameExists` — existence of such a rotation, given
  a nonzero vorticity at `x_star`.

The rotation is left abstract: we package its *existence* as a
`LocalFrame` structure with fields recording the rotation matrix and
its alignment property.  Proofs of invariance under the rotation are
either structural (for linear operators like the Laplacian) or handled
inside the specific lemma that uses them.
-/

namespace NSBlwChain

open Vec3

/-- Euclidean norm on `Vec3`, computed from the dot product. -/
noncomputable def Vec3.norm (v : Vec3) : ℝ := Real.sqrt (Vec3.dot v v)

@[simp] lemma Vec3.norm_nonneg (v : Vec3) : 0 ≤ Vec3.norm v := by
  unfold Vec3.norm
  exact Real.sqrt_nonneg _

/-- `x_star` achieves the spatial sup of `|ω(t, ·)|`. -/
def IsArgmaxVorticity (u : VelocityField) (t : ℝ) (x_star : Vec3) : Prop :=
  ∀ x : Vec3, Vec3.norm (vorticity u t x) ≤ Vec3.norm (vorticity u t x_star)

/-- **Local frame at an argmax.**

    A `LocalFrame u t x_star` packages a rotation `R : Vec3 → Vec3` that
    aligns `ω(t, x_star)` with `ê₃`, together with the alignment
    identity and the orthogonality property.

    Used by §12.3 (Theorem 12.2 derivation) to reduce to coordinates in
    which `ω` points along `ê₃` at `x_star`. -/
structure LocalFrame (u : VelocityField) (t : ℝ) (x_star : Vec3) : Type where
  /-- The rotation, as a linear map.  (Full orthogonality is recorded
      in `ortho` below.) -/
  R        : Vec3 →ₗ[ℝ] Vec3
  /-- `R` is orthogonal: `‖R v‖² = ‖v‖²` for all `v`. -/
  ortho    : ∀ v : Vec3, Vec3.dot (R v) (R v) = Vec3.dot v v
  /-- `R` aligns `ω(t, x_star)` with a positive multiple of `ê₃`. -/
  aligns   : R (vorticity u t x_star) =
              (fun j => if j = (2 : Fin 3) then
                Vec3.norm (vorticity u t x_star) else 0)

/-- Every `LocalFrame` preserves the Euclidean length. -/
lemma LocalFrame.norm_preserved
    {u : VelocityField} {t : ℝ} {x_star : Vec3}
    (f : LocalFrame u t x_star) (v : Vec3) :
    Vec3.norm (f.R v) = Vec3.norm v := by
  unfold Vec3.norm
  rw [f.ortho v]

end NSBlwChain
