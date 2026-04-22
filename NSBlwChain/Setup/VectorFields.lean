-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib

/-!
# 3-vector fields and basic differential operators

This file sets up 3-vector fields on $\mathbb{R}^3$ together with the basic
differential operators (divergence, curl, Laplacian, gradient) used
throughout the BLW-gradient chain.

We use the concrete representation `Fin 3 → ℝ` for vectors in
$\mathbb{R}^3$.  This avoids any instance-synthesis subtleties around
`EuclideanSpace` and keeps all projections definitionally computable.

## Main definitions

* `NSBlwChain.Vec3`     — shorthand for `Fin 3 → ℝ`.
* `NSBlwChain.Vec3.dot` — 3D dot product.
* `NSBlwChain.Vec3.e`   — standard basis vector.
* `NSBlwChain.partialDeriv`    — `i`-th partial derivative of a scalar.
* `NSBlwChain.partialDerivVec` — `i`-th partial derivative of a vector field.
* `NSBlwChain.gradient`        — gradient of a scalar field.
* `NSBlwChain.divergence`      — divergence of a vector field.
* `NSBlwChain.curl`            — curl of a vector field.
* `NSBlwChain.scalarLaplacian` — scalar Laplacian `Δ φ = Σᵢ ∂ᵢ² φ`.
* `NSBlwChain.vectorLaplacian` — componentwise Laplacian of a vector field.

## Scope

This initial pass establishes *definitions only* — just enough for the
downstream modules to state their results typefully.  Classical vector-
calculus identities such as `curl (curl F) = grad (div F) - Δ F` and
`div (curl F) = 0` will be added in a subsequent commit, discharged from
mathlib's `fderiv` + symmetry of mixed partials.
-/

namespace NSBlwChain

open scoped BigOperators
open Real

/-- Concrete 3-vector: a function `Fin 3 → ℝ`.  Aliased for readability. -/
abbrev Vec3 : Type := Fin 3 → ℝ

namespace Vec3

/-- Standard basis vector `e i ∈ ℝ³`. -/
def e (i : Fin 3) : Vec3 := fun j => if j = i then 1 else 0

@[simp] lemma e_self (i : Fin 3) : e i i = 1 := by
  simp [e]

lemma e_of_ne {i j : Fin 3} (h : j ≠ i) : e i j = 0 := by
  simp [e, h]

/-- 3D dot product. -/
def dot (a b : Vec3) : ℝ := ∑ i : Fin 3, a i * b i

/-- Symmetry of the dot product. -/
lemma dot_comm (a b : Vec3) : dot a b = dot b a := by
  unfold dot
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end Vec3

/-! ## Differential operators on vector fields

We treat vector fields as `Vec3 → Vec3`.  The partial derivative
`∂ᵢ Fⱼ` is `fderiv ℝ F x (Vec3.e i) j`.  For convenience we package
the most common operators below. -/

/-- `i`-th partial derivative of a function `f : Vec3 → ℝ`. -/
noncomputable def partialDeriv (f : Vec3 → ℝ) (i : Fin 3) (x : Vec3) : ℝ :=
  fderiv ℝ f x (Vec3.e i)

/-- `i`-th partial derivative of a vector field `F : Vec3 → Vec3`,
    returning the vector `∂_i F` at the point `x`. -/
noncomputable def partialDerivVec (F : Vec3 → Vec3) (i : Fin 3) (x : Vec3) : Vec3 :=
  fderiv ℝ F x (Vec3.e i)

/-- Gradient of a scalar field `φ : Vec3 → ℝ`. -/
noncomputable def gradient (φ : Vec3 → ℝ) (x : Vec3) : Vec3 :=
  fun i => partialDeriv φ i x

/-- Divergence of a vector field `F : Vec3 → Vec3`, defined as the trace
    of its Jacobian: `div F = Σᵢ ∂ᵢ Fᵢ`. -/
noncomputable def divergence (F : Vec3 → Vec3) (x : Vec3) : ℝ :=
  ∑ i : Fin 3, partialDerivVec F i x i

/-- Curl of a vector field `F : Vec3 → Vec3`.  Componentwise:
    `(curl F)₀ = ∂₁F₂ - ∂₂F₁`,
    `(curl F)₁ = ∂₂F₀ - ∂₀F₂`,
    `(curl F)₂ = ∂₀F₁ - ∂₁F₀`. -/
noncomputable def curl (F : Vec3 → Vec3) (x : Vec3) : Vec3 := fun i =>
  if i = 0 then partialDerivVec F 1 x 2 - partialDerivVec F 2 x 1
  else if i = 1 then partialDerivVec F 2 x 0 - partialDerivVec F 0 x 2
  else partialDerivVec F 0 x 1 - partialDerivVec F 1 x 0

/-- Scalar Laplacian `Δ φ = ∑ᵢ ∂ᵢ² φ`. -/
noncomputable def scalarLaplacian (φ : Vec3 → ℝ) (x : Vec3) : ℝ :=
  ∑ i : Fin 3, partialDeriv (fun y => partialDeriv φ i y) i x

/-- Componentwise (vector) Laplacian `(Δ F)ⱼ = Δ (Fⱼ)`. -/
noncomputable def vectorLaplacian (F : Vec3 → Vec3) (x : Vec3) : Vec3 := fun j =>
  scalarLaplacian (fun y => F y j) x

end NSBlwChain
