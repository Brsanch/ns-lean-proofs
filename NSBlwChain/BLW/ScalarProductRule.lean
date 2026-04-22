-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Setup.VectorFields

/-!
# Pointwise scalar product-rule identity

This file discharges the pointwise product-rule identity
  `∂_i (f²)(x) = 2 · f(x) · ∂_i f(x)`
for a scalar function `f : Vec3 → ℝ` differentiable at `x`, and
the vector-valued corollary
  `∂_i (Σ_k ω_k²)(x) = 2 · Σ_k ω_k(x) · ∂_i ω_k(x)`,
used in `NSBlwChain.BLW.HessianExpansionIdentity` and the
`LocalFrameDerivativeData.sqNorm_deriv_identity` field.

## Main results

* `partialDeriv_sq_eq` — scalar identity
  `partialDeriv (fun y => (f y)^2) i x = 2 * f x * partialDeriv f i x`
  for `f : Vec3 → ℝ` differentiable at `x`.
* `sum_self_mul_eq_dot` — trivial rewriting of `∑ k, a k * a k` as
  `Vec3.dot a a`.
* `partialDeriv_sqNorm_eq` — vector-field identity
  `partialDeriv (fun y => Σ_k (ω y k)^2) i x =
      2 * Σ_k (ω x k) * partialDeriv (fun y => ω y k) i x`
  for each component of `ω : Vec3 → Vec3` differentiable at `x`.
* `partialDeriv_dot_self_eq` — the same identity restated in terms
  of `Vec3.dot (ω ·) (ω ·)`, i.e.
  `∂_i (ω · ω) = 2 · Σ_k ω_k · ∂_i ω_k`.

## Source of the identity

Each scalar identity `(★)` is `fderiv_pow` at `n = 2` applied to the
basis direction `Vec3.e i`:
  `fderiv ℝ (fun y => (f y)^2) x = (2 • f x) • fderiv ℝ f x`,
then evaluated at `Vec3.e i` yields `2 · f x · partialDeriv f i x`.
Summing over `k` and using `fderiv_sum` (all componentwise terms are
differentiable) delivers the vector version.

Everything is a direct mathlib consequence — no `sorry`, no `axiom`.
-/

namespace NSBlwChain.BLW

open scoped BigOperators
open NSBlwChain

/-! ### Scalar product-rule identity -/

/-- **Scalar product-rule at a point via `fderiv_pow`.**

    For `f : Vec3 → ℝ` differentiable at `x`, the partial derivative
    of `f²` in direction `i` is
      `∂_i (f²)(x) = 2 · f(x) · ∂_i f(x)`. -/
theorem partialDeriv_sq_eq
    {f : Vec3 → ℝ} {x : Vec3} (hf : DifferentiableAt ℝ f x) (i : Fin 3) :
    partialDeriv (fun y => (f y) ^ 2) i x
      = 2 * f x * partialDeriv f i x := by
  -- `fderiv_pow` gives the fderiv of `y ↦ (f y)^2` as
  --   `(2 • (f x)^1) • fderiv ℝ f x`
  have hfd :
      fderiv ℝ (fun y => (f y) ^ 2) x
        = (2 • (f x) ^ (2 - 1)) • fderiv ℝ f x :=
    fderiv_pow (𝕜 := ℝ) 2 hf
  -- Unfold `partialDeriv` and evaluate both sides at `Vec3.e i`.
  unfold partialDeriv
  rw [hfd]
  -- `((2 • f x^1) • fderiv ℝ f x) (Vec3.e i)
  --   = (2 • f x) * fderiv ℝ f x (Vec3.e i)`
  -- via `ContinuousLinearMap.smul_apply`, then `2 • f x = 2 * f x`
  -- via `nsmul_eq_mul`.
  rw [ContinuousLinearMap.smul_apply]
  simp [pow_one, nsmul_eq_mul, smul_eq_mul, mul_assoc]

/-- **Alternative form using `HasFDerivAt` hypothesis.**

    Often the caller has `HasFDerivAt f f' x` in scope; this is the
    same identity packaged through that. -/
theorem partialDeriv_sq_eq_of_hasFDerivAt
    {f : Vec3 → ℝ} {x : Vec3}
    {f' : Vec3 →L[ℝ] ℝ} (hf : HasFDerivAt f f' x) (i : Fin 3) :
    partialDeriv (fun y => (f y) ^ 2) i x
      = 2 * f x * partialDeriv f i x :=
  partialDeriv_sq_eq hf.differentiableAt i

/-- **Scalar identity, `f·f` form.**  Sometimes the downstream code
    writes `|ω_k|² = ω_k · ω_k` rather than `ω_k^2`. -/
theorem partialDeriv_mul_self_eq
    {f : Vec3 → ℝ} {x : Vec3} (hf : DifferentiableAt ℝ f x) (i : Fin 3) :
    partialDeriv (fun y => f y * f y) i x
      = 2 * f x * partialDeriv f i x := by
  have h := partialDeriv_sq_eq hf i
  -- `(f y)^2 = f y * f y` pointwise in `y` ⇒ the two partial
  -- derivatives coincide.
  have hfun : (fun y => (f y) ^ 2) = (fun y => f y * f y) := by
    funext y; ring
  rw [hfun] at h
  exact h

/-! ### Sum-of-squares ↔ `Vec3.dot` -/

/-- **Trivial rewrite.**  For any `a : Fin 3 → ℝ`,
    `Σ k, a k · a k = Vec3.dot a a`. -/
@[simp] lemma sum_self_mul_eq_dot (a : Vec3) :
    (∑ k : Fin 3, a k * a k) = Vec3.dot a a := by
  rfl

/-- **Sum-of-squares form.**  For any `a : Fin 3 → ℝ`,
    `Σ k, (a k)^2 = Vec3.dot a a`. -/
@[simp] lemma sum_sq_eq_dot (a : Vec3) :
    (∑ k : Fin 3, (a k) ^ 2) = Vec3.dot a a := by
  unfold Vec3.dot
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-! ### Vector-valued product rule on `|ω|²` -/

/-- **Vector product-rule identity on `Σ_k ω_k²`.**

    For `ω : Vec3 → Vec3` such that each component `y ↦ ω y k` is
    differentiable at `x`, we have
      `∂_i (Σ_k (ω ·)_k²)(x) = 2 · Σ_k ω_k(x) · ∂_i ω_k(x)`.

    Proof: write the sum as `∑ k, (fun y => (ω y k)^2)` at `x`,
    use `fderiv_sum` to split, then apply the scalar
    `partialDeriv_sq_eq` componentwise. -/
theorem partialDeriv_sqNorm_eq
    {ω : Vec3 → Vec3} {x : Vec3}
    (hω : ∀ k : Fin 3, DifferentiableAt ℝ (fun y => ω y k) x)
    (i : Fin 3) :
    partialDeriv (fun y => ∑ k : Fin 3, (ω y k) ^ 2) i x
      = 2 * ∑ k : Fin 3, ω x k * partialDeriv (fun y => ω y k) i x := by
  -- Commute partialDeriv with the finite sum using `fderiv_fun_sum`.
  have hsum :
      fderiv ℝ (fun y => ∑ k : Fin 3, (ω y k) ^ 2) x
        = ∑ k : Fin 3, fderiv ℝ (fun y => (ω y k) ^ 2) x := by
    refine fderiv_fun_sum (u := (Finset.univ : Finset (Fin 3)))
      (A := fun k y => (ω y k) ^ 2) ?_
    intro k _
    exact (hω k).pow 2
  unfold partialDeriv
  rw [hsum]
  -- Evaluate the sum of CLMs at `Vec3.e i`.
  rw [ContinuousLinearMap.sum_apply]
  -- Apply scalar identity in each summand.
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : partialDeriv (fun y => (ω y k) ^ 2) i x
      = 2 * ω x k * partialDeriv (fun y => ω y k) i x :=
    partialDeriv_sq_eq (hω k) i
  -- `partialDeriv f i x = fderiv ℝ f x (Vec3.e i)` by definition.
  have hk' :
      fderiv ℝ (fun y => (ω y k) ^ 2) x (Vec3.e i)
        = 2 * ω x k * fderiv ℝ (fun y => ω y k) x (Vec3.e i) := hk
  rw [hk']
  ring

/-- **`Vec3.dot` form.**  The same identity expressed via the bundled
    dot product:
      `∂_i (y ↦ (ω y) · (ω y))(x) = 2 · Σ_k ω_k(x) · ∂_i ω_k(x)`. -/
theorem partialDeriv_dot_self_eq
    {ω : Vec3 → Vec3} {x : Vec3}
    (hω : ∀ k : Fin 3, DifferentiableAt ℝ (fun y => ω y k) x)
    (i : Fin 3) :
    partialDeriv (fun y => Vec3.dot (ω y) (ω y)) i x
      = 2 * ∑ k : Fin 3, ω x k * partialDeriv (fun y => ω y k) i x := by
  have hfun :
      (fun y => Vec3.dot (ω y) (ω y))
        = (fun y => ∑ k : Fin 3, (ω y k) ^ 2) := by
    funext y
    unfold Vec3.dot
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hfun]
  exact partialDeriv_sqNorm_eq hω i

end NSBlwChain.BLW
