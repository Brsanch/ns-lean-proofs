-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.BLW.HessianExpansionIdentity
import NSBlwChain.BLW.ScalarProductRule

/-!
# Step (ii) analytical discharge — pointwise `(f²)'' = 2(f')² + 2 f · f''`

This file discharges the scalar second-derivative identity

  `(f²)''(t) = 2 · (f'(t))² + 2 · f(t) · f''(t)`        (★★)

for a `C²` scalar slice `f : ℝ → ℝ` via mathlib's `HasDerivAt.pow`
(for the first derivative `(f²)' = 2 f f'`) followed by a second
product-rule application (for the derivative of `2 f f'` at `t`).

Summing `(★★)` over directions `i ∈ Fin 3` and components
`k ∈ Fin 3` delivers

  `Δ|ω|²(x*) = 2 · |∇ω|²(x*) + 2 · ω(x*) · Δω(x*)`,

which is exactly the content recorded as
`HessianExpansionData.sum_scalar_identity` in
`NSBlwChain.BLW.HessianExpansionIdentity`.  The constructor
`HessianExpansionData.ofScalarIdentities` in this file accepts the
three per-component scalar identities and discharges the bundle's
`sum_scalar_identity` field by pure algebra.

## Main results

* `hasDerivAt_sq_first`
    — pointwise `HasDerivAt (f²) (2 · f t · f' t) t`
      from `HasDerivAt f (f' t) t`, via `HasDerivAt.pow`.

* `hasDerivAt_sq_second`
    — pointwise `HasDerivAt (2 · f · f') (2 · (f' t)² + 2 · f t · f'' t) t`
      from `HasDerivAt f (f' t) t` and `HasDerivAt f' (f'' t) t`,
      via product rule on `2 f f'`.

* `scalar_sq_second_deriv_eq`
    — the extracted real equality
      `(f²)''(t) = 2 · (f' t)² + 2 · f t · f'' t`,
      where `(f²)''` means `deriv (deriv (f²))`.

* `HessianExpansionData.ofScalarIdentities`
    — constructor for `HessianExpansionData` consuming the three
      scalar `(★)` identities per component and the four
      consistency equations, discharging `sum_scalar_identity` by
      linear algebra.

## Relationship to the bundle

`HessianExpansionData.sum_scalar_identity` records the **sum over
`k`** of `(★)` at a fixed point `x*`:

  `Δ|ω|²(x*) = Σ_k (2 · |∇ω_k|²(x*) + 2 · ω_k(x*) · Δω_k(x*))`.

To discharge it from `C²` data, the caller provides three
per-component scalar identities plus the three consistency
equations (`|ω|² = Σ ω_k²`, `|∇ω|² = Σ |∇ω_k|²`, `ω·Δω = Σ ω_k Δω_k`)
— each of which is a pure algebraic rewriting, taken as input.
`ofScalarIdentities` assembles these into the bundle.
-/

namespace NSBlwChain.BLW

open scoped BigOperators

/-! ### 1-D core: pointwise first and second derivatives of `f²` -/

/-- **First derivative of `f²`.**

    If `HasDerivAt f (f' t) t`, then
      `HasDerivAt (fun s => (f s)^2) (2 · f t · f' t) t`.

    This is `HasDerivAt.pow 2` with `pow_one` simp. -/
theorem hasDerivAt_sq_first
    {f : ℝ → ℝ} {f'_t : ℝ} {t : ℝ}
    (hf : HasDerivAt f f'_t t) :
    HasDerivAt (fun s => (f s) ^ 2) (2 * f t * f'_t) t := by
  -- `HasDerivAt.pow` gives
  --   `HasDerivAt (fun s => (f s)^2) (↑2 * (f t)^(2-1) * f'_t) t`
  -- With `pow_one` and `Nat.cast` simplification, this becomes
  -- `2 * f t * f'_t`.
  have h := hf.pow (n := 2)
  simpa [pow_one] using h

/-- **Second derivative of `f²` via product rule on `2 f · f'`.**

    Assume:
    * `hf  : ∀ s, HasDerivAt f (f' s) s` — the first derivative exists
      in a neighborhood of `t`, recorded as the function `f' : ℝ → ℝ`;
    * `hf'' : HasDerivAt f' f''_t t` — the first derivative is itself
      differentiable at `t`, with value `f''_t`.

    Then the function `s ↦ 2 · f s · f' s` (which agrees with `(f²)'`
    pointwise by `hasDerivAt_sq_first`) has derivative
    `2 · (f' t)² + 2 · f t · f''_t` at `t`, i.e.
      `(f²)''(t) = 2 · (f' t)² + 2 · f t · f''_t`. -/
theorem hasDerivAt_sq_second
    {f f' : ℝ → ℝ} {f''_t t : ℝ}
    (hf : ∀ s, HasDerivAt f (f' s) s)
    (hf'' : HasDerivAt f' f''_t t) :
    HasDerivAt (fun s => 2 * f s * f' s)
      (2 * (f' t) ^ 2 + 2 * f t * f''_t) t := by
  -- Inner product rule on `f · f'`:
  --   `HasDerivAt (fun s => f s * f' s) (f' t * f' t + f t * f''_t) t`.
  have h_prod : HasDerivAt (fun s => f s * f' s)
      (f' t * f' t + f t * f''_t) t := (hf t).mul hf''
  -- Multiply by the constant `2`.
  have h2 : HasDerivAt (fun s => 2 * (f s * f' s))
      (2 * (f' t * f' t + f t * f''_t)) t := h_prod.const_mul 2
  -- Reshape the function: `2 * (f s * f' s) = 2 * f s * f' s`.
  have hrw_fun : (fun s => 2 * (f s * f' s)) = (fun s => 2 * f s * f' s) := by
    funext s; ring
  rw [hrw_fun] at h2
  -- Reshape the derivative value.
  have hrw_val :
      2 * (f' t * f' t + f t * f''_t)
        = 2 * (f' t) ^ 2 + 2 * f t * f''_t := by ring
  rw [hrw_val] at h2
  exact h2

/-! ### Scalar pointwise identity `(f²)''(t) = 2(f')² + 2 f f''`

The extractable scalar equality used to discharge each slice's
`(★)` in `HessianExpansionData`. -/

/-- **Extracted derivative value — `2 f f'` form.**

    `hasDerivAt_sq_second` gives the `HasDerivAt`-level statement;
    reading off the derivative value yields the scalar equality
      `deriv (fun s => 2 · f s · f' s) t = 2 · (f' t)² + 2 · f t · f'' t`. -/
theorem deriv_two_mul_f_mul_f'_eq
    {f f' : ℝ → ℝ} {f''_t t : ℝ}
    (hf : ∀ s, HasDerivAt f (f' s) s)
    (hf'' : HasDerivAt f' f''_t t) :
    deriv (fun s => 2 * f s * f' s) t
      = 2 * (f' t) ^ 2 + 2 * f t * f''_t :=
  (hasDerivAt_sq_second hf hf'').deriv

/-- **Scalar pointwise `(★★)` identity as a real equality.**

    For `f : ℝ → ℝ` with `HasDerivAt f (f' s) s` for all `s` and
    `HasDerivAt f' f''_t t`, we have
      `(f²)''(t) = 2 · (f' t)² + 2 · f t · f'' t`,
    where `(f²)''` is `deriv (deriv (fun s => (f s)²))`. -/
theorem scalar_sq_second_deriv_eq
    {f f' : ℝ → ℝ} {f''_t t : ℝ}
    (hf : ∀ s, HasDerivAt f (f' s) s)
    (hf'' : HasDerivAt f' f''_t t) :
    deriv (deriv (fun s => (f s) ^ 2)) t
      = 2 * (f' t) ^ 2 + 2 * f t * f''_t := by
  -- Pointwise, `deriv (f²) s = 2 · f s · f' s` by `hasDerivAt_sq_first`.
  have h_first_eq : ∀ s,
      deriv (fun u => (f u) ^ 2) s = 2 * f s * f' s := by
    intro s; exact (hasDerivAt_sq_first (hf s)).deriv
  -- As functions, `deriv (f²) = fun s => 2 · f s · f' s`.
  have h_fun_eq :
      (fun s => deriv (fun u => (f u) ^ 2) s)
        = (fun s => 2 * f s * f' s) := by
    funext s; exact h_first_eq s
  -- Rewrite `deriv (deriv (f²))` as `deriv (fun s => 2 f s f' s)`.
  have h_step : deriv (deriv (fun u => (f u) ^ 2)) t
      = deriv (fun s => 2 * f s * f' s) t := by
    change deriv (fun s => deriv (fun u => (f u) ^ 2) s) t
        = deriv (fun s => 2 * f s * f' s) t
    rw [h_fun_eq]
  rw [h_step]
  exact deriv_two_mul_f_mul_f'_eq hf hf''

/-! ### Constructor: assemble `HessianExpansionData` from scalar identities -/

/-- **Scalar-identity-driven constructor for `HessianExpansionData`.**

    Consumes, at a fixed point `x*`:

    * Per-component values `ω_k, gradSqNorm_k, Δω_k` for `k ∈ {0,1,2}`.
    * The four vector-level quantities `|ω|², |∇ω|², Δ|ω|², ω·Δω`.
    * **Three consistency equations:** `|ω|² = Σ ω_k²`,
      `|∇ω|² = Σ |∇ω_k|²`, `ω·Δω = Σ ω_k Δω_k`.
    * **Three per-component scalar identities `(★)`:**
        `Δ(ω_k²)(x*) = 2 · |∇ω_k|²(x*) + 2 · ω_k(x*) · Δω_k(x*)`
      as real equalities — each the direction-summed form of the
      per-slice identity `scalar_sq_second_deriv_eq`.
    * **Laplacian linearity:**
        `Δ|ω|²(x*) = Σ_k Δ(ω_k²)(x*)`,
      recorded as `h_laplace_sq_of_component_sq` — pure linearity
      of the scalar Laplacian combined with the expansion
      `|ω|² = Σ_k ω_k²`.

    Produces the `HessianExpansionData` bundle with
    `sum_scalar_identity` discharged. -/
def HessianExpansionData.ofScalarIdentities
    (ω_0 ω_1 ω_2 : ℝ)
    (gradSqNorm_0 gradSqNorm_1 gradSqNorm_2 : ℝ)
    (laplace_0 laplace_1 laplace_2 : ℝ)
    (sqNorm_value gradSqNorm_total laplace_sqNorm omega_dot_laplace : ℝ)
    (laplace_sq_0 laplace_sq_1 laplace_sq_2 : ℝ)
    (h_sqNorm : sqNorm_value = ω_0 ^ 2 + ω_1 ^ 2 + ω_2 ^ 2)
    (h_gradSq : gradSqNorm_total = gradSqNorm_0 + gradSqNorm_1 + gradSqNorm_2)
    (h_dot :
      omega_dot_laplace
        = ω_0 * laplace_0 + ω_1 * laplace_1 + ω_2 * laplace_2)
    (h_star_0 :
      laplace_sq_0 = 2 * gradSqNorm_0 + 2 * ω_0 * laplace_0)
    (h_star_1 :
      laplace_sq_1 = 2 * gradSqNorm_1 + 2 * ω_1 * laplace_1)
    (h_star_2 :
      laplace_sq_2 = 2 * gradSqNorm_2 + 2 * ω_2 * laplace_2)
    (h_laplace_sq_of_component_sq :
      laplace_sqNorm = laplace_sq_0 + laplace_sq_1 + laplace_sq_2) :
    HessianExpansionData where
  ω_0 := ω_0
  ω_1 := ω_1
  ω_2 := ω_2
  gradSqNorm_0 := gradSqNorm_0
  gradSqNorm_1 := gradSqNorm_1
  gradSqNorm_2 := gradSqNorm_2
  laplace_0 := laplace_0
  laplace_1 := laplace_1
  laplace_2 := laplace_2
  sqNorm_value := sqNorm_value
  gradSqNorm_total := gradSqNorm_total
  laplace_sqNorm := laplace_sqNorm
  omega_dot_laplace := omega_dot_laplace
  sqNorm_expansion := h_sqNorm
  gradSqNorm_expansion := h_gradSq
  omega_dot_laplace_expansion := h_dot
  sum_scalar_identity := by
    -- Expand `laplace_sqNorm` via Laplacian linearity, then
    -- substitute the three `(★)` identities.
    rw [h_laplace_sq_of_component_sq, h_star_0, h_star_1, h_star_2]

end NSBlwChain.BLW
