-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.BLW.HessianExpansionFromC2
import NSBlwChain.BLW.HessianExpansionIdentity

/-!
# Per-component `(★)` identity via Fin 3 sum of slice identities

For a scalar component `f` of a vector field `ω` at a fixed point
`x*`, the pointwise identity

  `Δ(f²)(x*) = 2·|∇f|²(x*) + 2·f(x*)·Δf(x*)`                (★)

follows from the 1-D per-direction slice identity

  `∂²_i(f²)(x*) = 2·(∂_i f(x*))² + 2·f(x*)·∂²_i f(x*)`

(which is `scalar_sq_second_deriv_eq` applied to the slice function
`s ↦ f(x* + s · e_i)`) by summing over `i ∈ Fin 3` and using

* `Δ(f²)(x*) = Σ_i ∂²_i(f²)(x*)`,
* `|∇f|²(x*) = Σ_i (∂_i f(x*))²`,
* `Δf(x*)   = Σ_i ∂²_i f(x*)`.

This file discharges `(★)` at the per-component level — exactly the
shape consumed by `HessianExpansionData.ofScalarIdentities` (one
application per component `k ∈ {0,1,2}`).  Summing three such `(★)`s
over `k` then delivers the vector-level

  `Δ|ω|²(x*) = 2·|∇ω|²(x*) + 2·(ω·Δω)(x*)`.

## Main results

* `laplace_sq_eq_of_slice_identities`
    — the three-directional scalar `(★)` identity assembled from three
      slice identities by pure algebra.

* `laplace_sq_eq_of_slice_identities_fin3`
    — `Fin 3`-indexed packaging of the same assembly.

* `laplace_sq_eq_of_C2_slices`
    — `(★)` produced from 1-D `HasDerivAt` slice data, via
      `scalar_sq_second_deriv_eq` applied directionwise.

All results are **per-component scalar identities** — no vector-field
calculus is performed here; the file is pure algebra plus three
applications of `scalar_sq_second_deriv_eq`.
-/

namespace NSBlwChain.BLW

open scoped BigOperators

/-- **Per-component `(★)` identity from 3 scalar slice identities.**

    Algebraic assembly of three slice identities
    `d2f_sq_i = 2·grad_sq_i + 2·f·d2f_i`  (`i = 0, 1, 2`)
    into the Laplacian-level identity
    `Δ(f²) = 2·|∇f|² + 2·f·Δf`,
    using the three consistency equations that the summed slice
    quantities equal the vector-level Laplacian/gradient-squared/
    Laplacian quantities.

    Pure `ring` — no analytical content. -/
theorem laplace_sq_eq_of_slice_identities
    (f laplace_sq grad_sq laplace_f : ℝ)
    (d2f_sq_0 d2f_sq_1 d2f_sq_2 : ℝ)
    (grad_sq_0 grad_sq_1 grad_sq_2 : ℝ)
    (d2f_0 d2f_1 d2f_2 : ℝ)
    (h_lap_sq_sum : laplace_sq = d2f_sq_0 + d2f_sq_1 + d2f_sq_2)
    (h_grad_sq_sum : grad_sq = grad_sq_0 + grad_sq_1 + grad_sq_2)
    (h_lap_sum : laplace_f = d2f_0 + d2f_1 + d2f_2)
    (h_slice_0 : d2f_sq_0 = 2 * grad_sq_0 + 2 * f * d2f_0)
    (h_slice_1 : d2f_sq_1 = 2 * grad_sq_1 + 2 * f * d2f_1)
    (h_slice_2 : d2f_sq_2 = 2 * grad_sq_2 + 2 * f * d2f_2) :
    laplace_sq = 2 * grad_sq + 2 * f * laplace_f := by
  rw [h_lap_sq_sum, h_grad_sq_sum, h_lap_sum,
      h_slice_0, h_slice_1, h_slice_2]
  ring

/-- **`Fin 3`-indexed version.**  Same assembly as
    `laplace_sq_eq_of_slice_identities`, but with the three
    slice quantities packaged as `Fin 3 → ℝ`. -/
theorem laplace_sq_eq_of_slice_identities_fin3
    (f laplace_sq grad_sq laplace_f : ℝ)
    (d2f_sq grad_sq_i d2f : Fin 3 → ℝ)
    (h_lap_sq_sum : laplace_sq = ∑ i, d2f_sq i)
    (h_grad_sq_sum : grad_sq = ∑ i, grad_sq_i i)
    (h_lap_sum : laplace_f = ∑ i, d2f i)
    (h_slice : ∀ i, d2f_sq i = 2 * grad_sq_i i + 2 * f * d2f i) :
    laplace_sq = 2 * grad_sq + 2 * f * laplace_f := by
  have h0 := h_slice 0
  have h1 := h_slice 1
  have h2 := h_slice 2
  rw [h_lap_sq_sum, h_grad_sq_sum, h_lap_sum]
  simp only [Fin.sum_univ_three]
  rw [h0, h1, h2]
  ring

/-- **`(★)` from 1-D `HasDerivAt` slice data.**

    Consume, for each direction `i ∈ Fin 3`:
    * the slice `g i : ℝ → ℝ` (abstract stand-in for
      `s ↦ f(x* + s · e_i)`) with `g i 0 = f`,
    * its first derivative `g' i : ℝ → ℝ` with
      `HasDerivAt (g i) (g' i s) s` for all `s`,
    * its second derivative value `g''_0 i : ℝ` at `s = 0` with
      `HasDerivAt (g' i) (g''_0 i) 0`;
    together with consistency equations identifying the per-direction
    quantities `d2f_sq i`, `grad_sq_i i`, `d2f i` with
    `deriv (deriv (fun s => (g i s)²)) 0`, `(g' i 0)²`, `g''_0 i`.

    Output: the per-component `(★)` identity
    `laplace_sq = 2·grad_sq + 2·f·laplace_f`
    derived from three applications of
    `scalar_sq_second_deriv_eq` plus the Fin 3 algebraic
    assembly. -/
theorem laplace_sq_eq_of_C2_slices
    (f laplace_sq grad_sq laplace_f : ℝ)
    (g g' : Fin 3 → ℝ → ℝ)
    (g''_0 : Fin 3 → ℝ)
    (hg  : ∀ i s, HasDerivAt (g i) (g' i s) s)
    (hg' : ∀ i, HasDerivAt (g' i) (g''_0 i) 0)
    (hg_0 : ∀ i, g i 0 = f)
    (d2f_sq grad_sq_i d2f : Fin 3 → ℝ)
    (hd2f_sq_eq : ∀ i,
      d2f_sq i = deriv (deriv (fun s => (g i s) ^ 2)) 0)
    (hgrad_sq_eq : ∀ i, grad_sq_i i = (g' i 0) ^ 2)
    (hd2f_eq : ∀ i, d2f i = g''_0 i)
    (h_lap_sq_sum : laplace_sq = ∑ i, d2f_sq i)
    (h_grad_sq_sum : grad_sq = ∑ i, grad_sq_i i)
    (h_lap_sum : laplace_f = ∑ i, d2f i) :
    laplace_sq = 2 * grad_sq + 2 * f * laplace_f := by
  -- Derive each per-direction slice identity from
  -- `scalar_sq_second_deriv_eq` at `t = 0`.
  have h_slice : ∀ i, d2f_sq i = 2 * grad_sq_i i + 2 * f * d2f i := by
    intro i
    have h := scalar_sq_second_deriv_eq (hg i) (hg' i)
    -- `h : deriv (deriv (fun s => (g i s) ^ 2)) 0
    --        = 2 * (g' i 0) ^ 2 + 2 * g i 0 * g''_0 i`
    rw [hd2f_sq_eq i, hgrad_sq_eq i, hd2f_eq i, ← hg_0 i]
    exact h
  exact laplace_sq_eq_of_slice_identities_fin3
    f laplace_sq grad_sq laplace_f
    d2f_sq grad_sq_i d2f
    h_lap_sq_sum h_grad_sq_sum h_lap_sum h_slice

end NSBlwChain.BLW
