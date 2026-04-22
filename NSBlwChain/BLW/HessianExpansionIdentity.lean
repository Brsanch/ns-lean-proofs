-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.BLW.HessianAtArgmaxFromFrame

/-!
# Step (ii) — pointwise Hessian-expansion identity

This file packages the pointwise identity
  `Δ|ω|²(x) = 2 · |∇ω|²(x) + 2 · ω(x) · Δω(x)`
for a `C²` vector field `ω : ℝ³ → ℝ³` used in step (ii) of
Theorem 12.2.

## Derivation

Componentwise, for each scalar field `f := ω_k` of class `C²`, the
product rule plus equality of mixed partials gives the scalar
identity
  `Δ(f²)(x) = 2 · |∇f|²(x) + 2 · f(x) · Δf(x)`.        (★)

Summing `(★)` over `k ∈ {0,1,2}` and using
  `|ω|²   = Σ_k (ω_k)²`,
  `|∇ω|²  = Σ_k |∇ω_k|²`,
  `ω · Δω = Σ_k ω_k · Δω_k`,
one obtains the vector-field identity
  `Δ|ω|² = 2 · |∇ω|² + 2 · ω · Δω`.

## Scope of this file

The actual scalar calculus identity `(★)` is **taken as a named
hypothesis** in the bundle below.  Its derivation from `fderiv` /
`contDiff`-level machinery in Mathlib is nontrivial and left for a
separate analytical pass; every downstream file that consumes the
vector identity simply assumes `(★)` at the scalar level.

## Contents

* `HessianExpansionData` — scalar per-component bundle at a fixed
  point `x*`, packaging the three scalar `(★)` identities together
  with the consistency equations defining `|ω|²`, `|∇ω|²`, and the
  dot-product form of `ω · Δω`.
* `HessianExpansionData.hessian_expansion` — the vector identity
  `Δ|ω|²(x*) = 2 · |∇ω|²(x*) + 2 · (ω_0·Δω_0 + ω_1·Δω_1 + ω_2·Δω_2)`,
  proved from the three scalar `(★)`s by pure algebra.
* `HessianExpansionData.omega_laplace_omega_value` — the packed
  scalar `ω · Δω` value in the form expected downstream.
* `HessianExpansionData.toHessianLocalFrameData` — wire the
  hessian-expansion bundle into `HessianLocalFrameData` given the
  local-frame alignment hypotheses (`ω_0(x*) = 0`, `ω_1(x*) = 0`,
  `ω_2(x*) = M`) and the `Δω_2`/`Δω_k ≤ 0` bounds.

The `k` indexing here uses `0, 1, 2` (matching Lean conventions);
the downstream `HessianLocalFrameData` uses `ω_3` for the aligned
component — we wire `ω_2(x*) = M` to `omega_3_at_xstar = M` and
`laplace_2` to `laplaceOmega3` at the conversion boundary.
-/

namespace NSBlwChain.BLW

/-- **Scalar per-component Hessian-expansion bundle at a point `x*`.**

    This structure packages, at the level of real scalars, the values
    that feed the pointwise identity
      `Δ|ω|²(x*) = 2 · |∇ω|²(x*) + 2 · ω(x*) · Δω(x*)`.

    The fields `ω_k`, `gradSqNorm_k`, `laplace_k` record
    `ω_k(x*)`, `|∇ω_k|²(x*)`, `Δω_k(x*)` respectively, and
    `sqNorm_value`, `gradSqNorm_total`, `laplace_sqNorm`,
    `omega_dot_laplace` record the four vector-level quantities
    `|ω|²(x*)`, `|∇ω|²(x*)`, `Δ|ω|²(x*)`, and `ω·Δω(x*)`.

    The hypotheses are:
    * Consistency: the three vector-level quantities are the
      componentwise sums of the scalar per-component values.
    * Scalar `(★)` identities: one per component `k ∈ {0,1,2}`,
      expressing `Δ(ω_k²)(x*) = 2·|∇ω_k|²(x*) + 2·ω_k(x*)·Δω_k(x*)`
      — since we only ever need their **sum** at `x*`, the bundle
      records the sum-form directly as `sum_scalar_identity`. -/
structure HessianExpansionData where
  /-- Component value `ω_0(x*)`. -/
  ω_0 : ℝ
  /-- Component value `ω_1(x*)`. -/
  ω_1 : ℝ
  /-- Component value `ω_2(x*)`. -/
  ω_2 : ℝ
  /-- `|∇ω_0|²(x*)`. -/
  gradSqNorm_0 : ℝ
  /-- `|∇ω_1|²(x*)`. -/
  gradSqNorm_1 : ℝ
  /-- `|∇ω_2|²(x*)`. -/
  gradSqNorm_2 : ℝ
  /-- `Δω_0(x*)`. -/
  laplace_0 : ℝ
  /-- `Δω_1(x*)`. -/
  laplace_1 : ℝ
  /-- `Δω_2(x*)`. -/
  laplace_2 : ℝ
  /-- `|ω|²(x*)`. -/
  sqNorm_value : ℝ
  /-- `|∇ω|²(x*)`. -/
  gradSqNorm_total : ℝ
  /-- `Δ|ω|²(x*)` — the object we want to expand. -/
  laplace_sqNorm : ℝ
  /-- `ω·Δω(x*)`. -/
  omega_dot_laplace : ℝ
  /-- Consistency: `|ω|²(x*) = Σ_k (ω_k(x*))²`. -/
  sqNorm_expansion :
    sqNorm_value = ω_0 ^ 2 + ω_1 ^ 2 + ω_2 ^ 2
  /-- Consistency: `|∇ω|²(x*) = Σ_k |∇ω_k|²(x*)`. -/
  gradSqNorm_expansion :
    gradSqNorm_total = gradSqNorm_0 + gradSqNorm_1 + gradSqNorm_2
  /-- Consistency: `ω·Δω(x*) = Σ_k ω_k(x*)·Δω_k(x*)`. -/
  omega_dot_laplace_expansion :
    omega_dot_laplace = ω_0 * laplace_0 + ω_1 * laplace_1 + ω_2 * laplace_2
  /-- **Scalar `(★)` identity, summed over `k`.**  This records
      `Σ_k Δ(ω_k²)(x*) = Σ_k (2·|∇ω_k|²(x*) + 2·ω_k(x*)·Δω_k(x*))`
      together with the fact that the left-hand side equals
      `Δ|ω|²(x*)` since `Δ` is linear and `|ω|² = Σ_k (ω_k)²`.
      That combined statement is exactly:
        `laplace_sqNorm = Σ_k (2·|∇ω_k|² + 2·ω_k·Δω_k)`. -/
  sum_scalar_identity :
    laplace_sqNorm
      = (2 * gradSqNorm_0 + 2 * ω_0 * laplace_0)
        + (2 * gradSqNorm_1 + 2 * ω_1 * laplace_1)
        + (2 * gradSqNorm_2 + 2 * ω_2 * laplace_2)

namespace HessianExpansionData

variable (d : HessianExpansionData)

/-- **Vector-level pointwise Hessian-expansion identity.**

    From the three scalar `(★)` identities (packaged in summed form
    as `sum_scalar_identity`) and the consistency equations for
    `|∇ω|²` and `ω·Δω`, we obtain
      `Δ|ω|²(x*) = 2·|∇ω|²(x*) + 2·(ω_0·Δω_0 + ω_1·Δω_1 + ω_2·Δω_2)`.

    Pure algebraic rearrangement; no analytical content. -/
theorem hessian_expansion :
    d.laplace_sqNorm
      = 2 * d.gradSqNorm_total
        + 2 * (d.ω_0 * d.laplace_0
              + d.ω_1 * d.laplace_1
              + d.ω_2 * d.laplace_2) := by
  have h := d.sum_scalar_identity
  rw [d.gradSqNorm_expansion]
  linarith

/-- **Packed form.**  Same identity, expressed via the bundled
    scalar `ω·Δω(x*)` field. -/
theorem hessian_expansion_packed :
    d.laplace_sqNorm = 2 * d.gradSqNorm_total + 2 * d.omega_dot_laplace := by
  have h := d.hessian_expansion
  rw [d.omega_dot_laplace_expansion]
  linarith

end HessianExpansionData

/-! ### Conversion to `HessianLocalFrameData`

    Given a `HessianExpansionData` bundle at `x*` **together with**
    the local-frame alignment hypotheses and the two local-max
    sign bounds, produce the `HessianLocalFrameData` bundle
    consumed in `HessianAtArgmaxFromFrame`.

    The alignment sends:
    * `ω_0(x*) = 0`,
    * `ω_1(x*) = 0`,
    * `ω_2(x*) = M`        (identified with `ω_3` downstream).

    The Laplacian sign bounds:
    * `Δ|ω|²(x*) ≤ 0` (local max of `|ω|²`),
    * `Δω_2(x*) ≤ 0` (local max of the aligned component).
-/

namespace HessianExpansionData

variable (d : HessianExpansionData)

/-- **Wire a `HessianExpansionData` bundle into `HessianLocalFrameData`.**

    Consumes:
    * `M` — envelope value, with `0 ≤ M`.
    * Alignment: `ω_0(x*) = 0`, `ω_1(x*) = 0`, `ω_2(x*) = M`.
    * `Δ|ω|²(x*) ≤ 0` and `Δω_2(x*) ≤ 0`.

    Produces a `HessianLocalFrameData` whose:
    * `omega_laplace_omega := ω_0·Δω_0 + ω_1·Δω_1 + ω_2·Δω_2`
      (i.e., `d.omega_dot_laplace`).
    * `hess_expansion` is discharged by `hessian_expansion_packed`.
    * `dot_expansion` is discharged by `omega_dot_laplace_expansion`
      after identifying `ω_3` with `ω_2` and `laplaceOmega3` with
      `laplace_2`. -/
def toHessianLocalFrameData
    (M : ℝ)
    (hM_nonneg : 0 ≤ M)
    (hω0_zero : d.ω_0 = 0)
    (hω1_zero : d.ω_1 = 0)
    (hω2_eq_M : d.ω_2 = M)
    (h_hess_nonpos : d.laplace_sqNorm ≤ 0)
    (h_lap2_nonpos : d.laplace_2 ≤ 0) :
    HessianLocalFrameData where
  M := M
  gradSqNorm := d.gradSqNorm_total
  laplaceSqNorm := d.laplace_sqNorm
  laplaceOmega3 := d.laplace_2
  omega_laplace_omega := d.omega_dot_laplace
  omega_0_at_xstar := d.ω_0
  omega_1_at_xstar := d.ω_1
  omega_3_at_xstar := d.ω_2
  laplace_omega_0 := d.laplace_0
  laplace_omega_1 := d.laplace_1
  M_nonneg := hM_nonneg
  omega_0_zero := hω0_zero
  omega_1_zero := hω1_zero
  omega_3_eq_M := hω2_eq_M
  dot_expansion := d.omega_dot_laplace_expansion
  hess_expansion := d.hessian_expansion_packed
  hess_trace_nonpos := h_hess_nonpos
  laplace_nonpos := h_lap2_nonpos

end HessianExpansionData

end NSBlwChain.BLW
