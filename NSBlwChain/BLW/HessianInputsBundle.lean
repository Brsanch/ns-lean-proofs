-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Setup.NSHypothesis

/-!
# Hessian-expansion scalar bundle

Packaging of the 15 per-component scalar items that the
fully-discharged BLW capstone consumes to derive the Hessian-expansion
identity

  `hessian_trace_sqNorm = 2 · gradSqNorm + 2 · omega_laplace_omega`.

The capstone
`gradient_bound_from_ns_axioms_time_analytic` currently takes:

* 9 per-component scalars (`gradSqNorm_k`, `laplace_k`, `laplace_sq_k`
  for `k ∈ {0, 1, 2}`),
* 3 vector-level decomposition identities (`h_gradSq_decomp`,
  `h_omega_lap_decomp`, `h_trace_decomp`),
* 3 per-component `(★)` identities (`h_star_0`, `h_star_1`, `h_star_2`).

This file packages those 15 items into a single `HessianInputs`
structure so the capstone signature shrinks by 15 named arguments.

## Derivation roadmap (future work)

The 9 scalars + 6 equations are provable from `ContDiff 3 (ω)` on
concrete definitional matchings:

* Set `gradSqNorm_k := Σ_i (deriv (slice (ω_k) xStar i) 0)²`
  (the squared slice gradient at `xStar`, direction `e_i`).
* Set `laplace_k     := Σ_i deriv (deriv (slice (ω_k) xStar i)) 0`.
* Set `laplace_sq_k  := Σ_i deriv (deriv (slice (ω_k²) xStar i)) 0`.

Then:

* `h_star_k` follows from `scalar_sq_second_deriv_eq` applied to each
  slice `s ↦ ω_k(xStar + s · e_i)` summed over `i : Fin 3`
  (cf. `laplace_sq_eq_of_C2_slices` in
  `HessianExpansionScalar.lean`).
* The three decomposition identities follow from linearity of slice
  Laplacian / squared-gradient over the 3 vorticity components plus
  the definitional tie between the vector-level abstract scalars
  (`gradSqNorm`, `omega_laplace_omega`, `hessian_trace_sqNorm`) and
  their slice-sum formulas.

`HessianInputs.ofNSEvolutionAxioms` — the smoothness-side constructor
— is the multi-hundred-LOC analytical-machinery target; this file
only provides the *trivial* (explicit-scalars) constructor, leaving
the smoothness-side constructor as a clearly-named TODO.
-/

namespace NSBlwChain.BLW

open NSBlwChain

/-- **Hessian-expansion scalar inputs bundle.**

    Packages the 9 per-component scalars + 6 consistency equations
    that the fully-discharged BLW capstone needs to derive the
    Hessian-expansion identity
    `hessian_trace_sqNorm = 2·gradSqNorm + 2·omega_laplace_omega`.

    The three `ω_k_value` fields record the three pointwise values
    `ω(t, xStar) k` that show up in `h_omega_lap_decomp`.  They are
    asserted equal via `h_ω_k_match` to the live values
    `vorticity u t xStar k` so the bundle composes downstream. -/
structure HessianInputs
    (u : VelocityField) (t : ℝ) (xStar : Vec3)
    (gradSqNorm omega_laplace_omega hessian_trace_sqNorm : ℝ) where
  /-- `ω_0(t, xStar)` recorded scalar. -/
  ω0_val          : ℝ
  /-- `ω_1(t, xStar)` recorded scalar. -/
  ω1_val          : ℝ
  /-- `ω_2(t, xStar)` recorded scalar. -/
  ω2_val          : ℝ
  /-- `|∇ω_0|²(xStar)`. -/
  gradSqNorm_0    : ℝ
  /-- `|∇ω_1|²(xStar)`. -/
  gradSqNorm_1    : ℝ
  /-- `|∇ω_2|²(xStar)`. -/
  gradSqNorm_2    : ℝ
  /-- `Δω_0(xStar)`. -/
  laplace_0       : ℝ
  /-- `Δω_1(xStar)`. -/
  laplace_1       : ℝ
  /-- `Δω_2(xStar)`. -/
  laplace_2       : ℝ
  /-- `Δ(ω_0²)(xStar)`. -/
  laplace_sq_0    : ℝ
  /-- `Δ(ω_1²)(xStar)`. -/
  laplace_sq_1    : ℝ
  /-- `Δ(ω_2²)(xStar)`. -/
  laplace_sq_2    : ℝ
  /-- Match `ω0_val = vorticity u t xStar 0`. -/
  h_ω0_match      : ω0_val = vorticity u t xStar 0
  /-- Match `ω1_val = vorticity u t xStar 1`. -/
  h_ω1_match      : ω1_val = vorticity u t xStar 1
  /-- Match `ω2_val = vorticity u t xStar 2`. -/
  h_ω2_match      : ω2_val = vorticity u t xStar 2
  /-- `gradSqNorm = Σ_k gradSqNorm_k`. -/
  h_gradSq_decomp :
    gradSqNorm = gradSqNorm_0 + gradSqNorm_1 + gradSqNorm_2
  /-- `omega_laplace_omega = Σ_k ω_k(xStar) · laplace_k`. -/
  h_omega_lap_decomp :
    omega_laplace_omega
      = ω0_val * laplace_0 + ω1_val * laplace_1 + ω2_val * laplace_2
  /-- `hessian_trace_sqNorm = Σ_k laplace_sq_k`. -/
  h_trace_decomp :
    hessian_trace_sqNorm
      = laplace_sq_0 + laplace_sq_1 + laplace_sq_2
  /-- Per-component `(★)_0`:
      `Δ(ω_0²) = 2·|∇ω_0|² + 2·ω_0·Δω_0`. -/
  h_star_0        :
    laplace_sq_0 = 2 * gradSqNorm_0 + 2 * ω0_val * laplace_0
  /-- Per-component `(★)_1`. -/
  h_star_1        :
    laplace_sq_1 = 2 * gradSqNorm_1 + 2 * ω1_val * laplace_1
  /-- Per-component `(★)_2`. -/
  h_star_2        :
    laplace_sq_2 = 2 * gradSqNorm_2 + 2 * ω2_val * laplace_2

/-- **Vector-level Hessian-expansion identity from the bundle.**

    The bundle delivers the abstract identity
    `hessian_trace_sqNorm = 2 · gradSqNorm + 2 · omega_laplace_omega`
    via `rw` on the 6 consistency equations + `ring` on the 3
    `(★)` identities — the exact derivation pattern used inline in
    `gradient_bound_fully_discharged`. -/
theorem HessianInputs.hessian_expansion
    {u : VelocityField} {t : ℝ} {xStar : Vec3}
    {gradSqNorm omega_laplace_omega hessian_trace_sqNorm : ℝ}
    (H : HessianInputs u t xStar
          gradSqNorm omega_laplace_omega hessian_trace_sqNorm) :
    hessian_trace_sqNorm = 2 * gradSqNorm + 2 * omega_laplace_omega := by
  rw [H.h_trace_decomp, H.h_star_0, H.h_star_1, H.h_star_2,
      H.h_gradSq_decomp, H.h_omega_lap_decomp]
  ring

/-- **Omega-Laplace decomposition in the live `vorticity u t xStar k`
    form.**  Converts the bundle's internal `ω_k_val * laplace_k`
    decomposition to the `vorticity u t xStar k * laplace_k` form
    expected by the downstream
    `gradient_bound_fully_discharged` capstone. -/
theorem HessianInputs.omega_lap_decomp_live
    {u : VelocityField} {t : ℝ} {xStar : Vec3}
    {gradSqNorm omega_laplace_omega hessian_trace_sqNorm : ℝ}
    (H : HessianInputs u t xStar
          gradSqNorm omega_laplace_omega hessian_trace_sqNorm) :
    omega_laplace_omega
      = vorticity u t xStar 0 * H.laplace_0
        + vorticity u t xStar 1 * H.laplace_1
        + vorticity u t xStar 2 * H.laplace_2 := by
  rw [H.h_omega_lap_decomp, H.h_ω0_match, H.h_ω1_match, H.h_ω2_match]

/-- **Per-component `(★)_k` in the live `vorticity u t xStar k` form.**
    `h_star_0` restated with `ω0_val` replaced by
    `vorticity u t xStar 0`. -/
theorem HessianInputs.h_star_0_live
    {u : VelocityField} {t : ℝ} {xStar : Vec3}
    {gradSqNorm omega_laplace_omega hessian_trace_sqNorm : ℝ}
    (H : HessianInputs u t xStar
          gradSqNorm omega_laplace_omega hessian_trace_sqNorm) :
    H.laplace_sq_0
      = 2 * H.gradSqNorm_0 + 2 * vorticity u t xStar 0 * H.laplace_0 := by
  rw [H.h_star_0, H.h_ω0_match]

/-- Per-component `(★)_1` in live form. -/
theorem HessianInputs.h_star_1_live
    {u : VelocityField} {t : ℝ} {xStar : Vec3}
    {gradSqNorm omega_laplace_omega hessian_trace_sqNorm : ℝ}
    (H : HessianInputs u t xStar
          gradSqNorm omega_laplace_omega hessian_trace_sqNorm) :
    H.laplace_sq_1
      = 2 * H.gradSqNorm_1 + 2 * vorticity u t xStar 1 * H.laplace_1 := by
  rw [H.h_star_1, H.h_ω1_match]

/-- Per-component `(★)_2` in live form. -/
theorem HessianInputs.h_star_2_live
    {u : VelocityField} {t : ℝ} {xStar : Vec3}
    {gradSqNorm omega_laplace_omega hessian_trace_sqNorm : ℝ}
    (H : HessianInputs u t xStar
          gradSqNorm omega_laplace_omega hessian_trace_sqNorm) :
    H.laplace_sq_2
      = 2 * H.gradSqNorm_2 + 2 * vorticity u t xStar 2 * H.laplace_2 := by
  rw [H.h_star_2, H.h_ω2_match]

end NSBlwChain.BLW
