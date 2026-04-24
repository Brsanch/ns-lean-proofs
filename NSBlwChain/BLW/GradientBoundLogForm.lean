-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.BLW.GradientBoundTopLevelBundled

/-!
# Gradient bound in log-M form

Forward composition of the NS-axioms-side gradient bound with the
Biot–Savart strain bound `σ ≤ 4 M log M` (output of §12.4 log-
absorption — packaged here as a hypothesis, discharged elsewhere via
the `BiotSavartSelfStrainBound` classical axiom).

Composes:

* `|∇ω|²(x*) ≤ M²·σ/ν` (from `gradient_bound_from_NSEvolutionAxioms_bundled`)
* `σ ≤ 4·M·log M` (Biot–Savart + implicit-bound discharge)

to produce

* `|∇ω|²(x*) ≤ 4·M³·log M / ν`.

This is pure real-arithmetic composition; no PDE content.  The shape
matches the downstream §12.4 step (iii) → ODE transition used by
`FullScalarChain.full_scalar_chain`.

## Main result

* `gradient_bound_log_M_form` — `|∇ω|² ≤ 4·M³·log M / ν` under the
  strain hypothesis.
-/

namespace NSBlwChain.BLW

open Real

/-- **Scalar-level composition: gradient bound × strain bound.**

    Given `gradSqNorm ≤ M² · σ / ν` and `σ ≤ 4 · M · log M` with
    `0 < ν`, `0 ≤ M`, `0 ≤ log M`, conclude
    `gradSqNorm ≤ 4 · M³ · log M / ν`.  Pure real arithmetic. -/
theorem gradient_bound_log_M_form_scalar
    {gradSqNorm M σ ν : ℝ}
    (hM_nn : 0 ≤ M) (hν_pos : 0 < ν) (hlogM_nn : 0 ≤ Real.log M)
    (h_grad : gradSqNorm ≤ M ^ 2 * σ / ν)
    (h_strain : σ ≤ 4 * M * Real.log M) :
    gradSqNorm ≤ 4 * M ^ 3 * Real.log M / ν := by
  -- Step 1: `M² ≥ 0`.
  have hM2_nn : 0 ≤ M ^ 2 := sq_nonneg M
  -- Step 2: `M² · σ ≤ M² · (4 · M · log M)` (multiply strain by M² ≥ 0).
  have h_step_num : M ^ 2 * σ ≤ M ^ 2 * (4 * M * Real.log M) :=
    mul_le_mul_of_nonneg_left h_strain hM2_nn
  -- Step 3: Divide by ν > 0 preserves inequality.
  have h_step_div :
      M ^ 2 * σ / ν ≤ M ^ 2 * (4 * M * Real.log M) / ν :=
    div_le_div_of_nonneg_right h_step_num (le_of_lt hν_pos)
  -- Step 4: Simplify RHS to `4 · M³ · log M / ν`.
  have h_rhs_eq :
      M ^ 2 * (4 * M * Real.log M) / ν
        = 4 * M ^ 3 * Real.log M / ν := by ring
  rw [h_rhs_eq] at h_step_div
  -- Step 5: Chain `gradSqNorm ≤ ... ≤ 4·M³·log M / ν`.
  exact le_trans h_grad h_step_div

/-- **Gradient bound in log-M form (from NSEvolutionAxioms + strain).**

    Takes everything `gradient_bound_from_NSEvolutionAxioms_bundled`
    takes plus an explicit strain bound `σ ≤ 4 · M · log M` and
    regularity `0 ≤ log M`.  Concludes `gradSqNorm ≤ 4·M³·log M / ν`.

    The strain bound is produced by `§12.4 log-absorption` (Biot–
    Savart classical axiom + implicit-bound / Banach-fixed-point
    discharge) — in the `1 ≤ M` regime consumed downstream by
    `FullScalarChain.full_scalar_chain`. -/
theorem gradient_bound_log_M_form
    {u : VelocityField} {ν T : ℝ} (ax : NSEvolutionAxioms u ν T)
    (t : ℝ) (ht0 : 0 < t) (htT : t < T)
    (xStar : Vec3)
    (hmax : IsLocalMax
      (fun y : Vec3 => Vec3.dot (vorticity u t y) (vorticity u t y))
      xStar)
    (M σ Mdot gradSqNorm laplaceOmega3
      omega_laplace_omega hessian_trace_sqNorm : ℝ)
    (hM_pos : 0 < M)
    (hω0 : vorticity u t xStar 0 = 0)
    (hω1 : vorticity u t xStar 1 = 0)
    (hω2 : vorticity u t xStar 2 = M)
    (h_omega_lap_def :
      omega_laplace_omega
        = Vec3.dot (vorticity u t xStar)
            (fun j => vectorLaplacian (vorticity u t) xStar j))
    (h_laplace3_def :
      laplaceOmega3 = vectorLaplacian (vorticity u t) xStar 2)
    (h_σ_def :
      σ = partialDeriv (fun y => u t y 2) 2 xStar)
    (h_trace_sum_def :
      hessian_trace_sqNorm
        = ∑ i : Fin 3, deriv (deriv (slice
            (fun y => Vec3.dot (vorticity u t y) (vorticity u t y))
            xStar i)) 0)
    (h_lap3_sum_def :
      laplaceOmega3
        = ∑ i : Fin 3, deriv (deriv (slice
            (fun y => vorticity u t y 2) xStar i)) 0)
    (h_gradSq_match :
      gradSqNorm
        = ∑ k : Fin 3, ∑ i : Fin 3,
            (deriv (slice (fun y => vorticity u t y k) xStar i) 0) ^ 2)
    (h_omega_lap_match :
      omega_laplace_omega
        = ∑ k : Fin 3,
            vorticity u t xStar k
              * (∑ i : Fin 3,
                  deriv (deriv
                    (slice (fun y => vorticity u t y k) xStar i)) 0))
    (h_trace_match :
      hessian_trace_sqNorm
        = ∑ k : Fin 3, ∑ i : Fin 3,
            deriv (deriv (fun s =>
              (slice (fun y => vorticity u t y k) xStar i s) ^ 2)) 0)
    (E : EnvelopeAtArgmax u t xStar M Mdot)
    (h_growth_nonneg : 0 ≤ Mdot)
    -- Additional strain hypothesis (Biot–Savart output):
    (h_strain : σ ≤ 4 * M * Real.log M)
    (hlogM_nn : 0 ≤ Real.log M) :
    gradSqNorm ≤ 4 * M ^ 3 * Real.log M / ν := by
  have h_grad :=
    gradient_bound_from_NSEvolutionAxioms_bundled
      ax t ht0 htT xStar hmax
      M σ Mdot gradSqNorm laplaceOmega3
      omega_laplace_omega hessian_trace_sqNorm
      hM_pos hω0 hω1 hω2
      h_omega_lap_def h_laplace3_def h_σ_def
      h_trace_sum_def h_lap3_sum_def
      h_gradSq_match h_omega_lap_match h_trace_match
      E h_growth_nonneg
  exact gradient_bound_log_M_form_scalar (le_of_lt hM_pos) ax.nu_pos hlogM_nn
    h_grad h_strain

end NSBlwChain.BLW
