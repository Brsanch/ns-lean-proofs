-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.BLW.GradientBoundFromNSAxiomsTimeAnalytic
import NSBlwChain.BLW.HessianInputsBundle

/-!
# Gradient bound with Hessian inputs bundled

Wrapper around `gradient_bound_from_ns_axioms_time_analytic` that
consumes the 15 per-component Hessian-expansion scalars as a single
`HessianInputs` structure instead of 9 separate scalars + 6 separate
equations.

## Signature reduction

`gradient_bound_from_ns_axioms_time_analytic` takes **30+** named
arguments.  After this wrapper:

- 15 Hessian items (`gradSqNorm_0/1/2`, `laplace_0/1/2`,
  `laplace_sq_0/1/2`, `h_gradSq_decomp`, `h_omega_lap_decomp`,
  `h_trace_decomp`, `h_star_0/1/2`) are replaced by a single
  `HessianInputs u t xStar gradSqNorm omega_laplace_omega hessian_trace_sqNorm`
  bundle.

Net: ~15 → 1 input.  Purely cosmetic; the analytical content is
unchanged.  (The smoothness-side constructor
`HessianInputs.ofNSEvolutionAxioms` that would replace the 15 items
with a theorem is the multi-hundred-LOC future deliverable.)

## Main result

* `gradient_bound_from_ns_axioms_time_analytic_hessian_bundled` —
  same conclusion `gradSqNorm ≤ M²·σ/ν`, with the Hessian inputs
  consumed through the bundle.
-/

namespace NSBlwChain.BLW

open Filter Topology
open scoped BigOperators
open NSBlwChain

/-- **Gradient-bound capstone with Hessian inputs bundled.**

    Same conclusion as `gradient_bound_from_ns_axioms_time_analytic`,
    with the 15 per-component Hessian-expansion items consumed
    through a single `HessianInputs` bundle.  Unpacks the bundle's
    fields and forwards them (via `omega_lap_decomp_live` and
    `h_star_k_live` rewrites) to the downstream capstone. -/
theorem gradient_bound_from_ns_axioms_time_analytic_hessian_bundled
    {u : VelocityField} {ν T : ℝ} (ax : NSEvolutionAxioms u ν T)
    (t : ℝ) (ht0 : 0 < t) (htT : t < T)
    (xStar : Vec3)
    (hmax : IsLocalMax
      (fun y : Vec3 => Vec3.dot (vorticity u t y) (vorticity u t y))
      xStar)
    (M σ Mdot gradSqNorm laplaceOmega3
      omega_laplace_omega hessian_trace_sqNorm : ℝ)
    (hM_pos : 0 < M)
    -- Alignment:
    (hω0 : vorticity u t xStar 0 = 0)
    (hω1 : vorticity u t xStar 1 = 0)
    (hω2 : vorticity u t xStar 2 = M)
    -- Alignment-algebra definitions:
    (h_omega_lap_def :
      omega_laplace_omega
        = Vec3.dot (vorticity u t xStar)
            (fun j => vectorLaplacian (vorticity u t) xStar j))
    (h_laplace3_def :
      laplaceOmega3 = vectorLaplacian (vorticity u t) xStar 2)
    (h_σ_def :
      σ = partialDeriv (fun y => u t y 2) 2 xStar)
    -- Sign definitions:
    (h_trace_sum_def :
      hessian_trace_sqNorm
        = ∑ i : Fin 3, deriv (deriv (slice
            (fun y => Vec3.dot (vorticity u t y) (vorticity u t y))
            xStar i)) 0)
    (h_lap3_sum_def :
      laplaceOmega3
        = ∑ i : Fin 3, deriv (deriv (slice
            (fun y => vorticity u t y 2) xStar i)) 0)
    -- Envelope (Danskin):
    (M_fn : ℝ → ℝ)
    (h_M_fn_at_t : M_fn t = M)
    (h_M_fn_deriv : HasDerivAt M_fn Mdot t)
    (h_env_dom : ∀ y τ,
      Vec3.dot (vorticity u τ y) (vorticity u τ y) / 2
        ≤ (M_fn τ) ^ 2 / 2)
    (h_env_hit :
      Vec3.dot (vorticity u t xStar) (vorticity u t xStar) / 2
        = (M_fn t) ^ 2 / 2)
    (h_slice_diff :
      DifferentiableAt ℝ
        (fun τ => Vec3.dot (vorticity u τ xStar)
                           (vorticity u τ xStar) / 2) t)
    -- Hessian-expansion content, bundled:
    (H : HessianInputs u t xStar
          gradSqNorm omega_laplace_omega hessian_trace_sqNorm)
    -- Growth regime:
    (h_growth_nonneg : 0 ≤ Mdot) :
    gradSqNorm ≤ M ^ 2 * σ / ν := by
  -- Forward to the time-analytic capstone, unpacking H's fields.
  exact gradient_bound_from_ns_axioms_time_analytic
    ax t ht0 htT xStar hmax
    M σ Mdot gradSqNorm laplaceOmega3
    omega_laplace_omega hessian_trace_sqNorm
    hM_pos hω0 hω1 hω2
    h_omega_lap_def h_laplace3_def h_σ_def
    h_trace_sum_def h_lap3_sum_def
    M_fn h_M_fn_at_t h_M_fn_deriv h_env_dom h_env_hit h_slice_diff
    H.gradSqNorm_0 H.gradSqNorm_1 H.gradSqNorm_2
    H.laplace_0 H.laplace_1 H.laplace_2
    H.laplace_sq_0 H.laplace_sq_1 H.laplace_sq_2
    H.h_gradSq_decomp
    (H.omega_lap_decomp_live)
    H.h_trace_decomp
    (H.h_star_0_live)
    (H.h_star_1_live)
    (H.h_star_2_live)
    h_growth_nonneg

end NSBlwChain.BLW
