-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.BLW.GradientBoundTopLevel
import NSBlwChain.BLW.EnvelopeAtArgmax

/-!
# Fully-bundled top-level NS-axioms-side gradient-bound capstone

Wraps `gradient_bound_from_NSEvolutionAxioms` with the envelope
inputs consumed through an `EnvelopeAtArgmax` structure rather than
six separate arguments.

## Signature reduction

Starting from `gradient_bound_from_NSEvolutionAxioms`:

- 6 envelope items (`M_fn`, `h_M_fn_at_t`, `h_M_fn_deriv`,
  `h_env_dom`, `h_env_hit`, `h_slice_diff`) are replaced by one
  `EnvelopeAtArgmax u t xStar M Mdot` bundle.

**Final user-facing signature:**

* `NSEvolutionAxioms u ν T`
* structural: `0 < t < T`, `xStar`, `IsLocalMax |ω|²`
* alignment (3), positivity (1), growth (1)
* 5 alignment-algebra / sign definitions
* 3 `HessianInputs` total matchings (Fin 3 × Fin 3 slice sums)
* **1 `EnvelopeAtArgmax` bundle**

Conclusion: `gradSqNorm ≤ M² · σ / ν`.

All per-component analytical content, slice/time smoothness,
and Hessian-expansion identities are auto-discharged from
`NSEvolutionAxioms` + `NS_time_analyticity`.  The envelope bundle is
the last remaining item whose derivation from `NSEvolutionAxioms` +
`DecayAtInfinity` is deferred (multi-session classical Danskin
theorem).

## Main result

* `gradient_bound_from_NSEvolutionAxioms_bundled` — the fully-
  bundled NS-axioms-side capstone.
-/

namespace NSBlwChain.BLW

open Filter Topology
open scoped BigOperators
open NSBlwChain

/-- **Fully-bundled top-level NS-axioms-side gradient-bound capstone.**

    Same conclusion as `gradient_bound_from_NSEvolutionAxioms`, with
    the envelope inputs consumed through a single `EnvelopeAtArgmax`
    bundle.  Delegates to `gradient_bound_from_NSEvolutionAxioms` by
    unpacking the bundle's 6 fields. -/
theorem gradient_bound_from_NSEvolutionAxioms_bundled
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
    -- HessianInputs total matchings (3):
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
    -- Envelope, bundled:
    (E : EnvelopeAtArgmax u t xStar M Mdot)
    -- Growth regime:
    (h_growth_nonneg : 0 ≤ Mdot) :
    gradSqNorm ≤ M ^ 2 * σ / ν :=
  gradient_bound_from_NSEvolutionAxioms
    ax t ht0 htT xStar hmax
    M σ Mdot gradSqNorm laplaceOmega3
    omega_laplace_omega hessian_trace_sqNorm
    hM_pos hω0 hω1 hω2
    h_omega_lap_def h_laplace3_def h_σ_def
    h_trace_sum_def h_lap3_sum_def
    h_gradSq_match h_omega_lap_match h_trace_match
    E.M_fn E.h_at_t E.h_deriv E.h_dom E.h_hit E.h_slice_diff
    h_growth_nonneg

end NSBlwChain.BLW
