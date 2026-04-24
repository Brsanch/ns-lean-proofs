-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.BLW.GradientBoundFromNSAxioms
import NSBlwChain.Setup.ClassicalAxioms

/-!
# Gradient bound from `NSEvolutionAxioms` + `NS_time_analyticity`

Wrapper around `gradient_bound_from_ns_axioms` that additionally
discharges the per-component vorticity time-differentiability
hypothesis `h_time_diff` by consuming the `NS_time_analyticity`
classical axiom.

## Derivation chain

```
NS_time_analyticity ax : NSTimeAnalyticity u ν T
        │
        ▼
(NS_time_analyticity ax).vorticity_component_hasDerivAt t₀ h0 hT xStar k
        │
        ▼
HasDerivAt (fun τ => vorticity u τ xStar k) (deriv _ t₀) t₀
```

## Remaining explicit inputs after this wrapper

- `NSEvolutionAxioms u ν T`
- `IsLocalMax |ω|² xStar`
- alignment (`ω(x*)_0 = 0`, `_1 = 0`, `_2 = M`)
- `0 < M`, `0 < t`, `t < T`, `0 ≤ Mdot`
- definitional matchings (scalar-to-physical)
- envelope `M_fn` + its four bundle properties
- Hessian-expansion component data (9 scalars + 6 equations)

**No more slice- or time-smoothness witnesses.**  The only remaining
"analytical" hypothesis is the envelope bundle (which the caller
supplies by constructing a Danskin-envelope for `|ω|²(τ, ·)` over
the argmax track), and the Hessian component decomposition (9 per-
component scalars).

## Main result

* `gradient_bound_from_ns_axioms_time_analytic` — `gradSqNorm ≤ M²·σ/ν`
  at an argmax of `|ω(t, ·)|²` under alignment, from `NSEvolutionAxioms`
  plus `NS_time_analyticity` plus envelope + component data.  Requires
  `t ∈ (0, T)` (strict lower bound) so the time-analyticity axiom
  applies at `t`.
-/

namespace NSBlwChain.BLW

open Filter Topology
open scoped BigOperators
open NSBlwChain

/-- **Gradient-bound capstone from `NSEvolutionAxioms` + time analyticity.**

    Same conclusion `gradSqNorm ≤ M²·σ/ν` as
    `gradient_bound_from_ns_axioms`, but with the per-component
    vorticity time-differentiability witness `h_time_diff` discharged
    from the `NS_time_analyticity` classical axiom via the
    `vorticity_component_hasDerivAt` field on `NSTimeAnalyticity`.

    **Strict time lower bound.**  `NS_time_analyticity` provides the
    analyticity window only on the *open* interior `(0, T)`, so we
    require `0 < t` (not just `0 ≤ t`). -/
theorem gradient_bound_from_ns_axioms_time_analytic
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
    -- Hessian expansion component data.
    (gradSqNorm_0 gradSqNorm_1 gradSqNorm_2 : ℝ)
    (laplace_0 laplace_1 laplace_2 : ℝ)
    (laplace_sq_0 laplace_sq_1 laplace_sq_2 : ℝ)
    (h_gradSq_decomp :
      gradSqNorm = gradSqNorm_0 + gradSqNorm_1 + gradSqNorm_2)
    (h_omega_lap_decomp :
      omega_laplace_omega
        = vorticity u t xStar 0 * laplace_0
          + vorticity u t xStar 1 * laplace_1
          + vorticity u t xStar 2 * laplace_2)
    (h_trace_decomp :
      hessian_trace_sqNorm
        = laplace_sq_0 + laplace_sq_1 + laplace_sq_2)
    (h_star_0 :
      laplace_sq_0
        = 2 * gradSqNorm_0 + 2 * vorticity u t xStar 0 * laplace_0)
    (h_star_1 :
      laplace_sq_1
        = 2 * gradSqNorm_1 + 2 * vorticity u t xStar 1 * laplace_1)
    (h_star_2 :
      laplace_sq_2
        = 2 * gradSqNorm_2 + 2 * vorticity u t xStar 2 * laplace_2)
    -- Growth regime:
    (h_growth_nonneg : 0 ≤ Mdot) :
    gradSqNorm ≤ M ^ 2 * σ / ν := by
  -- Discharge per-component vorticity time-differentiability from
  -- NS_time_analyticity's `vorticity_component_hasDerivAt` field.
  have h_time_diff : ∀ k : Fin 3,
      HasDerivAt (fun τ => vorticity u τ xStar k)
        (deriv (fun τ => vorticity u τ xStar k) t) t := fun k =>
    (NS_time_analyticity ax).vorticity_component_hasDerivAt t ht0 htT xStar k
  -- Delegate to the NS-axioms-slice-discharge capstone.  Note the
  -- weaker `0 ≤ t` is implied by `0 < t`.
  exact gradient_bound_from_ns_axioms
    ax t (le_of_lt ht0) htT xStar hmax
    M σ Mdot gradSqNorm laplaceOmega3
    omega_laplace_omega hessian_trace_sqNorm
    hM_pos hω0 hω1 hω2
    h_omega_lap_def h_laplace3_def h_σ_def
    h_trace_sum_def h_lap3_sum_def
    h_time_diff
    M_fn h_M_fn_at_t h_M_fn_deriv h_env_dom h_env_hit h_slice_diff
    gradSqNorm_0 gradSqNorm_1 gradSqNorm_2
    laplace_0 laplace_1 laplace_2
    laplace_sq_0 laplace_sq_1 laplace_sq_2
    h_gradSq_decomp h_omega_lap_decomp h_trace_decomp
    h_star_0 h_star_1 h_star_2
    h_growth_nonneg

end NSBlwChain.BLW
