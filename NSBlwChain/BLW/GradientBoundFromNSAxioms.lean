-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.BLW.GradientBoundFullyDischarged
import NSBlwChain.BLW.SliceSmoothness

/-!
# Gradient bound from `NSEvolutionAxioms` + structural inputs

Capstone wrapper around `gradient_bound_fully_discharged`.  The
underlying 8-of-8 capstone closes all named scalar hypotheses
internally but still exposes the per-slice `DifferentiableAt`
witnesses (`hf_nhd_sqNorm`, `hD_sqNorm`, `hf_nhd_ω3`, `hD_ω3`) as
explicit inputs.  Those four witnesses are all extractable from
the NS bundle's `C⁴` spatial smoothness:

- `ContDiff ℝ 4 (u t)` ⇒ `ContDiff ℝ 3 (ω(t, ·))` (curl smoothness)
- ⇒ `ContDiff ℝ 3` for `|ω|²` and each component `ω_k` (sum/project)
- ⇒ `ContDiff ℝ 3` for each slice (composition with affine `sliceMap`)
- ⇒ slices are differentiable everywhere and their derivatives are
  differentiable at `0`.

This file discharges those four witnesses and delegates to
`gradient_bound_fully_discharged`.  The only slice-level witness
that **remains** explicit is the per-component time-derivative
`h_time_diff`, which depends on `NS_time_analyticity` (a separate
classical axiom), and the Danskin envelope packaging (`M_fn`,
`h_M_fn_*`, `h_env_*`, `h_slice_diff`) which is supplied by the
caller's choice of envelope.

## Main result

* `gradient_bound_from_ns_axioms` — Same conclusion
  `gradSqNorm ≤ M²·σ/ν` as `gradient_bound_fully_discharged`, but
  with the four slice-smoothness witnesses discharged internally
  from `NSEvolutionAxioms`.

After this wrapper, the taken inputs reduce to:

- `NSEvolutionAxioms u ν T`
- `IsLocalMax |ω|² xStar`
- alignment (`ω(x*)_0 = 0`, `ω(x*)_1 = 0`, `ω(x*)_2 = M`)
- `0 < M`, `0 ≤ Ṁ`
- definitional matchings
- per-component time-differentiability (from `NS_time_analyticity`)
- envelope function `M_fn` + its three bundle properties
- Hessian-expansion component data (3 gradSqNorm_k, 3 laplace_k,
  3 laplace_sq_k + 3 decompositions + 3 (★) identities)
-/

namespace NSBlwChain.BLW

open Filter Topology
open scoped BigOperators
open NSBlwChain

/-- **Gradient-bound capstone from `NSEvolutionAxioms`.**

    Same statement as `gradient_bound_fully_discharged`, with the
    four slice-smoothness witnesses (`hf_nhd_sqNorm`, `hD_sqNorm`,
    `hf_nhd_ω3`, `hD_ω3`) discharged internally from the bundle's
    `C⁴` spatial smoothness of `u`. -/
theorem gradient_bound_from_ns_axioms
    {u : VelocityField} {ν T : ℝ} (ax : NSEvolutionAxioms u ν T)
    (t : ℝ) (ht : 0 ≤ t) (htT : t < T)
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
    -- Time chain rule: per-component time differentiability at t.
    (h_time_diff : ∀ k : Fin 3,
      HasDerivAt (fun τ => vorticity u τ xStar k)
        (deriv (fun τ => vorticity u τ xStar k) t) t)
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
  -- Discharge the four slice-smoothness witnesses from `ax`.
  have hf_nhd_sqNorm : ∀ i : Fin 3,
      ∀ᶠ s in 𝓝 (0 : ℝ),
        DifferentiableAt ℝ
          (slice (fun y =>
            Vec3.dot (vorticity u t y) (vorticity u t y)) xStar i) s :=
    fun i => ax.sqNormVort_slice_differentiableAt_nhds ht htT xStar i
  have hD_sqNorm : ∀ i : Fin 3,
      DifferentiableAt ℝ
        (deriv (slice (fun y =>
          Vec3.dot (vorticity u t y) (vorticity u t y)) xStar i)) 0 :=
    fun i => ax.sqNormVort_sliceDeriv_differentiableAt_zero ht htT xStar i
  have hf_nhd_ω3 : ∀ i : Fin 3,
      ∀ᶠ s in 𝓝 (0 : ℝ),
        DifferentiableAt ℝ
          (slice (fun y => vorticity u t y 2) xStar i) s :=
    fun i => ax.omega3_slice_differentiableAt_nhds ht htT xStar i
  have hD_ω3 : ∀ i : Fin 3,
      DifferentiableAt ℝ
        (deriv (slice (fun y => vorticity u t y 2) xStar i)) 0 :=
    fun i => ax.omega3_sliceDeriv_differentiableAt_zero ht htT xStar i
  -- Delegate to the 8-of-8 capstone.
  exact gradient_bound_fully_discharged
    ax t ht htT xStar hmax M σ Mdot gradSqNorm laplaceOmega3
    omega_laplace_omega hessian_trace_sqNorm
    hM_pos hω0 hω1 hω2
    h_omega_lap_def h_laplace3_def h_σ_def
    h_trace_sum_def h_lap3_sum_def
    hf_nhd_sqNorm hD_sqNorm hf_nhd_ω3 hD_ω3
    h_time_diff
    M_fn h_M_fn_at_t h_M_fn_deriv h_env_dom h_env_hit h_slice_diff
    gradSqNorm_0 gradSqNorm_1 gradSqNorm_2
    laplace_0 laplace_1 laplace_2
    laplace_sq_0 laplace_sq_1 laplace_sq_2
    h_gradSq_decomp h_omega_lap_decomp h_trace_decomp
    h_star_0 h_star_1 h_star_2
    h_growth_nonneg

end NSBlwChain.BLW
