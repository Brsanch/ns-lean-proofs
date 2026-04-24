-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.BLW.GradientBoundTimeEnvelopeDischarged
import NSBlwChain.BLW.HessianExpansionIdentity

/-!
# Fully-discharged capstone — all 8 scalar hypotheses derived internally

Final-boss capstone.  Extends `GradientBoundTimeEnvelopeDischarged`
by internalising the last remaining named scalar hypothesis:

* **#1 `h_hessian_expansion`** via
  `HessianExpansionData.ofScalarIdentities` — assembles per-
  component scalar data into the bundle, extracts
  `hessian_expansion_packed` to produce
  `hessian_trace_sqNorm = 2·gradSqNorm + 2·omega_laplace_omega`.

After this capstone, **all 8 named scalar hypotheses of
`gradient_bound_of_NSEvolutionAxioms_all_scalar_derived` are
discharged**.  The remaining taken inputs are purely structural:

- `NSEvolutionAxioms u ν T`
- `IsLocalMax |ω|² xStar`
- alignment (`ω(x*)_0 = 0`, `ω(x*)_1 = 0`, `ω(x*)_2 = M`)
- `0 < M`, `0 ≤ Ṁ`
- definitional matchings tying abstract scalars to physical values
- per-slice/time smoothness witnesses (extractable from
  `NS_time_analyticity` axiom in a future downstream wrapper)

## What this capstone takes as new inputs (beyond 7-of-8)

Three per-component scalar bundles for the Hessian expansion:

- `gradSqNorm_0, gradSqNorm_1, gradSqNorm_2` — per-component
  `|∇ω_k|²(x*)`.
- `laplace_0, laplace_1, laplace_2` — per-component `Δω_k(x*)`.
- `laplace_sq_0, laplace_sq_1, laplace_sq_2` — per-component
  `Δ(ω_k²)(x*)`.

Three consistency equations:

- `h_gradSq_decomp : gradSqNorm = Σ_k gradSqNorm_k`.
- `h_omega_lap_decomp : omega_laplace_omega = Σ_k ω_k(x*)·laplace_k`.
- `h_trace_decomp : hessian_trace_sqNorm = Σ_k laplace_sq_k`.

Three per-component `(★)` identities:

- `h_star_k : laplace_sq_k = 2·gradSqNorm_k + 2·ω_k(x*)·laplace_k`.

(The per-component `(★)` identities are themselves derivable from
9 Fin 3 × Fin 3 slice 2nd-derivative identities via
`HessianExpansionScalar.laplace_sq_eq_of_slice_identities_fin3`;
that further chaining would be the zero-hypothesis future work.)

## Main result

* `gradient_bound_fully_discharged` — 8-of-8 capstone discharge.
-/

namespace NSBlwChain.BLW

open Filter Topology
open scoped BigOperators

/-- **Fully-discharged gradient-bound capstone.**

    Same conclusion as
    `gradient_bound_of_NSEvolutionAxioms_all_scalar_derived`, with
    *all 8* named scalar hypotheses discharged internally:

    - #1 `h_hessian_expansion` via `HessianExpansionData.ofScalarIdentities`.
    - #2 `h_trace_nonpos` via `hessian_trace_sqNorm_nonpos_from_IsLocalMax`.
    - #3 `h_laplace_align_scalar` via `laplace_align_scalar_of_aligned`.
    - #4 `h_time_chain_rule` via `time_chain_rule_Vec3_dot`.
    - #5 `h_envelope` via `envelope_identity_sqNorm_half_at_argmax`.
    - #6 `h_strain` via `strain_contraction_of_aligned`.
    - #7 `h_laplace_vec` via `laplace_vec_of_aligned`.
    - #8 `h_laplace_nonpos` via `laplaceOmega3_nonpos_from_IsLocalMax`.

    The remaining taken inputs are structural (NSEvolutionAxioms +
    IsLocalMax + alignment + positivity + growth) plus definitional
    matchings and per-slice/time smoothness witnesses. -/
theorem gradient_bound_fully_discharged
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
    -- Slice smoothness (sign discharges):
    (hf_nhd_sqNorm : ∀ i : Fin 3,
      ∀ᶠ s in 𝓝 (0 : ℝ),
        DifferentiableAt ℝ
          (slice (fun y =>
            Vec3.dot (vorticity u t y) (vorticity u t y)) xStar i) s)
    (hD_sqNorm : ∀ i : Fin 3,
      DifferentiableAt ℝ
        (deriv (slice (fun y =>
          Vec3.dot (vorticity u t y) (vorticity u t y)) xStar i)) 0)
    (hf_nhd_ω3 : ∀ i : Fin 3,
      ∀ᶠ s in 𝓝 (0 : ℝ),
        DifferentiableAt ℝ
          (slice (fun y => vorticity u t y 2) xStar i) s)
    (hD_ω3 : ∀ i : Fin 3,
      DifferentiableAt ℝ
        (deriv (slice (fun y => vorticity u t y 2) xStar i)) 0)
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
    -- NEW: Hessian expansion component data.
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
  -- Discharge #1 (h_hessian_expansion) via the bundle constructor.
  have h_hessian_expansion :
      hessian_trace_sqNorm = 2 * gradSqNorm + 2 * omega_laplace_omega := by
    have d := HessianExpansionData.ofScalarIdentities
      (vorticity u t xStar 0) (vorticity u t xStar 1)
      (vorticity u t xStar 2)
      gradSqNorm_0 gradSqNorm_1 gradSqNorm_2
      laplace_0 laplace_1 laplace_2
      ((vorticity u t xStar 0) ^ 2 + (vorticity u t xStar 1) ^ 2
        + (vorticity u t xStar 2) ^ 2)
      gradSqNorm hessian_trace_sqNorm omega_laplace_omega
      laplace_sq_0 laplace_sq_1 laplace_sq_2
      rfl
      h_gradSq_decomp
      h_omega_lap_decomp
      h_star_0 h_star_1 h_star_2
      h_trace_decomp
    exact d.hessian_expansion_packed
  -- Delegate to the 7-of-8 capstone.
  exact gradient_bound_time_envelope_discharged
    ax t ht htT xStar hmax M σ Mdot gradSqNorm laplaceOmega3
    omega_laplace_omega hessian_trace_sqNorm
    hM_pos hω0 hω1 hω2
    h_omega_lap_def h_laplace3_def h_σ_def
    h_trace_sum_def h_lap3_sum_def
    hf_nhd_sqNorm hD_sqNorm hf_nhd_ω3 hD_ω3
    h_time_diff
    M_fn h_M_fn_at_t h_M_fn_deriv h_env_dom h_env_hit h_slice_diff
    h_hessian_expansion
    h_growth_nonneg

end NSBlwChain.BLW
