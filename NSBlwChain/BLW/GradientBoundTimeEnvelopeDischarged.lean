-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.BLW.GradientBoundSignAlignDischarged
import NSBlwChain.BLW.TimeChainRuleDot

/-!
# Stronger partial-discharge capstone — sign+align+time+envelope internalised

Extends `GradientBoundSignAlignDischarged` by also internalising:

* **#4 `h_time_chain_rule`** via `time_chain_rule_Vec3_dot` (product
  rule on `Vec3.dot` from per-component `HasDerivAt`).

* **#5 `h_envelope`** via
  `envelope_identity_sqNorm_half_at_argmax` (Danskin envelope for
  `|ω|²/2` dominated by `(M_fn τ)²/2`).

Combined with the sign+alignment discharges, this capstone reduces
the 8 named hypotheses to **exactly 1 remaining explicit**:

- `h_hessian_expansion` (#1) — the vector-level Hessian-expansion
  identity `Δ|ω|² = 2|∇ω|² + 2·(ω·Δω)`.

This final residual could in principle be discharged via the
`HessianExpansionScalar.laplace_sq_eq_of_slice_identities_fin3`
machinery applied component-wise, but requires ~9 per-(component,
direction) slice 2nd-derivative identities + 4 consistency
equations — a substantial signature-bloat not undertaken here.

## Main result

* `gradient_bound_time_envelope_discharged` — 7-of-8 capstone
  discharge; only `h_hessian_expansion` remains explicit.
-/

namespace NSBlwChain.BLW

open Filter Topology
open scoped BigOperators

/-- **Time-envelope partial-discharge capstone.**

    Same conclusion as
    `gradient_bound_of_NSEvolutionAxioms_all_scalar_derived`, with
    seven of its eight named hypotheses discharged internally.

    Seven discharged:
    - Alignment algebra: `h_laplace_align_scalar` (#3),
      `h_strain` (#6), `h_laplace_vec` (#7).
    - Sign: `h_trace_nonpos` (#2), `h_laplace_nonpos` (#8).
    - Time: `h_time_chain_rule` (#4), `h_envelope` (#5).

    One remains explicit: `h_hessian_expansion` (#1). -/
theorem gradient_bound_time_envelope_discharged
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
    -- Step (ii) Hessian expansion — still explicit:
    (h_hessian_expansion :
      hessian_trace_sqNorm = 2 * gradSqNorm + 2 * omega_laplace_omega)
    -- Growth regime:
    (h_growth_nonneg : 0 ≤ Mdot) :
    gradSqNorm ≤ M ^ 2 * σ / ν := by
  -- Discharge #4 (h_time_chain_rule) via per-component product rule.
  have h_time_chain_rule :
      Vec3.dot (vorticity u t xStar)
               (fun j => deriv (fun τ => vorticity u τ xStar j) t)
        = deriv (fun τ =>
            Vec3.dot (vorticity u τ xStar) (vorticity u τ xStar) / 2) t :=
    time_chain_rule_Vec3_dot
      (fun τ => vorticity u τ xStar)
      (fun j => deriv (fun τ => vorticity u τ xStar j) t)
      t h_time_diff
  -- Discharge #5 (h_envelope) via Danskin.
  -- The slice deriv value we name is exactly the deriv we want.
  set slice_deriv :=
    deriv (fun τ => Vec3.dot (vorticity u τ xStar)
                               (vorticity u τ xStar) / 2) t with h_slice_deriv_def
  have h_slice : HasDerivAt
      (fun τ => Vec3.dot (vorticity u τ xStar)
                         (vorticity u τ xStar) / 2)
      slice_deriv t := h_slice_diff.hasDerivAt
  -- envelope_identity_sqNorm_half_at_argmax: slice_deriv = M t * deriv M t.
  -- In our setup: M_fn t = M and deriv M_fn t = Mdot (from h_M_fn_deriv.deriv).
  have h_env_result :
      slice_deriv = M_fn t * deriv M_fn t :=
    envelope_identity_sqNorm_half_at_argmax
      (fun y τ => vorticity u τ y) M_fn xStar t Mdot slice_deriv
      h_env_dom h_env_hit h_M_fn_deriv h_slice
  have h_envelope :
      deriv (fun τ => Vec3.dot (vorticity u τ xStar)
                                 (vorticity u τ xStar) / 2) t
        = M * Mdot := by
    rw [← h_slice_deriv_def, h_env_result, h_M_fn_at_t, h_M_fn_deriv.deriv]
  -- Delegate to the sign+alignment-discharged capstone.
  exact gradient_bound_sign_and_alignment_discharged
    ax t ht htT xStar hmax M σ Mdot gradSqNorm laplaceOmega3
    omega_laplace_omega hessian_trace_sqNorm
    hM_pos hω0 hω1 hω2
    h_omega_lap_def h_laplace3_def h_σ_def
    h_trace_sum_def h_lap3_sum_def
    hf_nhd_sqNorm hD_sqNorm hf_nhd_ω3 hD_ω3
    h_hessian_expansion
    h_time_chain_rule h_envelope
    h_growth_nonneg

end NSBlwChain.BLW
