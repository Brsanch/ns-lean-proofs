-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.BLW.GradientBoundWithAlignmentDischarged
import NSBlwChain.BLW.LaplaceOmega3Nonpos

/-!
# Strengthened partial-discharge capstone — alignment + sign internalised

Extends `GradientBoundWithAlignmentDischarged` by also internalising
the two sign conditions:

* **#2 `h_trace_nonpos`** via `hessian_trace_sqNorm_nonpos_from_IsLocalMax`
* **#8 `h_laplace_nonpos`** via `laplaceOmega3_nonpos_from_IsLocalMax`

Combined with the three alignment-algebra discharges
(`h_laplace_align_scalar`, `h_strain`, `h_laplace_vec`), this
capstone reduces the 8-hypothesis count to **3** remaining:

- `h_hessian_expansion` (#1) — needs 9 Fin 3 × Fin 3 slice identities.
- `h_time_chain_rule` (#4) — needs per-component time-differentiability.
- `h_envelope` (#5) — needs envelope dominance + argmax hit + slice time-deriv.

The discharge of #1, #4, #5 would require substantially more smoothness
infrastructure; they are left as explicit hypotheses in this capstone.

## Design

The sign discharges take per-slice differentiability on `|ω|²`
(for #2) and on `ω_3` (for #8), plus definitional matchings tying
the abstract scalars `hessian_trace_sqNorm` and `laplaceOmega3` to
the corresponding Fin 3 sums of slice 2nd-derivatives.  These ~10
additional hypothesis slots replace the 2 sign hypotheses — net
LOC/signature increase — but the capstone now exposes *exactly*
the smoothness data that a future `NSEvolutionAxioms`-driven
capstone would extract from `ax.smooth`.

## Main result

* `gradient_bound_sign_and_alignment_discharged` — 5-of-8 capstone
  hypotheses discharged internally.
-/

namespace NSBlwChain.BLW

open Filter Topology
open scoped BigOperators

/-- **Sign + alignment partial-discharge capstone.**

    Same conclusion as `gradient_bound_of_NSEvolutionAxioms_all_scalar_derived`,
    with five of its eight named hypotheses discharged internally:

    - Alignment algebra: `h_laplace_align_scalar` (#3),
      `h_strain` (#6), `h_laplace_vec` (#7) — from
      `GradientBoundWithAlignmentDischarged`.
    - Sign conditions: `h_trace_nonpos` (#2), `h_laplace_nonpos` (#8)
      — from `LaplaceOmega3Nonpos` via slice 2nd-derivative tests.

    Three remain explicit: `h_hessian_expansion` (#1),
    `h_time_chain_rule` (#4), `h_envelope` (#5). -/
theorem gradient_bound_sign_and_alignment_discharged
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
    -- Definitional matchings for alignment algebra:
    (h_omega_lap_def :
      omega_laplace_omega
        = Vec3.dot (vorticity u t xStar)
            (fun j => vectorLaplacian (vorticity u t) xStar j))
    (h_laplace3_def :
      laplaceOmega3 = vectorLaplacian (vorticity u t) xStar 2)
    (h_σ_def :
      σ = partialDeriv (fun y => u t y 2) 2 xStar)
    -- Definitional matchings for the two sign discharges:
    (h_trace_sum_def :
      hessian_trace_sqNorm
        = ∑ i : Fin 3, deriv (deriv (slice
            (fun y => Vec3.dot (vorticity u t y) (vorticity u t y))
            xStar i)) 0)
    (h_lap3_sum_def :
      laplaceOmega3
        = ∑ i : Fin 3, deriv (deriv (slice
            (fun y => vorticity u t y 2) xStar i)) 0)
    -- Smoothness hypotheses for #2 (|ω|² slice):
    (hf_nhd_sqNorm : ∀ i : Fin 3,
      ∀ᶠ s in 𝓝 (0 : ℝ),
        DifferentiableAt ℝ
          (slice (fun y =>
            Vec3.dot (vorticity u t y) (vorticity u t y)) xStar i) s)
    (hD_sqNorm : ∀ i : Fin 3,
      DifferentiableAt ℝ
        (deriv (slice (fun y =>
          Vec3.dot (vorticity u t y) (vorticity u t y)) xStar i)) 0)
    -- Smoothness hypotheses for #8 (ω_3 slice):
    (hf_nhd_ω3 : ∀ i : Fin 3,
      ∀ᶠ s in 𝓝 (0 : ℝ),
        DifferentiableAt ℝ
          (slice (fun y => vorticity u t y 2) xStar i) s)
    (hD_ω3 : ∀ i : Fin 3,
      DifferentiableAt ℝ
        (deriv (slice (fun y => vorticity u t y 2) xStar i)) 0)
    -- Step (ii) Hessian expansion still taken:
    (h_hessian_expansion :
      hessian_trace_sqNorm = 2 * gradSqNorm + 2 * omega_laplace_omega)
    -- Step (iii) time identities still taken:
    (h_time_chain_rule :
      Vec3.dot (vorticity u t xStar)
               (fun j => deriv (fun τ => vorticity u τ xStar j) t)
        = deriv (fun τ =>
            Vec3.dot (vorticity u τ xStar) (vorticity u τ xStar) / 2) t)
    (h_envelope :
      deriv (fun τ =>
        Vec3.dot (vorticity u τ xStar) (vorticity u τ xStar) / 2) t
        = M * Mdot)
    -- Growth regime:
    (h_growth_nonneg : 0 ≤ Mdot) :
    gradSqNorm ≤ M ^ 2 * σ / ν := by
  -- Discharge #2 (h_trace_nonpos) via IsLocalMax |ω|².
  have h_trace_nonpos : hessian_trace_sqNorm ≤ 0 := by
    rw [h_trace_sum_def]
    exact hessian_trace_sqNorm_nonpos_from_IsLocalMax
      (fun y => vorticity u t y) xStar hmax hf_nhd_sqNorm hD_sqNorm
  -- Discharge #8 (h_laplace_nonpos) via IsLocalMax + alignment + Cauchy-Schwarz.
  have h_laplace_nonpos : laplaceOmega3 ≤ 0 := by
    rw [h_lap3_sum_def]
    exact laplaceOmega3_nonpos_from_IsLocalMax
      (fun y => vorticity u t y) xStar M (le_of_lt hM_pos)
      hω0 hω1 hω2 hmax hf_nhd_ω3 hD_ω3
  -- Delegate to the alignment-discharged capstone.
  exact gradient_bound_with_alignment_discharged
    ax t ht htT xStar hmax M σ Mdot gradSqNorm laplaceOmega3
    omega_laplace_omega hessian_trace_sqNorm
    hM_pos hω0 hω1 hω2
    h_omega_lap_def h_laplace3_def h_σ_def
    h_hessian_expansion h_trace_nonpos
    h_time_chain_rule h_envelope
    h_laplace_nonpos h_growth_nonneg

end NSBlwChain.BLW
