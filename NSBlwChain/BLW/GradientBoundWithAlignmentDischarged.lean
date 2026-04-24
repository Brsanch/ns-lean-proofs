-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.BLW.GradientBoundAllScalarDerived
import NSBlwChain.BLW.LaplaceAlignScalar
import NSBlwChain.BLW.StrainAlignScalar

/-!
# Partial-discharge capstone — alignment-algebra identities internalised

Composes the three **pure alignment-algebra** discharges
(v0.16–v0.17) into `gradient_bound_of_NSEvolutionAxioms_all_scalar_derived`:

* **#3 `h_laplace_align_scalar`** via `laplace_align_scalar_of_aligned`
* **#6 `h_strain`** via `strain_contraction_of_aligned`
* **#7 `h_laplace_vec`** via `laplace_vec_of_aligned`

The five remaining capstone hypotheses (calculus-requiring) stay
explicit, since their discharge lemmas take additional smoothness /
time-differentiability inputs that would bloat this capstone's
signature: `h_hessian_expansion` (#1), `h_trace_nonpos` (#2),
`h_time_chain_rule` (#4), `h_envelope` (#5), `h_laplace_nonpos` (#8).

## Design choice

The alignment-algebra discharges only need the alignment hypotheses
`ω(x*) = (0, 0, M)` and three definitional matchings (for
`omega_laplace_omega`, `laplaceOmega3`, and `σ`) already in scope at
the scalar level.  The remaining five need per-component slice /
time smoothness and envelope dominance witnesses, which are
substantially more verbose.  This capstone thus cleanly saves three
hypotheses and demonstrates the composition pattern; a full
"zero-scalar-hypothesis" capstone is a natural future deliverable.

## Main result

* `gradient_bound_with_alignment_discharged` — takes 8 h_* count
  reduced to 5, using alignment + scalar-definition matchings to
  discharge the three alignment-algebra identities internally.
-/

namespace NSBlwChain.BLW

open scoped BigOperators

/-- **Partial-discharge capstone: alignment identities internalized.**

    Same conclusion as `gradient_bound_of_NSEvolutionAxioms_all_scalar_derived`
    but with the three alignment-algebra hypotheses
    (`h_laplace_align_scalar`, `h_strain`, `h_laplace_vec`) replaced
    by the alignment data plus definitional matchings.  Internally
    invokes `laplace_align_scalar_of_aligned`, `laplace_vec_of_aligned`,
    and `strain_contraction_of_aligned` to reconstruct them. -/
theorem gradient_bound_with_alignment_discharged
    {u : VelocityField} {ν T : ℝ} (ax : NSEvolutionAxioms u ν T)
    (t : ℝ) (ht : 0 ≤ t) (htT : t < T)
    (xStar : Vec3)
    (hmax : IsLocalMax
      (fun y : Vec3 => Vec3.dot (vorticity u t y) (vorticity u t y))
      xStar)
    (M σ Mdot gradSqNorm laplaceOmega3
      omega_laplace_omega hessian_trace_sqNorm : ℝ)
    (hM_pos : 0 < M)
    -- Alignment (replaces three capstone identities internally):
    (hω0 : vorticity u t xStar 0 = 0)
    (hω1 : vorticity u t xStar 1 = 0)
    (hω2 : vorticity u t xStar 2 = M)
    -- Definitional matchings:
    (h_omega_lap_def :
      omega_laplace_omega
        = Vec3.dot (vorticity u t xStar)
            (fun j => vectorLaplacian (vorticity u t) xStar j))
    (h_laplace3_def :
      laplaceOmega3 = vectorLaplacian (vorticity u t) xStar 2)
    (h_σ_def :
      σ = partialDeriv (fun y => u t y 2) 2 xStar)
    -- Step (ii) physical identities still taken:
    (h_hessian_expansion :
      hessian_trace_sqNorm = 2 * gradSqNorm + 2 * omega_laplace_omega)
    (h_trace_nonpos : hessian_trace_sqNorm ≤ 0)
    -- Step (iii) physical identities still taken:
    (h_time_chain_rule :
      Vec3.dot (vorticity u t xStar)
               (fun j => deriv (fun τ => vorticity u τ xStar j) t)
        = deriv (fun τ =>
            Vec3.dot (vorticity u τ xStar) (vorticity u τ xStar) / 2) t)
    (h_envelope :
      deriv (fun τ =>
        Vec3.dot (vorticity u τ xStar) (vorticity u τ xStar) / 2) t
        = M * Mdot)
    -- Local-frame sign + growth regime:
    (h_laplace_nonpos : laplaceOmega3 ≤ 0)
    (h_growth_nonneg : 0 ≤ Mdot) :
    gradSqNorm ≤ M ^ 2 * σ / ν := by
  -- Derive #3 (h_laplace_align_scalar) from alignment + definitions.
  have h_laplace_align_scalar :
      omega_laplace_omega = M * laplaceOmega3 :=
    laplace_align_scalar_of_aligned
      (vorticity u t xStar)
      (fun j => vectorLaplacian (vorticity u t) xStar j)
      h_omega_lap_def h_laplace3_def hω0 hω1 hω2
  -- Derive #7 (h_laplace_vec) from alignment.
  have h_laplace_vec :
      Vec3.dot (vorticity u t xStar)
               (fun j => vectorLaplacian (vorticity u t) xStar j)
        = M * laplaceOmega3 :=
    laplace_vec_of_aligned
      (vorticity u t xStar)
      (fun j => vectorLaplacian (vorticity u t) xStar j)
      h_laplace3_def hω0 hω1 hω2
  -- Derive #6 (h_strain) from alignment + σ definition.
  have h_strain :
      Vec3.dot (vorticity u t xStar)
               (vortexStretching u (vorticity u) t xStar)
        = M ^ 2 * σ :=
    strain_contraction_of_aligned u (vorticity u) t xStar hω0 hω1 hω2 h_σ_def
  -- Apply the all-scalar-derived capstone with the three filled-in identities.
  exact gradient_bound_of_NSEvolutionAxioms_all_scalar_derived
    ax t ht htT xStar hmax M σ Mdot gradSqNorm laplaceOmega3
    omega_laplace_omega hessian_trace_sqNorm
    hM_pos
    h_hessian_expansion h_trace_nonpos h_laplace_align_scalar
    h_time_chain_rule h_envelope h_strain h_laplace_vec
    h_laplace_nonpos h_growth_nonneg

end NSBlwChain.BLW
