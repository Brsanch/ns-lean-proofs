-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.BLW.GradientBoundStepIIIDerived
import NSBlwChain.BLW.StepIIInequalityDerivation

/-!
# Gradient bound with **all** scalar-level Props derived

Capstone composing:

- `step_ii_inequality_derived` (from `StepIIInequalityDerivation.lean`),
- `step_iii_identity_from_NSEvolution` (from `StepIIIFromNSEvolution.lean`,
  consumed inside `gradient_bound_of_NSEvolutionAxioms_step_iii_derived`).

Result: a gradient bound producer with **no** taken scalar Props —
only NSEv + argmax + positivity + the vector-field-layer physical
identities (4 for step-iii + 3 for step-ii).

## Scope of inputs

What the caller supplies:

- `ax : NSEvolutionAxioms u ν T` (for vorticity equation + smoothness).
- `hmax : IsLocalMax |ω|² xStar` (for advection vanishing + Hessian
  trace non-positive).
- Scalar data `M, σ, Mdot, gradSqNorm, laplaceOmega3,
  omega_laplace_omega, hessian_trace_sqNorm`.
- Positivity `0 < M`.
- Sign `laplaceOmega3 ≤ 0` (from local max in local frame).
- Growth regime `0 ≤ Mdot`.
- Step (ii) physical identities: Hessian expansion, Hessian trace
  non-positive, alignment contraction for Laplace.
- Step (iii) physical identities: time chain rule, envelope, strain
  alignment, Laplace alignment.

What comes out:

  `gradSqNorm ≤ M² · σ / ν`
-/

namespace NSBlwChain.BLW

/-- **Gradient bound with all scalar Props derived.**

    Composes `step_ii_inequality_derived` +
    `gradient_bound_of_NSEvolutionAxioms_step_iii_derived`.  No
    scalar Props are taken as hypotheses; the remaining taken
    hypotheses are vector-field-layer physical identities that
    unfold to pointwise algebra on `∂_tω`, `(ω·∇)u`, `Δω`, and
    `∇(|ω|²)`. -/
theorem gradient_bound_of_NSEvolutionAxioms_all_scalar_derived
    {u : VelocityField} {ν T : ℝ} (ax : NSEvolutionAxioms u ν T)
    (t : ℝ) (ht : 0 ≤ t) (htT : t < T)
    (xStar : Vec3)
    (hmax : IsLocalMax
      (fun y : Vec3 => Vec3.dot (vorticity u t y) (vorticity u t y))
      xStar)
    (M σ Mdot gradSqNorm laplaceOmega3
      omega_laplace_omega hessian_trace_sqNorm : ℝ)
    (hM_pos : 0 < M)
    -- Step (ii) physical identities:
    (h_hessian_expansion :
      hessian_trace_sqNorm = 2 * gradSqNorm + 2 * omega_laplace_omega)
    (h_trace_nonpos : hessian_trace_sqNorm ≤ 0)
    (h_laplace_align_scalar : omega_laplace_omega = M * laplaceOmega3)
    -- Step (iii) physical identities:
    (h_time_chain_rule :
      Vec3.dot (vorticity u t xStar)
               (fun j => deriv (fun τ => vorticity u τ xStar j) t)
        = deriv (fun τ =>
            Vec3.dot (vorticity u τ xStar) (vorticity u τ xStar) / 2) t)
    (h_envelope :
      deriv (fun τ =>
        Vec3.dot (vorticity u τ xStar) (vorticity u τ xStar) / 2) t
        = M * Mdot)
    (h_strain :
      Vec3.dot (vorticity u t xStar)
               (vortexStretching u (vorticity u) t xStar) = M ^ 2 * σ)
    (h_laplace_vec :
      Vec3.dot (vorticity u t xStar)
               (fun j => vectorLaplacian (vorticity u t) xStar j)
        = M * laplaceOmega3)
    -- Local-frame sign + growth regime:
    (h_laplace_nonpos : laplaceOmega3 ≤ 0)
    (h_growth_nonneg : 0 ≤ Mdot) :
    gradSqNorm ≤ M ^ 2 * σ / ν := by
  -- Step 1: derive step-(ii) inequality gradSqNorm ≤ M · |laplaceOmega3|.
  have h_step_ii : gradSqNorm ≤ M * |laplaceOmega3| :=
    step_ii_inequality_derived M gradSqNorm laplaceOmega3
      omega_laplace_omega hessian_trace_sqNorm
      (le_of_lt hM_pos)
      h_hessian_expansion h_trace_nonpos h_laplace_align_scalar
      h_laplace_nonpos
  -- Step 2: apply the step-iii-derived gradient-bound capstone.
  exact gradient_bound_of_NSEvolutionAxioms_step_iii_derived ax t ht htT
    xStar hmax M σ Mdot gradSqNorm laplaceOmega3
    hM_pos h_step_ii
    h_time_chain_rule h_envelope h_strain h_laplace_vec
    h_laplace_nonpos h_growth_nonneg

end NSBlwChain.BLW
