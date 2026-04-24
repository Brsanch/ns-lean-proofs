-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Setup.VectorFields

set_option diagnostics true
set_option diagnostics.threshold 100

/-!
# Step (ii) inequality from Hessian trace + Hessian expansion + alignment

Derives the step-(ii) inequality `|∇ω|²(x*) ≤ M · |Δω_3(x*)|` from:

1. **Hessian trace non-positive** at a local max of `|ω|²`
   (from `MaxPrinciple.ScalarLocalMaxSecondDeriv.trace_nonpos`):
   `Δ(|ω|²)(x*) ≤ 0`.
2. **Hessian expansion** (from `HessianExpansionFromC2`):
   `Δ(|ω|²) = 2·|∇ω|² + 2·ω·Δω`.
3. **Alignment contraction** (from `AlignmentContraction.dot_of_aligned`
   or `StrainContractionAligned.laplace_contraction_of_aligned`):
   `ω·Δω(x*) = M · Δω_3(x*)` under alignment `ω(x*) = M·ê₂`.
4. **Sign condition** at local max:
   `Δω_3(x*) ≤ 0`.
5. **Positivity**: `0 ≤ M`.

Combining: `|∇ω|² ≤ -ω·Δω = -M·Δω_3 = M·|Δω_3|` (the last using
`|Δω_3| = -Δω_3` when `Δω_3 ≤ 0`).

## Positioning

Step-ii was the last taken scalar Prop at the L9 grand-compose /
`gradient_bound_of_NSEvolutionAxioms_step_iii_derived` capstone.
With this derivation, the gradient bound `|∇ω|² ≤ M²·σ/ν` is
producible from NSEv + argmax + alignment + Danskin + 4 vector-field
physical identities, with NO remaining scalar Props taken.

## Result

`step_ii_inequality_derived`: scalar-level lemma.
-/

namespace NSBlwChain.BLW

/-- **Step (ii) inequality from Hessian-trace + expansion + alignment.**

    Given scalar inputs:
    * `M` with `0 ≤ M`,
    * `gradSqNorm` (= `|∇ω|²(x*)`),
    * `laplaceOmega3` (= `Δω_3(x*)` in the local frame, with
      `laplaceOmega3 ≤ 0` from local-max sign),
    * `omega_laplace_omega` (= `ω · Δω(x*)`),
    * `hessian_trace_sqNorm` (= `Δ(|ω|²)(x*)`),

    and the three identities/inequalities:
    * `h_expansion : hessian_trace_sqNorm = 2 · gradSqNorm + 2 · omega_laplace_omega`,
    * `h_trace_nonpos : hessian_trace_sqNorm ≤ 0`,
    * `h_laplace_align : omega_laplace_omega = M · laplaceOmega3`,

    conclude `gradSqNorm ≤ M · |laplaceOmega3|`. -/
theorem step_ii_inequality_derived
    (M gradSqNorm laplaceOmega3 omega_laplace_omega
      hessian_trace_sqNorm : ℝ)
    (hM_nonneg : 0 ≤ M)
    (h_expansion :
      hessian_trace_sqNorm = 2 * gradSqNorm + 2 * omega_laplace_omega)
    (h_trace_nonpos : hessian_trace_sqNorm ≤ 0)
    (h_laplace_align : omega_laplace_omega = M * laplaceOmega3)
    (h_laplace_nonpos : laplaceOmega3 ≤ 0) :
    gradSqNorm ≤ M * |laplaceOmega3| := by
  -- Step 1: 2·gradSqNorm + 2·omega_laplace_omega ≤ 0, so
  -- gradSqNorm ≤ -omega_laplace_omega.
  have h1 : gradSqNorm ≤ -omega_laplace_omega := by
    linarith [h_expansion, h_trace_nonpos]
  -- Step 2: substitute omega_laplace_omega = M · laplaceOmega3.
  rw [h_laplace_align] at h1
  -- h1 : gradSqNorm ≤ -(M * laplaceOmega3)
  -- Step 3: |laplaceOmega3| = -laplaceOmega3 since laplaceOmega3 ≤ 0.
  have h_abs : |laplaceOmega3| = -laplaceOmega3 := abs_of_nonpos h_laplace_nonpos
  rw [h_abs]
  -- Goal: gradSqNorm ≤ M * (-laplaceOmega3)
  -- From h1 and the algebra M · (-laplaceOmega3) = -(M · laplaceOmega3).
  have h_neg : M * (-laplaceOmega3) = -(M * laplaceOmega3) := by ring
  linarith [h1, h_neg]

end NSBlwChain.BLW
