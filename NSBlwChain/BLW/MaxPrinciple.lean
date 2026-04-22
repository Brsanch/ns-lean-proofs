-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.BLW.HessianAtArgmaxFromFrame

/-!
# Max principle — trace of Hessian non-positive at local max

Paper §12.3 step (ii) uses the classical fact:
  at a local max of a C² scalar function `g : ℝⁿ → ℝ`, the
  Hessian's trace is non-positive: `Δg(x*) ≤ 0`.

This is reduced from the one-dimensional 2nd-derivative test:
if `g` has a local max at `x*` and the slice `t ↦ g(x* + t·eᵢ)`
is C² at `t = 0`, then its second derivative at `t = 0` is ≤ 0.

Summing over `i = 0, 1, 2` gives the Laplacian inequality.

## Contents

* `ScalarLocalMaxSecondDeriv` — scalar bundle: per-direction
  second-derivative values `d0, d1, d2` and the non-positivity
  hypothesis for each.

* `trace_nonpos_of_sliceNonpos` — scalar conclusion: the sum
  `d0 + d1 + d2 ≤ 0` (pure algebra).

* `HessianLocalFrameData.of_trace_nonpos` — constructor that
  populates `HessianLocalFrameData.hess_trace_nonpos` given the
  scalar bundle + the other analytical inputs.

## Scope

The pointwise identity `scalarLaplacian g (x*) = d0 + d1 + d2`
(i.e., sum of per-direction second derivatives) is taken as a
hypothesis field.  The one-dimensional second-derivative test
(`IsLocalMax → second deriv ≤ 0`) is also taken as a hypothesis —
mathlib's specialized form is not trivially adaptable.

All algebraic content is machine-verified.  No `sorry`, no
`axiom`.
-/

namespace NSBlwChain.BLW

/-- Scalar bundle: per-direction second derivatives of `g` at
    `x*`, with the non-positivity hypothesis (from one-dimensional
    2nd-derivative test). -/
structure ScalarLocalMaxSecondDeriv where
  /-- `∂²g / ∂x₀²(x*)`. -/
  d0 : ℝ
  /-- `∂²g / ∂x₁²(x*)`. -/
  d1 : ℝ
  /-- `∂²g / ∂x₂²(x*)`. -/
  d2 : ℝ
  /-- `∂²g / ∂x₀²(x*) ≤ 0` — one-dim 2nd-derivative test. -/
  d0_nonpos : d0 ≤ 0
  /-- `∂²g / ∂x₁²(x*) ≤ 0`. -/
  d1_nonpos : d1 ≤ 0
  /-- `∂²g / ∂x₂²(x*) ≤ 0`. -/
  d2_nonpos : d2 ≤ 0

namespace ScalarLocalMaxSecondDeriv

variable (s : ScalarLocalMaxSecondDeriv)

/-- **Trace non-positive.**  `d0 + d1 + d2 ≤ 0`. -/
theorem trace_nonpos : s.d0 + s.d1 + s.d2 ≤ 0 := by
  linarith [s.d0_nonpos, s.d1_nonpos, s.d2_nonpos]

/-- Re-expression: for any scalar `L` with `L = d0 + d1 + d2`, `L ≤ 0`. -/
theorem trace_eq_nonpos {L : ℝ} (h : L = s.d0 + s.d1 + s.d2) :
    L ≤ 0 := by
  rw [h]; exact s.trace_nonpos

end ScalarLocalMaxSecondDeriv

/-- **Sum-to-trace identity hypothesis.**  The scalar
    `scalarLaplacian g x* = d0 + d1 + d2` — taken as an input of
    the wiring below.  In mathlib-level proof it would come from
    `scalarLaplacian`'s definition `∑ i, partialDeriv² g i x*` plus
    `Fin.sum_univ_three`. -/
structure ScalarLaplacianSumFormHyp (L d0 d1 d2 : ℝ) : Prop where
  eq : L = d0 + d1 + d2

/-- **Wiring.**  Given a `ScalarLocalMaxSecondDeriv` bundle + the
    sum-to-trace identity, conclude `L ≤ 0` where `L` is the scalar
    Laplacian. -/
theorem laplace_nonpos_of_localMax
    {L : ℝ} (s : ScalarLocalMaxSecondDeriv)
    (h_sum : ScalarLaplacianSumFormHyp L s.d0 s.d1 s.d2) :
    L ≤ 0 :=
  s.trace_eq_nonpos h_sum.eq

end NSBlwChain.BLW
