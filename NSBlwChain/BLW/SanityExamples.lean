-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.BLW.GradientBound
import NSBlwChain.BLW.ArgmaxGradient
import NSBlwChain.BLW.ArgmaxIdentities

/-!
# Sanity-check examples for the BLW-chain scalar bundles

Concrete instantiations of the scalar hypothesis bundles with
explicit numerical values, verifying that:

* `GradBoundHypotheses` can be populated.
* `ArgmaxGradientInputs` can be populated.
* The conclusion `gradient_bound` computes the expected scalar.

These examples are **not load-bearing** for any downstream proof.
They serve as smoke tests: confirming the structural bundles are
instantiable and the algebraic conclusions deliver sensible
numbers.

## Contents

* `example_gradBoundHypotheses` — `ν = 1, M = 10, σ = 4, gradSqNorm = 40,
  laplaceOmega3 = -4, growth = 0`.  Checks `gradient_bound`
  conclusion `gradSqNorm ≤ 400`.

* `example_argmaxGradientInputs` — trivial instance with
  `M = 10, ∂ω₃ = 0`.

Both are `example` declarations (no namespace pollution).
-/

namespace NSBlwChain.BLW

open NSBlwChain

/-- Concrete `GradBoundHypotheses` instance with ν=1, M=10, σ=4,
    gradSqNorm=40, laplaceOmega3=-4, growth=0. -/
noncomputable def exampleGradBound : GradBoundHypotheses where
  ν                              := 1
  M                              := 10
  sigma                          := 4
  gradSqNorm                     := 40
  laplaceOmega3                  := -4
  growth                         := 0
  nu_pos                         := by norm_num
  M_nonneg                       := by norm_num
  gradSqNorm_le_M_laplace        := by
    have h : |(-4 : ℝ)| = 4 := by
      rw [abs_of_nonpos (by norm_num : (-4 : ℝ) ≤ 0)]
      norm_num
    rw [h]; norm_num
  laplace_eq_growth_minus_strain := by norm_num
  laplace_nonpos                 := by norm_num
  growth_nonneg                  := le_refl 0

/-- Sanity check: the concrete bundle yields `gradSqNorm ≤ 400 = 10²·4/1`. -/
example : exampleGradBound.gradSqNorm ≤ exampleGradBound.M ^ 2 *
    exampleGradBound.sigma / exampleGradBound.ν :=
  exampleGradBound.gradient_bound

/-- Concrete `ArgmaxGradientInputs` with M=10, ∂ω₃=0, ∂|ω|²=0. -/
def exampleArgmaxGradient : ArgmaxGradientInputs where
  M               := 10
  partial_omega_3 := 0
  partial_sqNorm  := 0
  sqNorm_form     := by norm_num
  sqNorm_zero     := rfl

/-- Sanity check: step (i) yields `M · ∂ᵢω₃ = 0`. -/
example : exampleArgmaxGradient.M * exampleArgmaxGradient.partial_omega_3 = 0 :=
  exampleArgmaxGradient.step_i

end NSBlwChain.BLW
