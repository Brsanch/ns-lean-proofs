-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.BLW.ArgmaxGradient
import NSBlwChain.BLW.HessianAtArgmax
import NSBlwChain.BLW.VorticityAtArgmax
import NSBlwChain.BLW.ArgmaxIdentities
import NSBlwChain.BLW.GradientBound

/-!
# Composition of Theorem 12.2 steps (i), (ii), (iii)

This file wires the scalar-algebra hypothesis bundles for steps
(ii) (`HessianAtArgmaxInputs`) and (iii) (`VorticityAtArgmaxInputs`)
into the unified `ArgmaxAnalyticalBundle` of `BLW/ArgmaxIdentities.lean`,
given they share the scalars `M, laplaceOmega3` and together with a
growth-regime hypothesis `0 ≤ dM/dt`.

Step (i) contributes implicitly: its conclusion `M · ∂ᵢω_3 = 0` is
already absorbed into `HessianAtArgmaxInputs.laplace_sqNorm_expansion`
(the Hessian-expansion step drops the `(∂ᵢω_3)²` terms because of
step (i)).  We do not thread step (i) as a separate input here; it
is simply part of the analytical discharge that produces the Hessian
expansion.

## Downstream

Combining with `ArgmaxAnalyticalBundle.gradient_bound`, this yields
`gradSqNorm ≤ M² · σ / ν` as a one-line consequence of the two
scalar-algebra bundles plus a single `0 ≤ dM/dt` hypothesis.
-/

namespace NSBlwChain.BLW

/-- Consistency hypothesis: step (ii) and step (iii) bundles agree on
    the scalars that appear in both. -/
structure StepsCompatibility
    (h₂ : HessianAtArgmaxInputs) (h₃ : VorticityAtArgmaxInputs) : Prop where
  M_eq : h₂.M = h₃.M
  laplace_eq : h₂.laplaceOmega3 = h₃.laplaceOmega3

/-- Compose step (ii) + step (iii) + growth hypothesis into an
    `ArgmaxAnalyticalBundle`.

    The growth-regime hypothesis `0 ≤ h₃.growth` is required by
    `ArgmaxAnalyticalBundle.growth_nonneg`, and corresponds to the
    paper's Theorem 12.2 hypothesis `dM/dt(t) ≥ 0`. -/
def ArgmaxAnalyticalBundle.ofSteps
    (h₂ : HessianAtArgmaxInputs) (h₃ : VorticityAtArgmaxInputs)
    (hc : StepsCompatibility h₂ h₃)
    (hg : 0 ≤ h₃.growth) : ArgmaxAnalyticalBundle where
  ν             := h₃.ν
  M             := h₃.M
  sigma         := h₃.sigma
  gradSqNorm    := h₂.gradSqNorm
  laplaceOmega3 := h₃.laplaceOmega3
  growth        := h₃.growth
  nu_pos        := h₃.nu_pos
  M_nonneg      := le_of_lt h₃.M_pos
  step_i_M_zero_or_zero := trivial
  step_ii := by
    have h := h₂.step_ii
    -- h : h₂.gradSqNorm ≤ h₂.M * |h₂.laplaceOmega3|
    -- target: h₂.gradSqNorm ≤ h₃.M * |h₃.laplaceOmega3|
    rw [← hc.M_eq, ← hc.laplace_eq]
    exact h
  step_iii := h₃.step_iii
  laplace_nonpos := by
    rw [← hc.laplace_eq]
    exact h₂.laplace_nonpos
  growth_nonneg := hg

/-- **End-to-end.**  From the two step-bundles, plus compatibility
    and the growth-regime hypothesis, the gradient bound
    `|∇ω|²(x*) ≤ M² σ / ν` is one line. -/
theorem gradient_bound_of_steps
    (h₂ : HessianAtArgmaxInputs) (h₃ : VorticityAtArgmaxInputs)
    (hc : StepsCompatibility h₂ h₃)
    (hg : 0 ≤ h₃.growth) :
    h₂.gradSqNorm ≤ h₃.M ^ 2 * h₃.sigma / h₃.ν :=
  (ArgmaxAnalyticalBundle.ofSteps h₂ h₃ hc hg).gradient_bound

end NSBlwChain.BLW
