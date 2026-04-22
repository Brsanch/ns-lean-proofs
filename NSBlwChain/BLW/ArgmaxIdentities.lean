-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Setup.VectorFields
import NSBlwChain.Setup.NSHypothesis
import NSBlwChain.Setup.ArgmaxFrame
import NSBlwChain.BLW.GradientBound

/-!
# Argmax identities feeding Theorem 12.2 (step (i)–(iii))

This file formalizes the three pointwise-at-argmax identities that
feed `GradBoundHypotheses` (see `BLW/GradientBound.lean`):

* **Step (i)** — `∇|ω|²(x*) = 0` ⇒ `M · ∂ᵢ ω_3 (x*) = 0`.
* **Step (ii)** — `Hess(|ω|²)(x*) ≤ 0` (trace form) gives
  `|∇ω|²(x*) ≤ M · |Δω_3(x*)|`.
* **Step (iii)** — vorticity equation at `x*` gives
  `ν · Δω_3(x*) = dM/dt - M · σ(x*)`.

Each step is packaged here as a *hypothesis bundle* (a named
structure over the scalar quantities) together with the one-line
algebraic combination that produces the corresponding field of
`GradBoundHypotheses`.

The analytical discharge of each hypothesis bundle from
`NSEvolutionAxioms` is left for a subsequent pass; this file
isolates the algebraic glue so that the discharge can be attacked
step-by-step without perturbing the consumer side.

## Philosophy

Step (i)–(iii) are *pointwise* identities: they hold at a single
fixed `(x*, t)` and are finite-dimensional calculus — no functional-
analytic machinery.  The analytical content is:

* Step (i): `∇|ω|² = 2 ∑_k ω_k ∇ω_k` + argmax identity.
* Step (ii): Hessian of a local max has non-positive trace; expand
  `Δ|ω|² = 2 |∇ω|² + 2 ω · Δω` and use step (i) to drop
  off-diagonal terms.
* Step (iii): pointwise vorticity equation `∂_t ω = S ω - u·∇ω + ν Δω`
  evaluated at `x*`, combined with the argmax identity
  `u · ∇|ω|²(x*) = 0` and `ω(x*) = M ê₃` in the local frame.

None of these steps require real-analysis machinery beyond
multivariable calculus.  They are analytical in the same sense that
`ddx x² = 2x` is analytical.
-/

namespace NSBlwChain.BLW

open NSBlwChain

/-- **Argmax analytical hypotheses.**

    Packages the three pointwise identities that feed Theorem 12.2,
    each stated as a scalar identity over the local-frame quantities.
    The fields correspond directly to the fields of
    `GradBoundHypotheses`:

    * `step_i`   — from `∇|ω|² = 0` and `ω = M ê₃`.
    * `step_ii`  — from trace of Hessian.
    * `step_iii` — from vorticity equation at `x*`.

    Discharging this bundle from `NSEvolutionAxioms` is the content
    of the analytical-pass files `BLW/ArgmaxCalculus.lean` (step i/ii)
    and `BLW/VorticityAtArgmax.lean` (step iii), to be written. -/
structure ArgmaxAnalyticalBundle where
  /-- Viscosity, `ν > 0`. -/
  ν             : ℝ
  /-- `|ω(x*, t)|`, the argmax value. -/
  M             : ℝ
  /-- `σ(x*, t) = ω̂ · S ω̂`. -/
  sigma         : ℝ
  /-- `|∇ω|²(x*, t)`, the spatial-gradient norm-squared. -/
  gradSqNorm    : ℝ
  /-- `Δω_3(x*, t)` in the local frame. -/
  laplaceOmega3 : ℝ
  /-- `dM/dt(t)`, the envelope time-derivative. -/
  growth        : ℝ
  nu_pos        : 0 < ν
  M_nonneg      : 0 ≤ M
  /-- Step (i): `M · ∂ᵢω_3(x*) = 0`.  In this scalar packaging, we
      record only the *downstream* consequence: off-diagonal squared-
      derivative contributions drop out of step (ii). -/
  step_i_M_zero_or_zero :
    True  -- placeholder: records that step (i) is consumed only
          -- via its effect on step (ii).
  /-- Step (ii): `|∇ω|²(x*) ≤ M · |Δω_3(x*)|`. -/
  step_ii  : gradSqNorm ≤ M * |laplaceOmega3|
  /-- Step (iii): `ν · Δω_3(x*) = dM/dt - M · σ(x*)`. -/
  step_iii : ν * laplaceOmega3 = growth - M * sigma
  /-- `ω_3` is locally maximal at `x*` in the local frame, so
      `Δω_3(x*) ≤ 0`. -/
  laplace_nonpos : laplaceOmega3 ≤ 0
  /-- Growth-regime hypothesis `dM/dt(t) ≥ 0`. -/
  growth_nonneg : 0 ≤ growth

/-- **Wiring to `GradBoundHypotheses`.**

    Given an `ArgmaxAnalyticalBundle`, produce the corresponding
    `GradBoundHypotheses`, which is then consumed by the algebraic
    `gradient_bound` theorem to deliver Theorem 12.2. -/
def ArgmaxAnalyticalBundle.toGradBoundHypotheses
    (a : ArgmaxAnalyticalBundle) : GradBoundHypotheses where
  ν             := a.ν
  M             := a.M
  sigma         := a.sigma
  gradSqNorm    := a.gradSqNorm
  laplaceOmega3 := a.laplaceOmega3
  growth        := a.growth
  nu_pos        := a.nu_pos
  M_nonneg      := a.M_nonneg
  gradSqNorm_le_M_laplace       := a.step_ii
  laplace_eq_growth_minus_strain := a.step_iii
  laplace_nonpos                 := a.laplace_nonpos
  growth_nonneg                  := a.growth_nonneg

/-- **Theorem 12.2 on the analytical bundle.**

    Given an `ArgmaxAnalyticalBundle`, the gradient bound
    `|∇ω|²(x*) ≤ M² σ(x*) / ν` holds.

    This composes `ArgmaxAnalyticalBundle.toGradBoundHypotheses`
    with `GradBoundHypotheses.gradient_bound`. -/
theorem ArgmaxAnalyticalBundle.gradient_bound
    (a : ArgmaxAnalyticalBundle) :
    a.gradSqNorm ≤ a.M ^ 2 * a.sigma / a.ν :=
  a.toGradBoundHypotheses.gradient_bound

end NSBlwChain.BLW
