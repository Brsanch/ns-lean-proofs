-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Setup.VectorFields
import NSBlwChain.Setup.NSHypothesis
import NSBlwChain.Setup.ArgmaxFrame

/-!
# Theorem 12.2 — pointwise gradient bound at the vorticity argmax

This file formalizes the *algebraic* core of **Theorem 12.2** from
§12.3 of the companion paper:

  `|∇ω|²(x*, t) ≤ M(t)² · σ(x*, t) / ν`,

under the hypothesis `dM/dt(t) ≥ 0`, where

  `M(t) = |ω(x*(t), t)|`,     `σ(x*, t) = hat ω · S hat ω`.

The analytical content of §12.3 breaks into five pointwise steps:

  (i)   `∇|ω|²(x*) = 0` ⇒ `M · ∂_i ω_3 (x*) = 0`       (argmax identity)
  (ii)  `Hess(|ω|²)(x*) ≤ 0` (trace)
            ⇒ `|∇ω|²(x*) ≤ M · |Δ ω_3(x*)|`               (Hessian bound)
  (iii) Vorticity equation at x* ⇒
            `ν Δ ω_3(x*) = dM/dt - M σ(x*)`              (time-derivative)
  (iv)  `dM/dt ≥ 0` + (ii)(iii) + `Δ ω_3(x*) ≤ 0`
            ⇒ `ν |Δ ω_3(x*)| ≤ M σ(x*)`                    (sign step)
  (v)   Combine (ii) and (iv)
            ⇒ `|∇ω|²(x*) ≤ M² σ(x*) / ν`.                 (conclusion)

Steps (i)–(iii) are analytical and live on the `Setup/*` side:
they rely on the vorticity equation, the vanishing-gradient identity
at an argmax, and trace-non-positivity of the Hessian.  Those steps
are packaged below as named *hypotheses* (to be discharged from
richer Setup content in a later pass).

**This file carries out steps (iv) and (v) — pure algebra — rigorously,
with no `sorry` and no axiomatic content.**  The "rigorous proof of
Theorem 12.2" in this project is thus reduced to the discharge of
the four named pointwise hypotheses in `GradBoundHypotheses` below.

## Why bother with the algebraic core first

Isolating the pure-algebra step makes the dependency graph explicit:
every analytical subtlety in §12.3 is confined to the hypotheses of
`GradBoundHypotheses`, and the chain's numerical conclusion is a
one-line consequence.  This mirrors the SQG-project's practice of
separating algebraic manipulations from the analytical identities
that feed them.
-/

namespace NSBlwChain.BLW

open NSBlwChain

/-- **Hypothesis bundle for the gradient bound.**

    Packages the four pointwise analytical identities that together
    imply `|∇ω|²(x*) ≤ M² σ(x*) / ν`.  Each field corresponds exactly
    to one numbered equation in the companion paper §12.3:

    * `gradSqNorm_le_M_laplace`  — equation (12.4).
    * `laplace_eq_growth_minus_strain` — equation (12.5).
    * `laplace_nonpos`           — local-max of `ω_3` at `x*`
      (paper's remark after Step (ii)).
    * `growth_nonneg`            — the theorem's main hypothesis
      `dM/dt(t) ≥ 0` (the "growth regime" of Caveat C1).

    The four scalars `gradSqNorm, M, sigma, laplaceOmega3, growth`
    represent the physical quantities:

    * `gradSqNorm` — `|∇ω|²(x*)`.
    * `M`          — `|ω(x*)|`.
    * `sigma`      — `σ(x*) = hat ω · S hat ω`.
    * `laplaceOmega3` — `Δ ω_3(x*)` in the local frame.
    * `growth`    — `dM/dt` at the time under consideration.

    All five live in `ℝ`. -/
structure GradBoundHypotheses where
  ν             : ℝ
  M             : ℝ
  sigma         : ℝ
  gradSqNorm    : ℝ
  laplaceOmega3 : ℝ
  growth        : ℝ
  /-- Positive viscosity. -/
  nu_pos        : 0 < ν
  /-- `M` is non-negative (it is a norm). -/
  M_nonneg      : 0 ≤ M
  /-- Equation (12.4): the Hessian bound. -/
  gradSqNorm_le_M_laplace :
    gradSqNorm ≤ M * |laplaceOmega3|
  /-- Equation (12.5): time-derivative at `x*`. -/
  laplace_eq_growth_minus_strain :
    ν * laplaceOmega3 = growth - M * sigma
  /-- `ω_3` attains a local max at `x*`, so `Δω_3(x*) ≤ 0`. -/
  laplace_nonpos : laplaceOmega3 ≤ 0
  /-- Growth-regime hypothesis `dM/dt(t) ≥ 0`. -/
  growth_nonneg  : 0 ≤ growth

namespace GradBoundHypotheses

variable (h : GradBoundHypotheses)

/-- **Step (iv).**  From the sign hypotheses plus (12.5),
    `ν |Δω_3(x*)| ≤ M σ(x*)`. -/
lemma abs_laplace_bound : h.ν * |h.laplaceOmega3| ≤ h.M * h.sigma := by
  have habs : |h.laplaceOmega3| = - h.laplaceOmega3 :=
    abs_of_nonpos h.laplace_nonpos
  -- From (12.5): ν · laplaceOmega3 = growth - M σ, so
  -- ν · (- laplaceOmega3) = M σ - growth ≤ M σ (since growth ≥ 0).
  calc h.ν * |h.laplaceOmega3|
      = h.ν * (- h.laplaceOmega3) := by rw [habs]
    _ = - (h.ν * h.laplaceOmega3) := by ring
    _ = - (h.growth - h.M * h.sigma) := by
          rw [h.laplace_eq_growth_minus_strain]
    _ = h.M * h.sigma - h.growth := by ring
    _ ≤ h.M * h.sigma := by linarith [h.growth_nonneg]

/-- **Step (v).**  The gradient bound:
    `|∇ω|²(x*) ≤ M² σ(x*) / ν`. -/
theorem gradient_bound : h.gradSqNorm ≤ h.M ^ 2 * h.sigma / h.ν := by
  -- Chain: gradSqNorm ≤ M |Δω_3|  (step_ii)
  --        ν |Δω_3| ≤ M σ          (step_iv)
  -- Multiply step_ii by ν > 0 and use step_iv on the RHS.
  have step_ii : h.gradSqNorm ≤ h.M * |h.laplaceOmega3| :=
    h.gradSqNorm_le_M_laplace
  have step_iv : h.ν * |h.laplaceOmega3| ≤ h.M * h.sigma :=
    h.abs_laplace_bound
  have hν_pos := h.nu_pos
  have hν_nn := le_of_lt hν_pos
  have hν_ne : h.ν ≠ 0 := ne_of_gt hν_pos
  have hM_nonneg := h.M_nonneg
  -- ν · gradSqNorm ≤ ν · (M |Δω_3|) = M · (ν |Δω_3|) ≤ M · (M σ) = M² σ.
  have key : h.gradSqNorm * h.ν ≤ h.M ^ 2 * h.sigma := by
    calc h.gradSqNorm * h.ν
        = h.ν * h.gradSqNorm := by ring
      _ ≤ h.ν * (h.M * |h.laplaceOmega3|) :=
          mul_le_mul_of_nonneg_left step_ii hν_nn
      _ = h.M * (h.ν * |h.laplaceOmega3|) := by ring
      _ ≤ h.M * (h.M * h.sigma) :=
          mul_le_mul_of_nonneg_left step_iv hM_nonneg
      _ = h.M ^ 2 * h.sigma := by ring
  -- Rearrange: `M² σ / ν - gradSqNorm = (M² σ - gradSqNorm · ν) / ν ≥ 0`.
  have num_nonneg : 0 ≤ h.M ^ 2 * h.sigma - h.gradSqNorm * h.ν := by linarith
  have diff_eq :
      h.M ^ 2 * h.sigma / h.ν - h.gradSqNorm
        = (h.M ^ 2 * h.sigma - h.gradSqNorm * h.ν) / h.ν := by
    field_simp
  have diff_nonneg : 0 ≤ h.M ^ 2 * h.sigma / h.ν - h.gradSqNorm := by
    rw [diff_eq]
    exact div_nonneg num_nonneg hν_nn
  linarith

end GradBoundHypotheses

end NSBlwChain.BLW
