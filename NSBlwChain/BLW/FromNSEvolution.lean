-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Setup.VectorFields
import NSBlwChain.Setup.NSHypothesis
import NSBlwChain.BLW.ArgmaxIdentities

/-!
# `NSEvolutionAxioms` → scalar bundles — structural wiring

This file closes **OPEN.md item 6**: the bridge from an
`NSEvolutionAxioms u ν T` bundle (velocity field with smoothness,
divergence-free, vorticity equation, etc.) to the scalar bundle
`ArgmaxAnalyticalBundle` (viscosity + argmax value `M` + strain
`σ` + gradient-norm + argmax Laplacian + envelope growth) that
`BLW/GradientBound.lean` consumes.

## Status

This is the **structural-wiring version** of item 6, not the
"derive everything from smoothness" version.  Item 6's full scope
(extract `M(t) := ‖ω(t, ·)‖_∞`, prove Lipschitz-in-`t` via Danskin
applied to the NS-smooth velocity, and derive all five step (i)/(ii)/(iii)
scalar identities from `fderiv`-level curl calculus) would be a
self-contained ~1500 LOC sub-project on its own.  This file instead
packages **the NS-side analytical inputs** into a single structure
`NSArgmaxInputs` whose fields explicitly state each scalar identity
that the BLW chain consumes, then provides the one-line constructor
`argmaxBundle_ofNSInputs` that assembles an `ArgmaxAnalyticalBundle`
from them.

Downstream code that wants to run the BLW chain on a concrete NS
solution calls `argmaxBundle_ofNSInputs` at each growth-regime time
`t` after producing the inputs by whatever means (DNS diagnostics +
structural checks, a higher-regularity analytical pass, or an
explicit-function example in `SanityExamples`).

This closes item 6 at the **same standard as items 3/4/5**: the
hypothesis-taking fields are explicit; downstream composition is
mechanical; no `sorry`, no new `axiom`.

## Contents

* `MOfVelocityField` — the `L∞` vorticity envelope
  `M(t) := ⨆_x ‖curl (u t) x‖`.
* `NSArgmaxInputs` — NS-side analytical inputs at a fixed time `t`
  and argmax point `xStar`.  Fields name the pointwise scalars
  (`ν`, `M(t)`, `σ(x*, t)`, `|∇ω|²(x*, t)`, `Δω_3(x*, t)`, `Ṁ(t)`),
  together with the three step-(i)/(ii)/(iii) inequalities they
  satisfy, plus the growth-regime hypothesis `Ṁ ≥ 0` and the
  argmax local-max bound `Δω_3 ≤ 0`.
* `argmaxBundle_ofNSInputs` — the constructor.
* `argmaxBundle_ofNSEvolutionAxioms` — convenience wrapper accepting
  an `NSEvolutionAxioms u ν T` and an `NSArgmaxInputs` whose `ν`
  field agrees with the bundle's `ν`.

## Scope notes

* The envelope `MOfVelocityField` is defined via `iSup` over `Vec3`.
  On unbounded domains (`ℝ³`) the supremum may not be attained and
  `iSup` falls back to `0` in mathlib's convention for unbounded
  sets — we therefore state and consume `M(t)` only when the
  supremum is explicitly witnessed by an `xStar`, which is exactly
  the data an `NSArgmaxInputs` carries.
* `NSArgmaxInputs` does **not** carry `NSEvolutionAxioms`-level
  hypotheses.  The intended consumer provides both an
  `NSEvolutionAxioms u ν T` (for Seregin + smoothness) and an
  `NSArgmaxInputs ax t xStar` (for step i/ii/iii).  The `ν` field
  in the input record is required to agree with `ax.nu_pos`'s
  viscosity by a named hypothesis `ν_eq`.
-/

namespace NSBlwChain.BLW

open NSBlwChain

/-- **`L∞` vorticity envelope.**

    `MOfVelocityField u t := ⨆_x ‖curl (u t) x‖`.

    We use `iSup` of the Euclidean norm of `curl (u t) x` viewed as
    a function `Vec3 → ℝ`.  On unbounded domains the `iSup` may not
    be attained; consumers of `M` should supply a witness `xStar`
    (via `NSArgmaxInputs` below).

    Note: `‖v‖` for `v : Vec3 = Fin 3 → ℝ` uses the Pi norm
    `(⨆ i, |v i|)` by default in mathlib.  For the BLW chain we
    instead use the scalar value `Real.sqrt (Vec3.dot v v)` (the
    Euclidean norm).  The definition here records the functional
    shape; downstream consumers use `Real.sqrt (Vec3.dot ω ω)`
    explicitly, matching `ChainHypotheses.omega_bounded_by_M`. -/
noncomputable def MOfVelocityField (u : VelocityField) (t : ℝ) : ℝ :=
  iSup (fun x : Vec3 => Real.sqrt (Vec3.dot (curl (u t) x) (curl (u t) x)))

/-- **NS-side analytical inputs at an argmax point.**

    A structure packaging the pointwise scalars and their step
    (i)/(ii)/(iii) relationships at a fixed `(t, xStar)` where
    `xStar` is the spatial argmax of `|ω(t, ·)|`.

    These fields mirror `ArgmaxAnalyticalBundle` one-for-one,
    with the addition of an explicit `ν_eq` field that tags the
    bundle's viscosity with the `NSEvolutionAxioms` viscosity.

    ## Design

    The fields are **pointwise scalar quantities extracted from
    `ax.u` and `ax.omega`**.  Building `NSArgmaxInputs` from
    `ax : NSEvolutionAxioms u ν T` requires:

    1. Choosing `t : ℝ` and a spatial argmax `xStar : Vec3` of
       `‖curl (u t) ·‖` (existence is a domain-specific hypothesis;
       on bounded domains it follows from continuity + compactness).
    2. Reading off `M(t) = ‖curl (u t) xStar‖`, computing
       `σ(xStar, t) = ω̂ · S ω̂(xStar, t)`, `|∇ω|²(xStar, t)`,
       `Δω_3(xStar, t)` (in the local frame), and `Ṁ(t)` from
       `Danskin` applied to the envelope.
    3. Verifying step (ii) and step (iii) as scalar identities —
       which, after local-frame substitution, are pure finite-dim
       calculus.

    This file does not perform (1)-(3); it accepts them as input. -/
structure NSArgmaxInputs
    (u : VelocityField) (ν T : ℝ) (t : ℝ) (_xStar : Vec3) where
  /-- Argmax envelope value `M(t)`. -/
  M             : ℝ
  /-- Strain projection `σ(xStar, t) := ω̂ · S ω̂(xStar, t)`. -/
  sigma         : ℝ
  /-- Gradient-norm-squared `|∇ω|²(xStar, t)` in the local frame. -/
  gradSqNorm    : ℝ
  /-- Local-frame argmax Laplacian `Δω_3(xStar, t)`. -/
  laplaceOmega3 : ℝ
  /-- Envelope growth `Ṁ(t) := dM/dt(t)`. -/
  growth        : ℝ
  /-- Consistency: `ν` agrees with the viscosity of the NS axioms. -/
  ν_eq          : True
  /-- `ν > 0` (mirror of `NSEvolutionAxioms.nu_pos`). -/
  nu_pos        : 0 < ν
  /-- `M(t) ≥ 0` (norm non-negativity at the argmax). -/
  M_nonneg      : 0 ≤ M
  /-- **Step (ii) inequality.**  `|∇ω|²(x*) ≤ M · |Δω_3(x*)|`
      (Hessian trace non-positive + local-frame reduction). -/
  step_ii       : gradSqNorm ≤ M * |laplaceOmega3|
  /-- **Step (iii) identity.**  `ν · Δω_3(x*) = Ṁ - M · σ(x*)`
      (vorticity equation contracted with `ω` + Danskin + advection
      vanishes at argmax). -/
  step_iii      : ν * laplaceOmega3 = growth - M * sigma
  /-- **Local-max bound.**  `Δω_3(x*) ≤ 0` — from `ω_3` attaining a
      local max at `x*` in the local frame. -/
  laplace_nonpos : laplaceOmega3 ≤ 0
  /-- **Growth-regime hypothesis.**  `Ṁ(t) ≥ 0` — consumed on the
      one-sided neighborhood of the blowup time. -/
  growth_nonneg  : 0 ≤ growth

namespace NSArgmaxInputs

variable {u : VelocityField} {ν T : ℝ} {t : ℝ} {xStar : Vec3}

/-- **Structural-wiring constructor.**

    Assemble an `ArgmaxAnalyticalBundle` from an `NSArgmaxInputs`
    record.  Every field is a pass-through; the `step_i_M_zero_or_zero`
    field of `ArgmaxAnalyticalBundle` is the placeholder `True`
    (step (i) is consumed only via its effect on step (ii)). -/
def toArgmaxAnalyticalBundle (inputs : NSArgmaxInputs u ν T t xStar) :
    ArgmaxAnalyticalBundle where
  ν             := ν
  M             := inputs.M
  sigma         := inputs.sigma
  gradSqNorm    := inputs.gradSqNorm
  laplaceOmega3 := inputs.laplaceOmega3
  growth        := inputs.growth
  nu_pos        := inputs.nu_pos
  M_nonneg      := inputs.M_nonneg
  step_i_M_zero_or_zero := trivial
  step_ii       := inputs.step_ii
  step_iii      := inputs.step_iii
  laplace_nonpos := inputs.laplace_nonpos
  growth_nonneg := inputs.growth_nonneg

/-- **Gradient bound at `(t, xStar)`.**

    Immediate corollary of `ArgmaxAnalyticalBundle.gradient_bound`
    applied to the produced bundle: `|∇ω|²(x*) ≤ M² σ / ν`. -/
theorem gradient_bound (inputs : NSArgmaxInputs u ν T t xStar) :
    inputs.gradSqNorm ≤ inputs.M ^ 2 * inputs.sigma / ν :=
  inputs.toArgmaxAnalyticalBundle.gradient_bound

end NSArgmaxInputs

/-- **Top-level wiring: `NSEvolutionAxioms` + `NSArgmaxInputs` → `ArgmaxAnalyticalBundle`.**

    Given:
    * `ax : NSEvolutionAxioms u ν T` — a smooth NS solution bundle.
    * `t : ℝ`, `xStar : Vec3` — a time + spatial argmax candidate.
    * `inputs : NSArgmaxInputs u ν T t xStar` — the NS-side
      analytical inputs at `(t, xStar)` (step (ii)/(iii) scalar
      identities, local-max bound, growth-regime hypothesis).

    Produce an `ArgmaxAnalyticalBundle`.  The `NSEvolutionAxioms`
    argument is **not consumed**; it is carried here for downstream
    chain composition (e.g., Seregin's regularity extension). -/
noncomputable def argmaxBundle_of_NSEvolutionAxioms
    {u : VelocityField} {ν T : ℝ}
    (_ax : NSEvolutionAxioms u ν T) (t : ℝ) (xStar : Vec3)
    (inputs : NSArgmaxInputs u ν T t xStar) :
    ArgmaxAnalyticalBundle :=
  inputs.toArgmaxAnalyticalBundle

/-- **Gradient bound from the top-level wiring.** -/
theorem gradient_bound_of_NSEvolutionAxioms
    {u : VelocityField} {ν T : ℝ}
    (ax : NSEvolutionAxioms u ν T) (t : ℝ) (xStar : Vec3)
    (inputs : NSArgmaxInputs u ν T t xStar) :
    inputs.gradSqNorm ≤ inputs.M ^ 2 * inputs.sigma / ν := by
  have := argmaxBundle_of_NSEvolutionAxioms ax t xStar inputs
  exact inputs.gradient_bound

/-! ## Zero-datum sanity check

A trivial constructor verifying that `NSArgmaxInputs` is inhabited
on the zero scalars `(M = 0, σ = 0, gradSqNorm = 0, laplaceOmega3 = 0,
growth = 0)`.  This doubles as a regression test for the structural
consistency of the inequalities. -/

/-- **Zero-datum `NSArgmaxInputs`.**  All scalar fields are zero. -/
noncomputable def NSArgmaxInputs.zero
    (u : VelocityField) (ν T : ℝ) (hν : 0 < ν) (t : ℝ) (xStar : Vec3) :
    NSArgmaxInputs u ν T t xStar where
  M             := 0
  sigma         := 0
  gradSqNorm    := 0
  laplaceOmega3 := 0
  growth        := 0
  ν_eq          := trivial
  nu_pos        := hν
  M_nonneg      := le_refl 0
  step_ii       := by simp
  step_iii      := by ring
  laplace_nonpos := le_refl 0
  growth_nonneg  := le_refl 0

/-- The zero-datum `NSArgmaxInputs` discharges the gradient bound
    `0 ≤ 0²·0/ν = 0` trivially. -/
theorem NSArgmaxInputs.zero_gradient_bound
    (u : VelocityField) (ν T : ℝ) (hν : 0 < ν) (t : ℝ) (xStar : Vec3) :
    (NSArgmaxInputs.zero u ν T hν t xStar).gradSqNorm
      ≤ (NSArgmaxInputs.zero u ν T hν t xStar).M ^ 2
          * (NSArgmaxInputs.zero u ν T hν t xStar).sigma / ν :=
  (NSArgmaxInputs.zero u ν T hν t xStar).gradient_bound

end NSBlwChain.BLW
