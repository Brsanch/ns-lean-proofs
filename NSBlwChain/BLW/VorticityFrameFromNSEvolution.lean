-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Setup.NSHypothesis
import NSBlwChain.BLW.VorticityAtArgmaxFromFrame
import NSBlwChain.BLW.VorticityEquationAtPoint

/-!
# `VorticityLocalFrameData` from `NSEvolutionAxioms`

Step (iii) of the BLW gradient chain's analytical inputs at the
argmax: the **vorticity-equation identity** `ν·Δω_3 = Ṁ - M·σ`
(rearrangement of `Ṁ = M·σ + ν·Δω_3` from the NS vorticity equation
contracted with `ω` at the argmax, after using advection-vanishes-
at-argmax and Danskin-envelope-for-|ω|²).

This file provides the step (iii) analog of
`LocalFrameDerivativeData.ofNSEvolutionAxioms` (step (i)) and
`ScalarLocalMaxSecondDeriv.ofNSEvolutionAxioms` (step (ii)):

`VorticityLocalFrameData.ofNSEvolutionAxioms` — given
`ax : NSEvolutionAxioms u ν T` plus scalar inputs `(M, σ, growth, Δω₃)`
satisfying the step-(iii) identity `ν·Δω_3 = growth - M·σ`, produce
the full `VorticityLocalFrameData` bundle with all 5 hypothesis
fields discharged by pure algebra.

## Scope

This is a **thin** wrapper, matching the L3 / L6 patterns.  It takes
the step-(iii) identity as a caller-supplied hypothesis rather than
deriving it from `ax.vorticity_equation_contracted_with_omega`.  The
full derivation requires additionally:

- time-differentiability of `ω` at `(xStar, t)` (from `NS_time_analyticity`
  axiom or a caller-supplied chain-rule hypothesis),
- advection-vanishes-at-argmax (from `AdvectionVanishes.lean`),
- Danskin envelope for `|ω|²/2` (from `EnvelopeIdentity.lean` +
  `ChainRuleMSquared.lean`),
- local-frame alignment `ω(xStar) = M·ê₂` (a choice of coordinate
  frame, not a derivable fact).

A follow-up commit can assemble these into an `ofNSEvolutionAxioms_full`
constructor that takes only `ax`, alignment, and argmax existence.
The present thin version matches the step (i)/(ii) API for uniformity.
-/

namespace NSBlwChain.BLW

/-- **Step (iii) bundle from NSEvolutionAxioms (thin wrapper).**

    Given a smooth NS solution bundle `ax`, a time `t ∈ [0, T)`, and
    scalar inputs `M, σ, growth, Δω_3` at `(t, xStar)` satisfying the
    step-(iii) identity `ν·Δω_3 = growth - M·σ`, produce a
    `VorticityLocalFrameData` bundle.

    The 5 hypothesis fields of `VorticityLocalFrameData` are
    discharged by algebra:
    - `strain_form`, `laplace_form`, `advection_vanishes`, `envelope_form`
      hold by definition (each is `rfl` given the data choices below).
    - `vorticity_eq_contracted` follows from the step-(iii) identity
      via `nlinarith`. -/
noncomputable def VorticityLocalFrameData.ofNSEvolutionAxioms
    {u : VelocityField} {ν T : ℝ}
    (_ax : NSEvolutionAxioms u ν T)
    (_t : ℝ) (_ht : 0 ≤ _t) (_htT : _t < T)
    (_xStar : Vec3) (M σ growth laplaceOmega3 : ℝ)
    (hν : 0 < ν) (hM : 0 < M)
    (step_iii : ν * laplaceOmega3 = growth - M * σ) :
    VorticityLocalFrameData where
  ν := ν
  M := M
  sigma := σ
  growth := growth
  laplaceOmega3 := laplaceOmega3
  omega_S_omega := M ^ 2 * σ
  omega_laplace_omega := M * laplaceOmega3
  time_deriv_half_sqN := M * growth
  advectionAtArgmax := 0
  nu_pos := hν
  M_pos := hM
  vorticity_eq_contracted := by
    -- Goal: M * growth = M^2 * σ - 0 + ν * (M * laplaceOmega3)
    -- From step_iii: ν * laplaceOmega3 = growth - M * σ
    -- Multiply by M: M * ν * laplaceOmega3 = M * growth - M^2 * σ
    -- Rearrange: M * growth = M^2 * σ + M * (ν * laplaceOmega3)
    --          = M^2 * σ + ν * (M * laplaceOmega3)
    -- Use nlinarith with step_iii as a hint.
    nlinarith [step_iii, hM, sq_nonneg M]
  advection_vanishes := rfl
  strain_form := rfl
  laplace_form := rfl
  envelope_form := rfl

end NSBlwChain.BLW
