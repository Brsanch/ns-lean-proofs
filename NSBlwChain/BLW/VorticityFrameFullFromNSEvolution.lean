-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.BLW.VorticityFrameFromNSEvolution
import NSBlwChain.BLW.StepIIIFromNSEvolution

set_option diagnostics true
set_option diagnostics.threshold 100

/-!
# Full `VorticityLocalFrameData` wrapper from `NSEvolutionAxioms`

This file provides a "full" step-(iii) wrapper that takes
**only** the minimal taken hypotheses and derives the
step-(iii) identity internally via
`step_iii_identity_from_NSEvolution`.

The thin wrapper `VorticityLocalFrameData.ofNSEvolutionAxioms` in
`VorticityFrameFromNSEvolution.lean` requires the caller to supply
the step-(iii) identity `ν · laplaceOmega3 = growth - M · σ` as a
hypothesis.  The present full wrapper
`VorticityLocalFrameData.ofNSEvolutionAxioms_full` derives it from:

- `ax : NSEvolutionAxioms u ν T` (for the vorticity equation).
- `hmax : IsLocalMax |ω|² xStar` (for advection vanishing).
- `h_time_chain_rule`: `ω · ∂_tω = ∂_t(|ω|²/2)`.
- `h_envelope`: `∂_t(|ω|²/2)(xStar, t) = M · Ṁ` (Danskin form).
- `h_strain`: `ω · (ω·∇)u = M² · σ` at `xStar` (alignment).
- `h_laplace`: `ω · Δω = M · laplaceOmega3` at `xStar` (alignment).

These 4 taken hypotheses are each derivable at the vector-field layer
where the physical `∂_tω`, `(ω·∇)u`, `Δω` vectors are in scope;
they remain hypotheses here because the full derivation from
`NSEvolutionAxioms` would also require time-differentiability of `ω`
at `(xStar, t)` (from `NS_time_analyticity`) and explicit pointwise
evaluations of the velocity gradient.

## Usage

Replaces the thin wrapper at call sites where the caller has all of
the Danskin/alignment/time-chain hypotheses in hand but not the
composite step-(iii) identity.
-/

namespace NSBlwChain.BLW

/-- **Full `VorticityLocalFrameData` from `NSEvolutionAxioms`.**

    Takes minimal hypotheses (NSEv, argmax, 4 Danskin/alignment/time-chain
    identities, positivity) and assembles the step-(iii) bundle with
    the step-(iii) identity derived internally via
    `step_iii_identity_from_NSEvolution`. -/
noncomputable def VorticityLocalFrameData.ofNSEvolutionAxioms_full
    {u : VelocityField} {ν T : ℝ} (ax : NSEvolutionAxioms u ν T)
    (t : ℝ) (ht : 0 ≤ t) (htT : t < T)
    (xStar : Vec3)
    (hmax : IsLocalMax
      (fun y : Vec3 => Vec3.dot (vorticity u t y) (vorticity u t y))
      xStar)
    (M σ Mdot laplaceOmega3 : ℝ) (hM_pos : 0 < M)
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
    (h_laplace :
      Vec3.dot (vorticity u t xStar)
               (fun j => vectorLaplacian (vorticity u t) xStar j)
        = M * laplaceOmega3) :
    VorticityLocalFrameData := by
  -- Derive the step-(iii) identity from NSEv + the 4 taken hypotheses.
  have h_step_iii : ν * laplaceOmega3 = Mdot - M * σ :=
    step_iii_identity_from_NSEvolution ax ht htT xStar hmax
      M σ Mdot laplaceOmega3 hM_pos
      h_time_chain_rule h_envelope h_strain h_laplace
  -- Feed into the thin wrapper.
  exact VorticityLocalFrameData.ofNSEvolutionAxioms ax t ht htT xStar
    M σ Mdot laplaceOmega3 ax.nu_pos hM_pos h_step_iii

end NSBlwChain.BLW
