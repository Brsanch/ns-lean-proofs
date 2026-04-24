-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.BLW.ArgmaxBundleFromNSEvolution
import NSBlwChain.BLW.StepIIIFromNSEvolution

/-!
# Gradient bound with step (iii) identity derived from `NSEvolutionAxioms`

Capstone theorem composing tonight's two big pieces:

1. `step_iii_identity_from_NSEvolution` (in `StepIIIFromNSEvolution.lean`)
   — derives `ν · Δω_3 = Ṁ - M · σ` from NSEv + IsLocalMax + 4 physical
   identities (time-chain-rule, Danskin envelope, strain alignment,
   laplace alignment).
2. `ArgmaxAnalyticalBundle.ofNSEvolutionAxioms` +
   `gradient_bound_of_NSEvolutionAxioms_via_scalars` (in
   `ArgmaxBundleFromNSEvolution.lean`) — grand-compose producing the
   gradient bound `gradSqNorm ≤ M² · σ / ν` from an
   `ArgmaxAnalyticalBundle`.

The step (iii) identity was a hypothesis of L9's grand-compose; here
we derive it.

## Result

`gradient_bound_of_NSEvolutionAxioms_step_iii_derived`: takes NSEv
+ argmax + step-(ii) inequality (still taken — its derivation requires
full Hessian composition) + 4 physical identities, produces the
gradient bound `gradSqNorm ≤ M² · σ / ν`.

## Remaining taken hypotheses

- `h_step_ii : gradSqNorm ≤ M · |laplaceOmega3|` — the Hessian bound.
  Deriving from L3 + L6 + Hessian expansion is the next natural
  tightening (requires `HessianLocalFrameData` instead of just
  `ScalarLocalMaxSecondDeriv`).
- Four physical identities (time-chain-rule, envelope, strain, laplace)
  — each a line of vector-field algebra given the pointwise vectors.
-/

namespace NSBlwChain.BLW

/-- **Gradient bound with step-(iii) identity derived.**

    Composition: `step_iii_identity_from_NSEvolution` +
    `gradient_bound_of_NSEvolutionAxioms_via_scalars`.

    Reduces the L9 grand-compose's hypothesis count by one (drops the
    `h_step_iii` hypothesis in favor of NSEv + argmax + 4 physical
    identities).  The step-(ii) inequality remains taken as a
    hypothesis (next natural tightening). -/
theorem gradient_bound_of_NSEvolutionAxioms_step_iii_derived
    {u : VelocityField} {ν T : ℝ} (ax : NSEvolutionAxioms u ν T)
    (t : ℝ) (ht : 0 ≤ t) (htT : t < T)
    (xStar : Vec3)
    (hmax : IsLocalMax
      (fun y : Vec3 => Vec3.dot (vorticity u t y) (vorticity u t y))
      xStar)
    (M σ Mdot gradSqNorm laplaceOmega3 : ℝ)
    (hM_pos : 0 < M)
    (h_step_ii : gradSqNorm ≤ M * |laplaceOmega3|)
    -- Step (iii) physical identities (derived step_iii internally):
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
        = M * laplaceOmega3)
    (h_laplace_nonpos : laplaceOmega3 ≤ 0)
    (h_growth_nonneg : 0 ≤ Mdot) :
    gradSqNorm ≤ M ^ 2 * σ / ν := by
  -- Derive the step-(iii) identity via tonight's capstone.
  have h_step_iii : ν * laplaceOmega3 = Mdot - M * σ :=
    step_iii_identity_from_NSEvolution ax ht htT xStar hmax
      M σ Mdot laplaceOmega3 hM_pos
      h_time_chain_rule h_envelope h_strain h_laplace
  -- Feed into L9 grand-compose.
  exact gradient_bound_of_NSEvolutionAxioms_via_scalars ax t ht htT xStar
    M σ Mdot gradSqNorm laplaceOmega3 ax.nu_pos (le_of_lt hM_pos)
    h_step_ii h_step_iii h_laplace_nonpos h_growth_nonneg

end NSBlwChain.BLW
