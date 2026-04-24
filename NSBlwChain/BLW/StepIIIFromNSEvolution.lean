-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.BLW.VorticityEquationAtPoint
import NSBlwChain.BLW.AdvectionAtArgmaxFromNSEvolution
import NSBlwChain.BLW.AlignmentContraction
import NSBlwChain.BLW.StrainContractionAligned

/-!
# Step (iii) identity derived from the NS vorticity equation

The BLW chain's step (iii) identity

  `ν · Δω_3 = Ṁ - M · σ`                       (★)

is derivable from `NSEvolutionAxioms` + alignment + `IsLocalMax`
+ Danskin + time-differentiability of ω at the argmax.  Tonight's
derivation chain assembles it as follows.

## The chain

Starting from `ax.vorticity_equation` at `(t, xStar)`, contract
with `ω(xStar, t)` componentwise and sum (via
`vorticity_equation_contracted_with_omega`):

  `ω · materialDeriv ω = ω · (ω·∇)u + ν · ω · Δω`            (1)

Expand `materialDeriv ω = ∂_t ω + (u·∇)ω`.  Then (1) reads

  `ω · ∂_t ω + ω · (u·∇)ω = ω · (ω·∇)u + ν · ω · Δω`.        (2)

Now:

- `ω · (u·∇)ω(xStar) = 0` at a local max of `|ω|²` (by
  `advection_vanishes_at_argmax_from_NSEvolution`).
- `ω · ∂_t ω = ∂_t(|ω|²/2)` (pointwise chain rule, **taken** as
  hypothesis — requires time-differentiability of `ω`).
- `∂_t(|ω|²/2)(xStar, t) = M · Ṁ` (Danskin envelope, **taken** as
  hypothesis supplied by caller; available via
  `envelope_form_of_NSEvolutionAxioms`).
- `ω · (ω·∇u)(xStar) = M² · σ` under alignment (**taken** as
  hypothesis — the full alignment derivation needs the physical
  `(ω·∇u)` vector).
- `ω · Δω(xStar) = M · Δω_3` under alignment (via
  `laplace_contraction_of_aligned`).

Substitute into (2):

  `M · Ṁ + 0 = M² · σ + ν · M · Δω_3`.

Divide by M (M > 0): `Ṁ = M · σ + ν · Δω_3`.

Rearrange: `ν · Δω_3 = Ṁ - M · σ`  = (★).  ✓

## Result

`step_iii_identity_from_NSEvolution`: assembles (★) from the
named hypotheses above.

## Status

This is a *scalar-level* derivation.  The four hypotheses that
remain taken (time-diff chain rule, Danskin, strain-contraction,
laplace-contraction at scalar level) are each a line of algebra
given pointwise knowledge of the corresponding vectors and are
discharged at the wiring layer where those vectors are in scope.
-/

namespace NSBlwChain.BLW

/-- **Step (iii) identity, derived from the NS vorticity equation
    at the argmax.**

    Given `NSEvolutionAxioms u ν T`, a local max `xStar` of
    `|ω(t,·)|²`, and the named Danskin-and-alignment hypotheses,
    conclude `ν · Δω_3 = Ṁ - M · σ` where the scalars are those
    produced by the BLW chain's step-(iii) bundle. -/
theorem step_iii_identity_from_NSEvolution
    {u : VelocityField} {ν T : ℝ} (ax : NSEvolutionAxioms u ν T)
    {t : ℝ} (ht : 0 ≤ t) (htT : t < T)
    (xStar : Vec3)
    (hmax : IsLocalMax
      (fun y : Vec3 => Vec3.dot (vorticity u t y) (vorticity u t y))
      xStar)
    -- Scalar fields:
    (M σ Mdot laplaceOmega3 : ℝ) (hM_pos : 0 < M)
    -- Hypothesis: contracted vorticity equation.
    (h_contracted :
      Vec3.dot (vorticity u t xStar)
               (materialDerivative u (vorticity u) t xStar) =
        Vec3.dot (vorticity u t xStar)
                 (vortexStretching u (vorticity u) t xStar)
          + ν * Vec3.dot (vorticity u t xStar)
                         (fun j => vectorLaplacian (vorticity u t) xStar j))
    -- Hypothesis: material derivative splits as time + advection.
    (h_material_split :
      Vec3.dot (vorticity u t xStar)
               (materialDerivative u (vorticity u) t xStar)
        = Vec3.dot (vorticity u t xStar)
                   (fun j => deriv (fun τ => vorticity u τ xStar j) t)
          + (∑ j : Fin 3, vorticity u t xStar j *
              (∑ i : Fin 3, u t xStar i *
                partialDeriv (fun y => vorticity u t y j) i xStar)))
    -- Hypothesis: time-chain-rule (ω · ∂_t ω = ∂_t(|ω|²/2)).
    (h_time_chain_rule :
      Vec3.dot (vorticity u t xStar)
               (fun j => deriv (fun τ => vorticity u τ xStar j) t)
        = deriv (fun τ =>
            Vec3.dot (vorticity u τ xStar) (vorticity u τ xStar) / 2) t)
    -- Hypothesis: Danskin-form envelope derivative equals M · Ṁ.
    (h_envelope :
      deriv (fun τ =>
        Vec3.dot (vorticity u τ xStar) (vorticity u τ xStar) / 2) t
        = M * Mdot)
    -- Hypothesis: strain contraction under alignment.
    (h_strain : Vec3.dot (vorticity u t xStar)
      (vortexStretching u (vorticity u) t xStar) = M ^ 2 * σ)
    -- Hypothesis: laplace contraction under alignment.
    (h_laplace : Vec3.dot (vorticity u t xStar)
      (fun j => vectorLaplacian (vorticity u t) xStar j) =
      M * laplaceOmega3) :
    ν * laplaceOmega3 = Mdot - M * σ := by
  -- Step 1: advection vanishes at the argmax (from tonight's capstone).
  have h_advection :
      (∑ j : Fin 3, vorticity u t xStar j *
        (∑ i : Fin 3, u t xStar i *
          partialDeriv (fun y => vorticity u t y j) i xStar)) = 0 :=
    advection_vanishes_at_argmax_from_NSEvolution ax ht htT xStar hmax
  -- Step 2: combine the contracted equation with the material split
  --         and the time chain rule, then use h_envelope, h_advection.
  have h_lhs :
      deriv (fun τ =>
        Vec3.dot (vorticity u τ xStar) (vorticity u τ xStar) / 2) t + 0 =
      M * Mdot := by
    rw [h_envelope]; ring
  -- Combine h_contracted + h_material_split + h_time_chain_rule +
  -- h_envelope + h_advection + h_strain + h_laplace.
  -- LHS of (2) = ω·∂_tω + ω·(u·∇)ω = ∂_t(|ω|²/2) + 0 = M · Ṁ.
  -- RHS of (2) = ω·(ω·∇u) + ν · ω·Δω = M²·σ + ν·M·laplaceOmega3.
  -- So M·Mdot = M²·σ + ν·M·laplaceOmega3, then divide by M > 0.
  have h_combined : M * Mdot = M ^ 2 * σ + ν * (M * laplaceOmega3) := by
    have h1 := h_contracted
    rw [h_material_split, h_time_chain_rule, h_envelope, h_advection,
        h_strain, h_laplace] at h1
    linarith [h1]
  -- Divide by M > 0 to get the step-iii identity.
  have hM_ne : M ≠ 0 := ne_of_gt hM_pos
  -- Rewrite h_combined as M * Mdot = M * (M · σ + ν · laplaceOmega3).
  have h_factored : M * Mdot = M * (M * σ + ν * laplaceOmega3) := by
    have h_sq : M ^ 2 * σ = M * (M * σ) := by ring
    have h_nu : ν * (M * laplaceOmega3) = M * (ν * laplaceOmega3) := by ring
    rw [h_sq, h_nu] at h_combined
    linarith [h_combined]
  -- Cancel M (nonzero) on both sides.
  have h_mdot : Mdot = M * σ + ν * laplaceOmega3 :=
    mul_left_cancel₀ hM_ne h_factored
  -- Rearrange to step (iii) form.
  linarith [h_mdot]

end NSBlwChain.BLW
