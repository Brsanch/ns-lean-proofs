-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Setup.VectorFields

/-!
# Navier–Stokes hypothesis bundle

This file defines the `NSEvolutionAxioms` bundle: the package of
structural hypotheses that any "3D NS solution on a finite time
interval" is assumed to satisfy throughout the BLW-gradient chain.

It is the analog of `SqgEvolutionAxioms_strong` from the sister
project `sqg-lean-proofs`.  Like that bundle, it is *not* claiming
existence of solutions — it only fixes notation and structural
identities so that the downstream BLW-chain arguments can be stated
without carrying a long list of prerequisites in every signature.

## Contents

* `NSBlwChain.VelocityField` — time-dependent vector field
  `ℝ → Vec3 → Vec3`.
* `NSBlwChain.Vorticity`     — shorthand for the curl of a velocity field.
* `NSBlwChain.NSEvolutionAxioms` — the bundle (smoothness, divergence-free,
  zero-mean, vorticity equation, evolution on `[0, T)`).

## Structural caveats

1. We state the hypotheses on $\mathbb{R}^3$, *not* on the torus; the
   torus version is obtained by imposing additional periodicity
   hypotheses in a downstream file (`Torus/*`).
2. The vorticity equation is stated pointwise.  Weak-form identities
   (Leray-style weak solutions) are **not** part of this bundle — the
   BLW-chain arguments are run on the smooth-solution side, matching
   the paper's scope.
3. Regularity in time is asserted only *up to* the blowup time `T`;
   the full Kato-type analyticity statement is a *separate* classical
   axiom (`NS_time_analyticity` in `ClassicalAxioms.lean`), not part
   of this bundle.
-/

namespace NSBlwChain

/-- Time-dependent vector field on $\mathbb{R}^3$.

    We index time by `ℝ` for simplicity; when we need to specialize to
    a finite-time interval `[0, T)` we do so via the evolution-axioms
    bundle, which records the interval explicitly. -/
abbrev VelocityField : Type := ℝ → Vec3 → Vec3

/-- Vorticity of a velocity field, `ω = ∇ × u`. -/
noncomputable def vorticity (u : VelocityField) (t : ℝ) (x : Vec3) : Vec3 :=
  curl (u t) x

/-- Material (convective) derivative `D_t f = ∂_t f + u · ∇ f` applied
    componentwise to a time-dependent vector field `V`. -/
noncomputable def materialDerivative
    (u : VelocityField) (V : ℝ → Vec3 → Vec3) (t : ℝ) (x : Vec3) : Vec3 :=
  fun j =>
    -- ∂_t Vⱼ(t, x) + Σᵢ uᵢ(t, x) · ∂ᵢ Vⱼ(t, x)
    (deriv (fun τ => V τ x j) t)
      + ∑ i : Fin 3, u t x i * partialDeriv (fun y => V t y j) i x

/-- Vortex-stretching term `(ω · ∇) u`, pointwise. -/
noncomputable def vortexStretching
    (u : VelocityField) (ω : ℝ → Vec3 → Vec3) (t : ℝ) (x : Vec3) : Vec3 :=
  fun j =>
    ∑ i : Fin 3, ω t x i * partialDeriv (fun y => u t y j) i x

/-- **NS evolution-axioms bundle.**

    A packaging of the structural hypotheses that all BLW-chain
    arguments consume.  Given a velocity field `u`, viscosity `ν > 0`,
    and blowup time `T > 0`, the bundle asserts:

    1. *Smoothness.* `u` is $C^\infty$ in space at every `t ∈ [0, T)`.
    2. *Divergence-free.* `div (u t) x = 0` for every `t ∈ [0, T)`, `x`.
    3. *Zero-mean (optional).* If the solution is on the torus, we
       also require `u` to have zero spatial mean; on $\mathbb{R}^3$
       we instead impose a decay hypothesis.  Since this file is the
       $\mathbb{R}^3$ version, we omit zero-mean and defer it to
       the torus overlay.
    4. *Vorticity equation.* Pointwise on `[0, T) × \mathbb{R}^3`:
       `D_t ω = (ω · ∇) u + ν Δ ω`.
    5. *Time-continuity / `C¹`-in-`t`.* The map `t ↦ u t x` is
       continuously differentiable for every fixed `x` on `[0, T)`.

    Only the *structural* content is asserted; there is no existence
    claim.  Downstream arguments consume the bundle by destructuring. -/
structure NSEvolutionAxioms
    (u : VelocityField) (ν : ℝ) (T : ℝ) : Prop where
  /-- Positive viscosity. -/
  nu_pos : 0 < ν
  /-- Positive blowup time. -/
  T_pos  : 0 < T
  /-- Smoothness in space at every time in `[0, T)`. -/
  smooth_in_space :
    ∀ t : ℝ, 0 ≤ t → t < T → ContDiff ℝ ∞ (u t)
  /-- Divergence-free. -/
  div_free :
    ∀ t : ℝ, 0 ≤ t → t < T → ∀ x : Vec3, divergence (u t) x = 0
  /-- Vorticity equation (pointwise).  Here `ω = ∇ × u`. -/
  vorticity_equation :
    ∀ t : ℝ, 0 ≤ t → t < T → ∀ x : Vec3,
      materialDerivative u (vorticity u) t x
        = fun j =>
            vortexStretching u (vorticity u) t x j
              + ν * vectorLaplacian (vorticity u t) x j
  /-- Continuity of `u` in time (pointwise). -/
  time_cont :
    ∀ x : Vec3, ContinuousOn (fun t : ℝ => u t x) (Set.Ico 0 T)

/-- Shorthand: the vorticity of a bundled NS solution. -/
noncomputable abbrev NSEvolutionAxioms.omega
    {u : VelocityField} {ν T : ℝ} (_ : NSEvolutionAxioms u ν T) :
    ℝ → Vec3 → Vec3 := vorticity u

end NSBlwChain
