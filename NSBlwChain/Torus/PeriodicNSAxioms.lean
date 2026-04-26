-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Setup.NSHypothesis

set_option diagnostics true
set_option diagnostics.threshold 100

/-!
# Periodic NS axioms (torus overlay)

Adds periodicity hypotheses on top of `NSEvolutionAxioms` to give the
torus version `NSEvolutionAxiomsPeriodic`.  The bundle is a thin
extension that pairs an ℝ³ NS axiom bundle with:

* a positive period `L > 0`,
* spatial periodicity `u(t, x + L · e_i) = u(t, x)` for every
  coordinate direction `i ∈ Fin 3`,
* zero spatial mean of `u` over the fundamental cell `[0, L]³`.

The downstream payoff: spatial argmax existence on the fundamental
cell follows from compactness alone, without the ℝ³-specific
`DecayAtInfinity` hypothesis.

## Main definitions

* `IsPeriodic3D` — periodicity predicate for a function
  `Vec3 → α` with period `L`.
* `NSEvolutionAxiomsPeriodic` — torus bundle extending the ℝ³ one.
-/

namespace NSBlwChain

open scoped BigOperators

/-- **Coordinate-direction periodicity for `Vec3 → α` functions.**

    `IsPeriodic3D L f` asserts `f (x + L · e_i) = f x` for every
    coordinate axis `i ∈ Fin 3`, where `e_i` is the standard basis
    vector that adds `L` to coordinate `i` and leaves the other two
    fixed. -/
def IsPeriodic3D {α : Type*} (L : ℝ) (f : Vec3 → α) : Prop :=
  ∀ (i : Fin 3) (x : Vec3),
    f (Function.update x i (x i + L)) = f x

/-- A constant function is `IsPeriodic3D` for every `L`. -/
lemma IsPeriodic3D.const {α : Type*} (L : ℝ) (a : α) :
    IsPeriodic3D L (fun _ : Vec3 => a) :=
  fun _ _ => rfl

/-- **Time-dependent periodicity.**  Lifts `IsPeriodic3D` along the
    time coordinate. -/
def IsPeriodic3DTime {α : Type*} (L : ℝ)
    (u : ℝ → Vec3 → α) : Prop :=
  ∀ t : ℝ, IsPeriodic3D L (u t)

/-- **Periodic NS evolution-axioms bundle.**

    A torus-overlay extension of `NSEvolutionAxioms`.  Given the
    underlying ℝ³ bundle, the periodic version pins:

    * `L > 0`            — the spatial period,
    * `u_periodic`       — spatial periodicity of the velocity field,
    * `vorticity_periodic` — derived periodicity of the vorticity
       (recorded for ergonomic downstream use; provable from
       `u_periodic` + the curl operator's locality, but kept as a
       bundle field to avoid re-deriving in every consumer),
    * `zero_mean`        — `∫_{[0,L]³} u t = 0` (zero spatial mean).

    Periodicity is stated as `f(x + L·eᵢ) = f(x)` per coordinate
    direction; the standard `Function.update`-based `e_i` form is
    used to avoid a separate `Pi.basisFun` setup. -/
structure NSEvolutionAxiomsPeriodic
    (u : VelocityField) (ν T L : ℝ) : Prop where
  /-- Underlying ℝ³ NS axioms. -/
  base : NSEvolutionAxioms u ν T
  /-- Positive spatial period. -/
  L_pos : 0 < L
  /-- Spatial periodicity of the velocity field, at each time. -/
  u_periodic :
    ∀ t : ℝ, 0 ≤ t → t < T → IsPeriodic3D L (u t)
  /-- Spatial periodicity of the vorticity (= curl of u), at each
      time.  Provable from `u_periodic` and translation-invariance
      of `curl`; bundled here for ergonomics. -/
  vorticity_periodic :
    ∀ t : ℝ, 0 ≤ t → t < T → IsPeriodic3D L (vorticity u t)
  /-- **Zero spatial mean** of `u` over the fundamental cell.
      Stated coordinate-wise: each component integrates to 0 over
      `[0, L]³`.  This rules out the constant-velocity drift mode
      that would otherwise destroy the energy/enstrophy balance
      on the torus. -/
  zero_mean :
    ∀ t : ℝ, 0 ≤ t → t < T → ∀ k : Fin 3,
      (∫ x in Set.Icc (0 : Vec3) (fun _ => L), u t x k) = 0

/-- The underlying ℝ³ axioms project trivially out. -/
lemma NSEvolutionAxiomsPeriodic.toBase
    {u : VelocityField} {ν T L : ℝ}
    (P : NSEvolutionAxiomsPeriodic u ν T L) :
    NSEvolutionAxioms u ν T := P.base

end NSBlwChain
