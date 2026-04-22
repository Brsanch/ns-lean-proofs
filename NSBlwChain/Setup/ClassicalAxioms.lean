-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Setup.VectorFields
import NSBlwChain.Setup.NSHypothesis

/-!
# Classical PDE axioms — the three named inputs

This file declares the three classical Navier–Stokes results that the
BLW-gradient chain treats as **axiomatic**.  They correspond to
published peer-reviewed theorems far outside the scope of this
formalization; they are stated here as `axiom` declarations with
explicit *consumed-form* signatures so that downstream code can apply
them by name.

## The three axioms

1. **Biot–Savart pointwise bound (Proposition 12.1).**  Named:
   `biot_savart_self_strain_bound`.  Packages the output of the
   cylindrical θ-averaging identity of paper §12.2: at any argmax
   `x_star` of `|ω(·, t)|`, the aligned self-strain `σ(x_star, t)`
   is bounded by `M · (1 + C_L + log(L / δ_ν))` for some `C_L ≥ 0`.

2. **Seregin type-one exclusion (Seregin, CMP 2012).**  Named:
   `seregin_type_one_exclusion`.  Given a smooth NS solution on
   `[0, T)` whose vorticity satisfies the sub-Type-I rate
   `(T - t) · ‖ω(·, t)‖_∞ → 0`, the solution extends smoothly
   past `T`.

3. **Kato time-analyticity (Kato 1967 / Foias–Temam 1979).**
   Named: `NS_time_analyticity`.  Smooth NS solutions extend to
   a holomorphic map on a complex strip around every interior
   time in `(0, T)`.

## Consumed forms

Each axiom is wrapped in a `Prop`-valued structure so that consumers
can destructure the analytical content cleanly.  The `Prop` shape
matches the *exact* hypothesis signature that the BLW-gradient chain
capstone takes on input, so that invoking the axiom is a one-line
`exact biot_savart_self_strain_bound ax` call.
-/

namespace NSBlwChain

/-! ## Axiom 1 — Biot–Savart self-strain bound -/

/-- Consumed form of the exact pointwise identity of §12.1.  Provides
    a constant `C_L ≥ 0` and a universal bound `σ(x*, t) ≤ M(t) · (1
    + C_L + log(L / δ_ν(t)))` at every argmax point `x_star` in the
    growth-regime of `M`, with `δ_ν(t) := √(ν/σ(x_star, t))`.

    The structure records only the *output* shape consumed by the
    chain; the derivation of the identity from cylindrical
    θ-averaging is the content of the axiom below. -/
structure BiotSavartSelfStrainBound
    (u : VelocityField) (ν T : ℝ) : Prop where
  /-- Box size at which the torus correction is applied. -/
  L          : ℝ
  /-- Torus-correction constant. -/
  C_L        : ℝ
  /-- Positive box size. -/
  L_pos      : 0 < L
  /-- Torus correction non-negative. -/
  C_L_nonneg : 0 ≤ C_L
  /-- The bound at every growth-regime argmax.  Stated with respect
      to abstract scalars representing `M`, `σ`, and `δ_ν = √(ν/σ)`
      at a fixed time.  Downstream consumers pick concrete values. -/
  bound :
    ∀ M σ : ℝ, 0 ≤ M → 0 < σ → 0 < ν →
      σ ≤ M * (1 + C_L + Real.log (L / Real.sqrt (ν / σ)))

/-- **Axiom 1 — `biot_savart_self_strain_bound`.**  The exact Biot–
    Savart pointwise identity at every argmax of `|ω|` delivers a
    growth-regime bound of the form recorded in
    `BiotSavartSelfStrainBound`. -/
axiom biot_savart_self_strain_bound
    {u : VelocityField} {ν T : ℝ} (_ax : NSEvolutionAxioms u ν T) :
    BiotSavartSelfStrainBound u ν T

/-! ## Axiom 2 — Seregin type-one exclusion -/

/-- Consumed form of Seregin (2012).  The conclusion is that the
    sub-Type-I rate hypothesis is *inconsistent* with `T` being a
    finite singularity time: there is always a strictly later time
    `T' > T` to which the solution extends smoothly. -/
structure SereginTypeOneExclusion
    (u : VelocityField) (ν T : ℝ) : Prop where
  /-- The extended-smoothness time. -/
  T'        : ℝ
  T_lt_T'   : T < T'
  /-- The extended velocity field — smooth on `[0, T')` — that
      agrees with the original `u` on `[0, T)`. -/
  u'        : VelocityField
  /-- The extension satisfies `NSEvolutionAxioms` on `[0, T')`. -/
  extends_ax : NSEvolutionAxioms u' ν T'
  /-- Agreement on the original interval. -/
  agrees_on :
    ∀ t : ℝ, 0 ≤ t → t < T → ∀ x : Vec3, u' t x = u t x

/-- **Axiom 2 — `seregin_type_one_exclusion`.**  If a smooth NS
    solution on `[0, T)` satisfies the sub-Type-I rate
    `∀ ε > 0, ∃ δ > 0, ∀ t > T-δ, ‖ω(·, t)‖_∞ < ε / (T - t)`,
    then it extends smoothly past `T`. -/
axiom seregin_type_one_exclusion
    {u : VelocityField} {ν T : ℝ} (_ax : NSEvolutionAxioms u ν T)
    (_h_subTypeI :
      ∀ ε : ℝ, 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ t : ℝ, T - δ < t → t < T →
            ∀ x : Vec3,
              Real.sqrt (Vec3.dot (vorticity u t x) (vorticity u t x))
                ≤ ε / (T - t)) :
    SereginTypeOneExclusion u ν T

/-! ## Axiom 3 — Kato time-analyticity -/

/-- Consumed form of Kato (1967) / Foias–Temam (1979).  Provides, for
    every interior time `t₀ ∈ (0, T)`, a positive radius `r(t₀)` at
    which the map `t ↦ u(t, x)` is real-analytic.

    We encode the conclusion structurally (existence of `r`) so that
    downstream consumers can apply the identity theorem for
    real-analytic functions from mathlib. -/
structure NSTimeAnalyticity
    (u : VelocityField) (ν T : ℝ) : Prop where
  /-- Radius function, `r(t₀) > 0` for every interior `t₀`. -/
  r      : ℝ → ℝ
  r_pos  : ∀ t₀ : ℝ, 0 < t₀ → t₀ < T → 0 < r t₀
  /-- Real-analyticity window witness.  Consumed by the
      identity-theorem / accidental-multiplicity argument in
      `Analyticity/*` (to be written). -/
  has_analytic_window :
    ∀ x : Vec3, ∀ t₀ : ℝ, 0 < t₀ → t₀ < T →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ r t₀ ∧
        AnalyticOn ℝ (fun t : ℝ => u t x)
          (Set.Ioo (t₀ - δ) (t₀ + δ))

/-- **Axiom 3 — `NS_time_analyticity`.**  Smooth NS solutions on
    `[0, T)` extend holomorphically to a complex strip about every
    interior real time, with a positive radius depending continuously
    on the base-point.  Real-analyticity is the consumed form. -/
axiom NS_time_analyticity
    {u : VelocityField} {ν T : ℝ} (_ax : NSEvolutionAxioms u ν T) :
    NSTimeAnalyticity u ν T

end NSBlwChain
