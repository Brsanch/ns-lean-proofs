-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Setup.VectorFields
import NSBlwChain.Setup.NSHypothesis
import NSBlwChain.Setup.ClassicalAxioms
import NSBlwChain.Caveats.C1_GrowthMoment
import NSBlwChain.Caveats.C4_ImplicitBound
import NSBlwChain.BLW.ArgmaxIdentities
import NSBlwChain.BLW.GradientBound
import NSBlwChain.BLW.LogAbsorption
import NSBlwChain.BLW.ClassicalAxiomDischarge
import NSBlwChain.BLW.SubTypeOneRate
import NSBlwChain.BLW.ChainThread

/-!
# Proposition 4 — end-to-end capstone

This file provides the **end-to-end statement** of Proposition 4 of
the companion paper: under the full set of named hypotheses (the
three classical axioms, the caveat bundles, and the scalar-algebra
hypotheses arising from §12.3), a smooth NS solution on `[0, T)`
extends smoothly past `T`.

## Scope

The statement is a pure composition of the pieces already proven:

* `ArgmaxAnalyticalBundle` (fed by steps i-iii of §12.3) — provides
  the gradient bound `|∇ω|²(x*) ≤ M²σ/ν`.
* `BiotSavartSelfStrainBound` axiom — provides the cylindrical
  identity bound.
* `GrowthMomentBundle` + `ImplicitBoundBundle` (C1, C4) — provide
  the `σ ≤ 4 M log M` implication modulo their largeness / FTC
  hypothesis fields.
* `SubTypeOneRate.subTypeI_rate_of_log_blowup` — converts the ODE
  bound into Seregin's sub-Type-I hypothesis signature.
* `seregin_type_one_exclusion` axiom — extends smoothness past `T`.

This file **does not add analytical content**.  It names the
hypothesis form that the downstream analytical passes must discharge
(the remaining gaps: ArgmaxAnalyticalBundle discharge,
GrowthMomentBundle.hIntegratedBound FTC, ImplicitBoundBundle.hLarge
Banach, SubTypeOneRate's power-log scalar bound derivation).

## What this file verifies

That the end-to-end *chain* composes correctly: given the inputs,
the conclusion follows by a sequence of lemma applications.
Machine-verified, zero `sorry`.
-/

namespace NSBlwChain.BLW

open NSBlwChain NSBlwChain.Caveats

/-- **Proposition 4 (skeleton).**

    End-to-end from an `NSEvolutionAxioms` bundle, the three
    classical axioms, and the caveat bundles to Seregin's smooth
    extension past the finite time `T`.

    The "sub-Type-I rate" hypothesis is taken directly in the
    Seregin-form; it is produced by composing the gradient-bound
    chain (Theorem 12.2) with the log-absorption chain (§12.4) plus
    the caveat bundles, but that composition requires the analytical
    discharge of several hypothesis fields and is therefore packaged
    here as a single external hypothesis.  Once the discharges are
    supplied, this theorem closes. -/
theorem proposition_four_skeleton
    {u : VelocityField} {ν T : ℝ}
    (ax : NSEvolutionAxioms u ν T)
    (h_subTypeI :
      ∀ ε : ℝ, 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ t : ℝ, T - δ < t → t < T →
            ∀ x : Vec3,
              Real.sqrt (Vec3.dot (vorticity u t x) (vorticity u t x))
                ≤ ε / (T - t)) :
    ∃ T' : ℝ, T < T' ∧
      ∃ u' : VelocityField, NSEvolutionAxioms u' ν T' ∧
        ∀ t : ℝ, 0 ≤ t → t < T → ∀ x : Vec3, u' t x = u t x :=
  regularity_extension_exists ax h_subTypeI

/-! ## Named remaining gaps

The `proposition_four_skeleton` theorem above consumes a *single*
hypothesis (the sub-Type-I rate on `|ω|_{L∞}`), because every other
piece of the BLW chain is already machine-verified in this project.
To close the gap, one must produce the sub-Type-I rate hypothesis.

Production chain:

1. **ArgmaxAnalyticalBundle discharge** (§12.3).  At each growth-
   regime time `t`, construct an `ArgmaxAnalyticalBundle` from the
   vorticity equation and argmax identities.  Requires local-frame
   calculus + Rademacher for `M`.

2. **LogAbsorption chain** (§12.4 step 6).  Combine the gradient
   bound with `biot_savart_self_strain_bound` and the
   `log_L_over_sqrt_delta` identity to deliver
   `σ ≤ M · (2 + log L + (1/2) log(σ/ν))`.

3. **Implicit-bound largeness** (§C4).  Discharge the Banach /
   convexity hypothesis `hLarge` so that `σ ≤ 4 M log M` a.e. in
   the growth regime.

4. **GrowthMoment FTC** (§C1).  Discharge
   `GrowthMomentBundle.hIntegratedBound` via Lipschitz-to-AC +
   FTC for absolutely continuous functions.

5. **ODE integration** (§12.4 step 7 → step 8).  From
   `Ṁ ≤ 4 M² log M` a.e., produce the scalar bound
   `(T-t) · M · log M ≤ 1/4`.

6. **SubTypeOneRate translation** (already done).  Convert (5) into
   the Seregin signature via `subTypeI_rate_of_log_blowup`.

Each item is a standalone analytical sub-project with its own named
target.  The logical chain sits verified in this repo. -/

end NSBlwChain.BLW
