-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Setup.VectorFields
import NSBlwChain.Setup.NSHypothesis
import NSBlwChain.Setup.ClassicalAxioms
import NSBlwChain.Caveats.C1_GrowthMoment
import NSBlwChain.Caveats.C4_ImplicitBound
import NSBlwChain.BLW.LogAbsorption

/-!
# End-to-end threading: classical axioms + caveat bundles → Seregin

This file threads the pieces of the BLW-gradient chain into a single
named statement: given

* an `NSEvolutionAxioms` bundle,
* the classical axioms (`biot_savart_self_strain_bound`,
  `seregin_type_one_exclusion`),
* caveat bundles (`GrowthMomentBundle`, `ImplicitBoundBundle`),
* a "sub-Type-I rate" hypothesis (to be derived from the BLW chain
  in a subsequent pass — taken here as input for the threading),

the conclusion is that the solution extends past `T` — i.e.,
`T` is *not* the first finite singularity.

## What is verified here

* The threading itself: structural composition of the six inputs
  into the Seregin application.  **Machine-verified, no `sorry`.**

## What is not verified here

* Discharge of the sub-Type-I rate from `GrowthMomentBundle` +
  `ImplicitBoundBundle` + the gradient bound.  This is the ODE
  integration of §12.4 step 7 → step 8; it is packaged here as a
  named input hypothesis.
* Discharge of `GrowthMomentBundle` from `NSEvolutionAxioms`
  (Lipschitz of `M`, FTC, Rademacher).
* Discharge of `ImplicitBoundBundle.hLarge` via Banach fixed point.

Each discharge has its own caveat file and will be closed in
subsequent passes.  The threading below verifies that *if* those
discharges are achieved, the chain closes.
-/

namespace NSBlwChain.BLW

open NSBlwChain NSBlwChain.Caveats

/-- **End-to-end threading.**  Given `NSEvolutionAxioms u ν T` and a
    "sub-Type-I rate" hypothesis on `u`'s vorticity, apply
    `seregin_type_one_exclusion` to produce a smooth extension past
    `T`.

    The sub-Type-I hypothesis has the explicit form required by
    `seregin_type_one_exclusion`:

      `∀ ε > 0, ∃ δ > 0, ∀ t ∈ (T-δ, T), ∀ x, |ω(t, x)| ≤ ε / (T-t)`.

    No actual content of the BLW chain is invoked in this threading
    theorem — it is purely an axiom application.  The content lives
    in the discharge of the hypothesis, which consumes the gradient
    bound, log-absorption, implicit-bound, and growth-moment
    machinery in turn.

    The threaded conclusion returns a `SereginTypeOneExclusion`
    package — existence of `T' > T` plus a smooth-extended `u'`.
    Since `SereginTypeOneExclusion` is a data-carrying structure
    (not a `Prop`), this is a `def` rather than a `theorem`. -/
noncomputable def extends_past_T_of_subTypeI
    {u : VelocityField} {ν T : ℝ}
    (ax : NSEvolutionAxioms u ν T)
    (h_subTypeI :
      ∀ ε : ℝ, 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ t : ℝ, T - δ < t → t < T →
            ∀ x : Vec3,
              Real.sqrt (Vec3.dot (vorticity u t x) (vorticity u t x))
                ≤ ε / (T - t)) :
    SereginTypeOneExclusion u ν T :=
  seregin_type_one_exclusion ax h_subTypeI

/-- **Threaded regularity statement.**  Names the contrapositive:
    if `NSEvolutionAxioms u ν T` holds *and* the sub-Type-I rate
    holds, then there exists `T' > T` to which the evolution
    extends.  A one-line re-export of `extends_past_T_of_subTypeI`
    with the data unpacked. -/
theorem regularity_extension_exists
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
        ∀ t : ℝ, 0 ≤ t → t < T → ∀ x : Vec3, u' t x = u t x := by
  obtain ⟨T', hTT', u', hax', hagree⟩ :=
    extends_past_T_of_subTypeI ax h_subTypeI
  exact ⟨T', hTT', u', hax', hagree⟩

/-! ## Future-work interface

The "sub-Type-I rate" hypothesis is the single remaining analytical
gap at this level of the formalization.  The BLW-gradient chain
delivers it via:

* **From `GradientBound` + `LogAbsorption` + `BiotSavartSelfStrainBound`:**
  at every growth-regime argmax, `σ(x*) ≤ M · (2 + log L + (1/2) log(σ/ν))`.
* **From `ImplicitBoundBundle`:** this self-consistency implies
  `σ(x*) ≤ 4 M log M` for `M` large.
* **From `C1 GrowthMomentBundle` + `C2_AeOde`:** a.e. `Ṁ ≤ 4 M² log M`.
* **ODE integration (§12.4 step 8):** sub-Type-I rate
  `(T-t) · ‖ω‖_∞ → 0`.

The threading theorem `regularity_extension_exists` above confirms
that closing those four steps closes the chain.  Each is an open
analytical task in its own file — packaged explicitly so that the
total remaining work is enumerated. -/

end NSBlwChain.BLW
