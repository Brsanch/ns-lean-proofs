-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Setup.ClassicalAxioms
import NSBlwChain.Caveats.AngularIntegrals

/-!
# §12.2 — Biot–Savart cylindrical-coordinate identity (structural skeleton)

This file packages the **near-field / far-field scalar bookkeeping** of
Proposition 12.1 (the exact pointwise Biot–Savart integral identity for
the aligned self-strain at an argmax of `|ω|`).  The *integral identity
itself* — including the change of variables to cylindrical coordinates
`(ρ, θ, Z)`, the θ-averaging that produces `ω̄_φ(ρ, Z)`, and the
application of Fubini on `ℝ³` — is classical and is taken as the
named axiom `NSBlwChain.biot_savart_self_strain_bound` in
`Setup/ClassicalAxioms.lean`.

**What lives here.**  A Prop-valued hypothesis bundle packaging the four
scalar inputs that the near/far split of §12.2 consumes:

* the **cylindrical-radius cutoff** `δ_ν > 0` and the **box radius**
  `L ≥ δ_ν`;
* a **near-field Lipschitz estimate** on the θ-averaged vorticity
  `ω̄_φ` (scalar form, expressed as a pointwise bound on the relevant
  one-dimensional integral at radius `r = √(ρ² + Z²)`);
* a **far-field uniform bound** on `ω̄_φ` by the argmax value `M`;
* the **angular identity** `∫₀^π sin²θ · |cos θ| dθ = 2/3` (evaluated
  in `Caveats/AngularIntegrals.lean`);
* the **far-field log identity** `∫_{δ_ν}^L (1/r) dr = log(L/δ_ν)` (also
  in `Caveats/AngularIntegrals.lean`).

From these we derive, algebraically, the three consumed scalar
inequalities of §12.2:

1. `near_field_bound` — `I_near ≤ (2/3) · M`,
2. `far_field_bound`  — `I_far  ≤ (2/3) · M · log(L / δ_ν)`,
3. `sigma_near_far_bound` — `I_near + I_far ≤ M · (2/3) · (1 + log(L/δ_ν))`.

Here `I_near` and `I_far` are the scalar placeholders for the
near-zone and far-zone contributions to the integral identity of
Proposition 12.1 after the change of variables to `(ρ, Z)` and the
angular integration has been performed.  The hypotheses treat them as
first-class scalar data; *no* three-dimensional integrability claims
are made inside this file.

This follows the SQG-project pattern: isolate the pure-algebra step,
so the downstream chain (`BiotSavartSelfStrainBound`) consumes a
`Prop`-shaped conclusion whose analytical inputs are explicitly named.

## Relationship to `BiotSavartSelfStrainBound`

The axiom `biot_savart_self_strain_bound` delivers the *full*
Proposition-12.1 inequality for `σ(x*, t)` in a form bundling the
torus correction `C_L`.  This file does **not** discharge that axiom;
it provides the scalar scaffolding that *would* replace the axiom once
the three-dimensional integrability content is in place (cylindrical
Fubini, θ-averaging, integrability on `(0, ∞) × ℝ`).  The structural
theorems in this file are consumed by `BLW/AnalyticalToImplicit.lean`
only as hypothesis-level specifications — they do not appear in the
capstone Theorem 1/2 proofs.
-/

namespace NSBlwChain.BLW

open Real NSBlwChain NSBlwChain.Caveats

/-! ## Cylindrical-data hypothesis bundle

A `Prop`-valued packaging of the scalars produced by the cylindrical
change-of-variables step of §12.2.  Prop-valued so that no data-field
choices are made at this layer; consumers supply the scalars and the
bounds on the integrals they denote. -/

/-- **Cylindrical-coordinate hypothesis bundle for §12.2.**

    All five fields are scalars (no fields of function type).  The
    consumer supplies numerical witnesses `I_near, I_far, M, δ_ν, L`
    together with the three classical inequalities:

    * `near_le` — near-zone integral after angular evaluation,
      `I_near ≤ (2/3) · M`.  Physically: the near-zone integrand is
      `ρ²Z / r⁵ · ω̄_φ(ρ, Z)` on `{r ≤ δ_ν}`; after spherical-angular
      integration (using D.3.1) and the Lipschitz bound
      `|ω̄_φ(ρ, Z)| ≤ |∇ω|(x*) · r` with Theorem 12.2
      (`|∇ω|(x*) ≤ M / δ_ν`), the result is at most `(2/3) · M`.

    * `far_le` — far-zone integral after angular and radial evaluation,
      `I_far ≤ (2/3) · M · log(L / δ_ν)`.  Physically: on `{δ_ν < r ≤ L}`
      the integrand is bounded by `ρ²Z / r⁵ · M`, and after angular
      (D.3.1) and radial (D.3.2) integration the factor is
      `(2/3) · log(L / δ_ν)`.

    The remaining fields (`M_nonneg`, `δ_pos`, `δ_le_L`) record the
    elementary positivity/sizing assumptions needed to apply
    `Real.log_le_log_iff` and the D.3.2 identity. -/
structure CylindricalData where
  /-- Argmax value `|ω(x*, t)|`. -/
  M        : ℝ
  /-- Viscous cutoff radius `δ_ν = √(ν / σ(x*, t))`. -/
  δ_ν      : ℝ
  /-- Box scale at which the torus correction is applied. -/
  L        : ℝ
  /-- Near-zone integral placeholder: value of
      `∫_{r ≤ δ_ν} (ρ² Z / r⁵) · ω̄_φ(ρ, Z) dρ dZ`
      after the cylindrical-to-spherical angular integration. -/
  I_near   : ℝ
  /-- Far-zone integral placeholder: value of
      `∫_{δ_ν < r ≤ L} (ρ² Z / r⁵) · ω̄_φ(ρ, Z) dρ dZ`
      after the cylindrical-to-spherical angular integration. -/
  I_far    : ℝ
  /-- `M ≥ 0`. -/
  M_nonneg : 0 ≤ M
  /-- Near cutoff is strictly positive. -/
  δ_pos    : 0 < δ_ν
  /-- Near cutoff does not exceed the far cutoff. -/
  δ_le_L   : δ_ν ≤ L
  /-- **Near-field Lipschitz scalar bound.**
      Consumed form of
      `|ω̄_φ(ρ, Z)| ≤ |∇ω|(x*) · √(ρ² + Z²)` combined with
      `|∇ω|(x*) ≤ M / δ_ν` (Theorem 12.2) and the spherical angular
      identity D.3.1 `∫_0^π sin²θ · |cos θ| dθ = 2/3`.
      Delivers the scalar
      `I_near ≤ (2/3) · M`. -/
  near_le  : I_near ≤ (2 / 3) * M
  /-- **Far-field uniform scalar bound.**
      Consumed form of `|ω̄_φ(ρ, Z)| ≤ M` combined with the spherical
      angular identity D.3.1 `∫_0^π sin²θ · |cos θ| dθ = 2/3` and the
      far-field log identity D.3.2
      `∫_{δ_ν}^L (1/r) dr = log(L / δ_ν)`.  Delivers the scalar
      `I_far ≤ (2/3) · M · log(L / δ_ν)`. -/
  far_le   : I_far ≤ (2 / 3) * M * Real.log (L / δ_ν)

namespace CylindricalData

variable (cd : CylindricalData)

/-! ## Elementary scalar facts -/

/-- `L > 0` — immediate from `0 < δ_ν ≤ L`. -/
lemma L_pos : 0 < cd.L := lt_of_lt_of_le cd.δ_pos cd.δ_le_L

/-- `L / δ_ν ≥ 1` — immediate from `δ_ν ≤ L` with `δ_ν > 0`. -/
lemma one_le_L_div_δ : 1 ≤ cd.L / cd.δ_ν :=
  (one_le_div cd.δ_pos).mpr cd.δ_le_L

/-- `log(L / δ_ν) ≥ 0`. -/
lemma log_L_div_δ_nonneg : 0 ≤ Real.log (cd.L / cd.δ_ν) := by
  have h : 1 ≤ cd.L / cd.δ_ν := cd.one_le_L_div_δ
  have := Real.log_nonneg h
  exact this

/-! ## The three scalar reductions of §12.2 -/

/-- **Near-field scalar reduction (§12.2, near zone).**

    `I_near ≤ (2/3) · M`.

    Direct consumption of the `near_le` field.  Stated as a named theorem
    for use at call sites that want the inequality by name rather than by
    field access. -/
theorem near_field_bound : cd.I_near ≤ (2 / 3) * cd.M := cd.near_le

/-- **Far-field scalar reduction (§12.2, far zone).**

    `I_far ≤ (2/3) · M · log(L / δ_ν)`.

    Direct consumption of the `far_le` field.  Stated as a named theorem
    mirroring `near_field_bound`. -/
theorem far_field_bound :
    cd.I_far ≤ (2 / 3) * cd.M * Real.log (cd.L / cd.δ_ν) := cd.far_le

/-- **Combined near/far scalar bound (§12.2, top-level).**

    `I_near + I_far ≤ M · (2/3) · (1 + log(L / δ_ν))`.

    This is the scalar content of Proposition 12.1's near/far
    decomposition, prior to the absorption step in §12.4 that closes
    the chain.  Proof: add the two reductions and factor. -/
theorem sigma_near_far_bound :
    cd.I_near + cd.I_far
      ≤ cd.M * ((2 / 3) * (1 + Real.log (cd.L / cd.δ_ν))) := by
  have h_near : cd.I_near ≤ (2 / 3) * cd.M := cd.near_field_bound
  have h_far  : cd.I_far  ≤ (2 / 3) * cd.M * Real.log (cd.L / cd.δ_ν) :=
    cd.far_field_bound
  have h_add : cd.I_near + cd.I_far
      ≤ (2 / 3) * cd.M + (2 / 3) * cd.M * Real.log (cd.L / cd.δ_ν) :=
    add_le_add h_near h_far
  -- Factor the right-hand side:
  --   (2/3) M + (2/3) M · log = M · (2/3) · (1 + log).
  have h_ring :
      (2 / 3) * cd.M + (2 / 3) * cd.M * Real.log (cd.L / cd.δ_ν)
        = cd.M * ((2 / 3) * (1 + Real.log (cd.L / cd.δ_ν))) := by
    ring
  rw [← h_ring]
  exact h_add

/-! ## Reference link to the angular and radial identities

    These re-exports pin down the numeric constant `2/3` and the log
    form used above to the classical integrals of
    `Caveats/AngularIntegrals.lean`, to make the derivation step from
    the three-dimensional identity to the scalar form auditable. -/

/-- Re-export of D.3.1 (`sin²θ · |cos θ|` integrates to `2/3`).  The
    angular coefficient in `near_field_bound` and `far_field_bound`
    arises from this identity. -/
theorem angular_integral_two_thirds :
    ∫ θ in (0 : ℝ)..Real.pi, (Real.sin θ)^2 * |Real.cos θ| = 2 / 3 :=
  NSBlwChain.Caveats.sin_sq_mul_abs_cos_integral_zero_to_pi

/-- Re-export of D.3.2 (`∫_{δ_ν}^L (1/r) dr = log(L/δ_ν)`).  The log
    factor in `far_field_bound` arises from this identity. -/
theorem far_field_log_integral :
    ∫ r in cd.δ_ν..cd.L, (1 / r) = Real.log (cd.L / cd.δ_ν) :=
  NSBlwChain.Caveats.one_over_r_integral_log_div cd.δ_pos cd.δ_le_L

end CylindricalData

/-! ## Bridge to the `BiotSavartSelfStrainBound` axiom shape

    The axiom `biot_savart_self_strain_bound` produces a
    `BiotSavartSelfStrainBound` structure whose `bound` field carries
    the *full* §12.2 conclusion with torus correction `C_L`.  The
    following wrapper exhibits how a `CylindricalData` witness would
    feed the scalar side of that axiom once the three-dimensional
    identity is in place — i.e. the transition
    `I_near + I_far ↦ σ(x*, t)`.

    This is a *specification-level* statement only: it does not try to
    equate `I_near + I_far` with `σ`, which is the content of the
    axiomatized identity.  It simply records the shape so downstream
    code can trace the dependency. -/

/-- **Specification wrapper.**  Given a `CylindricalData` witness with
    `I_near + I_far = σ` (the axiomatized identity of §12.2, supplied
    here as a bare hypothesis `h_identity`), the combined bound reads
    `σ ≤ M · (2/3) · (1 + log(L/δ_ν))`.

    No torus-correction constant `C_L` appears here; adding it to match
    `BiotSavartSelfStrainBound.bound` is done at the call site in
    `BLW/AnalyticalToImplicit.lean`.  This wrapper isolates the
    scalar-arithmetic content. -/
theorem sigma_bound_of_cylindricalData
    (cd : CylindricalData) {σ : ℝ}
    (h_identity : σ = cd.I_near + cd.I_far) :
    σ ≤ cd.M * ((2 / 3) * (1 + Real.log (cd.L / cd.δ_ν))) := by
  rw [h_identity]
  exact cd.sigma_near_far_bound

end NSBlwChain.BLW
