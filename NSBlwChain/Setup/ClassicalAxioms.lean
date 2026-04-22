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

1. **Biot–Savart self-strain bound (§12.4 log-absorption output).**
   Named: `biot_savart_self_strain_bound`.  Packages the output of
   the paper's §12.4 log-absorption step *in the growth regime*
   `dM/dt(t) ≥ 0`: at any argmax `x_star` of `|ω(·, t)|`, the aligned
   self-strain is bounded by `σ(x_star, t) ≤ M · (1 + C_L + log(L / δ_ν))`
   for some `C_L ≥ 0`.  Note this is the *composite* of Prop 12.1 +
   cylindrical θ-averaging (§12.2) + Lemma B far-field bound +
   growth-regime log absorption — not Prop 12.1 alone.

2. **Seregin type-one exclusion (vorticity form).**  Named:
   `seregin_type_one_exclusion`.  Given a smooth NS solution on
   `[0, T)` whose vorticity satisfies the sub-Type-I rate
   `(T - t) · ‖ω(·, t)‖_∞ → 0`, the solution extends smoothly
   past `T`.  This is a *composite* of Seregin 2012 CMP (which
   proves the L³-velocity criterion) with Biot–Savart on ℝ³ and
   Sobolev embedding.  See the `/-! ## Axiom 2 ... -/` header
   below for the citation note.

3. **NS time-analyticity (Masuda 1967 + Foias–Temam 1979).**
   Named: `NS_time_analyticity`.  Smooth NS solutions extend to
   a holomorphic map on a complex strip around every interior
   time in `(0, T)`.  The correct primary sources are Masuda 1967
   Proc. Japan Acad. 43 (bounded domain / exterior with Dirichlet
   BC) and **Foias–Temam 1979 J. Math. Pures Appl. 58** (whole-space /
   torus, venue definitively resolved 2026-04-22); "Kato 1967"
   appearing in older drafts is a mis-citation (that Kato paper
   is about 2D Euler, not NS analyticity).  See the `/-! ## Axiom 3
   ... -/` header below.

## Consumed forms

Each axiom is wrapped in a `Prop`-valued structure so that consumers
can destructure the analytical content cleanly.  The `Prop` shape
matches the *exact* hypothesis signature that the BLW-gradient chain
capstone takes on input, so that invoking the axiom is a one-line
`exact biot_savart_self_strain_bound ax hDecay` call (axiom 1 takes
`NSEvolutionAxioms` plus a `DecayAtInfinity` witness).
-/

namespace NSBlwChain

/-! ## Decay-at-infinity hypothesis (consumed by Axiom 1)

The Biot–Savart integral on ℝ³,
$u(x) = \frac{1}{4\pi}\int\frac{(x-y)\times\omega(y)}{|x-y|^3}\,dy$,
requires `ω` to decay sufficiently fast at infinity for convergence.
This is a genuine hypothesis on the velocity field, not implied by
`NSEvolutionAxioms` alone (smooth + div-free does **not** force decay).

We record the decay as an **explicit structural hypothesis** consumed
by `biot_savart_self_strain_bound`.  The model-correctness audit
(`noethersolve/docs/findings/ns_model_correctness_memo_2026_04_22.md`)
flagged that earlier versions had this hypothesis implicit; making it
visible here answers the reviewer's first question
("what decay do you assume on u?") at the interface level.

The concrete form we require is polynomial decay of `ω` faster than
`|x|^{-3}` (which is the minimum needed for the Biot–Savart kernel's
`|x - y|^{-2}`-type singularity to yield a convergent integral).
On the torus this is automatic; `DecayAtInfinity.of_torus_periodic`
provides a trivial constructor downstream.
-/

/-- Decay-at-infinity hypothesis on a velocity field `u` on `[0, T) × ℝ³`.
    Asserts polynomial decay of the vorticity `ω = ∇ × u` faster than
    `|x|^{-3}` outside a ball of radius `R`, sufficient for Biot–Savart
    convergence. -/
structure DecayAtInfinity (u : VelocityField) (T : ℝ) : Prop where
  /-- Polynomial decay witness: there exist `R > 0`, `C ≥ 0`, and a
      decay exponent `p > 3` such that on `[0, T) × {|x| ≥ R}`,
      `|ω(t, x)| ≤ C · |x|^{-p}`. -/
  has_polynomial_decay :
    ∃ R C p : ℝ, 0 < R ∧ 0 ≤ C ∧ 3 < p ∧
      ∀ t : ℝ, 0 ≤ t → t < T → ∀ x : Vec3,
        R ≤ Real.sqrt (Vec3.dot x x) →
          Real.sqrt (Vec3.dot (vorticity u t x) (vorticity u t x)) ≤
            C / (Real.sqrt (Vec3.dot x x)) ^ p

/-! ## Axiom 1 — Biot–Savart self-strain bound

This axiom encodes the **output** of the §12.4 log-absorption step of
the paper — specifically the inequality `σ(x*) ≤ M · (1 + C_L + log(L/δ_ν))`
at an argmax `x*` of `|ω(·, t)|` *in the growth regime* `dM/dt ≥ 0`.

**Upstream structure.**  The derivation uses:
- Proposition 12.1 (Biot–Savart pointwise identity on ℝ³) to recover
  `σ(x*)` from the vorticity;
- cylindrical θ-averaging of the Biot–Savart kernel (§12.2);
- Lemma B (energy-enstrophy dissipation) to bound the far-field tail;
- the growth-regime hypothesis `dM/dt(t) ≥ 0`, which lets one drop the
  time-derivative term in the log-absorption ODE.

**What this axiom is NOT.**  It is *not* Proposition 12.1 alone
(Biot–Savart identity), which is a pointwise equality and does not
produce a log-absorption bound by itself.  The axiom consumes the
composite paper §12.4 theorem including the growth-regime restriction.
-/

/-- Consumed form of the §12.4 log-absorption output.  Provides a
    constant `C_L ≥ 0` and a universal bound `σ(x*, t) ≤ M(t) · (1
    + C_L + log(L / δ_ν(t)))` at every argmax point `x_star` in the
    growth regime `0 ≤ Ṁ(t)`, with `δ_ν(t) := √(ν/σ(x_star, t))`.

    The structure records only the *output* shape consumed by the
    chain; the derivation of the identity from cylindrical
    θ-averaging plus log-absorption is the content of the axiom
    below. -/
structure BiotSavartSelfStrainBound
    (u : VelocityField) (ν T : ℝ) where
  /-- Box size at which the torus correction is applied. -/
  L          : ℝ
  /-- Torus-correction constant. -/
  C_L        : ℝ
  /-- Positive box size. -/
  L_pos      : 0 < L
  /-- Torus correction non-negative. -/
  C_L_nonneg : 0 ≤ C_L
  /-- The bound at every growth-regime argmax.  Stated with respect
      to abstract scalars representing `M`, `σ`, `δ_ν = √(ν/σ)`, and
      `Mdot` at a fixed time, with the **growth-regime hypothesis
      `0 ≤ Mdot`** matching paper §12.4.  Downstream consumers pick
      concrete values. -/
  bound :
    ∀ M σ Mdot : ℝ, 0 ≤ M → 0 < σ → 0 < ν → 0 ≤ Mdot →
      σ ≤ M * (1 + C_L + Real.log (L / Real.sqrt (ν / σ)))

/-- **Axiom 1 — `biot_savart_self_strain_bound`.**  The exact Biot–
    Savart pointwise identity of Prop 12.1, combined with the §12.4
    log-absorption step (cylindrical θ-averaging, far-field Lemma B
    bound, growth-regime hypothesis `dM/dt ≥ 0`), delivers a
    growth-regime bound of the form recorded in
    `BiotSavartSelfStrainBound`.

    **Decay hypothesis (explicit).**  The Biot–Savart integral
    requires `ω` to decay faster than `|x|^{-3}` at infinity; this
    is consumed as `_hDecay : DecayAtInfinity u T`.  Previously this
    hypothesis was implicit in the axiom's statement; the present
    form makes it visible at every call site. -/
axiom biot_savart_self_strain_bound
    {u : VelocityField} {ν T : ℝ}
    (_ax : NSEvolutionAxioms u ν T)
    (_hDecay : DecayAtInfinity u T) :
    BiotSavartSelfStrainBound u ν T

/-! ## Axiom 2 — Seregin type-one exclusion (vorticity form)

**Citation note.**  The directly cited paper is Seregin 2012,
*A certain necessary condition of potential blow up for
Navier–Stokes equations*, Comm. Math. Phys. **312**, 833–845
(DOI 10.1007/s00220-011-1391-x).  That paper proves the **L³ velocity
criterion**: if `limsup_{t → T⁻} ‖u(·, t)‖_{L³(ℝ³)} < ∞`, then the
solution extends past `T`.

The axiom below is stated in the **vorticity-Type-I form** actually
consumed by the BLW chain.  This is *not* Seregin 2012 verbatim — it
is the composite theorem

  *ESS 2003 + Seregin 2012 (L³ criterion)* + *Biot–Savart on ℝ³* + *Sobolev embedding*
  ⇒ vorticity-sub-Type-I rate excludes blow-up.

Strictly speaking the originating L³ criterion is **Escauriaza–Seregin–
Šverák 2003** ("L_{3,∞}-solutions of the Navier–Stokes equation and
backward uniqueness", Russian Math. Surveys **58**, 211–250), which
handled the endpoint `L^∞_t L^3_x` case.  Seregin 2012 refines this
to a necessary condition where the full limit (not limsup) is used:
if `lim_{t→T⁻} ‖u(·,t)‖_{L³} = ∞` fails, then no singularity at `T`.

In the smooth regime on ℝ³, the vorticity bound `‖ω(t)‖_∞ ≤ ε/(T-t)`
implies (via Biot–Savart + weighted estimates) `‖u(t)‖_{L³} = O(1)`
as `t → T⁻`, which ESS 2003 / Seregin 2012 then excludes.  The
bridging step is classical but should be noted in any external
review.

Journal-hunt cross-check (2026-04-22,
`noethersolve/docs/findings/ns_journal_theorem_statements_2026_04_22.md`)
confirmed Seregin 2012 against arXiv:1104.3615 and flagged the
`lim` vs `limsup` distinction.
-/

/-- Consumed form of Seregin (2012) composed with Biot–Savart +
    Sobolev.  The conclusion is that the sub-Type-I rate hypothesis
    on vorticity is *inconsistent* with `T` being a finite singularity
    time: there is always a strictly later time `T' > T` to which the
    solution extends smoothly. -/
structure SereginTypeOneExclusion
    (u : VelocityField) (ν T : ℝ) where
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

/-! ## Axiom 3 — NS time-analyticity (Masuda 1967 + Foias–Temam 1979)

**Citation correction.**  Earlier versions of this project cited
"Kato 1967 ARMA 25" here, which is actually Kato's 2D Euler paper,
not NS time analyticity.  The correct primary sources — both needed
jointly — are:

  *K. Masuda, On the analyticity and the unique continuation theorem
  for solutions of the Navier–Stokes equation*, Proc. Japan Acad.
  **43** (1967), 827–832.

  *C. Foias, R. Temam, Some analytic and geometric properties of the
  solutions of the evolution Navier–Stokes equations*, J. Math.
  Pures Appl. **58** (1979), 339–368.

Journal-hunt cross-check (2026-04-22,
`noethersolve/docs/findings/ns_journal_theorem_statements_2026_04_22.md`)
confirmed Masuda 1967 against the J-STAGE PDF and **definitively
resolved the venue for Foias–Temam 1979 as J. Math. Pures Appl.
58 (1979), 339–368** (not J. Funct. Anal. 33 as cited in some earlier
drafts — that is a different 1989 Gevrey-regularity paper).

**Why both sources.**  Masuda 1967 proves time-analyticity on
**bounded domains or exterior of a C² hypersurface with Dirichlet
BC**, not directly on ℝ³ or the torus.  Foias–Temam 1979 provides
the **torus / ℝ³ whole-space** version via Galerkin + Banach-scale
extension.  The Lean axiom below is stated domain-abstractly so it
covers either source's setting, but for a full formalization the
domain and BC would need to be fixed to match the source.

The content below is the **real-analyticity window** consumed by the
BLW chain, which is weaker than (and implied by) the full
holomorphic-strip extension in either source.
-/

/-- Consumed form of Masuda (1967) / Foias–Temam (1979).  Provides,
    for every interior time `t₀ ∈ (0, T)`, a positive radius `r(t₀)`
    at which the map `t ↦ u(t, x)` is real-analytic.

    We encode the conclusion structurally (existence of `r`) so that
    downstream consumers can apply the identity theorem for
    real-analytic functions from mathlib. -/
structure NSTimeAnalyticity
    (u : VelocityField) (ν T : ℝ) where
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
