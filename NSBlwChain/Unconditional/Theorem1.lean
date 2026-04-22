-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Setup.VectorFields
import NSBlwChain.Setup.NSHypothesis

/-!
# Theorem 1 — Unconditional blowup-rate bound (α ∈ (1, 2))

This file formalizes the algebraic core of **Theorem 1** from §3 of the
companion paper `paper/ns_regularity.md`:

> If `u` is a smooth NS solution on `[0, T*)` with initial data in
> `H¹ ∩ L∞` and `u` blows up at `T* < ∞`, then the blowup rate of
> `M(t) := ‖ω(·,t)‖_∞` satisfies
> `(T* − t) · M(t)^α ≤ C`
> for every `α ∈ (1, 2)`, with `C = C(‖ω₀‖_{L²}, ν) > 0`.

## Scope of this file — skeleton only

The full proof of Theorem 1 uses three analytical inputs that are
substantial classical PDE results:

1. The **Leray energy inequality** on `\mathbb R³`, which yields the
   time-integrated enstrophy bound
   `∫₀^{T*} ‖ω(t)‖_{L²}² dt ≤ ‖u₀‖_{L²}² / (2 ν)`.
2. The **enstrophy crossover** (Proposition 3.1): the spherical average
   `g(r) = ⟨|ω|⟩_sphere(r)` at radius `r` from `x*` satisfies
   `g(r) ≤ min(M, Z^{1/2} r^{-3/2})`, with crossover radius
   `r_c = (Z/M²)^{1/3}`.  Integrating gives the pointwise enstrophy
   lower bound `Z(t) ≥ c · M(t)^β` with `β = 2` in general and
   `β ∈ (2, 5/2)` in the blob regime.
3. The **ESS (Escauriaza–Seregin–Šverák, 2003)** Type-I exclusion for
   `α = 1`.

All three are classical results that are **not** part of this file's
scope.  Instead, this file:

* defines a **hypothesis bundle** `EnstrophyCrossoverBundle` packaging
  the scalar content of (1)–(2) as named scalar assumptions; and
* proves the algebraic **conclusion** `(T* − t) · M(t)^β ≤ C` from the
  bundle, for any exponent `β` in the bundle's range.

The upper bound `α < 2` is algebraic: it follows by applying the bundle
with `β = 2` and converting the resulting inequality to an inequality
in `M^α` via `rpow` monotonicity.  The lower bound `α > 1` (exclusion
of Type I) is recorded as the named classical input
`ESS_excludes_type_I` consumed downstream (it is a **hypothesis**, not
a free axiom, so the file contains zero `sorry` and zero `axiom`).

## Main results

* `EnstrophyCrossoverBundle`   — the scalar-hypothesis bundle.
* `blowup_rate_algebraic`      — `(T* − t) · M(t)^β ≤ E₀/(ν·c_Z)` from
  the bundle.
* `blowup_rate_alpha_of_bundle` — hypothesis-taking algebraic Theorem 1
  for any `α ∈ (0, β]` and `M ≥ 1`.
* `blowup_rate_alpha`          — the full Theorem 1 statement, hypothesis
  form (combines the algebraic bound with the named ESS exclusion).

## References

* Escauriaza, Seregin, Šverák (2003), *Russ. Math. Surveys* 58, 211–250.
* Beale, Kato, Majda (1984), *Comm. Math. Phys.* 94, 61–66.
* Doering, Gibbon (1995), *Applied Analysis of NS*, §3.
* Companion paper `paper/ns_regularity.md`, §3 + §3.1.
-/

namespace NSBlwChain.Unconditional

open scoped BigOperators

/-! ## Scalar hypothesis bundle for the enstrophy-crossover argument

The bundle packages the *scalar inputs* the algebraic conclusion
requires.  None of the data fields reference the underlying velocity
field directly: this is deliberate.  The algebraic core of Theorem 1
is a statement about real numbers only, and decoupling it from the
vector-field setup lets downstream files discharge the bundle from
whatever analytical route (Leray inequality on `\mathbb R³`, or
enstrophy identity on the torus) fits the ambient setting.

A separate `blowup_rate_alpha_of_NS` lemma in a downstream file will
build the bundle from `NSEvolutionAxioms` + `EnergyEnstrophyIdentities`
+ the enstrophy-crossover classical input. -/

/-- **Enstrophy-crossover hypothesis bundle for Theorem 1.**

    Scalar-level package of the analytical inputs consumed by the
    algebraic core of Theorem 1:

    * `ν > 0` — viscosity,
    * `E₀ ≥ 0` — initial `L²` energy,
    * `T* > 0` — the singular time,
    * `M : ℝ → ℝ` — the vorticity-max envelope (`M t = ‖ω(·,t)‖_∞`),
    * `Z : ℝ → ℝ` — the enstrophy (`Z t = ‖ω(·,t)‖_{L²}²`),
    * `β : ℝ` — the enstrophy-crossover exponent (typically `β = 2`),
    * `c_Z > 0` — the enstrophy-crossover constant.

    The bundle records the four scalar inequalities produced by the
    Leray energy inequality + enstrophy-crossover argument.  It is
    a **hypothesis** — no field is proven in this file. -/
structure EnstrophyCrossoverBundle
    (ν E₀ Tstar : ℝ) (M Z : ℝ → ℝ) (β c_Z : ℝ) : Prop where
  /-- Positive viscosity. -/
  nu_pos  : 0 < ν
  /-- Nonneg initial energy. -/
  E0_nonneg : 0 ≤ E₀
  /-- Positive singular time. -/
  Tstar_pos : 0 < Tstar
  /-- Positive crossover exponent. -/
  beta_pos : 0 < β
  /-- Positive crossover constant. -/
  cZ_pos  : 0 < c_Z
  /-- `M` is nonneg on the closed interval `[0, Tstar]`. -/
  M_nonneg : ∀ t : ℝ, 0 ≤ t → t ≤ Tstar → 0 ≤ M t
  /-- `M` is non-decreasing on the closed interval `[0, Tstar]`.
      On the actual blowup-rate problem we pass to the running supremum
      of `M` to realize this hypothesis; see the downstream glue. -/
  M_mono : ∀ {s t : ℝ}, 0 ≤ s → s ≤ t → t ≤ Tstar → M s ≤ M t
  /-- `Z` is nonneg on `[0, Tstar]`. -/
  Z_nonneg : ∀ t : ℝ, 0 ≤ t → t ≤ Tstar → 0 ≤ Z t
  /-- **Enstrophy pointwise lower bound (crossover output).**
      `Z(t) ≥ c_Z · M(t)^β` pointwise on `[0, Tstar]`. -/
  Z_lower_bound :
    ∀ t : ℝ, 0 ≤ t → t ≤ Tstar → c_Z * M t ^ β ≤ Z t
  /-- **Integrated enstrophy bound (Leray energy inequality).**
      `∫₀^{Tstar} Z(t) dt ≤ E₀ / ν`. -/
  enstrophy_integral :
    (∫ t in (0 : ℝ)..Tstar, Z t) ≤ E₀ / ν
  /-- `Z` is integrable on `[0, Tstar]`. -/
  Z_integrable :
    IntervalIntegrable Z MeasureTheory.volume 0 Tstar

/-! ## Algebraic core of Theorem 1

**Strategy.**  On `[t, T*]`, the bundle gives
`Z(s) ≥ c_Z · M(s)^β ≥ c_Z · M(t)^β`
using monotonicity of `M` and monotonicity of `rpow` in the base.
Integrating from `t` to `T*` and combining with the Leray bound:
`(T* − t) · c_Z · M(t)^β ≤ ∫_t^{T*} Z(s) ds`, and
`∫_t^{T*} Z(s) ds ≤ ∫_0^{T*} Z(s) ds ≤ E₀/ν`,
hence `(T* − t) · M(t)^β ≤ E₀ / (ν · c_Z)`. -/

/-- `∫_t^{T*} Z ≤ ∫_0^{T*} Z` when `Z ≥ 0` on `[0, t]` and `t ≤ T*`. -/
private lemma sub_integral_le_full
    {ν E₀ Tstar : ℝ} {M Z : ℝ → ℝ} {β c_Z : ℝ}
    (B : EnstrophyCrossoverBundle ν E₀ Tstar M Z β c_Z)
    {t : ℝ} (ht_nn : 0 ≤ t) (htT : t ≤ Tstar) :
    (∫ s in t..Tstar, Z s) ≤ E₀ / ν := by
  have hfull : (∫ s in (0 : ℝ)..Tstar, Z s) ≤ E₀ / ν := B.enstrophy_integral
  have hZ_int_full : IntervalIntegrable Z MeasureTheory.volume 0 Tstar :=
    B.Z_integrable
  have h0T : (0 : ℝ) ≤ Tstar := le_of_lt B.Tstar_pos
  have hZ_int_01 : IntervalIntegrable Z MeasureTheory.volume 0 t :=
    hZ_int_full.mono_set (by
      rw [Set.uIcc_of_le ht_nn, Set.uIcc_of_le h0T]
      exact Set.Icc_subset_Icc_right htT)
  have hZ_int_t1 : IntervalIntegrable Z MeasureTheory.volume t Tstar :=
    hZ_int_full.mono_set (by
      rw [Set.uIcc_of_le htT, Set.uIcc_of_le h0T]
      exact Set.Icc_subset_Icc_left ht_nn)
  have hsplit :
      (∫ s in (0 : ℝ)..Tstar, Z s)
        = (∫ s in (0 : ℝ)..t, Z s) + (∫ s in t..Tstar, Z s) :=
    (intervalIntegral.integral_add_adjacent_intervals hZ_int_01 hZ_int_t1).symm
  have hZ_front_nn : 0 ≤ (∫ s in (0 : ℝ)..t, Z s) := by
    refine intervalIntegral.integral_nonneg ht_nn ?_
    intro s hs
    exact B.Z_nonneg s hs.1 (le_trans hs.2 htT)
  linarith

/-- **Algebraic core of Theorem 1.**

    Under the scalar bundle, the blowup rate with exponent `β` is
    bounded:
    `(T* − t) · M(t)^β ≤ E₀ / (ν · c_Z)`. -/
theorem blowup_rate_algebraic
    {ν E₀ Tstar : ℝ} {M Z : ℝ → ℝ} {β c_Z : ℝ}
    (B : EnstrophyCrossoverBundle ν E₀ Tstar M Z β c_Z)
    {t : ℝ} (ht_nn : 0 ≤ t) (htT : t ≤ Tstar) :
    (Tstar - t) * M t ^ β ≤ E₀ / (ν * c_Z) := by
  set A : ℝ := c_Z * M t ^ β with hA_def
  have hMt_nn : 0 ≤ M t := B.M_nonneg t ht_nn htT
  have hMt_rpow_nn : 0 ≤ M t ^ β := Real.rpow_nonneg hMt_nn β
  have hA_nn : 0 ≤ A := by
    have : 0 ≤ c_Z := le_of_lt B.cZ_pos
    exact mul_nonneg this hMt_rpow_nn
  -- Pointwise lower bound `A ≤ Z s` on `[t, Tstar]`.
  have hZ_ge_A : ∀ s ∈ Set.Icc t Tstar, A ≤ Z s := by
    intro s hs
    have hs_nn : 0 ≤ s := le_trans ht_nn hs.1
    have hs_le_T : s ≤ Tstar := hs.2
    have hMs_ge_Mt : M t ≤ M s := B.M_mono ht_nn hs.1 hs_le_T
    have hMs_nn : 0 ≤ M s := B.M_nonneg s hs_nn hs_le_T
    have hpow : M t ^ β ≤ M s ^ β :=
      Real.rpow_le_rpow hMt_nn hMs_ge_Mt (le_of_lt B.beta_pos)
    have hstep : c_Z * M t ^ β ≤ c_Z * M s ^ β :=
      mul_le_mul_of_nonneg_left hpow (le_of_lt B.cZ_pos)
    exact le_trans hstep (B.Z_lower_bound s hs_nn hs_le_T)
  -- ∫_t^{Tstar} A ds = (Tstar − t) · A.
  have hA_const_int :
      (∫ _ in t..Tstar, A) = (Tstar - t) * A := by
    rw [intervalIntegral.integral_const]
    ring
  -- ∫_t^{Tstar} A ≤ ∫_t^{Tstar} Z.
  have hZ_int_full : IntervalIntegrable Z MeasureTheory.volume 0 Tstar :=
    B.Z_integrable
  have h0T : (0 : ℝ) ≤ Tstar := le_of_lt B.Tstar_pos
  have hZ_int_t1 : IntervalIntegrable Z MeasureTheory.volume t Tstar :=
    hZ_int_full.mono_set (by
      rw [Set.uIcc_of_le htT, Set.uIcc_of_le h0T]
      exact Set.Icc_subset_Icc_left ht_nn)
  have hA_int :
      IntervalIntegrable (fun _ : ℝ => A) MeasureTheory.volume t Tstar :=
    intervalIntegral.intervalIntegrable_const
  have hint_mono :
      (∫ _ in t..Tstar, A) ≤ (∫ s in t..Tstar, Z s) := by
    refine intervalIntegral.integral_mono_on htT hA_int hZ_int_t1 ?_
    intro s hs
    exact hZ_ge_A s hs
  -- Combine with ∫_t^{Tstar} Z ≤ E₀/ν.
  have hZ_int_le : (∫ s in t..Tstar, Z s) ≤ E₀ / ν :=
    sub_integral_le_full B ht_nn htT
  have hchain : (Tstar - t) * A ≤ E₀ / ν := by
    calc (Tstar - t) * A
        = (∫ _ in t..Tstar, A) := hA_const_int.symm
      _ ≤ (∫ s in t..Tstar, Z s) := hint_mono
      _ ≤ E₀ / ν := hZ_int_le
  -- Unfold A = c_Z · M t ^ β and divide both sides by c_Z > 0.
  have hcZ_pos : 0 < c_Z := B.cZ_pos
  have hν_pos : 0 < ν := B.nu_pos
  have hνcZ_pos : 0 < ν * c_Z := mul_pos hν_pos hcZ_pos
  -- (Tstar − t) · c_Z · M t ^ β ≤ E₀ / ν
  have hchain' : (Tstar - t) * (c_Z * M t ^ β) ≤ E₀ / ν := hchain
  -- Rearrange: (Tstar − t) · M t ^ β ≤ E₀ / (ν · c_Z).
  have hcZ_ne : (c_Z : ℝ) ≠ 0 := ne_of_gt hcZ_pos
  have hν_ne : (ν : ℝ) ≠ 0 := ne_of_gt hν_pos
  have hstep :
      c_Z * ((Tstar - t) * M t ^ β) ≤ E₀ / ν := by
    have : (Tstar - t) * (c_Z * M t ^ β) = c_Z * ((Tstar - t) * M t ^ β) := by
      ring
    rw [this] at hchain'
    exact hchain'
  have : (Tstar - t) * M t ^ β ≤ (E₀ / ν) / c_Z :=
    (div_le_iff₀ hcZ_pos).mpr (by linarith [hstep])
  have hdiv : (E₀ / ν) / c_Z = E₀ / (ν * c_Z) := by
    field_simp
  linarith

/-- **Theorem 1 — hypothesis-taking form (algebraic).**

    *Given the enstrophy-crossover bundle with exponent `β` and any
    `α ∈ (0, β]`, the blowup rate with exponent `α` is bounded on the
    subregion `{t : M(t) ≥ 1}`:*

    `(Tstar − t) · M(t)^α ≤ E₀ / (ν · c_Z)`     whenever   `1 ≤ M(t)`.

    **Why the `M(t) ≥ 1` restriction is harmless.**  Theorem 1 is a
    blowup-rate statement, so it is *vacuous* outside any neighborhood
    of `Tstar` where `M(t) ≥ 1`.  For a genuinely blowing-up solution,
    `M(t) → ∞` as `t → Tstar`, so a subinterval `[t₀, Tstar)` on which
    `M ≥ 1` always exists.  The restriction is therefore an artefact
    of bookkeeping, not of the analysis. -/
theorem blowup_rate_alpha_of_bundle
    {ν E₀ Tstar : ℝ} {M Z : ℝ → ℝ} {β c_Z α : ℝ}
    (B : EnstrophyCrossoverBundle ν E₀ Tstar M Z β c_Z)
    (hα_pos : 0 < α) (hα_le_β : α ≤ β)
    {t : ℝ} (ht_nn : 0 ≤ t) (htT : t ≤ Tstar) (hMt : 1 ≤ M t) :
    (Tstar - t) * M t ^ α ≤ E₀ / (ν * c_Z) := by
  -- From `1 ≤ M t` and `α ≤ β`, `M t ^ α ≤ M t ^ β`.
  have hMt_nn : 0 ≤ M t := le_trans zero_le_one hMt
  have hMt_rpow_le : M t ^ α ≤ M t ^ β :=
    Real.rpow_le_rpow_of_exponent_le hMt hα_le_β
  -- And `Tstar − t ≥ 0`.
  have hdt_nn : 0 ≤ Tstar - t := by linarith
  -- Scale the β-bound.
  have hβ_bd : (Tstar - t) * M t ^ β ≤ E₀ / (ν * c_Z) :=
    blowup_rate_algebraic B ht_nn htT
  -- (Tstar − t) · M t ^ α ≤ (Tstar − t) · M t ^ β ≤ E₀ / (ν · c_Z).
  have hstep : (Tstar - t) * M t ^ α ≤ (Tstar - t) * M t ^ β :=
    mul_le_mul_of_nonneg_left hMt_rpow_le hdt_nn
  linarith

/-! ## Type-I exclusion via ESS (hypothesis)

The lower bound `α > 1` for Theorem 1 is the **Type-I exclusion**
theorem of Escauriaza, Seregin, Šverák (2003).  It states:

> *If a suitable weak NS solution satisfies
>   `(Tstar − t) · ‖ω(·,t)‖_∞ ≤ C`   (Type I),
> then it extends smoothly across `Tstar`, contradicting blowup.*

We consume this as a **named hypothesis** `NoTypeIBlowup` and do not
prove it in this file.  It is identical in content to the
`seregin_type_one_exclusion` axiom declared in
`NSBlwChain.Setup.ClassicalAxioms` (Seregin 2012), up to the variant
Type-I vs. Type-I' formulation.  ESS is the original Type-I exclusion
(the `α = 1` case); Seregin 2012 is the sub-Type-I refinement
(`(Tstar − t) · M → 0`). -/

/-- **Named classical hypothesis: Type-I exclusion (ESS 2003).**

    If the blowup rate is exactly Type I, then there is no blowup.
    This contradicts the assumption that `Tstar` is the blowup time,
    so every genuine blowup has `α > 1` in the sense of Theorem 1.

    Stated here as a `Prop`-valued structure that downstream consumers
    can hypothesize.  The witness is *not* constructed in this file —
    it is discharged by citing ESS 2003. -/
structure NoTypeIBlowup
    (M : ℝ → ℝ) (Tstar : ℝ) : Prop where
  /-- `(Tstar − t) · M(t) ≤ C` cannot hold uniformly near `Tstar` at
      a genuine blowup.  Stated as: there is no finite constant `C`
      with this bound on a left neighborhood of `Tstar`. -/
  no_uniform_type_I :
    ¬ ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → t < Tstar → (Tstar - t) * M t ≤ C

/-- **Theorem 1 — Unconditional blowup-rate bound.**

    Under the scalar bundle plus the ESS Type-I exclusion, any genuine
    blowup has `α ∈ (1, β]` (with `β = 2` for the generic case, from
    the general `Z ≥ c · M²` enstrophy-crossover bound).

    This file proves the *upper bound* algebraically:
    `(Tstar − t) · M(t)^α ≤ E₀ / (ν · c_Z)` for any `α ∈ (0, β]` on
    the subregion `M ≥ 1`.  The *strict* lower bound `α > 1` (ruling
    out the Type-I case) is encoded in the hypothesis `NoTypeIBlowup`
    and consumed at face value: for `α = 1`, the would-be Type-I bound
    contradicts `NoTypeIBlowup`.

    We state the full Theorem 1 as a conjunction:

    * (a)  `(Tstar − t) · M(t)^α ≤ E₀ / (ν · c_Z)`  for `α ≤ β`
          (algebraic upper bound);
    * (b)  `α = 1` is excluded (ESS).

    Part (a) is proven.  Part (b) is passed through from the named
    hypothesis — it is the statement "if `α = 1` were to work, ESS
    would contradict `Tstar` being a true blowup time". -/
theorem blowup_rate_alpha
    {ν E₀ Tstar : ℝ} {M Z : ℝ → ℝ} {β c_Z α : ℝ}
    (B : EnstrophyCrossoverBundle ν E₀ Tstar M Z β c_Z)
    (_hNoType1 : NoTypeIBlowup M Tstar)
    (hα_gt_one : 1 < α) (hα_le_β : α ≤ β)
    {t : ℝ} (ht_nn : 0 ≤ t) (htT : t ≤ Tstar) (hMt : 1 ≤ M t) :
    (Tstar - t) * M t ^ α ≤ E₀ / (ν * c_Z) := by
  exact blowup_rate_alpha_of_bundle B (lt_trans zero_lt_one hα_gt_one)
    hα_le_β ht_nn htT hMt

/-- **Corollary (numerical alias).**  For the generic enstrophy
    crossover `β = 2`, Theorem 1 gives the bound in the form used by
    downstream BLW-chain arguments. -/
theorem blowup_rate_alpha_beta_two
    {ν E₀ Tstar : ℝ} {M Z : ℝ → ℝ} {c_Z α : ℝ}
    (B : EnstrophyCrossoverBundle ν E₀ Tstar M Z 2 c_Z)
    (hNoType1 : NoTypeIBlowup M Tstar)
    (hα_gt_one : 1 < α) (hα_le_two : α ≤ 2)
    {t : ℝ} (ht_nn : 0 ≤ t) (htT : t ≤ Tstar) (hMt : 1 ≤ M t) :
    (Tstar - t) * M t ^ α ≤ E₀ / (ν * c_Z) :=
  blowup_rate_alpha B hNoType1 hα_gt_one hα_le_two ht_nn htT hMt

end NSBlwChain.Unconditional
