-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib

/-!
# §C2.4 — Identity theorem for real-analytic functions

This file formalizes the **identity theorem** machinery used by
§C2.4 of the companion note `ns_regularity_caveats_formal.md`:
the refinement of caveat C2 showing that the accidental
argmax-multiplicity set `𝓝_acc ⊂ [0, T^*)` of the BLW chain is
**discrete** (at most countable), not merely Lebesgue-measure-zero.

## Classical content

The key input is the identity theorem for real-analytic functions
of one variable: if `f : ℝ → ℝ` is real-analytic on an open set `U`
(in the sense of `AnalyticOnNhd ℝ f U`) and the coincidence set
`{t ∈ U : f t = g t}` has an accumulation point inside a
preconnected component of `U`, then `f = g` throughout that
component.  Mathlib provides this as
`AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`.

The corresponding "dichotomy" statement
`eqOn_or_eventually_ne_of_preconnected` furnishes the
**discrete-off-a-component** conclusion: if `f ≠ g` on some
preconnected open `U`, then `{t ∈ U : f t = g t}` is codiscrete
within `U` — i.e. the exceptional set is at most discrete.

## How this is used by §C2.4

For the BLW chain, take `f = φ(x₁, ·)` and `g = φ(x₂, ·)`, where
`φ = |ω|²` and `x₁, x₂` are two candidate argmax points.  Two
possibilities:

* `f ≡ g` on `(0, T^*)`: the pair `(x₁, x₂)` is a *persistent
  symmetry pair* (Proposition C2.6), which is absorbed by the
  Danskin envelope theorem (`Caveats/C2_Envelope.lean`) via
  `danskin_envelope_consistent`.

* `f ≢ g`: the set of tie-times
  `{t : f t = g t}` is discrete in the sense of `codiscreteWithin`,
  hence at most countable.

Combined over a countable dense family of rational pairs
`(x₁, x₂)`, the *accidental* multiplicity set becomes a countable
union of discrete sets, hence at most countable and Lebesgue-null.
This is the sharp version of caveat C2 promised in §C2.4.

## Scope of this file

This file intentionally stays on the classical-analysis side.
The NS-specific real-analyticity of the flow map
`t ↦ u(·, t)` (Kato 1967, Foias–Temam 1979) is an *axiom* of
the consuming §C2.4 application; it is not formalized here.
The lemmas below simply expose mathlib's identity theorem in the
exact shape §C2.4 consumes.

## References

* Krantz–Parks, *A Primer of Real Analytic Functions*, Theorem 1.2.6.
* Kato, *Arch. Rat. Mech. Anal.* 25 (1967), 188–200 (time-analyticity
  of NS).
* Foias–Temam, *J. Funct. Anal.* 33 (1979), 316–343 (complex
  strip of analyticity for NS on `𝕋³`).
* Giga–Kohn, *CPAM* 38 (1985), §2 (identity theorem applied to
  parabolic argmax trajectories).
* Companion note §C2.4 (`ns_regularity_caveats_formal.md`).
-/

namespace NSBlwChain.Analyticity

open Set Filter Topology

/-! ## Identity theorem — pair form -/

/-- **Identity theorem (real form).**

    If `f, g : ℝ → ℝ` are real-analytic on a neighborhood of a
    preconnected open set `U ⊆ ℝ` and agree *frequently in the
    punctured filter* at some `t₀ ∈ U`, then `f = g` throughout
    `U`.

    This is a thin wrapper around mathlib's
    `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`
    specialized to `𝕜 = E = ℝ`. -/
theorem eqOn_of_frequently_eq
    {f g : ℝ → ℝ} {U : Set ℝ} {t₀ : ℝ}
    (hf : AnalyticOnNhd ℝ f U) (hg : AnalyticOnNhd ℝ g U)
    (hU : IsPreconnected U) (h₀ : t₀ ∈ U)
    (hfg : ∃ᶠ t in 𝓝[≠] t₀, f t = g t) :
    EqOn f g U :=
  hf.eqOn_of_preconnected_of_frequently_eq hg hU h₀ hfg

/-- **Identity theorem via accumulation of the coincidence set.**

    Reformulation of `eqOn_of_frequently_eq` that takes an
    *accumulation-point* hypothesis on the set `{t : f t = g t}`
    (using `AccPt`) instead of a `Filter.Frequently` hypothesis.
    This is the form matched to §C2.4's usage: "the zero set of
    `φ_{x₁,x₂}` has an accumulation point, hence `φ_{x₁,x₂} ≡ 0`". -/
theorem eqOn_of_accPt
    {f g : ℝ → ℝ} {U : Set ℝ} {t₀ : ℝ}
    (hf : AnalyticOnNhd ℝ f U) (hg : AnalyticOnNhd ℝ g U)
    (hU : IsPreconnected U) (h₀ : t₀ ∈ U)
    (hacc : AccPt t₀ (𝓟 {t : ℝ | f t = g t})) :
    EqOn f g U := by
  -- Convert `AccPt` on the principal filter to `Filter.Frequently`.
  have hfreq : ∃ᶠ t in 𝓝[≠] t₀, f t = g t := by
    have := (accPt_iff_frequently_nhdsNE).mp hacc
    exact this
  exact eqOn_of_frequently_eq hf hg hU h₀ hfreq

/-! ## Dichotomy: identical, or coincidence set is codiscrete -/

/-- **Coincidence dichotomy.**

    On a preconnected open set `U`, two real-analytic functions
    are either identically equal on `U`, or else the coincidence
    set `{t ∈ U : f t = g t}` is codiscrete within `U` — i.e.
    the *disagreement* set is residual / the coincidence set has
    no accumulation points in `U`.

    Wrapper around mathlib's
    `AnalyticOnNhd.eqOn_or_eventually_ne_of_preconnected`. -/
theorem eqOn_or_codiscrete_ne
    {f g : ℝ → ℝ} {U : Set ℝ}
    (hf : AnalyticOnNhd ℝ f U) (hg : AnalyticOnNhd ℝ g U)
    (hU : IsPreconnected U) :
    EqOn f g U ∨ ∀ᶠ t in codiscreteWithin U, f t ≠ g t :=
  hf.eqOn_or_eventually_ne_of_preconnected hg hU

/-- **Discrete-set conclusion for non-identical analytic pairs.**

    Contrapositive-flavored shape of `eqOn_or_codiscrete_ne`: if
    `f` and `g` are real-analytic on a preconnected open `U` and
    *are not* identically equal on `U`, then the coincidence set
    `{t ∈ U : f t = g t}` is codiscrete within `U` — each point
    of the coincidence set is isolated from the rest (relative to
    `U`).

    This is the formal content of the §C2.4 claim: "outside of
    persistent-symmetry pairs, accidental argmax ties form an
    at-most-countable discrete set". -/
theorem codiscrete_eq_of_not_eqOn
    {f g : ℝ → ℝ} {U : Set ℝ}
    (hf : AnalyticOnNhd ℝ f U) (hg : AnalyticOnNhd ℝ g U)
    (hU : IsPreconnected U) (hne : ¬ EqOn f g U) :
    ∀ᶠ t in codiscreteWithin U, f t ≠ g t :=
  (eqOn_or_codiscrete_ne hf hg hU).resolve_left hne

/-! ## BLW specialization: pair of slices `φ(x, ·)` -/

/-- **§C2.4 specialization.**

    The BLW caveat setting.  Let `φ : X → ℝ → ℝ` be a field of
    real-analytic time-slices on a preconnected open time interval
    `U ⊆ ℝ`, and let `x₁, x₂ : X` be two candidate argmax points.
    If the slices agree at an accumulation point inside `U` — i.e.
    the tie set `{t : φ x₁ t = φ x₂ t}` accumulates at some `t₀ ∈ U`
    — then the slices are identically equal throughout `U`, i.e.
    `(x₁, x₂)` is a *persistent-symmetry pair* in the sense of
    §C2.4.

    Equivalently: if `(x₁, x₂)` is *not* a persistent-symmetry pair,
    the tie set is codiscrete (at most countable, discrete, and of
    Lebesgue measure zero). -/
theorem slices_eqOn_of_accPt_tie
    {X : Type*} (φ : X → ℝ → ℝ) {x₁ x₂ : X} {U : Set ℝ} {t₀ : ℝ}
    (hφ₁ : AnalyticOnNhd ℝ (φ x₁) U)
    (hφ₂ : AnalyticOnNhd ℝ (φ x₂) U)
    (hU : IsPreconnected U) (h₀ : t₀ ∈ U)
    (hacc : AccPt t₀ (𝓟 {t : ℝ | φ x₁ t = φ x₂ t})) :
    EqOn (φ x₁) (φ x₂) U :=
  eqOn_of_accPt hφ₁ hφ₂ hU h₀ hacc

/-- **§C2.4 discrete-tie conclusion.**

    Converse packaging of `slices_eqOn_of_accPt_tie`: if two
    analytic slices are *not* identically equal on the preconnected
    open `U`, their tie set is codiscrete within `U`.

    This is the §C2.4 statement used by the BLW chain: every
    accidental-multiplicity time is isolated. -/
theorem slices_tie_codiscrete_of_not_eqOn
    {X : Type*} (φ : X → ℝ → ℝ) {x₁ x₂ : X} {U : Set ℝ}
    (hφ₁ : AnalyticOnNhd ℝ (φ x₁) U)
    (hφ₂ : AnalyticOnNhd ℝ (φ x₂) U)
    (hU : IsPreconnected U) (hne : ¬ EqOn (φ x₁) (φ x₂) U) :
    ∀ᶠ t in codiscreteWithin U, φ x₁ t ≠ φ x₂ t :=
  codiscrete_eq_of_not_eqOn hφ₁ hφ₂ hU hne

/-! ## Sanity example: zeros of `sin` are isolated on `(0, π)` -/

section Examples

open Real

/-- Real-analyticity of `sin` on an arbitrary set (wrapper). -/
lemma analyticOnNhd_sin_on (s : Set ℝ) : AnalyticOnNhd ℝ sin s :=
  fun _ _ ↦ Real.analyticAt_sin

/-- Real-analyticity of the zero function. -/
lemma analyticOnNhd_zero_on (s : Set ℝ) : AnalyticOnNhd ℝ (fun _ : ℝ => (0 : ℝ)) s :=
  fun _ _ ↦ analyticAt_const

/-- **Sanity check.**

    `sin` is not identically zero on the preconnected open interval
    `(0, π)` (e.g. `sin (π/2) = 1 ≠ 0`), so its zero set inside
    `(0, π)` is codiscrete within `(0, π)` — i.e. each zero of
    `sin` in `(0, π)` is isolated.

    This is the miniature exemplar of the §C2.4 mechanism: the
    "tie times" `{t : sin t = 0}` inside a component form a
    discrete set because `sin ≢ 0`. -/
example :
    ∀ᶠ t in codiscreteWithin (Set.Ioo (0 : ℝ) π), sin t ≠ 0 := by
  -- `sin` and the zero function are both real-analytic on `(0, π)`.
  have hf : AnalyticOnNhd ℝ sin (Set.Ioo (0 : ℝ) π) :=
    analyticOnNhd_sin_on _
  have hg : AnalyticOnNhd ℝ (fun _ : ℝ => (0 : ℝ)) (Set.Ioo (0 : ℝ) π) :=
    analyticOnNhd_zero_on _
  -- `(0, π)` is preconnected.
  have hU : IsPreconnected (Set.Ioo (0 : ℝ) π) := isPreconnected_Ioo
  -- `sin` is not identically zero on `(0, π)` because `sin (π/2) = 1`.
  have hne : ¬ EqOn sin (fun _ : ℝ => (0 : ℝ)) (Set.Ioo (0 : ℝ) π) := by
    intro hEq
    have hmem : (π / 2) ∈ Set.Ioo (0 : ℝ) π := by
      refine ⟨?_, ?_⟩
      · exact half_pos Real.pi_pos
      · exact half_lt_self Real.pi_pos
    have hzero : sin (π / 2) = 0 := hEq hmem
    have hone : sin (π / 2) = 1 := Real.sin_pi_div_two
    linarith
  -- Conclude via the dichotomy.
  simpa using codiscrete_eq_of_not_eqOn hf hg hU hne

end Examples

end NSBlwChain.Analyticity
