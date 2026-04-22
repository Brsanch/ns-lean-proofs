-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib

/-!
# Caveat C1 — Growth-moment coverage (Jordan decomposition)

This file formalizes **Proposition C1** from the companion note
`paper/ns_regularity_caveats_formal.md`, the growth-moment packaging
used at §12.4 Step 7 of the BLW-gradient chain.

## Mathematical content

Let `M : ℝ → ℝ` be the `L∞`-vorticity envelope.  By Lemma C2.1,
`M` is locally Lipschitz on `[0, T*)`, hence absolutely continuous
and a.e.-differentiable.  Write

  `G := {t : Ṁ(t) ≥ 0}`,   `D := {t : Ṁ(t) < 0}`.

The integrated form of `Ṁ ≤ Φ(M)` on the growth set `G`, combined with
the trivial bound `Ṁ ≤ 0 ≤ Φ(M)` on the decay set `D`, yields a
total-variation inequality

  `M(t) - M(s) ≤ ∫_s^t Φ(M(τ)) dτ`  for `s ≤ t`.

The FTC proof of this inequality itself is deferred to a separate
pass (it uses Lebesgue-Stieltjes machinery on the a.e. derivative
of `M`; see §C1 of the paper).  Here we bundle the hypothesis form
and derive the two clean algebraic corollaries that downstream
consumers need:

* **Monotone case** (Φ ≤ 0 throughout): `M(t) ≤ M(0)` for all `t ≥ 0`.
* **Pointwise form**: from the hypothesis `∀ s ≤ t, M(t) - M(s) ≤
  ∫_s^t Φ(M(τ)) dτ`, setting `s = 0` gives
  `M(t) ≤ M(0) + ∫_0^t Φ(M(τ)) dτ`.

These are the exact shapes needed by §12.5 + §13.

## Structural organization

`GrowthMomentBundle` packages:
1. Lipschitz regularity of `M` on `[0, T)`.
2. The a.e. pointwise inequality `Ṁ(t) ≤ Φ(M(t))` on the growth set.
3. Integrability of `Φ ∘ M` on `[0, T)` (needed for the integrated
   form to be finite).
4. The integrated (total-variation) form
   `∀ s ≤ t, M(t) - M(s) ≤ ∫_s^t Φ(M(τ)) dτ`
   as a *hypothesis* (downstream FTC consumers prove this).

The algebraic consequences below unpack the bundle.

## References

* Companion note §C1 (caveats_formal.md): Jordan decomposition.
* Evans, *PDE* 2nd ed., §5.8: Lipschitz → abs. continuous → FTC.
-/

namespace NSBlwChain.Caveats

open MeasureTheory Set Filter
open scoped Topology

/-- **Growth-moment bundle (Proposition C1 data).**

    Packages an `L∞`-envelope `M : ℝ → ℝ` with:
    * Lipschitz regularity on `[0, T)` (provides a.e. differentiability);
    * A growth-rate function `Φ : ℝ → ℝ`, thought of as
      `Φ(m) = C · m^2 · log(m⁺)` or similar non-decreasing moment bound;
    * An *integrated inequality*
      `M(t) - M(s) ≤ ∫_s^t Φ(M(τ)) dτ`   for all `0 ≤ s ≤ t < T`,
      taken as a hypothesis.  (The FTC proof is deferred.)

    The `K` parameter is the Lipschitz constant of `M` (from Lemma C2.1,
    `K = ‖∂_t ω‖_{L∞}` on compact sub-intervals).  `T` is the maximal
    smoothness time; `[0, T)` is the domain of interest.

    The bundle is designed so that downstream theorems consume the
    *integrated form* (field `hIntegratedBound`) rather than having to
    know about `Ṁ` or measure theory directly. -/
structure GrowthMomentBundle where
  /-- The `L∞`-vorticity envelope. -/
  M : ℝ → ℝ
  /-- The growth-rate bound function.  No sign assumption by default. -/
  Φ : ℝ → ℝ
  /-- Maximal smoothness time. -/
  T : ℝ
  /-- Positivity of `T`. -/
  hTpos : 0 < T
  /-- Lipschitz constant of `M` on `[0, T)`. -/
  K : NNReal
  /-- Lipschitz regularity of `M` on the full line (extended by
      constant outside `[0, T)` is the usual practice; here we record
      the global Lipschitz statement, which is the form Rademacher
      consumes). -/
  hM_lip : LipschitzWith K M
  /-- Integrability of `Φ ∘ M` on every compact sub-interval of
      `[0, T)`.  Needed for the right-hand-side integral in
      `hIntegratedBound` to be finite. -/
  hInt_loc : ∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t < T →
    IntervalIntegrable (fun τ => Φ (M τ)) MeasureTheory.volume s t
  /-- **The main hypothesis (integrated form).**  Total-variation
      bound derived in the companion note via Jordan decomposition +
      FTC.  Consumed here as a structural input. -/
  hIntegratedBound : ∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t < T →
    M t - M s ≤ ∫ τ in s..t, Φ (M τ)

namespace GrowthMomentBundle

variable (B : GrowthMomentBundle)

/-- **Pointwise corollary from the integrated form.**

    Setting `s = 0` in the integrated bound gives the exact shape
    consumed by §12.5 and §13 of the paper:

      `M(t) ≤ M(0) + ∫_0^t Φ(M(τ)) dτ`    for `0 ≤ t < T`. -/
theorem pointwise_bound ⦃t : ℝ⦄ (h0t : 0 ≤ t) (htT : t < T B) :
    B.M t ≤ B.M 0 + ∫ τ in (0 : ℝ)..t, B.Φ (B.M τ) := by
  have h := B.hIntegratedBound (le_refl 0) h0t htT
  -- `h : M t - M 0 ≤ ∫ τ in 0..t, Φ (M τ)`
  linarith

/-- **Monotone case.**  If the growth-rate `Φ` is pointwise
    non-positive on the range of `M` (the "no-growth scenario":
    the decay set `D` is everything), then `M` is non-increasing
    on `[0, T)`.  Consequently `M(t) ≤ M(0)` for all `t ∈ [0, T)`.

    Proof: the RHS of the integrated bound is ≤ 0 since the
    integrand is ≤ 0 on `[0, t]`. -/
theorem M_le_M0_of_Φ_nonpos
    (hΦ_nonpos : ∀ t : ℝ, 0 ≤ t → t < T B → B.Φ (B.M t) ≤ 0)
    ⦃t : ℝ⦄ (h0t : 0 ≤ t) (htT : t < T B) :
    B.M t ≤ B.M 0 := by
  -- Integrated form.
  have h := B.pointwise_bound h0t htT
  -- The integrand is ≤ 0 on [0, t], so the integral is ≤ 0.
  have h_int_nonpos : ∫ τ in (0 : ℝ)..t, B.Φ (B.M τ) ≤ 0 := by
    -- Use `intervalIntegral.integral_nonpos`.
    have hle : (0 : ℝ) ≤ t := h0t
    apply intervalIntegral.integral_nonpos hle
    intro τ hτ
    -- hτ : τ ∈ Set.Ioc 0 t
    have hτ_nonneg : 0 ≤ τ := le_of_lt hτ.1
    have hτ_ltT : τ < T B := lt_of_le_of_lt hτ.2 htT
    exact hΦ_nonpos τ hτ_nonneg hτ_ltT
  linarith

/-- **Monotonicity refinement.**  Under the same non-positivity
    hypothesis, `M` is non-increasing on `[0, T)` in the two-point
    form `s ≤ t ⟹ M(t) ≤ M(s)`. -/
theorem M_antitone_of_Φ_nonpos
    (hΦ_nonpos : ∀ t : ℝ, 0 ≤ t → t < T B → B.Φ (B.M t) ≤ 0)
    ⦃s t : ℝ⦄ (h0s : 0 ≤ s) (hst : s ≤ t) (htT : t < T B) :
    B.M t ≤ B.M s := by
  have h := B.hIntegratedBound h0s hst htT
  have h_int_nonpos : ∫ τ in s..t, B.Φ (B.M τ) ≤ 0 := by
    apply intervalIntegral.integral_nonpos hst
    intro τ hτ
    have hτ_nonneg : 0 ≤ τ := le_trans h0s (le_of_lt hτ.1)
    have hτ_ltT : τ < T B := lt_of_le_of_lt hτ.2 htT
    exact hΦ_nonpos τ hτ_nonneg hτ_ltT
  linarith

/-- **Sub-additivity in time.**  The total-variation form implies
    a splitting: for `0 ≤ r ≤ s ≤ t < T`,
      `M(t) - M(r) ≤ ∫_r^s Φ(M) + ∫_s^t Φ(M)`
    i.e., the bound is additive across subdivisions. -/
theorem integrated_bound_split
    ⦃r s t : ℝ⦄ (h0r : 0 ≤ r) (hrs : r ≤ s) (hst : s ≤ t)
    (htT : t < T B) :
    B.M t - B.M r ≤
      (∫ τ in r..s, B.Φ (B.M τ)) + (∫ τ in s..t, B.Φ (B.M τ)) := by
  have h0s : 0 ≤ s := le_trans h0r hrs
  have hsT : s < T B := lt_of_le_of_lt hst htT
  have h1 := B.hIntegratedBound h0r hrs hsT
  have h2 := B.hIntegratedBound h0s hst htT
  -- h1 : M s - M r ≤ ∫_r^s Φ(M)
  -- h2 : M t - M s ≤ ∫_s^t Φ(M)
  linarith

end GrowthMomentBundle

/-! ## Structural lemmas decoupled from the bundle

Two small self-contained lemmas that downstream consumers sometimes
use without needing the full bundle.  Both are pure algebra on ℝ. -/

/-- **Pointwise form from hypothesis.**  If a function `M : ℝ → ℝ`
    satisfies the integrated inequality

      `∀ s t, 0 ≤ s ≤ t < T → M t - M s ≤ ∫_s^t Φ(M(τ)) dτ`,

    then setting `s = 0` gives the pointwise form

      `M(t) ≤ M(0) + ∫_0^t Φ(M(τ)) dτ`.

    Purely algebraic — no Lipschitz or integrability hypothesis
    needed at this level of the statement.  Downstream, the
    integrability is needed to make the RHS finite. -/
theorem M_pointwise_of_integrated
    {M Φ : ℝ → ℝ} {T : ℝ}
    (hI : ∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t < T →
      M t - M s ≤ ∫ τ in s..t, Φ (M τ))
    ⦃t : ℝ⦄ (h0t : 0 ≤ t) (htT : t < T) :
    M t ≤ M 0 + ∫ τ in (0 : ℝ)..t, Φ (M τ) := by
  have := hI (le_refl 0) h0t htT
  linarith

/-- **Monotonicity from pointwise non-positive bound.**  If
    `M(t) - M(0) ≤ 0` for all `t ∈ [0, T)`, then `M(t) ≤ M(0)`.
    Trivial re-packaging; kept here for readability of downstream
    proofs. -/
theorem M_le_init_of_diff_nonpos
    {M : ℝ → ℝ} {T : ℝ}
    (h : ∀ ⦃t : ℝ⦄, 0 ≤ t → t < T → M t - M 0 ≤ 0)
    ⦃t : ℝ⦄ (h0t : 0 ≤ t) (htT : t < T) :
    M t ≤ M 0 := by
  have := h h0t htT
  linarith

/-! ## Sanity check

A trivial example: constant `M` with `Φ ≡ 0` satisfies the bundle
trivially, and the pointwise form reduces to `M(t) ≤ M(0)` as an
equality.  The example exercises the structure layout. -/

example (c : ℝ) :
    let M : ℝ → ℝ := fun _ => c
    ∀ t, M t ≤ M 0 := by
  intro M t
  simp [M]

end NSBlwChain.Caveats
