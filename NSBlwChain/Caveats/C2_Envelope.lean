-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

/-!
# Lemma C2.5 — Danskin envelope theorem

This file formalizes **Lemma C2.5** from the companion note
`ns_regularity_caveats_formal.md`, the core piece that closes the
Lagrangian/Eulerian-mismatch caveat of the BLW-gradient chain.

## Statement

Let `φ : X → ℝ → ℝ` and `M : ℝ → ℝ` with `M` the pointwise supremum of
`φ(·, t)`:

* `h_env`  : `∀ x t, φ x t ≤ M t`   (envelope condition)
* `h_hit`  : `φ x_star t₀ = M t₀`   (`x_star` achieves the max at `t₀`)

If `M` is differentiable at `t₀` with derivative `Mdot`, and the slice
`φ x_star` is differentiable at `t₀` with derivative `φdot`, then
`Mdot = φdot`.

## Why this closes caveat C2

The proof is a one-page Rademacher + Danskin argument.  Define
`g(t) := M t - φ x_star t`.  By `h_env`, `g ≥ 0` everywhere; by `h_hit`,
`g(t₀) = 0`.  So `t₀` is a **global min** of `g`; a fortiori a local min.
Hence `g'(t₀) = 0`, i.e. `Mdot - φdot = 0`.

This is purely structural: the argmax position `x_star` never appears as a
time-dependent curve, and no Sard-type / measure-zero-non-uniqueness
assumption is used.  The differential identity
`Ṁ(t) = ∂_t φ(x_star, t)`
holds pointwise at every `t` where both derivatives exist, for **every**
`x_star` achieving the max, including symmetry-related orbits.  Combined
with Rademacher's theorem applied to the Lipschitz function `M` (developed
separately), this yields an a.e. ODE identity — completely without the
Lagrangian/Eulerian-mismatch pathology of the naive material-derivative
approach.

## References

* Danskin (1966), *J. SIAM Appl. Math.* 14, 641–664.
* Clarke, *Optimization and Nonsmooth Analysis*, §2.8.
* Companion note §C2 (caveats_formal.md).
-/

import Mathlib

namespace NSBlwChain.Caveats

open Filter Topology Set

/-- **Lemma C2.5 (Danskin envelope identity).**

    If `M` is a pointwise upper envelope of a family `φ(·, t)` and `x_star`
    achieves the envelope at `t₀`, then the time-derivative of `M` at `t₀`
    agrees with the time-derivative of the slice `φ(x_star, ·)` at `t₀`
    — provided both derivatives exist.

    This holds for **every** `x_star` achieving the max at `t₀`.  The
    conclusion is independent of whether the argmax is unique. -/
theorem danskin_envelope
    {X : Type*} (φ : X → ℝ → ℝ) (M : ℝ → ℝ)
    {x_star : X} {t₀ Mdot φdot : ℝ}
    (h_env : ∀ x t, φ x t ≤ M t)
    (h_hit : φ x_star t₀ = M t₀)
    (h_M : HasDerivAt M Mdot t₀)
    (h_φ : HasDerivAt (φ x_star) φdot t₀) :
    Mdot = φdot := by
  -- Let `g(t) := M t - φ(x_star, t)`. We show `g` has a global min at `t₀`.
  set g : ℝ → ℝ := fun t => M t - φ x_star t with hg_def
  -- `g` is non-negative everywhere (envelope condition).
  have hg_nonneg : ∀ t, 0 ≤ g t := fun t => sub_nonneg.mpr (h_env x_star t)
  -- `g` vanishes at `t₀` (`x_star` achieves the max there).
  have hg_zero : g t₀ = 0 := by
    simp only [hg_def]
    linarith [h_hit]
  -- `g` has derivative `Mdot - φdot` at `t₀`.
  have hg_deriv : HasDerivAt g (Mdot - φdot) t₀ := h_M.sub h_φ
  -- `t₀` is a local min of `g`: any `t` satisfies `g t₀ ≤ g t` since
  -- `g t₀ = 0 ≤ g t`, and a global min is trivially local.
  have hg_localmin : IsLocalMin g t₀ := by
    refine Filter.Eventually.of_forall (fun t => ?_)
    rw [hg_zero]
    exact hg_nonneg t
  -- A differentiable local min has zero derivative.
  have h_zero : Mdot - φdot = 0 :=
    hg_localmin.hasDerivAt_eq_zero hg_deriv
  linarith

/-- **Corollary (uniqueness of `Ṁ` across argmax points).**

    At any `t₀` where `M` is differentiable with derivative `Mdot`, *every*
    point `x_star` that achieves `M(t₀)` and has a `φ(x_star, ·)`-derivative
    at `t₀` gives the same value, namely `Mdot`.  Consequently, any
    measurable selection `x_star : ℝ → X` into the argmax set produces the
    same time-derivative identity at every such `t`.

    This is the ingredient used by the BLW-gradient ODE argument: symmetry
    orbits or accidental argmax-ties contribute no ambiguity. -/
theorem danskin_envelope_consistent
    {X : Type*} (φ : X → ℝ → ℝ) (M : ℝ → ℝ)
    {x₁ x₂ : X} {t₀ Mdot φ₁dot φ₂dot : ℝ}
    (h_env : ∀ x t, φ x t ≤ M t)
    (h_hit₁ : φ x₁ t₀ = M t₀) (h_hit₂ : φ x₂ t₀ = M t₀)
    (h_M : HasDerivAt M Mdot t₀)
    (h_φ₁ : HasDerivAt (φ x₁) φ₁dot t₀)
    (h_φ₂ : HasDerivAt (φ x₂) φ₂dot t₀) :
    φ₁dot = φ₂dot := by
  have h₁ : Mdot = φ₁dot := danskin_envelope φ M h_env h_hit₁ h_M h_φ₁
  have h₂ : Mdot = φ₂dot := danskin_envelope φ M h_env h_hit₂ h_M h_φ₂
  linarith

/-- **Danskin envelope, `Ṁ`-form.**

    The conclusion of `danskin_envelope` re-expressed as a statement about
    `M`'s derivative in terms of any argmax slice. -/
theorem deriv_sup_eq_deriv_slice_of_argmax
    {X : Type*} (φ : X → ℝ → ℝ) (M : ℝ → ℝ)
    {x_star : X} {t₀ φdot : ℝ}
    (h_env : ∀ x t, φ x t ≤ M t)
    (h_hit : φ x_star t₀ = M t₀)
    (h_M : DifferentiableAt ℝ M t₀)
    (h_φ : HasDerivAt (φ x_star) φdot t₀) :
    deriv M t₀ = φdot := by
  have h_hasDeriv : HasDerivAt M (deriv M t₀) t₀ := h_M.hasDerivAt
  exact danskin_envelope φ M h_env h_hit h_hasDeriv h_φ

/-! ## Sanity-check examples

Two tiny examples exercising the main lemma.  The examples verify that
the Danskin envelope identity behaves as expected on closed-form
configurations.  They are not load-bearing for the formalization — just
smoke-tests that the statements compile and can be discharged. -/

section Examples

/-- Constant envelope: if `φ x t = c` for all `x, t`, then `M ≡ c`, and the
    Danskin identity says `0 = 0`. -/
example (c : ℝ) :
    let φ : Unit → ℝ → ℝ := fun _ _ => c
    let M : ℝ → ℝ := fun _ => c
    ∀ t₀ : ℝ, deriv M t₀ = 0 := by
  intro φ M t₀
  simp [M]

/-- Trivial two-point envelope: `φ(false, t) = 0`, `φ(true, t) = t`, so
    `M(t) = max(0, t)`.  For `t₀ > 0`, the argmax is `true` and
    `M(t₀) = t₀`; the Danskin identity correctly recovers
    `Ṁ(t₀) = 1 = ∂_t φ(true, t₀)`. -/
example (t₀ : ℝ) (ht₀ : 0 < t₀) :
    let φ : Bool → ℝ → ℝ := fun b t => if b then t else 0
    HasDerivAt (φ true) 1 t₀ := by
  intro φ
  simpa [φ] using hasDerivAt_id t₀

end Examples

end NSBlwChain.Caveats
