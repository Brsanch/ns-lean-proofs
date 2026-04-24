-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Setup.NSHypothesis

/-!
# Danskin envelope bundle at an argmax point

Packages the six envelope-related inputs consumed by the BLW
gradient-bound capstone:

* `M_fn : ℝ → ℝ` — the time-envelope function (abstract `t ↦ M(t)`).
* `h_M_fn_at_t : M_fn t = M` — pins the envelope value at the argmax
  time.
* `h_M_fn_deriv : HasDerivAt M_fn Mdot t` — time-differentiability of
  the envelope at `t`.
* `h_env_dom : ∀ y τ, |ω(τ, y)|²/2 ≤ (M_fn τ)²/2` — the envelope
  dominates the scalar `|ω|²/2` on all `(τ, y)`.
* `h_env_hit : |ω(t, xStar)|²/2 = (M_fn t)²/2` — the envelope is
  attained at `(t, xStar)`.
* `h_slice_diff : DifferentiableAt ℝ (τ ↦ |ω(τ, xStar)|²/2) t` —
  differentiability of the slice through the argmax.

These six inputs **collectively encode Danskin's envelope theorem at
`(t, xStar)`** — the statement that the time-derivative of
`sup_y |ω(τ, ·)|²/2` at `t` equals the partial time-derivative at the
argmax.  The bundle packages them as ergonomic preconditions without
deriving them from `NSEvolutionAxioms` alone (which lacks decay at
infinity, required for the sup to exist).

## Future derivation roadmap (multi-session)

Deriving the bundle from `NSEvolutionAxioms` + `DecayAtInfinity`
requires:

1. **Sup existence** — `⨆_y |ω(τ, y)|²` is finite for every `τ ∈
   [0, T)` from polynomial decay + continuity.
2. **Argmax existence** — the sup is attained at a point `x*(τ) ∈
   Vec3` for every `τ`.
3. **Danskin's envelope theorem** — under the argmax uniqueness (at
   least locally around `t`) plus `C¹`-in-time regularity of `(τ, y) ↦
   |ω(τ, y)|²`, the sup is differentiable at `t` with derivative equal
   to the partial time-derivative at the argmax.

Items (1)–(3) are classical but substantial; they are not discharged
in this file.  The structure below exists so that downstream consumers
can take the envelope bundle as a single hypothesis, matching the
ergonomics of `HessianInputs` (the Hessian-expansion bundle).

## Main result

* `EnvelopeAtArgmax` — the 6-item bundle.
* `gradient_bound_from_NSEvolutionAxioms_envelopeBundled` — top-level
  capstone taking the envelope bundle as a single argument in place
  of the six separate inputs.
-/

namespace NSBlwChain.BLW

open scoped BigOperators
open NSBlwChain

/-- **Danskin envelope bundle at the argmax point `(t, xStar)`.**

    Packages the six envelope inputs consumed by the BLW gradient-
    bound capstone.  These collectively encode the envelope content of
    Danskin's theorem applied to `(τ, y) ↦ |ω(τ, y)|²/2` at its argmax
    `(t, xStar)`. -/
structure EnvelopeAtArgmax
    (u : VelocityField) (t : ℝ) (xStar : Vec3)
    (M Mdot : ℝ) where
  /-- Time-envelope function `M_fn : ℝ → ℝ`. -/
  M_fn           : ℝ → ℝ
  /-- `M_fn` at the argmax time equals `M`. -/
  h_at_t         : M_fn t = M
  /-- `M_fn` is differentiable at `t` with derivative `Mdot`. -/
  h_deriv        : HasDerivAt M_fn Mdot t
  /-- `M_fn` dominates the scalar `|ω|²/2` on all `(τ, y)`. -/
  h_dom          : ∀ y τ : _,
    Vec3.dot (vorticity u τ y) (vorticity u τ y) / 2
      ≤ (M_fn τ) ^ 2 / 2
  /-- The envelope is attained at the argmax `(t, xStar)`. -/
  h_hit          :
    Vec3.dot (vorticity u t xStar) (vorticity u t xStar) / 2
      = (M_fn t) ^ 2 / 2
  /-- The slice through the argmax is differentiable in time at `t`. -/
  h_slice_diff   :
    DifferentiableAt ℝ
      (fun τ : ℝ =>
        Vec3.dot (vorticity u τ xStar) (vorticity u τ xStar) / 2) t

/-! ### Danskin envelope derivative

From the `EnvelopeAtArgmax` bundle alone (no further analytical input),
we derive the envelope time-derivative identity

  `deriv (fun τ => |ω(τ, xStar)|² / 2) t = M · Mdot`.

**Argument.**  Consider `g(τ) := (M_fn τ)²/2 - |ω(τ, xStar)|²/2`.
From `h_dom` applied at `y = xStar`, `g(τ) ≥ 0` everywhere.  From
`h_hit`, `g(t) = 0`.  Hence `g` has a global minimum at `t`.  Since
`g` is differentiable at `t` (via `h_deriv` + `h_slice_diff`),
`deriv g t = 0`, which rearranges to the claim.

This is a pointwise Danskin-envelope identity: the time-derivative
of `sup_y |ω(τ, y)|²/2` at the argmax time equals the partial time-
derivative evaluated at the argmax point, provided the envelope
reaches its pointwise evaluation at that point.
-/

/-- **Envelope time-derivative identity at the argmax.**

    From the `EnvelopeAtArgmax` bundle, the time-derivative of
    `τ ↦ |ω(τ, xStar)|² / 2` at `t` equals `M · Mdot`. -/
theorem EnvelopeAtArgmax.deriv_scalar_half_eq
    {u : VelocityField} {t : ℝ} {xStar : Vec3} {M Mdot : ℝ}
    (E : EnvelopeAtArgmax u t xStar M Mdot) :
    deriv (fun τ : ℝ =>
        Vec3.dot (vorticity u τ xStar) (vorticity u τ xStar) / 2) t
      = M * Mdot := by
  -- Define the gap function `g(τ) := (M_fn τ)²/2 - |ω(τ, xStar)|²/2`.
  set ψ : ℝ → ℝ :=
    fun τ => Vec3.dot (vorticity u τ xStar) (vorticity u τ xStar) / 2
  set MSq : ℝ → ℝ := fun τ => (E.M_fn τ) ^ 2 / 2
  -- (a) `g ≥ 0` everywhere: from h_dom applied at y = xStar.
  have hg_nn : ∀ τ, 0 ≤ MSq τ - ψ τ := by
    intro τ
    have h := E.h_dom xStar τ
    -- h : ψ τ ≤ MSq τ
    linarith
  -- (b) `g(t) = 0`: from h_hit.
  have hg_t : MSq t - ψ t = 0 := by
    have h := E.h_hit
    -- h : ψ t = MSq t
    show MSq t - ψ t = 0
    linarith
  -- (c) So `g` has a minimum at `t`: g(t) ≤ g(τ) for all τ.
  have hg_min : ∀ τ, MSq t - ψ t ≤ MSq τ - ψ τ := by
    intro τ; rw [hg_t]; exact hg_nn τ
  -- (d) MSq is differentiable at t with derivative `M_fn t · Mdot = M · Mdot`.
  have h_MSq_deriv : HasDerivAt MSq (M * Mdot) t := by
    -- `MSq = fun τ => (M_fn τ)² / 2`
    -- Derivative: `M_fn t · Mdot` (chain rule on `^2` + `/2`).
    have h_pow : HasDerivAt (fun τ => (E.M_fn τ) ^ 2)
        (2 * E.M_fn t * Mdot) t := by
      have := E.h_deriv.pow 2
      simpa [pow_one] using this
    have h_div :
        HasDerivAt (fun τ => (E.M_fn τ) ^ 2 / 2)
          (2 * E.M_fn t * Mdot / 2) t := h_pow.div_const 2
    have h_simp : 2 * E.M_fn t * Mdot / 2 = M * Mdot := by
      rw [E.h_at_t]; ring
    rw [h_simp] at h_div
    exact h_div
  -- (e) ψ is differentiable at t by h_slice_diff.
  have h_ψ_diff : DifferentiableAt ℝ ψ t := E.h_slice_diff
  -- (f) So `MSq - ψ` is differentiable at t.
  have h_MSq_diff : DifferentiableAt ℝ MSq t := h_MSq_deriv.differentiableAt
  have h_gap_diff :
      DifferentiableAt ℝ (fun τ => MSq τ - ψ τ) t :=
    h_MSq_diff.sub h_ψ_diff
  -- (g) `MSq - ψ` has a local min at t, so its derivative vanishes.
  have h_local_min : IsLocalMin (fun τ => MSq τ - ψ τ) t := by
    refine Filter.Eventually.of_forall (fun τ => ?_)
    exact hg_min τ
  have h_deriv_gap_zero :
      deriv (fun τ => MSq τ - ψ τ) t = 0 :=
    h_local_min.deriv_eq_zero
  -- (h) `deriv (MSq - ψ) t = deriv MSq t - deriv ψ t = M·Mdot - deriv ψ t`.
  have h_deriv_gap_split :
      deriv (fun τ => MSq τ - ψ τ) t
        = deriv MSq t - deriv ψ t := by
    rw [deriv_sub h_MSq_diff h_ψ_diff]
  have h_MSq_deriv_eq : deriv MSq t = M * Mdot := h_MSq_deriv.deriv
  rw [h_deriv_gap_split, h_MSq_deriv_eq] at h_deriv_gap_zero
  -- h_deriv_gap_zero : M * Mdot - deriv ψ t = 0
  linarith

end NSBlwChain.BLW
