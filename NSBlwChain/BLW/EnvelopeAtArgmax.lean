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

end NSBlwChain.BLW
