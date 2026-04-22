-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Caveats.C2_Envelope

/-!
# Caveat C2 — a.e. ODE packaging (Proposition C2)

This file extends the Danskin envelope of `C2_Envelope.lean` into the
**a.e. ODE identity** consumed by the BLW-gradient chain at Step 6 of
§12.4:

  For a.e. `t ∈ [0, T)`, every argmax `x_star ∈ arg max_x φ(x, t)`
  satisfies `Ṁ(t) = ∂_t φ(x_star, t)`.

## Structure of the argument

The Rademacher step (Lipschitz `M` → differentiable a.e.) is **taken
as a hypothesis** in the lemmas below, because the direct form
`LipschitzWith.ae_differentiableAt` hits a typeclass-resolution
issue in mathlib 4.29.0 when specialized to `ℝ → ℝ` (see
`Setup/LipschitzToAE.lean` for the stub).  Downstream consumers
package the Rademacher conclusion with `MeasureTheory.ae` hypotheses
and pass them in explicitly.

## References

* Danskin (1966), *J. SIAM Appl. Math.* 14, 641–664.
* Companion note `paper/ns_regularity_caveats_formal.md`, §C2.
-/

namespace NSBlwChain.Caveats

open MeasureTheory Filter
open scoped Topology

/-- **Proposition C2 (a.e. ODE packaging).**

    Given:
    * An envelope `M : ℝ → ℝ` of a family `φ : X → ℝ → ℝ` (envelope
      condition and pointwise-hit).
    * A selection `x_star : ℝ → X` pointing into the argmax set at
      every time.
    * A *hypothesis* that `M` is differentiable a.e. (to be
      discharged via Rademacher).
    * A hypothesis that each slice `φ(x_star(t), ·)` is
      differentiable at `t` whenever `M` is.

    Conclude:
    * `HasDerivAt M (deriv (φ (x_star t)) t) t` a.e. — i.e., the
      envelope identity holds at almost every time, with `Ṁ(t)`
      computed by the slice derivative.

    This is Proposition C2 from the companion note.  The Rademacher
    conclusion is taken as an input hypothesis `hM_ae_diff` because
    its direct statement via `LipschitzWith.ae_differentiableAt`
    currently needs a manual typeclass-inference workaround. -/
lemma ae_envelope_ode
    {X : Type*} {φ : X → ℝ → ℝ} {M : ℝ → ℝ} {x_star : ℝ → X}
    (h_env : ∀ x t, φ x t ≤ M t)
    (h_hit : ∀ t, φ (x_star t) t = M t)
    (hM_ae_diff : ∀ᵐ t : ℝ, HasDerivAt M (deriv M t) t)
    (h_slice : ∀ t : ℝ, DifferentiableAt ℝ (φ (x_star t)) t) :
    ∀ᵐ t : ℝ,
      HasDerivAt M (deriv (φ (x_star t)) t) t := by
  filter_upwards [hM_ae_diff] with t ht
  have hφ_hasDeriv : HasDerivAt (φ (x_star t))
      (deriv (φ (x_star t)) t) t := (h_slice t).hasDerivAt
  have h_eq : deriv M t = deriv (φ (x_star t)) t :=
    danskin_envelope φ M (h_env) (h_hit t) ht hφ_hasDeriv
  rw [h_eq] at ht
  exact ht

/-- **Corollary (a.e. derivative bound).**

    If we additionally have a bound `∂_t φ(x_star(t), t) ≤ Φ(M(t))`
    at a.e. `t`, then the a.e. form of the ODE is
    `deriv M t ≤ Φ (M t)` a.e.

    The integrated form (the consumer of this lemma) uses
    Lipschitz `M` + absolute continuity + FTC — developed separately
    in `Caveats/C1_GrowthMoment.lean`. -/
lemma ae_derivM_bound
    {X : Type*} {φ : X → ℝ → ℝ} {M : ℝ → ℝ} {x_star : ℝ → X}
    {Φ : ℝ → ℝ}
    (h_env : ∀ x t, φ x t ≤ M t)
    (h_hit : ∀ t, φ (x_star t) t = M t)
    (hM_ae_diff : ∀ᵐ t : ℝ, HasDerivAt M (deriv M t) t)
    (h_slice : ∀ t : ℝ, DifferentiableAt ℝ (φ (x_star t)) t)
    (h_bound :
      ∀ᵐ t : ℝ, deriv (φ (x_star t)) t ≤ Φ (M t)) :
    ∀ᵐ t : ℝ, deriv M t ≤ Φ (M t) := by
  have h_ae := ae_envelope_ode h_env h_hit hM_ae_diff h_slice
  filter_upwards [h_ae, h_bound] with t h_ht h_b
  have h_deriv_eq : deriv M t = deriv (φ (x_star t)) t := h_ht.deriv
  rw [h_deriv_eq]
  exact h_b

end NSBlwChain.Caveats
