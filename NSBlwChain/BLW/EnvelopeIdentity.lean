-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Caveats.C2_Envelope
import NSBlwChain.BLW.ChainRuleMSquared

/-!
# Envelope identity for `|omega|^2 / 2` — §12.3 step (iii)

This file formalizes the **scalar envelope identity**

  `d/dt (|omega|^2 / 2)(x_star, t) = M(t) * dM/dt(t)`

used in step (iii) of Theorem 12.2 of `paper/ns_regularity.md`, where
`M(t) := ||omega(t, .)||_Linfinity` and `x_star` is any point achieving
the spatial maximum at time `t`.

## Derivation

Let `phi(x, t) := |omega(t, x)|^2 / 2`.  By definition of `M`,

  `phi(x, t) <= (M t)^2 / 2`  for all `(x, t)` and  `phi(x_star, t) = (M t)^2 / 2`.

The time-slice `phi(x_star, .)` is tangent-from-below to the envelope
`t \mapsto (M t)^2 / 2` at `t`, so Lemma C2.5 (`danskin_envelope` in
`NSBlwChain.Caveats.C2_Envelope`) gives

  `d/dt ((M t)^2 / 2) = d/dt phi(x_star, t)`                              (*)

at any `t` where both derivatives exist.

The classical chain-rule identity `d/dt (M^2/2) = M * dM/dt` closes the
identity.  Two forms are provided:

* `envelope_identity_for_sqNorm_half` — hypothesis-consumer form.
  The chain-rule connection `M_deriv = M t * deriv M t` is an explicit
  input; this is the lightest-weight statement and matches the usage
  site in §12.3.

* `envelope_identity_via_chainRule` — discharges the chain-rule
  connection internally using `hasDerivAt_sqHalf_of_hasDerivAt`
  (`NSBlwChain.BLW.ChainRuleMSquared`).  Caller only supplies
  `HasDerivAt M Mdot t`.

## References

* Paper `paper/ns_regularity.md`, §12.3 step (iii).
* `NSBlwChain.Caveats.C2_Envelope`, Lemma C2.5 (Danskin envelope).
* `NSBlwChain.BLW.ChainRuleMSquared`, chain-rule helper.
-/

namespace NSBlwChain.BLW

open Filter Topology Set
open NSBlwChain.Caveats

/-- **Envelope identity for `|omega|^2 / 2` (hypothesis-consumer form).**

    Given a real-valued family `phi : X -> R -> R` dominated by the
    envelope `t \mapsto (M t)^2 / 2` and attaining it at `x_star, t`, the
    time-slice derivative of `phi(x_star, .)` at `t` equals `M t * deriv M t`.

    The caller supplies:

    * `slice_deriv` : the scalar derivative of the time-slice
      `phi(x_star, .)` at `t` (usually obtained from Biot-Savart / vorticity
      equation inputs by a separate computation);
    * `M_deriv` : the scalar derivative of `t \mapsto (M t)^2 / 2` at `t`;
    * `h_connect` : the chain-rule connection
      `M_deriv = M t * deriv M t`, a classical identity that the caller
      typically has in hand from the `M`-derivative (and is discharged
      by `hasDerivAt_sqHalf_of_hasDerivAt` in the chain-rule form below).

    This lemma then glues these via Lemma C2.5 (`danskin_envelope`). -/
theorem envelope_identity_for_sqNorm_half
    {X : Type*} (phi : X → ℝ → ℝ) (M : ℝ → ℝ)
    (x_star : X) (t : ℝ)
    (M_deriv : ℝ) (slice_deriv : ℝ)
    (h_env : ∀ x t', phi x t' ≤ (M t') ^ 2 / 2)
    (h_hit : phi x_star t = (M t) ^ 2 / 2)
    (h_M2_deriv : HasDerivAt (fun τ => (M τ) ^ 2 / 2) M_deriv t)
    (h_slice : HasDerivAt (phi x_star) slice_deriv t)
    (h_connect : M_deriv = M t * deriv M t) :
    slice_deriv = M t * deriv M t := by
  -- Apply Lemma C2.5 with the envelope `t \mapsto (M t)^2 / 2`.
  have h_eq : M_deriv = slice_deriv :=
    danskin_envelope phi (fun τ => (M τ) ^ 2 / 2)
      h_env h_hit h_M2_deriv h_slice
  -- Now `slice_deriv = M_deriv = M t * deriv M t`.
  linarith [h_eq, h_connect]

/-- **Envelope identity, packaged as `HasDerivAt` of the slice.**

    Same content as `envelope_identity_for_sqNorm_half`, but packaged to
    state that the slice `phi(x_star, .)` has the expected derivative
    `M(t) * dM/dt(t)` at `t`, mirroring §12.3 step (iii) literally. -/
theorem envelope_identity_rhs
    {X : Type*} (phi : X → ℝ → ℝ) (M : ℝ → ℝ)
    (x_star : X) (t : ℝ)
    (M_deriv : ℝ) (slice_deriv : ℝ)
    (h_env : ∀ x t', phi x t' ≤ (M t') ^ 2 / 2)
    (h_hit : phi x_star t = (M t) ^ 2 / 2)
    (h_M2_deriv : HasDerivAt (fun τ => (M τ) ^ 2 / 2) M_deriv t)
    (h_slice : HasDerivAt (phi x_star) slice_deriv t)
    (h_connect : M_deriv = M t * deriv M t) :
    HasDerivAt (phi x_star) (M t * deriv M t) t := by
  have h_eq : slice_deriv = M t * deriv M t :=
    envelope_identity_for_sqNorm_half phi M x_star t M_deriv slice_deriv
      h_env h_hit h_M2_deriv h_slice h_connect
  simpa [h_eq] using h_slice

/-- **Envelope identity, chain-rule-discharging form.**

    Variant of `envelope_identity_for_sqNorm_half` where the chain-rule
    input `h_connect` and the `M^2/2`-derivative `h_M2_deriv` are both
    derived internally from `HasDerivAt M Mdot t` via
    `hasDerivAt_sqHalf_of_hasDerivAt`.

    Conclusion:  `slice_deriv = M t * Mdot`. -/
theorem envelope_identity_via_chainRule
    {X : Type*} (phi : X → ℝ → ℝ) (M : ℝ → ℝ)
    (x_star : X) (t : ℝ)
    (Mdot slice_deriv : ℝ)
    (h_env : ∀ x t', phi x t' ≤ (M t') ^ 2 / 2)
    (h_hit : phi x_star t = (M t) ^ 2 / 2)
    (h_M : HasDerivAt M Mdot t)
    (h_slice : HasDerivAt (phi x_star) slice_deriv t) :
    slice_deriv = M t * Mdot := by
  -- Deduce `HasDerivAt (M^2 / 2) (M t * Mdot) t` via the chain-rule helper.
  have h_M2 : HasDerivAt (fun τ => (M τ) ^ 2 / 2) (M t * Mdot) t :=
    hasDerivAt_sqHalf_of_hasDerivAt h_M
  -- Apply Lemma C2.5 directly.
  have h_eq : M t * Mdot = slice_deriv :=
    danskin_envelope phi (fun τ => (M τ) ^ 2 / 2)
      h_env h_hit h_M2 h_slice
  linarith [h_eq]

/-- **`deriv`-normalized form of `envelope_identity_via_chainRule`.**

    Replaces `Mdot` by `deriv M t` using `HasDerivAt.deriv`. -/
theorem envelope_identity_via_chainRule_deriv
    {X : Type*} (phi : X → ℝ → ℝ) (M : ℝ → ℝ)
    (x_star : X) (t : ℝ)
    (Mdot slice_deriv : ℝ)
    (h_env : ∀ x t', phi x t' ≤ (M t') ^ 2 / 2)
    (h_hit : phi x_star t = (M t) ^ 2 / 2)
    (h_M : HasDerivAt M Mdot t)
    (h_slice : HasDerivAt (phi x_star) slice_deriv t) :
    slice_deriv = M t * deriv M t := by
  have h := envelope_identity_via_chainRule phi M x_star t Mdot slice_deriv
    h_env h_hit h_M h_slice
  -- `h_M.deriv : deriv M t = Mdot`; rewrite it in `h`.
  rw [← h_M.deriv] at h
  exact h

/-! ## Sanity-check example

A trivial smoke-test: on a constant family `phi x t = c^2 / 2` with
envelope `M ≡ c`, both sides of the identity vanish. -/

section Examples

/-- Constant envelope: `phi x t = c^2 / 2`, `M ≡ c`.  Identity reduces
    to `0 = c * 0`. -/
example (c : ℝ) (t : ℝ) :
    (0 : ℝ) = c * deriv (fun _ : ℝ => c) t := by
  simp

end Examples

end NSBlwChain.BLW
