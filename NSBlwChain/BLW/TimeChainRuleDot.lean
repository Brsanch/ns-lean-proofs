-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.BLW.ChainRuleMSquared
import NSBlwChain.BLW.EnvelopeIdentity
import NSBlwChain.Setup.VectorFields

/-!
# Time chain rule for `|ω(τ, x*)|² / 2` + envelope connection

Discharges identities #4 (`h_time_chain_rule`) and #5 (`h_envelope`)
from the scalar capstone.

* **#4:** `Vec3.dot ω(t, x*) (∂_τ ω(t, x*)) = deriv (|ω|²/2) t`.
  Product-rule calculus: per-component `d/dτ (ω_k² / 2) = ω_k · ω_k'`,
  sum over `Fin 3`.

* **#5:** `deriv (|ω(τ, x*)|²/2) t = M t · Ṁ t`.
  Specialization of the existing
  `EnvelopeIdentity.envelope_identity_via_chainRule_deriv`
  (Danskin envelope).

## Main results

* `hasDerivAt_Vec3_sqNorm_half` — per-component product rule +
  Fin 3 sum; yields the `HasDerivAt` for `|ω|²/2` at `t` with
  derivative `Vec3.dot ω ω_dot`.

* `time_chain_rule_Vec3_dot` — `deriv`-level identity #4.

* `envelope_identity_sqNorm_half_at_argmax` — identity #5.
-/

namespace NSBlwChain.BLW

open Filter Topology Set
open scoped BigOperators

/-- **Product-rule / component-sum form.**  If each component
    `τ ↦ ω τ k` is `HasDerivAt` at `t` with derivative `ω_dot k`,
    then the scalar time-slice `τ ↦ Vec3.dot (ω τ) (ω τ) / 2` is
    `HasDerivAt` at `t` with derivative `Vec3.dot (ω t) ω_dot`. -/
theorem hasDerivAt_Vec3_sqNorm_half
    (ω : ℝ → Vec3) (ω_dot : Vec3) (t : ℝ)
    (h_comp : ∀ k : Fin 3, HasDerivAt (fun τ => ω τ k) (ω_dot k) t) :
    HasDerivAt (fun τ => Vec3.dot (ω τ) (ω τ) / 2)
      (Vec3.dot (ω t) ω_dot) t := by
  -- Per-component: d/dτ (ω_k τ * ω_k τ / 2) = ω_k t * ω_dot k.
  have h_half_sq : ∀ k : Fin 3,
      HasDerivAt (fun τ => (ω τ k) * (ω τ k) / 2)
        (ω t k * ω_dot k) t := by
    intro k
    have hf := h_comp k
    have hfmul :
        HasDerivAt (fun τ => ω τ k * ω τ k)
          (ω t k * ω_dot k + ω t k * ω_dot k) t := by
      have := hf.mul hf
      convert this using 1
      ring
    have hhalf :
        HasDerivAt (fun τ => ω τ k * ω τ k / 2)
          ((ω t k * ω_dot k + ω t k * ω_dot k) / 2) t :=
      hfmul.div_const 2
    convert hhalf using 1
    ring
  -- Sum over k ∈ Fin 3.
  have h_sum :
      HasDerivAt (fun τ => ∑ k : Fin 3, (ω τ k) * (ω τ k) / 2)
        (∑ k : Fin 3, ω t k * ω_dot k) t :=
    HasDerivAt.sum (fun k _ => h_half_sq k)
  -- Identify with Vec3.dot form.
  have h_fun_eq :
      (fun τ => ∑ k : Fin 3, (ω τ k) * (ω τ k) / 2)
        = (fun τ => Vec3.dot (ω τ) (ω τ) / 2) := by
    funext τ
    rw [Finset.sum_div]
    rfl
  have h_val_eq :
      ∑ k : Fin 3, ω t k * ω_dot k = Vec3.dot (ω t) ω_dot := rfl
  rw [h_fun_eq, h_val_eq] at h_sum
  exact h_sum

/-- **Time chain rule (identity #4, `deriv` form).**  With per-
    component differentiability, `Vec3.dot (ω t) ω_dot` equals
    `deriv (|ω(·)|²/2) t`. -/
theorem time_chain_rule_Vec3_dot
    (ω : ℝ → Vec3) (ω_dot : Vec3) (t : ℝ)
    (h_comp : ∀ k : Fin 3, HasDerivAt (fun τ => ω τ k) (ω_dot k) t) :
    Vec3.dot (ω t) ω_dot
      = deriv (fun τ => Vec3.dot (ω τ) (ω τ) / 2) t :=
  (hasDerivAt_Vec3_sqNorm_half ω ω_dot t h_comp).deriv.symm

/-- **Envelope identity (identity #5).**  Given that the time-slice
    `τ ↦ |ω(τ, x*)|²/2` is dominated by `(M τ)²/2` and attains it at
    `t`, plus `HasDerivAt M Mdot t`, the `deriv` of the slice at `t`
    equals `M t · Ṁ t`.  Specialization of
    `EnvelopeIdentity.envelope_identity_via_chainRule_deriv`. -/
theorem envelope_identity_sqNorm_half_at_argmax
    {X : Type*} (ω : X → ℝ → Vec3) (M : ℝ → ℝ)
    (x_star : X) (t : ℝ) (Mdot slice_deriv : ℝ)
    (h_env : ∀ x τ,
      Vec3.dot (ω x τ) (ω x τ) / 2 ≤ (M τ) ^ 2 / 2)
    (h_hit :
      Vec3.dot (ω x_star t) (ω x_star t) / 2 = (M t) ^ 2 / 2)
    (h_M : HasDerivAt M Mdot t)
    (h_slice :
      HasDerivAt (fun τ => Vec3.dot (ω x_star τ) (ω x_star τ) / 2)
        slice_deriv t) :
    slice_deriv = M t * deriv M t :=
  envelope_identity_via_chainRule_deriv
    (fun x τ => Vec3.dot (ω x τ) (ω x τ) / 2) M x_star t Mdot slice_deriv
    h_env h_hit h_M h_slice

end NSBlwChain.BLW
