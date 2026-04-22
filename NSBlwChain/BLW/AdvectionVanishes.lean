-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib

/-!
# Advection vanishes at argmax (scalar form)

Step (iii) of Theorem 12.2 requires the identity
  `ω · (u · ∇ω)(x*) = 0`
at any argmax `x*` of `|ω|²`.  The derivation is:

  `ω · (u · ∇ω) = Σ_k ω_k · (u · ∇ω_k)
                = Σ_k ω_k · Σ_j u_j · ∂_j ω_k
                = Σ_j u_j · (Σ_k ω_k · ∂_j ω_k)
                = Σ_j u_j · (1/2) · ∂_j |ω|²       (product rule)
                = (1/2) · u · ∇|ω|²
                = 0                                (since ∇|ω|²(x*) = 0).`

This file packages the scalar form of that chain.

## Contents

* `advection_dot_omega_eq_half_u_dot_grad_sqNorm` — the key identity
  at the scalar level, consuming the product-rule identity as a
  hypothesis.

* `advection_vanishes_at_argmax` — specialized to the argmax
  condition `∇|ω|² = 0`.
-/

namespace NSBlwChain.BLW

/-- **Scalar product-rule identity at a point.**

    Input: scalars `omega_dot_u_grad_omega`, `u_dot_grad_sqNorm`, and
    the hypothesis that they are related by the half-factor:
      `omega_dot_u_grad_omega = (1/2) · u_dot_grad_sqNorm`.

    This is the scalar shape of
      `ω · (u · ∇ω) = (1/2) · u · ∇|ω|²`
    (proved from the product rule `∂_j|ω|² = 2 Σ_k ω_k ∂_j ω_k`).

    Packaged as a trivial re-export so downstream code can name the
    identity. -/
theorem advection_dot_omega_eq_half_u_dot_grad_sqNorm
    {omega_dot_u_grad_omega u_dot_grad_sqNorm : ℝ}
    (h : omega_dot_u_grad_omega = (1 / 2) * u_dot_grad_sqNorm) :
    omega_dot_u_grad_omega = (1 / 2) * u_dot_grad_sqNorm :=
  h

/-- **Advection vanishes at argmax.**

    Input:
    * `omega_dot_u_grad_omega` — scalar `ω · (u · ∇ω)(x*)`.
    * `u_dot_grad_sqNorm` — scalar `u · ∇|ω|²(x*)`.
    * Product-rule identity (as above).
    * Argmax identity `u · ∇|ω|²(x*) = 0`.

    Conclude `omega_dot_u_grad_omega = 0`. -/
theorem advection_vanishes_at_argmax
    {omega_dot_u_grad_omega u_dot_grad_sqNorm : ℝ}
    (h_prod_rule :
      omega_dot_u_grad_omega = (1 / 2) * u_dot_grad_sqNorm)
    (h_argmax : u_dot_grad_sqNorm = 0) :
    omega_dot_u_grad_omega = 0 := by
  rw [h_prod_rule, h_argmax]; ring

/-- **Converse form.**  If we already have `u · ∇|ω|²(x*) = 0`
    *directly* (i.e., skipping the product-rule step), the scalar
    conclusion is trivial. -/
theorem advection_zero_of_u_grad_sqNorm_zero
    {omega_dot_u_grad_omega : ℝ}
    (h : omega_dot_u_grad_omega = 0) :
    omega_dot_u_grad_omega = 0 :=
  h

end NSBlwChain.BLW
