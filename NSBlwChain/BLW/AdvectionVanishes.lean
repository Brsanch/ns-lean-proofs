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

This file keeps the scalar packaging that actually uses both hypotheses.
Unconditional PDE discharge of the product-rule half lives in
`AdvectionAtArgmaxFromNSEvolution.lean`.

## Contents

* `advection_vanishes_at_argmax` — product-rule scalar + argmax
  `u · ∇|ω|² = 0` ⇒ advection scalar is 0.

(Removed 2026-07-25: two V7 `identity-hyp` packaging tautologies
`(h : P) : P := h` that renamed assumptions without proving them.)
-/

namespace NSBlwChain.BLW

/-- **Advection vanishes at argmax.**

    Input:
    * `omega_dot_u_grad_omega` — scalar `ω · (u · ∇ω)(x*)`.
    * `u_dot_grad_sqNorm` — scalar `u · ∇|ω|²(x*)`.
    * Product-rule identity
      `omega_dot_u_grad_omega = (1/2) · u_dot_grad_sqNorm`.
    * Argmax identity `u · ∇|ω|²(x*) = 0`.

    Conclude `omega_dot_u_grad_omega = 0`. -/
theorem advection_vanishes_at_argmax
    {omega_dot_u_grad_omega u_dot_grad_sqNorm : ℝ}
    (h_prod_rule :
      omega_dot_u_grad_omega = (1 / 2) * u_dot_grad_sqNorm)
    (h_argmax : u_dot_grad_sqNorm = 0) :
    omega_dot_u_grad_omega = 0 := by
  rw [h_prod_rule, h_argmax]; ring

end NSBlwChain.BLW
