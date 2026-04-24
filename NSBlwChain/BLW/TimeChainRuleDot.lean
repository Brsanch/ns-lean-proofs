-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.BLW.ChainRuleMSquared
import NSBlwChain.BLW.EnvelopeIdentity
import NSBlwChain.Setup.VectorFields

/-!
# Time chain rule for `|ω(τ, x*)|² / 2` + envelope connection

Discharges the sixth and seventh of the seven remaining vector-
field-layer physical identities:

* **`h_time_chain_rule` (#4):**
  `Vec3.dot ω(t, x*) (∂_τ ω(t, x*)) = deriv (fun τ => |ω(τ, x*)|² / 2) t`.

  Pure product-rule calculus: per-component `d/dτ (ω_k²/2) = ω_k · ω_k'`,
  sum over `Fin 3` → `d/dτ Σ_k ω_k²/2 = Σ_k ω_k · ω_k' = Vec3.dot ω ω'`.

* **`h_envelope` (#5):**
  `deriv (fun τ => |ω(τ, x*)|² / 2) t = M(t) · Ṁ(t)`.

  Follows from the Danskin envelope theorem (`EnvelopeIdentity.
  envelope_identity_via_chainRule_deriv`) applied with `phi :=
  (x, τ) ↦ Vec3.dot (ω τ x) (ω τ x) / 2`, using that `|ω(τ, x)|²/2`
  is dominated by `(M τ)²/2` and attains it at `x = x*(t)`.

Together with #1 (Hessian expansion) + #2 (Laplace trace ≤ 0) +
#3+#7 (Laplace alignment contraction) + #6 (strain alignment
contraction), these close the full set of 7 vector-field-layer
identities that the scalar capstone
`gradient_bound_of_NSEvolutionAxioms_all_scalar_derived` takes
as hypotheses — making the gradient bound derivable from the
`NSEvolutionAxioms` + `IsLocalMax |ω|²` + alignment + positivity/
growth hypotheses alone.

## Main results

* `hasDerivAt_Vec3_sqNorm_half` — product-rule/component-sum form:
  if each component is `HasDerivAt` at `t`, then the scalar
  `|ω(τ, x*)|²/2` is `HasDerivAt` with derivative `Vec3.dot ω ω'`.

* `time_chain_rule_Vec3_dot` — the `deriv`-level identity #4.

* `envelope_identity_sqNorm_half_at_argmax` — identity #5, a
  specialization of `envelope_identity_via_chainRule_deriv`.
-/

namespace NSBlwChain.BLW

open Filter Topology Set
open scoped BigOperators

/-- **Product-rule / component-sum form.**  Given per-component
    differentiability of `τ ↦ ω(τ, x*) k` at `t` with derivative
    values `ω_dot(k)`, the scalar time-slice
    `τ ↦ Vec3.dot (ω τ x*) (ω τ x*) / 2` is `HasDerivAt` at `t`
    with derivative `Vec3.dot (ω t x*) ω_dot`. -/
theorem hasDerivAt_Vec3_sqNorm_half
    (ω : ℝ → Vec3) (ω_dot : Vec3) (t : ℝ)
    (h_comp : ∀ k : Fin 3, HasDerivAt (fun τ => ω τ k) (ω_dot k) t) :
    HasDerivAt (fun τ => Vec3.dot (ω τ) (ω τ) / 2)
      (Vec3.dot (ω t) ω_dot) t := by
  -- Per-component: d/dτ (ω_k²) = 2 · ω_k(t) · ω_dot k.
  have h_sq : ∀ k : Fin 3,
      HasDerivAt (fun τ => (ω τ k) ^ 2)
        (2 * ω t k * ω_dot k) t := by
    intro k
    have := (h_comp k).pow 2
    simpa [pow_one, two_mul, mul_comm, mul_assoc] using this
  -- Sum over k ∈ Fin 3: d/dτ (Σ_k (ω τ k)²) = Σ_k 2 · ω_k(t) · ω_dot k.
  have h_sum :
      HasDerivAt (fun τ => ∑ k : Fin 3, (ω τ k) ^ 2)
        (∑ k : Fin 3, 2 * ω t k * ω_dot k) t := by
    have := HasDerivAt.sum
      (u := fun k τ => (ω τ k) ^ 2)
      (u' := fun k => 2 * ω t k * ω_dot k)
      (s := Finset.univ)
      (fun k _ => h_sq k)
    exact this
  -- Divide by 2: d/dτ (Σ_k (ω τ k)² / 2) = Σ_k ω_k(t) · ω_dot k.
  have h_div :
      HasDerivAt (fun τ => (∑ k : Fin 3, (ω τ k) ^ 2) / 2)
        ((∑ k : Fin 3, 2 * ω t k * ω_dot k) / 2) t :=
    h_sum.div_const 2
  -- Identify Σ_k (ω τ k)² = Vec3.dot (ω τ) (ω τ) and Σ_k 2·ω_k·ω_dot_k / 2 = Vec3.dot (ω t) ω_dot.
  have h_fun_eq :
      (fun τ => (∑ k : Fin 3, (ω τ k) ^ 2) / 2)
        = (fun τ => Vec3.dot (ω τ) (ω τ) / 2) := by
    funext τ
    simp [Vec3.dot, pow_two]
  have h_val_eq :
      (∑ k : Fin 3, 2 * ω t k * ω_dot k) / 2
        = Vec3.dot (ω t) ω_dot := by
    simp [Vec3.dot, Finset.mul_sum, ← Finset.sum_div]
    rw [← Finset.sum_div]
    congr 1
    · apply Finset.sum_congr rfl
      intro k _
      ring
  rw [h_fun_eq, h_val_eq] at h_div
  exact h_div

/-- **Time chain rule (identity #4, `deriv` form).**  With per-
    component differentiability, the `deriv` of `|ω(τ, x*)|²/2`
    at `t` equals `Vec3.dot (ω t x*) (fun k => deriv (· k) t)`. -/
theorem time_chain_rule_Vec3_dot
    (ω : ℝ → Vec3) (ω_dot : Vec3) (t : ℝ)
    (h_comp : ∀ k : Fin 3, HasDerivAt (fun τ => ω τ k) (ω_dot k) t) :
    Vec3.dot (ω t) ω_dot
      = deriv (fun τ => Vec3.dot (ω τ) (ω τ) / 2) t :=
  (hasDerivAt_Vec3_sqNorm_half ω ω_dot t h_comp).deriv.symm

/-- **Envelope identity (identity #5, `deriv` form).**  Given that
    the time-slice `τ ↦ Vec3.dot (ω τ x*) (ω τ x*) / 2` is
    dominated by `τ ↦ (M τ)² / 2` and attains it at `t`, plus
    `HasDerivAt M Mdot t`, the `deriv` of the slice at `t` equals
    `M t · Ṁ t`.  Direct specialization of
    `envelope_identity_via_chainRule_deriv`. -/
theorem envelope_identity_sqNorm_half_at_argmax
    {X : Type*} (ω : X → ℝ → Vec3) (M : ℝ → ℝ)
    (x_star : X) (t : ℝ) (Mdot : ℝ)
    (h_env : ∀ x τ,
      Vec3.dot (ω x τ) (ω x τ) / 2 ≤ (M τ) ^ 2 / 2)
    (h_hit :
      Vec3.dot (ω x_star t) (ω x_star t) / 2 = (M t) ^ 2 / 2)
    (h_M : HasDerivAt M Mdot t)
    (h_slice :
      HasDerivAt (fun τ => Vec3.dot (ω x_star τ) (ω x_star τ) / 2)
        (deriv (fun τ => Vec3.dot (ω x_star τ) (ω x_star τ) / 2) t)
        t) :
    deriv (fun τ => Vec3.dot (ω x_star τ) (ω x_star τ) / 2) t
      = M t * deriv M t :=
  envelope_identity_via_chainRule_deriv
    (fun x τ => Vec3.dot (ω x τ) (ω x τ) / 2) M x_star t Mdot _
    h_env h_hit h_M h_slice

end NSBlwChain.BLW
