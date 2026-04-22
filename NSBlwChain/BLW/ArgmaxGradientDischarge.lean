-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Setup.VectorFields
import NSBlwChain.BLW.ArgmaxGradient

/-!
# Analytical discharge of step (i) of Theorem 12.2 — argmax gradient identity

This file provides an **analytical** derivation of the hypothesis fields
`sqNorm_form` and `sqNorm_zero` in `NSBlwChain.BLW.ArgmaxGradientInputs`
from multivariable-calculus content at a base point `xStar : Vec3`, in the
local frame where `ω(xStar) = M · ê₃`.

## Strategy

We package as hypotheses:

* `align` — `ω(xStar) = M · ê₃`, i.e. the local-frame alignment assumption.
* `product_rule` — the pointwise product rule for the dot product
  `|ω|² = ω · ω` at `xStar`, stated as the scalar identity
  `∂ᵢ(|ω|²)(xStar) = 2 · Σ_k (ω(xStar)_k · ∂ᵢ(ω_k)(xStar))`.
  This is the key content of the derivative of an inner product with
  itself; in mathlib 4.29 it would normally be produced by
  `HasFDerivAt.inner` / `Pi.hasFDerivAt_apply` + chain rule, but we
  abstract it here to keep the module self-contained.
* `sqNorm_zero` — the argmax condition: `∂ᵢ(|ω|²)(xStar) = 0`.

From `align`, the sum `Σ_k (ω(xStar)_k · ∂ᵢ(ω_k)(xStar))` collapses because
only `k = 3` contributes (with coefficient `M`).  That collapse is
proved here (`sum_collapse_at_basis`).  Combining with `product_rule`
yields the local-frame form
`∂ᵢ(|ω|²)(xStar) = 2 · M · ∂ᵢ(ω_3)(xStar)`, and together with
`sqNorm_zero` this populates an `ArgmaxGradientInputs`.

The final def `discharge_step_i` returns the populated bundle.

## Scope and caveats

The product rule is stated as a hypothesis rather than proved from
`HasFDerivAt` primitives.  This keeps the file ~200 LOC and sidesteps
mathlib's `HasFDerivAt.inner` phrasing (which is for the mathlib
`inner` over `EuclideanSpace`, not our concrete `Vec3.dot`).  A pure
analytical proof of the product rule for `Vec3.dot` sits directly
below this file in the dependency graph and is deferred to a later
commit.
-/

namespace NSBlwChain.BLW

open NSBlwChain
open scoped BigOperators

/-- **Analytical inputs for the discharge of step (i).**

    Bundles:
    * a vector field `ω : Vec3 → Vec3`;
    * a base point `xStar : Vec3`;
    * a scalar `M : ℝ` with `ω(xStar) = M · ê₃` (local-frame alignment);
    * a direction `i : Fin 3`;
    * the pointwise product rule for `|ω|² = ω · ω` at `xStar`;
    * the argmax condition `∂ᵢ(|ω|²)(xStar) = 0`.
-/
structure ArgmaxGradientDischarge where
  ω : Vec3 → Vec3
  xStar : Vec3
  M : ℝ
  i : Fin 3
  /-- Local-frame alignment: `ω(xStar) = M · ê₃`. -/
  align : ω xStar = fun j => M * Vec3.e (2 : Fin 3) j
  /-- Product rule at `xStar`:
        `∂ᵢ(|ω|²)(xStar) = 2 · Σ_k (ω(xStar)_k · ∂ᵢ(ω_k)(xStar))`.
      This is the content of `HasFDerivAt.inner` for `Vec3.dot`. -/
  product_rule :
    partialDeriv (fun x => Vec3.dot (ω x) (ω x)) i xStar
      = 2 * ∑ k : Fin 3, ω xStar k * partialDeriv (fun x => ω x k) i xStar
  /-- Argmax condition: `∂ᵢ(|ω|²)(xStar) = 0`. -/
  sqNorm_zero :
    partialDeriv (fun x => Vec3.dot (ω x) (ω x)) i xStar = 0

namespace ArgmaxGradientDischarge

variable (h : ArgmaxGradientDischarge)

/-- Value of `ω(xStar)` at coordinate `k`, from the alignment hypothesis. -/
lemma omega_apply (k : Fin 3) :
    h.ω h.xStar k = h.M * Vec3.e (2 : Fin 3) k := by
  have := congrArg (fun f => f k) h.align
  simpa using this

/-- At the basis coordinate `k = (2 : Fin 3)` (the "third component" in
    physics notation with 0-indexed `Fin 3`), `ω(xStar)_2 = M`. -/
lemma omega_apply_three :
    h.ω h.xStar (2 : Fin 3) = h.M := by
  have := h.omega_apply (2 : Fin 3)
  rw [Vec3.e_self] at this
  simpa using this

/-- At basis coordinates `k ≠ (2 : Fin 3)`, `ω(xStar)_k = 0`. -/
lemma omega_apply_of_ne {k : Fin 3} (hk : k ≠ (2 : Fin 3)) :
    h.ω h.xStar k = 0 := by
  have := h.omega_apply k
  have h_e : Vec3.e (2 : Fin 3) k = 0 := Vec3.e_of_ne hk
  rw [h_e] at this
  simpa using this

/-- **Key sum collapse.**  In the local frame, only `k = 2` contributes:
    `Σ_k (ω(xStar)_k · ∂ᵢ(ω_k)(xStar)) = M · ∂ᵢ(ω_2)(xStar)`. -/
lemma sum_collapse :
    (∑ k : Fin 3, h.ω h.xStar k * partialDeriv (fun x => h.ω x k) h.i h.xStar)
      = h.M * partialDeriv (fun x => h.ω x (2 : Fin 3)) h.i h.xStar := by
  classical
  have h_single :
      (∑ k ∈ (Finset.univ : Finset (Fin 3)),
          h.ω h.xStar k * partialDeriv (fun x => h.ω x k) h.i h.xStar)
        = h.ω h.xStar (2 : Fin 3)
            * partialDeriv (fun x => h.ω x (2 : Fin 3)) h.i h.xStar := by
    refine Finset.sum_eq_single (2 : Fin 3) ?_ ?_
    · intro k _ hk_ne
      rw [h.omega_apply_of_ne hk_ne, zero_mul]
    · intro hmem
      exact (hmem (Finset.mem_univ _)).elim
  rw [h_single, h.omega_apply_three]

/-- **Local-frame form of the partial derivative of `|ω|²` at `xStar`.**

    Combining the product-rule hypothesis with the sum-collapse lemma
    gives `∂ᵢ(|ω|²)(xStar) = 2 · M · ∂ᵢ(ω_3)(xStar)`. -/
lemma partial_sqNorm_eq :
    partialDeriv (fun x => Vec3.dot (h.ω x) (h.ω x)) h.i h.xStar
      = 2 * h.M * partialDeriv (fun x => h.ω x (2 : Fin 3)) h.i h.xStar := by
  calc partialDeriv (fun x => Vec3.dot (h.ω x) (h.ω x)) h.i h.xStar
      = 2 * ∑ k : Fin 3, h.ω h.xStar k * partialDeriv (fun x => h.ω x k) h.i h.xStar :=
          h.product_rule
    _ = 2 * (h.M * partialDeriv (fun x => h.ω x (2 : Fin 3)) h.i h.xStar) := by
          rw [h.sum_collapse]
    _ = 2 * h.M * partialDeriv (fun x => h.ω x (2 : Fin 3)) h.i h.xStar := by ring

/-- **Analytical discharge of step (i).**

    From the analytical inputs (alignment + product rule + argmax zero),
    produce the scalar bundle `ArgmaxGradientInputs`.  Its `step_i`
    conclusion then gives `M · ∂ᵢ(ω_3)(xStar) = 0`. -/
noncomputable def toInputs : ArgmaxGradientInputs where
  M := h.M
  partial_omega_3 := partialDeriv (fun x => h.ω x (2 : Fin 3)) h.i h.xStar
  partial_sqNorm := partialDeriv (fun x => Vec3.dot (h.ω x) (h.ω x)) h.i h.xStar
  sqNorm_form := h.partial_sqNorm_eq
  sqNorm_zero := h.sqNorm_zero

/-- **Step (i) conclusion, analytical form.**  Directly from
    `toInputs.step_i`. -/
theorem step_i_analytical :
    h.M * partialDeriv (fun x => h.ω x (2 : Fin 3)) h.i h.xStar = 0 :=
  h.toInputs.step_i

/-- **Step (i) corollary, analytical form.**  If `M ≠ 0`, then
    `∂ᵢ(ω_3)(xStar) = 0`. -/
theorem partial_omega_3_zero_of_M_ne_zero (hM : h.M ≠ 0) :
    partialDeriv (fun x => h.ω x (2 : Fin 3)) h.i h.xStar = 0 :=
  h.toInputs.partial_omega_3_zero_of_M_ne_zero hM

end ArgmaxGradientDischarge

/-- **Top-level discharge.**  Given analytical inputs, produce a
    populated `ArgmaxGradientInputs`. -/
noncomputable def discharge_step_i (h : ArgmaxGradientDischarge) :
    ArgmaxGradientInputs := h.toInputs

end NSBlwChain.BLW
