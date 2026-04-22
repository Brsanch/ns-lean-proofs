-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Setup.VectorFields
import NSBlwChain.Setup.NSHypothesis
import NSBlwChain.Setup.ClassicalAxioms

/-!
# `DecayAtInfinity` constructors

`NSBlwChain.DecayAtInfinity` (in `ClassicalAxioms.lean`) records the
polynomial-decay hypothesis consumed by the Biot-Savart axiom.  This
file provides **constructors** that build a `DecayAtInfinity` witness
from concrete function-space hypotheses that a user is likely to have
on hand.

## Constructors

* `DecayAtInfinity.of_compactSupport_vorticity` — if the vorticity
  has compact support in a ball of radius `R`, the decay hypothesis
  is trivially satisfied with `C = 0` and any `p > 3`.

* `DecayAtInfinity.of_uniform_polynomial_bound` — if the vorticity is
  uniformly bounded by `C · |x|^{-p}` for some `p > 3` and all
  `t ∈ [0, T)`, `|x| ≥ R`, the hypothesis is satisfied directly.

The first is the most common use case: a compactly-supported initial
condition (standard in NS regularity proofs) preserves compact support
under smooth evolution on bounded time intervals provided the domain
is bounded — or under a decay-preservation hypothesis on unbounded
domains.
-/

namespace NSBlwChain.DecayAtInfinity

open NSBlwChain

/-- **Constructor from compact support of vorticity.**

    If for every `t ∈ [0, T)` the vorticity `ω(t, ·)` vanishes
    outside a ball of radius `R`, then the `DecayAtInfinity`
    hypothesis is trivially satisfied (any decay rate `p > 3` works
    with constant `C = 0`). -/
theorem of_compactSupport_vorticity
    {u : VelocityField} {T : ℝ}
    (R : ℝ) (hR : 0 < R)
    (h_support :
      ∀ t : ℝ, 0 ≤ t → t < T → ∀ x : Vec3,
        R ≤ Real.sqrt (Vec3.dot x x) →
          vorticity u t x = fun _ => 0) :
    DecayAtInfinity u T :=
  { has_polynomial_decay := by
      refine ⟨R, 0, 4, hR, le_refl 0, by norm_num, ?_⟩
      intro t ht hT x hxR
      have h_ω : vorticity u t x = fun _ => 0 := h_support t ht hT x hxR
      -- |ω(t, x)| = 0 on the far-field.
      have h_dot_zero :
          Vec3.dot (vorticity u t x) (vorticity u t x) = 0 := by
        unfold Vec3.dot
        simp [h_ω]
      have h_sqrt_zero :
          Real.sqrt (Vec3.dot (vorticity u t x) (vorticity u t x)) = 0 := by
        rw [h_dot_zero]; exact Real.sqrt_zero
      rw [h_sqrt_zero]
      -- Need: 0 ≤ 0 / (√(x·x))^4.
      have h_denom_nonneg :
          0 ≤ (Real.sqrt (Vec3.dot x x)) ^ 4 := by positivity
      positivity }

/-- **Constructor from uniform polynomial bound.**

    If there exists a polynomial bound on the vorticity of the form
    `|ω(t, x)| ≤ C · |x|^{-p}` for all `t ∈ [0, T)` and `|x| ≥ R`
    with `p > 3` and `C ≥ 0`, then the `DecayAtInfinity` hypothesis
    is satisfied directly. -/
theorem of_uniform_polynomial_bound
    {u : VelocityField} {T : ℝ}
    (R C p : ℝ) (hR : 0 < R) (hC : 0 ≤ C) (hp : 3 < p)
    (h_bound :
      ∀ t : ℝ, 0 ≤ t → t < T → ∀ x : Vec3,
        R ≤ Real.sqrt (Vec3.dot x x) →
          Real.sqrt (Vec3.dot (vorticity u t x) (vorticity u t x)) ≤
            C / (Real.sqrt (Vec3.dot x x)) ^ p) :
    DecayAtInfinity u T :=
  { has_polynomial_decay := ⟨R, C, p, hR, hC, hp, h_bound⟩ }

end NSBlwChain.DecayAtInfinity
