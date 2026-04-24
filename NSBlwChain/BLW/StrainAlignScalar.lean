-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.BLW.LaplaceAlignScalar
import NSBlwChain.Setup.NSHypothesis

/-!
# `ω · (ω·∇)u (x*) = M² · σ` under alignment — strain contraction

Discharges the fifth of the seven remaining vector-field-layer
physical identities (OPEN.md step (iii) item 6, `h_strain`) from
the alignment hypothesis `ω(x*) = (0, 0, M)`.

## The identity

Under alignment at `x*`:
```
Vec3.dot (ω t x*) (vortexStretching u ω t x*) = M² · σ
```
where `σ := ∂₃ u₃(x*)` is the scalar selected by alignment from the
strain tensor `ω̂ · S · ω̂ = S₃₃ = ∂₃ u₃` (using divergence-free /
definition of `S`).

## Proof

Two applications of the alignment contraction:

1. *Outer* alignment on `Vec3.dot`: by `dot_of_aligned_direct`,
   `Vec3.dot (ω t x*) v = M · v 2` for any `v : Vec3`.  Applied with
   `v := vortexStretching u ω t x*` gives
   `Vec3.dot ω (vortexStretching …) = M · (vortexStretching … ) 2`.

2. *Inner* alignment inside the `vortexStretching` sum:
   `(vortexStretching u ω t x*) 2 = Σᵢ (ω t x* i) · ∂ᵢ u₃(x*)`;
   under alignment the only non-zero term is `i = 2`, giving
   `M · ∂₃ u₃(x*) = M · σ` (definitionally, with `σ := ∂₃ u₃`).

Combining: `Vec3.dot ω (vortexStretching …) = M · (M · σ) = M² · σ`.
Pure alignment algebra, ~50 LOC.

## Main result

* `strain_contraction_of_aligned` — scalar identity #6 closure.

## Consumed by

- `GradientBoundAllScalarDerived.gradient_bound_of_NSEvolutionAxioms_all_scalar_derived`
  via its `h_strain` slot.
-/

namespace NSBlwChain.BLW

open scoped BigOperators

/-- **Strain contraction under alignment** (`h_strain`).

    Under alignment `ω t x = (0, 0, M)` at a point `x : Vec3`, the
    vortex-stretching contraction `Vec3.dot (ω t x) (vortexStretching u ω t x)`
    equals `M² · σ`, where `σ` is the abstract scalar satisfying
    `σ = ∂₃ u₃(x)` (the local-frame strain selector under alignment). -/
theorem strain_contraction_of_aligned
    (u : VelocityField) (ω : ℝ → Vec3 → Vec3) (t : ℝ) (x : Vec3)
    {M σ : ℝ}
    (h_0 : ω t x 0 = 0)
    (h_1 : ω t x 1 = 0)
    (h_2 : ω t x 2 = M)
    (h_σ_def : σ = partialDeriv (fun y => u t y 2) 2 x) :
    Vec3.dot (ω t x) (vortexStretching u ω t x) = M ^ 2 * σ := by
  -- Step 1: Outer alignment.  Vec3.dot (ω t x) v = M · v 2.
  rw [dot_of_aligned_direct h_0 h_1 h_2 (vortexStretching u ω t x)]
  -- Goal: M * (vortexStretching u ω t x) 2 = M² * σ.
  -- Step 2: Unfold vortexStretching at j = 2 and apply inner alignment.
  have h_vs_2 :
      vortexStretching u ω t x 2
        = M * partialDeriv (fun y => u t y 2) 2 x := by
    unfold vortexStretching
    simp only [Fin.sum_univ_three, h_0, h_1, h_2]
    ring
  rw [h_vs_2, h_σ_def]
  ring

end NSBlwChain.BLW
