-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.BLW.MaxPrincipleFromLocalMax

/-!
# `Δω₃(x*) ≤ 0` from `IsLocalMax |ω|²` + alignment

Paper Theorem 12.2 Step (ii) (tightened 2026-04-23 after second-pass
audit) derives the sign `Δω₃(x*) ≤ 0` from:

1. `|ω|²` attains a local max at `x*` (the argmax hypothesis).
2. Alignment: `ω(x*) = M · ê₃`, i.e., `ω₀(x*) = 0`, `ω₁(x*) = 0`,
   `ω₃(x*) = M`, with `M ≥ 0`.
3. Componentwise Cauchy–Schwarz: `(ω₃(x))² ≤ |ω(x)|²` always.

Combining (1)–(3) gives `(ω₃(x))² ≤ |ω(x)|² ≤ |ω(x*)|² = M²`
on a neighborhood of `x*`, so `|ω₃(x)| ≤ M = ω₃(x*)`; hence
`ω₃(x) ≤ ω₃(x*)` locally, i.e. the scalar `ω₃` attains a genuine
local max at `x*`.  Applying the scalar 1-D 2nd-derivative test
(`MaxPrincipleFromLocalMax.isLocalMax_second_deriv_nonpos`) in each
coordinate direction `i ∈ Fin 3` and summing gives

  `Δω₃(x*) = Σ_i ∂²_i ω₃(x*) ≤ 0`.

This file discharges **the second of the seven remaining vector-
field physical identities** (OPEN.md step (ii) item 2).  The
construction parallels `HessianExpansionScalar.lean` in scope —
pure Fin 3 algebra + per-slice 1-D reasoning — at ~100 LOC.

## Main results

* `vec3_component_sq_le_normSq` — pointwise `(v k)² ≤ Vec3.dot v v`
  for any `k : Fin 3` (elementary Cauchy–Schwarz squared form).

* `isLocalMax_omega3_of_isLocalMax_sqNorm` — the main structural
  lemma: `IsLocalMax ω₃` from `IsLocalMax |ω|²` + alignment.

* `laplaceOmega3_nonpos_from_IsLocalMax` — the final scalar
  inequality `(∑ i, ∂²_i ω₃(x*)) ≤ 0`.
-/

namespace NSBlwChain.BLW

open Filter
open scoped BigOperators Topology

/-- **Componentwise Cauchy–Schwarz (squared form).**
    For any `v : Fin 3 → ℝ` and any `k : Fin 3`:
    `(v k)² ≤ Vec3.dot v v = Σ_i (v i)²`. -/
theorem vec3_component_sq_le_normSq (v : Fin 3 → ℝ) (k : Fin 3) :
    (v k) ^ 2 ≤ Vec3.dot v v := by
  -- Direct via Finset.single_le_sum on the sum of non-negative terms,
  -- avoiding `fin_cases` which leaves unreduced `Fin.mk` indices.
  calc (v k) ^ 2
      = v k * v k                      := by ring
    _ ≤ ∑ i : Fin 3, v i * v i         :=
        Finset.single_le_sum
          (f := fun i : Fin 3 => v i * v i)
          (fun i _ => mul_self_nonneg (v i))
          (Finset.mem_univ k)
    _ = Vec3.dot v v                   := rfl

/-- **Local max of `ω₃` from local max of `|ω|²` + alignment.**

    Given a vector field `ω : Vec3 → (Fin 3 → ℝ)` such that
    `y ↦ Vec3.dot (ω y) (ω y)` attains a local max at `xStar`, plus
    the alignment condition `ω(xStar) = (0, 0, M)` with `M ≥ 0`, the
    scalar third component `fun y => ω y 2` attains a local max
    at `xStar`. -/
theorem isLocalMax_omega3_of_isLocalMax_sqNorm
    (ω : Vec3 → Fin 3 → ℝ) (xStar : Vec3) (M : ℝ)
    (hM_nonneg : 0 ≤ M)
    (hω0 : ω xStar 0 = 0)
    (hω1 : ω xStar 1 = 0)
    (hω3 : ω xStar 2 = M)
    (hmax : IsLocalMax (fun y => Vec3.dot (ω y) (ω y)) xStar) :
    IsLocalMax (fun y => ω y 2) xStar := by
  -- |ω(xStar)|² = ω_0² + ω_1² + ω_2² = 0 + 0 + M² = M².
  have hNorm_xStar : Vec3.dot (ω xStar) (ω xStar) = M ^ 2 := by
    simp only [Vec3.dot, Fin.sum_univ_three, hω0, hω1, hω3]
    ring
  -- On a neighborhood of xStar, |ω(y)|² ≤ M² and thus ω_3(y) ≤ M.
  filter_upwards [hmax] with y hy
  -- hy : Vec3.dot (ω y) (ω y) ≤ Vec3.dot (ω xStar) (ω xStar)
  rw [hNorm_xStar] at hy
  -- hy : Vec3.dot (ω y) (ω y) ≤ M²
  -- Cauchy–Schwarz: (ω y 2)² ≤ |ω(y)|².
  have h3_sq_le_norm : (ω y 2) ^ 2 ≤ Vec3.dot (ω y) (ω y) :=
    vec3_component_sq_le_normSq (ω y) 2
  have h3_sq_le_M_sq : (ω y 2) ^ 2 ≤ M ^ 2 := le_trans h3_sq_le_norm hy
  -- Take sqrt: |ω_3(y)| ≤ |M| = M (using M ≥ 0).
  have habs_le : |ω y 2| ≤ M := by
    have h1 : Real.sqrt ((ω y 2) ^ 2) ≤ Real.sqrt (M ^ 2) :=
      Real.sqrt_le_sqrt h3_sq_le_M_sq
    rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq hM_nonneg] at h1
  -- ω_3(y) ≤ |ω_3(y)| ≤ M = ω_3(xStar).
  calc ω y 2
      ≤ |ω y 2|    := le_abs_self _
    _ ≤ M          := habs_le
    _ = ω xStar 2  := hω3.symm

/-- **`Δω₃(x*) ≤ 0` from `IsLocalMax |ω|²` + alignment + slice
    smoothness.**

    Consumes the scalar alignment data `(ω, xStar, M, hM_nonneg, hω0,
    hω1, hω3)`, the argmax `hmax : IsLocalMax |ω|² xStar`, and the
    usual per-slice differentiability hypotheses `(hf_nhd, hD)` for
    the scalar component `fun y => ω y 2`.

    Produces `(∑ i : Fin 3, deriv (deriv (slice (fun y => ω y 2) xStar i)) 0) ≤ 0`,
    which is the scalar `Δω₃(x*) ≤ 0` in the `ArgmaxAnalyticalBundle`
    formulation downstream. -/
theorem laplaceOmega3_nonpos_from_IsLocalMax
    (ω : Vec3 → Fin 3 → ℝ) (xStar : Vec3) (M : ℝ)
    (hM_nonneg : 0 ≤ M)
    (hω0 : ω xStar 0 = 0)
    (hω1 : ω xStar 1 = 0)
    (hω3 : ω xStar 2 = M)
    (hmax : IsLocalMax (fun y => Vec3.dot (ω y) (ω y)) xStar)
    (hf_nhd : ∀ i : Fin 3,
      ∀ᶠ t in 𝓝 (0 : ℝ),
        DifferentiableAt ℝ (slice (fun y => ω y 2) xStar i) t)
    (hD : ∀ i : Fin 3,
      DifferentiableAt ℝ
        (deriv (slice (fun y => ω y 2) xStar i)) 0) :
    (∑ i : Fin 3,
        deriv (deriv (slice (fun y => ω y 2) xStar i)) 0) ≤ 0 := by
  -- Step 1: ω_3 attains a local max at xStar.
  have hmax_ω3 : IsLocalMax (fun y => ω y 2) xStar :=
    isLocalMax_omega3_of_isLocalMax_sqNorm ω xStar M
      hM_nonneg hω0 hω1 hω3 hmax
  -- Step 2: Apply the scalar local-max 2nd-derivative test per direction.
  have d0_nonpos :
      deriv (deriv (slice (fun y => ω y 2) xStar 0)) 0 ≤ 0 :=
    isLocalMax_second_deriv_nonpos
      (isLocalMax_slice hmax_ω3 0) (hf_nhd 0) (hD 0)
  have d1_nonpos :
      deriv (deriv (slice (fun y => ω y 2) xStar 1)) 0 ≤ 0 :=
    isLocalMax_second_deriv_nonpos
      (isLocalMax_slice hmax_ω3 1) (hf_nhd 1) (hD 1)
  have d2_nonpos :
      deriv (deriv (slice (fun y => ω y 2) xStar 2)) 0 ≤ 0 :=
    isLocalMax_second_deriv_nonpos
      (isLocalMax_slice hmax_ω3 2) (hf_nhd 2) (hD 2)
  -- Step 3: Sum over Fin 3.
  simp only [Fin.sum_univ_three]
  linarith

end NSBlwChain.BLW
