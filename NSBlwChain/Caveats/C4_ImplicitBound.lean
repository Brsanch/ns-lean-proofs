-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib

/-!
# Caveat C4 — Implicit-bound uniqueness

This file formalizes **Proposition C4** from
`paper/ns_regularity_caveats_formal.md`: the implicit inequality

  `σ ≤ Φ(σ) := M · (1 + log L + (1/2) log(σ/ν)) + K`,             (C4.1)

arising at §12.4 Step 4 of the BLW-gradient chain, has its largest
solution in `σ ≥ ν` bounded explicitly by

  `σ ≤ 4 M log M`                                                  (C4.2)

once `M` is sufficiently large.  The convexity argument underlying
(C4.2) — that `g(σ) := σ - Φ(σ)` is convex on `(0, ∞)` with minimum
at `σ = M/2`, positive at `σ₀ = 4M log M`, hence `g(σ) > 0` for
`σ ≥ σ₀` — is recorded in the paper.

## Structural organization

`ImplicitBoundBundle` packages the hypotheses of (C4.1):
* `ν > 0`, `L > 0`, `M ≥ 1`, `σ > 0`;
* The implicit inequality `σ ≤ M · (1 + log L + (1/2) log(σ/ν)) + K`
  (with an optional additive correction `K ≥ 0` absorbing the
  torus-lattice term `R_L` from Proposition C3).

The main structural consequence is a *hypothesis-consumer* theorem:
given the implicit bound plus the largeness hypothesis
`1 + log L + (1/2) log(σ/ν) ≤ 4 log M - K/M`, conclude
`σ ≤ 4 M log M`.

The largeness hypothesis itself is the output of the convexity / Banach
fixed-point analysis (Remark in §C4), which we do **not** reprove
here; it is taken as a named hypothesis.  Downstream consumers in the
main BLW chain discharge it on zero initial data via the explicit
threshold `M_*(L, ν, K)` also recorded in §C4.

## Why this shape

`ImplicitBoundBundle` is deliberately "field-heavy": it records
`ν, L, M, σ, K` separately rather than packing them into a tuple.
This matches the pattern `GrowthMomentBundle` (C1) and `C2_Envelope`
for consistency: the downstream BLW chain destructures these bundles
at a single site (`BLW/LogAbsorption.lean`, forthcoming).

## References

* Companion note §C4: convexity + two-root analysis; Banach fixed
  point on `[M, 4 M log M]`.
* Bertsekas, *Nonlinear Programming*, Prop. A.24 (fixed-point
  uniqueness via contraction).
-/

namespace NSBlwChain.Caveats

open Real

/-- **Implicit-bound bundle (Proposition C4 data).**

    Packages the implicit inequality (C4.1) into a single structure.

    The correction constant `K` absorbs the torus-lattice correction
    `R_L` from Proposition C3; for the whole-space formulation one
    sets `K = 0`.

    `M` is the `L∞` vorticity envelope at the time of evaluation;
    `σ` is the stretching functional `σ(x*, t)`; `ν` is viscosity;
    `L` is the torus side (set to `1` in the whole-space limit). -/
structure ImplicitBoundBundle where
  /-- Viscosity. -/
  ν : ℝ
  /-- Torus side length (or `1` for whole-space). -/
  L : ℝ
  /-- `L∞`-envelope of vorticity. -/
  M : ℝ
  /-- Stretching functional. -/
  σ : ℝ
  /-- Torus correction constant (set to `0` in whole-space). -/
  K : ℝ
  /-- Positivity of viscosity. -/
  hν_pos : 0 < ν
  /-- Positivity of torus side. -/
  hL_pos : 0 < L
  /-- `M ≥ 1` (the regime where the log-absorption argument operates;
      for `M < 1` the BLW chain is trivially controlled by energy). -/
  hM_ge_one : 1 ≤ M
  /-- Positivity of `σ`. -/
  hσ_pos : 0 < σ
  /-- Nonnegativity of the correction. -/
  hK_nonneg : 0 ≤ K
  /-- **The implicit inequality (C4.1).** -/
  hImplicit :
    σ ≤ M * (1 + Real.log L + (1/2) * Real.log (σ / ν)) + K

namespace ImplicitBoundBundle

variable (B : ImplicitBoundBundle)

/-- `M` is strictly positive (from `M ≥ 1`). -/
theorem M_pos : 0 < B.M := lt_of_lt_of_le zero_lt_one B.hM_ge_one

/-- `log M ≥ 0` (from `M ≥ 1`). -/
theorem log_M_nonneg : 0 ≤ Real.log B.M := Real.log_nonneg B.hM_ge_one

/-- **Main consequence (C4.2, hypothesis-consumer form).**

    Given the implicit inequality (C4.1) packaged in the bundle, and
    the *largeness hypothesis*

      `1 + log L + (1/2) log(σ/ν) ≤ 4 log M - K/M`,                (C4-large)

    we conclude `σ ≤ 4 M log M`.

    Downstream consumers (in `BLW/LogAbsorption.lean`) discharge
    (C4-large) via the convexity / two-root analysis recorded in §C4 of
    the companion note.  Here we isolate the algebraic step cleanly:
    *given* (C4-large), the implicit bound (C4.1) immediately yields
    (C4.2).

    The `K/M` correction appears because the implicit RHS has an
    additive `K` that scales relative to `M` after dividing through
    by `M > 0`. -/
theorem σ_le_of_largeness
    (hLarge :
      1 + Real.log B.L + (1/2) * Real.log (B.σ / B.ν)
        ≤ 4 * Real.log B.M - B.K / B.M) :
    B.σ ≤ 4 * B.M * Real.log B.M := by
  have hM_pos : 0 < B.M := B.M_pos
  -- Multiply (C4-large) through by M > 0.
  have hMul :
      B.M * (1 + Real.log B.L + (1/2) * Real.log (B.σ / B.ν))
        ≤ B.M * (4 * Real.log B.M - B.K / B.M) := by
    exact mul_le_mul_of_nonneg_left hLarge (le_of_lt hM_pos)
  -- Expand the RHS.  `M * (4 log M - K/M) = 4 M log M - K`.
  have hExpand :
      B.M * (4 * Real.log B.M - B.K / B.M)
        = 4 * B.M * Real.log B.M - B.K := by
    field_simp
    ring
  rw [hExpand] at hMul
  -- Combine with the implicit inequality (C4.1):
  --   σ ≤ M * (...) + K ≤ (4 M log M - K) + K = 4 M log M.
  have hChain :
      B.σ ≤ 4 * B.M * Real.log B.M - B.K + B.K := by
    calc
      B.σ ≤ B.M * (1 + Real.log B.L + (1/2) * Real.log (B.σ / B.ν)) + B.K :=
            B.hImplicit
      _ ≤ (4 * B.M * Real.log B.M - B.K) + B.K :=
            add_le_add_right hMul _
  linarith

/-- **Simplified form when `K = 0`.**  The whole-space (no
    torus-correction) version of `σ_le_of_largeness`. -/
theorem σ_le_of_largeness_of_K_zero
    (hK : B.K = 0)
    (hLarge :
      1 + Real.log B.L + (1/2) * Real.log (B.σ / B.ν)
        ≤ 4 * Real.log B.M) :
    B.σ ≤ 4 * B.M * Real.log B.M := by
  -- Rewrite `hLarge` in the form expected by `σ_le_of_largeness`:
  -- we need `4 log M - K/M ≥ 1 + log L + (1/2) log(σ/ν)`, and with
  -- K = 0 this is just `4 log M ≥ ...`.
  apply B.σ_le_of_largeness
  rw [hK]
  simp
  exact hLarge

/-- **Monotonicity of the RHS in `M`.**  Once we have `σ ≤ 4 M log M`,
    any weaker bound `σ ≤ 4 M' log M'` for `M' ≥ M` also holds,
    provided `M ≥ 1` (so `log` is monotone on the relevant range).

    This small algebraic step is used downstream when matching the
    implicit-bound output to the growth-moment input of C1 at a
    common majorant `M'`. -/
theorem σ_le_of_le
    (hσbound : B.σ ≤ 4 * B.M * Real.log B.M)
    {M' : ℝ} (hM'_ge : B.M ≤ M') :
    B.σ ≤ 4 * M' * Real.log M' := by
  have hM_pos : 0 < B.M := B.M_pos
  have hM'_pos : 0 < M' := lt_of_lt_of_le hM_pos hM'_ge
  have hM'_ge_one : 1 ≤ M' := le_trans B.hM_ge_one hM'_ge
  have hlog_le : Real.log B.M ≤ Real.log M' := Real.log_le_log hM_pos hM'_ge
  have hlog_nonneg : 0 ≤ Real.log B.M := Real.log_nonneg B.hM_ge_one
  have hlog_nonneg' : 0 ≤ Real.log M' := Real.log_nonneg hM'_ge_one
  -- `4 M log M ≤ 4 M' log M'`:
  have h1 : 4 * B.M * Real.log B.M ≤ 4 * M' * Real.log B.M := by
    have : B.M * Real.log B.M ≤ M' * Real.log B.M :=
      mul_le_mul_of_nonneg_right hM'_ge hlog_nonneg
    linarith
  have h2 : 4 * M' * Real.log B.M ≤ 4 * M' * Real.log M' := by
    have h4M'_nonneg : 0 ≤ 4 * M' := by positivity
    exact mul_le_mul_of_nonneg_left hlog_le h4M'_nonneg
  linarith

end ImplicitBoundBundle

/-! ## Structural lemmas decoupled from the bundle

A small algebraic lemma stating the (C4.2) conclusion directly, for
use in contexts where the full bundle is overkill.  Equivalent in
content to `σ_le_of_largeness`, but without the bundle wrapping. -/

/-- **Direct hypothesis-consumer form.**

    If `M ≥ 1`, `ν > 0`, `L > 0`, `σ > 0`, `K ≥ 0`, and the implicit
    bound (C4.1) plus the largeness hypothesis (C4-large) both hold,
    then `σ ≤ 4 M log M`.  This is the un-bundled form, useful when
    the caller has the hypotheses but has not packaged them into an
    `ImplicitBoundBundle`. -/
theorem σ_le_4M_log_M_of_implicit
    {ν L M σ K : ℝ}
    (hν_pos : 0 < ν) (hL_pos : 0 < L)
    (hM_ge_one : 1 ≤ M) (hσ_pos : 0 < σ) (hK_nonneg : 0 ≤ K)
    (hImplicit : σ ≤ M * (1 + Real.log L + (1/2) * Real.log (σ / ν)) + K)
    (hLarge : 1 + Real.log L + (1/2) * Real.log (σ / ν)
                ≤ 4 * Real.log M - K / M) :
    σ ≤ 4 * M * Real.log M := by
  let B : ImplicitBoundBundle :=
    { ν := ν, L := L, M := M, σ := σ, K := K,
      hν_pos := hν_pos, hL_pos := hL_pos,
      hM_ge_one := hM_ge_one, hσ_pos := hσ_pos,
      hK_nonneg := hK_nonneg,
      hImplicit := hImplicit }
  exact B.σ_le_of_largeness hLarge

/-! ## Sanity check

A trivial example: `M = 1`, `ν = 1`, `L = 1`, `σ = 1`, `K = 0`.  The
implicit inequality reduces to `1 ≤ 1 + 0 + 0 = 1`, holds with
equality.  The largeness hypothesis `1 + 0 + 0 ≤ 4 · 0 - 0` is
`1 ≤ 0`, which is FALSE — so this corner case correctly does not
satisfy the large-M regime.  Larger `M` is needed; the threshold is
the `M_*(L, ν, K)` of §C4.  We just record that the bundle is
instantiable. -/

example : ∃ (B : ImplicitBoundBundle), B.M = 1 := by
  refine ⟨
    { ν := 1, L := 1, M := 1, σ := 1, K := 0,
      hν_pos := zero_lt_one, hL_pos := zero_lt_one,
      hM_ge_one := le_refl 1, hσ_pos := zero_lt_one,
      hK_nonneg := le_refl 0,
      hImplicit := ?_ }, rfl⟩
  -- Show: 1 ≤ 1 * (1 + log 1 + (1/2) * log (1/1)) + 0
  simp [Real.log_one]

end NSBlwChain.Caveats
