-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.BLW.DecayToCocompact

/-!
# Decay → threshold-finder bridge with explicit constants

Real analytical content: from the polynomial-decay constants
`(R, C, p)` of `DecayAtInfinity` (made explicit, not threaded
through `Classical.choose`), build the threshold-finder
`R_of_ε : ℝ → ℝ` consumed by
`tendsto_cocompact_zero_of_threshold`.

## Strategy

Given `ε > 0`, choose `R_of_ε ε` satisfying:

* `R_of_ε ε ≥ R` (decay applies for `|x| ≥ R_of_ε ε`).
* `(R_of_ε ε)^(2p) ≥ C² / ε + 1` (rpow inequality giving room to
  conclude `|ω|² < ε`).

Then for any `x` with `ε ≤ |ω(t, x)|²`, the contrapositive gives
`|x|_2 ≤ R_of_ε ε`.

## Hypothesis form

This commit provides the **algebraic core** consuming explicit
decay constants `(R, C, p)` and a candidate threshold-finder
`R_of_ε` satisfying the two properties above.  The actual
rpow-arithmetic constructor producing
`R_of_ε ε := max R ((C²/ε + 1)^(1/(2p)))` is delegated to a
future commit.

## Main result

* `decay_threshold_property_from_explicit_constants` —
  algebraic-core theorem.
-/

namespace NSBlwChain.BLW

open Real
open scoped BigOperators
open NSBlwChain

/-- **Threshold property from explicit decay constants + radius bound.**

    Given the explicit decay constants `(R, C, p)` (with `0 < R`,
    `0 ≤ C`, `3 < p`) and the per-time decay statement
    `R ≤ |x|_2 ⇒ |ω(t, x)| ≤ C / |x|_2^p`, plus a candidate
    threshold-finder `R_of_ε` with:

    * `R_of_ε ε ≥ R` (so decay applies),
    * `R_of_ε ε > 0`,
    * `(R_of_ε ε)^(2*p) ≥ C^2 / ε + 1` (rpow margin for ε strict),

    derive the threshold property: `ε ≤ |ω(t, x)|² ⇒ |x|_2 ≤ R_of_ε ε`.

    Algebraic core: contrapositive on `|x|_2 > R_of_ε ε ⇒ |ω(t,x)|² < ε`,
    via decay + squaring + rpow monotonicity. -/
theorem decay_threshold_property_from_explicit_constants
    {u : VelocityField} {t : ℝ}
    {R C p : ℝ} (hR_pos : 0 < R) (hC_nn : 0 ≤ C) (hp_gt_3 : 3 < p)
    (h_decay : ∀ x : Vec3,
      R ≤ Real.sqrt (Vec3.dot x x) →
        Real.sqrt (Vec3.dot (vorticity u t x) (vorticity u t x)) ≤
          C / (Real.sqrt (Vec3.dot x x)) ^ p)
    (R_of_ε : ℝ → ℝ)
    (hR_of_ε_pos : ∀ ε : ℝ, 0 < ε → 0 < R_of_ε ε)
    (hR_of_ε_ge_R : ∀ ε : ℝ, 0 < ε → R ≤ R_of_ε ε)
    (h_rpow_bound :
      ∀ ε : ℝ, 0 < ε →
        C ^ 2 / ε + 1 ≤ (R_of_ε ε) ^ (2 * p)) :
    ∀ ε : ℝ, 0 < ε → ∀ x : Vec3,
      ε ≤ |Vec3.dot (vorticity u t x) (vorticity u t x)| →
        Real.sqrt (Vec3.dot x x) ≤ R_of_ε ε := by
  intro ε hε x h_ε_le
  -- Contrapositive: assume `R_of_ε ε < √(Vec3.dot x x)` and derive
  -- a contradiction with `ε ≤ |Vec3.dot (ω x) (ω x)|`.
  by_contra h_contra
  push_neg at h_contra
  -- `h_contra : R_of_ε ε < √(Vec3.dot x x)`.
  set rx : ℝ := Real.sqrt (Vec3.dot x x) with hrx_def
  have hrx_nn : 0 ≤ rx := Real.sqrt_nonneg _
  have hR_of_ε_pos_ε : 0 < R_of_ε ε := hR_of_ε_pos ε hε
  have hR_of_ε_ge_R_ε : R ≤ R_of_ε ε := hR_of_ε_ge_R ε hε
  have hrx_gt_R : R < rx :=
    lt_of_le_of_lt hR_of_ε_ge_R_ε h_contra
  have hrx_pos : 0 < rx := lt_of_lt_of_le hR_pos (le_of_lt hrx_gt_R)
  -- Apply decay at x: `√(Vec3.dot ω ω) ≤ C / rx^p`.
  have h_decay_x : Real.sqrt (Vec3.dot (vorticity u t x) (vorticity u t x))
      ≤ C / rx ^ p := h_decay x (le_of_lt hrx_gt_R)
  -- Both sides non-negative.
  have h_lhs_nn : 0 ≤ Real.sqrt (Vec3.dot (vorticity u t x) (vorticity u t x)) :=
    Real.sqrt_nonneg _
  have h_rxp_pos : 0 < rx ^ p := Real.rpow_pos_of_pos hrx_pos p
  have h_rhs_nn : 0 ≤ C / rx ^ p := div_nonneg hC_nn (le_of_lt h_rxp_pos)
  -- Square both sides: `Vec3.dot ω ω ≤ C² / rx^(2p)`.
  have h_dot_nn : 0 ≤ Vec3.dot (vorticity u t x) (vorticity u t x) := by
    unfold Vec3.dot
    apply Finset.sum_nonneg
    intro j _
    exact mul_self_nonneg _
  have h_dot_eq : Real.sqrt (Vec3.dot (vorticity u t x) (vorticity u t x)) ^ 2
      = Vec3.dot (vorticity u t x) (vorticity u t x) :=
    Real.sq_sqrt h_dot_nn
  have h_decay_sq :
      Vec3.dot (vorticity u t x) (vorticity u t x) ≤ (C / rx ^ p) ^ 2 := by
    rw [← h_dot_eq]
    exact pow_le_pow_left₀ h_lhs_nn h_decay_x 2
  -- Simplify `(C / rx^p)^2 = C^2 / rx^(2p)`.
  have h_rxp_ne : rx ^ p ≠ 0 := ne_of_gt h_rxp_pos
  have h_rx_2p_eq : rx ^ p * rx ^ p = rx ^ (2 * p) := by
    rw [← Real.rpow_add hrx_pos]; ring_nf
  have h_simplify : (C / rx ^ p) ^ 2 = C ^ 2 / rx ^ (2 * p) := by
    rw [div_pow, sq, ← h_rx_2p_eq]
  rw [h_simplify] at h_decay_sq
  -- So: Vec3.dot ω ω ≤ C^2 / rx^(2*p).
  -- Combined with ε ≤ |Vec3.dot ω ω| = Vec3.dot ω ω (positive):
  have h_abs_eq : |Vec3.dot (vorticity u t x) (vorticity u t x)|
      = Vec3.dot (vorticity u t x) (vorticity u t x) := abs_of_nonneg h_dot_nn
  rw [h_abs_eq] at h_ε_le
  -- ε ≤ Vec3.dot ω ω ≤ C^2 / rx^(2p), so ε ≤ C^2 / rx^(2p).
  have h_ε_le_quotient : ε ≤ C ^ 2 / rx ^ (2 * p) := le_trans h_ε_le h_decay_sq
  -- Rearrange: rx^(2p) · ε ≤ C^2.  Then C^2/ε ≥ rx^(2p).
  have h_rx2p_pos : 0 < rx ^ (2 * p) := Real.rpow_pos_of_pos hrx_pos _
  have h_mul : rx ^ (2 * p) * ε ≤ C ^ 2 := by
    have := h_ε_le_quotient
    rw [le_div_iff₀ h_rx2p_pos] at this
    linarith
  have h_div : rx ^ (2 * p) ≤ C ^ 2 / ε := by
    rw [le_div_iff₀ hε]; linarith
  -- But h_rpow_bound: C²/ε + 1 ≤ R_of_ε ε ^ (2p), so
  -- C²/ε < (R_of_ε ε)^(2p).
  have h_strict : C ^ 2 / ε < (R_of_ε ε) ^ (2 * p) := by
    have := h_rpow_bound ε hε
    linarith
  -- And rx > R_of_ε ε > 0, so rx^(2p) > (R_of_ε ε)^(2p) by rpow monotonicity.
  have h_rpow_strict : (R_of_ε ε) ^ (2 * p) < rx ^ (2 * p) := by
    have h2p_pos : 0 < 2 * p := by linarith
    exact Real.rpow_lt_rpow (le_of_lt hR_of_ε_pos_ε) h_contra h2p_pos
  -- Chain: rx^(2p) > R_of_ε ε ^ (2p) > C²/ε ≥ rx^(2p).  Contradiction.
  linarith

end NSBlwChain.BLW
