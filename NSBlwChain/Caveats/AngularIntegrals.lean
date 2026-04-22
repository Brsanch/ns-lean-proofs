-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib

/-!
# Angular and far-field integrals (paper §12.4, appendix D.3)

This file formalizes the two standalone real-integration identities that
appear in the BLW-gradient chain's near/far split:

* **D.3.1** — the angular kernel integral
  `∫_0^π sin²θ · |cos θ| dθ = 2/3`.
  Used to evaluate the angular part of the Biot–Savart kernel in the
  near-zone/far-zone decomposition.

* **D.3.2** — the far-field radial log
  `∫_δ^L (1/r) dr = log L − log δ  (= log(L/δ))` for `0 < δ ≤ L`.
  This is the elementary "log of the far-field annulus" factor.

Both identities are self-contained real analysis; they require no PDE
hypotheses and no classical axioms from the NS chain.

## Proofs

For D.3.1 we split `∫_0^π` at `θ = π/2`:

* On `[0, π/2]`, `cos θ ≥ 0` so `|cos θ| = cos θ` and the integrand is
  `sin²θ · cos θ`, whose antiderivative is `F(θ) = (sin θ)^3 / 3`.
  So `∫_0^{π/2} = F(π/2) - F(0) = 1/3 - 0 = 1/3`.

* On `[π/2, π]`, `cos θ ≤ 0` so `|cos θ| = - cos θ` and the integrand is
  `- sin²θ · cos θ`, whose antiderivative is `G(θ) = -(sin θ)^3 / 3`.
  So `∫_{π/2}^π = G(π) - G(π/2) = 0 - (-1/3) = 1/3`.

Sum: `1/3 + 1/3 = 2/3`.

For D.3.2 we use the standard antiderivative of `1/r` on a strictly
positive interval, given by `Real.log`.
-/

namespace NSBlwChain.Caveats

open Real MeasureTheory intervalIntegral

/-! ### Antiderivative pieces for D.3.1 -/

/-- The antiderivative of `sin²θ · cos θ` is `(sin θ)^3 / 3`. -/
lemma hasDerivAt_sin_cube_div_three (θ : ℝ) :
    HasDerivAt (fun x : ℝ => (Real.sin x)^3 / 3)
      ((Real.sin θ)^2 * Real.cos θ) θ := by
  -- d/dθ[(sin θ)^3 / 3] = 3 · (sin θ)^2 · cos θ / 3 = (sin θ)^2 · cos θ
  have h1 : HasDerivAt (fun x : ℝ => (Real.sin x)^3)
      (3 * (Real.sin θ)^2 * Real.cos θ) θ := by
    have hsin : HasDerivAt Real.sin (Real.cos θ) θ := Real.hasDerivAt_sin θ
    simpa using hsin.pow 3
  have h2 : HasDerivAt (fun x : ℝ => (Real.sin x)^3 / 3)
      (3 * (Real.sin θ)^2 * Real.cos θ / 3) θ := h1.div_const 3
  -- Simplify the derivative expression: `3 · a · cos θ / 3 = a · cos θ`.
  have heq : 3 * (Real.sin θ)^2 * Real.cos θ / 3
              = (Real.sin θ)^2 * Real.cos θ := by ring
  simpa [heq] using h2

/-- On `[0, π/2]`, `cos` is nonneg so `|cos θ| = cos θ` and the integrand
    `sin²θ · |cos θ|` equals `sin²θ · cos θ`. -/
lemma sin_sq_abs_cos_eq_on_first_half {θ : ℝ}
    (h₀ : 0 ≤ θ) (h₁ : θ ≤ Real.pi / 2) :
    (Real.sin θ)^2 * |Real.cos θ| = (Real.sin θ)^2 * Real.cos θ := by
  have hcos_nn : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le
      (by linarith [Real.pi_pos]) h₁
  rw [abs_of_nonneg hcos_nn]

/-- On `[π/2, π]`, `cos` is nonpositive so `|cos θ| = - cos θ` and the
    integrand `sin²θ · |cos θ|` equals `- sin²θ · cos θ`. -/
lemma sin_sq_abs_cos_eq_on_second_half {θ : ℝ}
    (h₀ : Real.pi / 2 ≤ θ) (h₁ : θ ≤ Real.pi) :
    (Real.sin θ)^2 * |Real.cos θ| = - ((Real.sin θ)^2 * Real.cos θ) := by
  have hcos_np : Real.cos θ ≤ 0 :=
    Real.cos_nonpos_of_pi_div_two_le_of_le h₀
      (by linarith [Real.pi_pos])
  rw [abs_of_nonpos hcos_np]
  ring

/-! ### D.3.1: the angular kernel integral -/

/-- Integral of `sin²θ · cos θ` from `0` to `π/2` equals `1/3`. -/
lemma integral_sin_sq_cos_zero_to_pi_div_two :
    ∫ θ in (0 : ℝ)..(Real.pi / 2), (Real.sin θ)^2 * Real.cos θ = 1 / 3 := by
  have hderiv : ∀ θ ∈ Set.uIcc (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun x : ℝ => (Real.sin x)^3 / 3)
        ((Real.sin θ)^2 * Real.cos θ) θ := by
    intro θ _
    exact hasDerivAt_sin_cube_div_three θ
  have hcont : IntervalIntegrable
      (fun θ : ℝ => (Real.sin θ)^2 * Real.cos θ)
      MeasureTheory.volume 0 (Real.pi / 2) := by
    exact (Continuous.intervalIntegrable
      (by continuity) 0 (Real.pi / 2))
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont
  -- h : ∫ = (sin(π/2))^3/3 - (sin 0)^3/3
  rw [h]
  simp [Real.sin_pi_div_two, Real.sin_zero]

/-- Integral of `sin²θ · cos θ` from `π/2` to `π` equals `-1/3`. -/
lemma integral_sin_sq_cos_pi_div_two_to_pi :
    ∫ θ in (Real.pi / 2)..Real.pi, (Real.sin θ)^2 * Real.cos θ = - (1 / 3) := by
  have hderiv : ∀ θ ∈ Set.uIcc (Real.pi / 2) Real.pi,
      HasDerivAt (fun x : ℝ => (Real.sin x)^3 / 3)
        ((Real.sin θ)^2 * Real.cos θ) θ := by
    intro θ _
    exact hasDerivAt_sin_cube_div_three θ
  have hcont : IntervalIntegrable
      (fun θ : ℝ => (Real.sin θ)^2 * Real.cos θ)
      MeasureTheory.volume (Real.pi / 2) Real.pi := by
    exact (Continuous.intervalIntegrable
      (by continuity) (Real.pi / 2) Real.pi)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont
  rw [h]
  simp [Real.sin_pi_div_two, Real.sin_pi]

/-- **D.3.1 — Angular kernel integral.**

    `∫_0^π sin²θ · |cos θ| dθ = 2/3`.

    This appears in the angular part of the near-zone/far-zone split of the
    Biot–Savart kernel in §12.4 of the NS BLW-gradient chain. -/
theorem sin_sq_mul_abs_cos_integral_zero_to_pi :
    ∫ θ in (0 : ℝ)..Real.pi, (Real.sin θ)^2 * |Real.cos θ| = 2 / 3 := by
  have hπ_pos : 0 < Real.pi := Real.pi_pos
  have hhalf_le : (0 : ℝ) ≤ Real.pi / 2 := by linarith
  have hle_pi : Real.pi / 2 ≤ Real.pi := by linarith
  -- Split the integral at π/2.
  have hcont_abs : Continuous
      (fun θ : ℝ => (Real.sin θ)^2 * |Real.cos θ|) := by
    exact (Real.continuous_sin.pow 2).mul Real.continuous_cos.abs
  have hII_left : IntervalIntegrable
      (fun θ : ℝ => (Real.sin θ)^2 * |Real.cos θ|)
      MeasureTheory.volume 0 (Real.pi / 2) :=
    hcont_abs.intervalIntegrable 0 (Real.pi / 2)
  have hII_right : IntervalIntegrable
      (fun θ : ℝ => (Real.sin θ)^2 * |Real.cos θ|)
      MeasureTheory.volume (Real.pi / 2) Real.pi :=
    hcont_abs.intervalIntegrable (Real.pi / 2) Real.pi
  have h_split :
      (∫ θ in (0 : ℝ)..Real.pi, (Real.sin θ)^2 * |Real.cos θ|)
        = (∫ θ in (0 : ℝ)..(Real.pi / 2), (Real.sin θ)^2 * |Real.cos θ|)
          + (∫ θ in (Real.pi / 2)..Real.pi, (Real.sin θ)^2 * |Real.cos θ|) :=
    (intervalIntegral.integral_add_adjacent_intervals hII_left hII_right).symm
  -- On each half, reduce to the plain `sin²θ · cos θ` integrand (up to sign).
  have h_left :
      (∫ θ in (0 : ℝ)..(Real.pi / 2), (Real.sin θ)^2 * |Real.cos θ|)
        = ∫ θ in (0 : ℝ)..(Real.pi / 2), (Real.sin θ)^2 * Real.cos θ := by
    refine intervalIntegral.integral_congr ?_
    intro θ hθ
    have hθ_mem : θ ∈ Set.uIcc (0 : ℝ) (Real.pi / 2) := hθ
    rw [Set.uIcc_of_le hhalf_le] at hθ_mem
    exact sin_sq_abs_cos_eq_on_first_half hθ_mem.1 hθ_mem.2
  have h_right :
      (∫ θ in (Real.pi / 2)..Real.pi, (Real.sin θ)^2 * |Real.cos θ|)
        = ∫ θ in (Real.pi / 2)..Real.pi, -((Real.sin θ)^2 * Real.cos θ) := by
    refine intervalIntegral.integral_congr ?_
    intro θ hθ
    have hθ_mem : θ ∈ Set.uIcc (Real.pi / 2) Real.pi := hθ
    rw [Set.uIcc_of_le hle_pi] at hθ_mem
    exact sin_sq_abs_cos_eq_on_second_half hθ_mem.1 hθ_mem.2
  -- Evaluate the signed-integrand integral on `[π/2, π]` via negation.
  have h_right_eval :
      (∫ θ in (Real.pi / 2)..Real.pi, -((Real.sin θ)^2 * Real.cos θ))
        = 1 / 3 := by
    rw [intervalIntegral.integral_neg,
        integral_sin_sq_cos_pi_div_two_to_pi]
    ring
  -- Assemble: 1/3 + 1/3 = 2/3.
  rw [h_split, h_left, h_right, integral_sin_sq_cos_zero_to_pi_div_two,
      h_right_eval]
  norm_num

/-! ### D.3.2: the far-field log integral -/

/-- **D.3.2 — Far-field log integral.**

    For `0 < δ ≤ L`,
    `∫_δ^L (1/r) dr = log L − log δ`.

    Equivalent to `log(L/δ)` by `Real.log_div` when `δ ≠ 0`. -/
theorem one_over_r_integral {δ L : ℝ} (hδ : 0 < δ) (hδL : δ ≤ L) :
    ∫ r in δ..L, (1 / r) = Real.log L - Real.log δ := by
  have hL : 0 < L := lt_of_lt_of_le hδ hδL
  -- `d/dr log r = 1/r` on the interval `[δ, L] ⊂ (0, ∞)`.
  have hderiv : ∀ r ∈ Set.uIcc δ L, HasDerivAt Real.log (1 / r) r := by
    intro r hr
    rw [Set.uIcc_of_le hδL] at hr
    have hr_pos : 0 < r := lt_of_lt_of_le hδ hr.1
    have := Real.hasDerivAt_log (ne_of_gt hr_pos)
    simpa [one_div] using this
  -- `1/r` is continuous, hence interval-integrable, on `[δ, L]`.
  have hcont : ContinuousOn (fun r : ℝ => 1 / r) (Set.uIcc δ L) := by
    rw [Set.uIcc_of_le hδL]
    refine ContinuousOn.div continuousOn_const continuousOn_id ?_
    intro r hr
    exact ne_of_gt (lt_of_lt_of_le hδ hr.1)
  have hII : IntervalIntegrable (fun r : ℝ => 1 / r)
      MeasureTheory.volume δ L := by
    rw [intervalIntegrable_iff]
    have : ContinuousOn (fun r : ℝ => 1 / r) (Set.Icc (min δ L) (max δ L)) := by
      rw [min_eq_left hδL, max_eq_right hδL]
      rw [Set.uIcc_of_le hδL] at hcont
      exact hcont
    exact this.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hII

/-- **D.3.2' — log-quotient form.**

    For `0 < δ ≤ L`, `∫_δ^L (1/r) dr = log (L / δ)`. -/
theorem one_over_r_integral_log_div {δ L : ℝ} (hδ : 0 < δ) (hδL : δ ≤ L) :
    ∫ r in δ..L, (1 / r) = Real.log (L / δ) := by
  have hL : 0 < L := lt_of_lt_of_le hδ hδL
  have hL_ne : L ≠ 0 := ne_of_gt hL
  have hδ_ne : δ ≠ 0 := ne_of_gt hδ
  rw [one_over_r_integral hδ hδL, Real.log_div hL_ne hδ_ne]

end NSBlwChain.Caveats
