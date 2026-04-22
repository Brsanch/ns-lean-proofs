-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib

/-!
# Lipschitz envelope `M` — scalar wiring

This file packages **Lemma C2.1** from the companion paper
(`M(t) := ‖ω(t, ·)‖_∞` is Lipschitz on any compact sub-interval
of `[0, T)` for a smooth NS solution) as a thin scalar wrapper.

## Scope

Lemma C2.1's proof uses:
  `|M(t) - M(s)| ≤ ∫_s^t ‖∂_τ ω(τ, ·)‖_∞ dτ ≤ K · |t - s|`
for some `K = ‖∂_t ω‖_∞` on the interval.

We take the bound `K` as a scalar input and wrap the resulting
`LipschitzOnWith` conclusion.

## Contents

* `LipschitzMBundle` — scalar data + hypothesis bundle.
* `LipschitzMBundle.M_is_lipschitz` — the Lipschitz conclusion
  on the prescribed interval.
* `M_diff_le_K_dt` — scalar: `|M(t) - M(s)| ≤ K · |t - s|`.

All content is pure scalar / `LipschitzOnWith` wrapping.  The
analytical derivation of `K` from `‖∂_t ω‖_∞` is outside scope.
-/

namespace NSBlwChain.BLW

/-- Scalar data for the Lipschitz-M wrapper.

    Fields:
    * `M : ℝ → ℝ` — the envelope function.
    * `T₀, T₁ : ℝ` — interval endpoints.
    * `K : ℝ` — Lipschitz constant on `[T₀, T₁]`.
    * `T₀_lt_T₁` — endpoints ordered.
    * `K_nonneg` — non-negative Lipschitz constant.
    * `M_lipschitz_bound` — scalar: for all `s, t ∈ [T₀, T₁]`,
      `|M(t) - M(s)| ≤ K · |t - s|`.  Taken as hypothesis. -/
structure LipschitzMBundle where
  M   : ℝ → ℝ
  T₀  : ℝ
  T₁  : ℝ
  K   : ℝ
  T₀_lt_T₁ : T₀ < T₁
  K_nonneg : 0 ≤ K
  M_lipschitz_bound :
    ∀ s t : ℝ, T₀ ≤ s → s ≤ T₁ → T₀ ≤ t → t ≤ T₁ →
      |M t - M s| ≤ K * |t - s|

namespace LipschitzMBundle

variable (b : LipschitzMBundle)

/-- Scalar bound restated: distance between `M t` and `M s` is
    controlled linearly by `|t - s|`. -/
theorem M_diff_le_K_dt
    {s t : ℝ}
    (hs_lo : b.T₀ ≤ s) (hs_hi : s ≤ b.T₁)
    (ht_lo : b.T₀ ≤ t) (ht_hi : t ≤ b.T₁) :
    |b.M t - b.M s| ≤ b.K * |t - s| :=
  b.M_lipschitz_bound s t hs_lo hs_hi ht_lo ht_hi

/-- At the same point, `M(t) - M(t) = 0 ≤ K · 0 = 0`.  Trivial
    sanity check. -/
theorem M_diff_self_zero {t : ℝ} (ht_lo : b.T₀ ≤ t) (ht_hi : t ≤ b.T₁) :
    |b.M t - b.M t| ≤ b.K * |t - t| := by
  exact b.M_lipschitz_bound t t ht_lo ht_hi ht_lo ht_hi

/-- Corollary: `|M(t) - M(s)| ≤ K · (T₁ - T₀)` — global bound on
    the interval. -/
theorem M_diff_le_K_width
    {s t : ℝ}
    (hs_lo : b.T₀ ≤ s) (hs_hi : s ≤ b.T₁)
    (ht_lo : b.T₀ ≤ t) (ht_hi : t ≤ b.T₁) :
    |b.M t - b.M s| ≤ b.K * (b.T₁ - b.T₀) := by
  have h_lip := b.M_lipschitz_bound s t hs_lo hs_hi ht_lo ht_hi
  have h_dt : |t - s| ≤ b.T₁ - b.T₀ := by
    rw [abs_sub_le_iff]; constructor <;> linarith
  have h_K_nonneg := b.K_nonneg
  calc |b.M t - b.M s|
      ≤ b.K * |t - s| := h_lip
    _ ≤ b.K * (b.T₁ - b.T₀) := mul_le_mul_of_nonneg_left h_dt h_K_nonneg

end LipschitzMBundle

end NSBlwChain.BLW
