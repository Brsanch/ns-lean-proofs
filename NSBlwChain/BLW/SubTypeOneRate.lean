-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib

/-!
# Sub-Type-I rate — algebraic derivation

This file formalizes the **sub-Type-I rate** conclusion of §12.4
step 8 in the companion paper, as an algebraic implication:

  From `(T - t) · M(t) · log M(t) ≤ 1/4` on `(0, T)` with
  `log M(t) > 0` and `log M → ∞` near `T`, we obtain the sub-Type-I
  rate form:
  `∀ ε > 0, ∃ δ > 0, ∀ t ∈ (T-δ, T), (T - t) · M(t) ≤ ε`.

## Scope

The ODE integration that produces `(T - t) · M · log M ≤ 1/4` from
`Ṁ ≤ 4 M² log M` is **not** proven here; it is taken as input.

## What is verified

The chain:
  `(T-t) · M · log M ≤ 1/4` + `log M large` ⇒ `(T-t) · M ≤ ε`.
is machine-verified as pure real-analysis algebra.
-/

namespace NSBlwChain.BLW

/-- **Sub-Type-I rate, pointwise form.**

    Given that at `t`:
    * `(T - t) · M(t) · log M(t) ≤ 1/4`,
    * `log M(t) > 0`,
    * `M(t) ≥ 0`,
    * `0 < T - t`,
    * `log M(t) ≥ 1 / (4 ε)` for some target `ε > 0`,
    conclude `(T - t) · M(t) ≤ ε`.

    This is the per-point reduction that the `nhdsWithin T (Iio T)`
    argument in the full sub-Type-I statement invokes pointwise
    after choosing `t` close enough to `T`. -/
theorem pointwise_subTypeI_bound
    {M_t Tmt log_M_t ε : ℝ}
    (h_bound : Tmt * M_t * log_M_t ≤ 1 / 4)
    (h_logM_pos : 0 < log_M_t)
    (h_M_nonneg : 0 ≤ M_t)
    (h_Tmt_pos : 0 < Tmt)
    (hε : 0 < ε)
    (h_log_large : 1 / (4 * ε) ≤ log_M_t) :
    Tmt * M_t ≤ ε := by
  -- Step 1: from h_bound, divide by log_M_t > 0 to get
  --   Tmt * M_t ≤ 1 / (4 * log_M_t).
  have h_div : Tmt * M_t ≤ 1 / (4 * log_M_t) := by
    rw [le_div_iff₀ (by positivity : 0 < 4 * log_M_t)]
    nlinarith [h_bound, h_logM_pos]
  -- Step 2: from h_log_large, 1 / (4 * log_M_t) ≤ ε.
  have h_inv : 1 / (4 * log_M_t) ≤ ε := by
    rw [div_le_iff₀ (by positivity : 0 < 4 * log_M_t)]
    -- Goal: 1 ≤ ε * (4 * log_M_t).
    have h4ε_pos : (0 : ℝ) < 4 * ε := by linarith
    have : (4 * ε) * (1 / (4 * ε)) = 1 := by
      field_simp
    calc (1 : ℝ)
        = (4 * ε) * (1 / (4 * ε)) := by rw [this]
      _ ≤ (4 * ε) * log_M_t :=
          mul_le_mul_of_nonneg_left h_log_large (le_of_lt h4ε_pos)
      _ = ε * (4 * log_M_t) := by ring
  linarith

/-- **Sub-Type-I rate, eventually form.**

    Packages `pointwise_subTypeI_bound` into a uniform-on-neighborhood
    form: if the bound `(T-t) · M · log M ≤ 1/4` holds on all of
    `(0, T)` with `log M > 0` and `log M → ∞`, then the sub-Type-I
    rate `(T-t) · M ≤ ε` holds for every `ε > 0` on a one-sided
    neighborhood of `T`.

    The "`log M → ∞`" hypothesis is encoded via an explicit
    function `δ_of_ε : ℝ → ℝ` that returns, for each `ε > 0`, a
    positive `δ` such that `log M(t) ≥ 1/(4ε)` on `(T - δ, T)`.
    (This encapsulates the `nhdsWithin T (Iio T)` argument cleanly.) -/
theorem subTypeI_rate_of_log_blowup
    {M : ℝ → ℝ} {T : ℝ}
    (h_bound : ∀ t : ℝ, 0 < t → t < T → (T - t) * M t * Real.log (M t) ≤ 1 / 4)
    (h_logM_pos : ∀ t : ℝ, 0 < t → t < T → 0 < Real.log (M t))
    (h_M_nonneg : ∀ t : ℝ, 0 < t → t < T → 0 ≤ M t)
    (hT_pos : 0 < T)
    (δ_of_ε : ℝ → ℝ)
    (δ_pos : ∀ ε : ℝ, 0 < ε → 0 < δ_of_ε ε)
    (δ_le : ∀ ε : ℝ, 0 < ε → δ_of_ε ε ≤ T)
    (h_log_large :
      ∀ ε : ℝ, 0 < ε →
        ∀ t : ℝ, T - δ_of_ε ε < t → t < T →
          1 / (4 * ε) ≤ Real.log (M t)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧
        ∀ t : ℝ, T - δ < t → t < T →
          (T - t) * M t ≤ ε := by
  intro ε hε
  refine ⟨δ_of_ε ε, δ_pos ε hε, ?_⟩
  intro t ht_low ht_up
  -- t ∈ (T - δ_of_ε ε, T), so `0 < T - t < δ_of_ε ε`.
  have h_Tmt_pos : 0 < T - t := by linarith
  -- Also `0 < t` since `T - δ_of_ε ε < t` and `δ_of_ε ε ≤ T`.
  have ht_pos : 0 < t := by
    have : T - δ_of_ε ε < t := ht_low
    linarith [δ_le ε hε]
  have h_b := h_bound t ht_pos ht_up
  have h_lp := h_logM_pos t ht_pos ht_up
  have h_mn := h_M_nonneg t ht_pos ht_up
  have h_ll := h_log_large ε hε t ht_low ht_up
  exact pointwise_subTypeI_bound h_b h_lp h_mn h_Tmt_pos hε h_ll

end NSBlwChain.BLW
