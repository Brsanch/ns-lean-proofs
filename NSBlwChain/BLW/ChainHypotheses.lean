-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Setup.VectorFields
import NSBlwChain.Setup.NSHypothesis
import NSBlwChain.Setup.ClassicalAxioms
import NSBlwChain.BLW.SubTypeOneRate

/-!
# Umbrella hypothesis bundle for the BLW chain

This file defines a single umbrella structure `BLWChainHypotheses`
that packages the collection of analytical hypotheses needed to
close the BLW-gradient chain end-to-end from `NSEvolutionAxioms` +
the three classical axioms to Seregin's regularity extension.

## Contents

* `BLWChainHypotheses` — umbrella bundle, fields enumerate the
  per-analytical-pass gaps that still need discharge.

* `proposition_four_of_hypotheses` — delivers regularity extension
  given `NSEvolutionAxioms` + the umbrella bundle.

## Scope

This is a pure structural wiring layer.  Each field of
`BLWChainHypotheses` corresponds to an analytical sub-project
that would be closed in its own file (step i/ii/iii discharges,
FTC for `M`, Banach fixed point for C4, ODE integration for
sub-Type-I).
-/

namespace NSBlwChain.BLW

open NSBlwChain

/-- **Umbrella bundle of remaining analytical hypotheses.**

    Given an `NSEvolutionAxioms u ν T`, the following scalar
    inputs suffice to run the BLW chain to Seregin's conclusion. -/
structure BLWChainHypotheses
    (u : VelocityField) (ν T : ℝ) where
  /-- The scalar envelope `M(t) := ‖ω(t, ·)‖_∞`. -/
  M : ℝ → ℝ
  /-- Positive viscosity (mirror of NSEvolutionAxioms.nu_pos). -/
  nu_pos : 0 < ν
  /-- Positive singular time. -/
  T_pos : 0 < T
  /-- `M` is non-negative on `[0, T)`. -/
  M_nonneg : ∀ t : ℝ, 0 ≤ t → t < T → 0 ≤ M t
  /-- `M(t) > 1` on a one-sided neighborhood of `T` (growth regime
      dominates near `T`). -/
  M_gt_one :
    ∃ t₀ : ℝ, 0 < t₀ ∧ t₀ < T ∧ ∀ t : ℝ, t₀ < t → t < T → 1 < M t
  /-- The integrated ODE bound
      `(T-t) · M · log M ≤ 1/4` on `(t₀, T)` for some `t₀ > 0`. -/
  ode_bound :
    ∀ t : ℝ, 0 < t → t < T → (T - t) * M t * Real.log (M t) ≤ 1 / 4
  /-- `log M > 0` on `(0, T)` (so `M > 1` on the growth regime). -/
  log_M_pos : ∀ t : ℝ, 0 < t → t < T → 0 < Real.log (M t)
  /-- `log M → ∞` at `T⁻`, encoded via a `δ_of_ε` function. -/
  δ_of_ε : ℝ → ℝ
  δ_of_ε_pos : ∀ ε : ℝ, 0 < ε → 0 < δ_of_ε ε
  δ_of_ε_le : ∀ ε : ℝ, 0 < ε → δ_of_ε ε ≤ T
  log_M_large :
    ∀ ε : ℝ, 0 < ε →
      ∀ t : ℝ, T - δ_of_ε ε < t → t < T →
        1 / (4 * ε) ≤ Real.log (M t)
  /-- Pointwise vorticity-envelope identification:
      `|ω(t, x)| ≤ M(t)` for all `x`. -/
  omega_bounded_by_M :
    ∀ t : ℝ, 0 ≤ t → t < T → ∀ x : Vec3,
      Real.sqrt (Vec3.dot (vorticity u t x) (vorticity u t x)) ≤ M t

/-- **End-to-end: Proposition 4 from the umbrella bundle.**

    Given an `NSEvolutionAxioms` and a `BLWChainHypotheses`
    umbrella, deliver Seregin's extension: the evolution extends
    to a time `T' > T`. -/
noncomputable def proposition_four_of_hypotheses
    {u : VelocityField} {ν T : ℝ}
    (ax : NSEvolutionAxioms u ν T)
    (H : BLWChainHypotheses u ν T) :
    SereginTypeOneExclusion u ν T := by
  -- Step 1: land the `(T-t) · M ≤ ε` form on a one-sided neighborhood.
  have hM_nn_strict : ∀ t : ℝ, 0 < t → t < T → 0 ≤ H.M t :=
    fun t ht htT => H.M_nonneg t (le_of_lt ht) htT
  have h_subTypeI_scalar :
      ∀ ε : ℝ, 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ t : ℝ, T - δ < t → t < T →
            (T - t) * H.M t ≤ ε :=
    subTypeI_rate_of_log_blowup H.ode_bound H.log_M_pos hM_nn_strict
      H.T_pos H.δ_of_ε H.δ_of_ε_pos H.δ_of_ε_le H.log_M_large
  -- Step 2: translate into Seregin's signature `|ω| ≤ ε/(T-t)`.
  have h_subTypeI_omega :
      ∀ ε : ℝ, 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ t : ℝ, T - δ < t → t < T →
            ∀ x : Vec3,
              Real.sqrt (Vec3.dot (vorticity u t x) (vorticity u t x))
                ≤ ε / (T - t) := by
    intro ε hε
    obtain ⟨δ, hδ_pos, hbound⟩ := h_subTypeI_scalar ε hε
    -- Refine δ so that `t > 0` is automatic.
    refine ⟨min δ T, lt_min hδ_pos H.T_pos, ?_⟩
    intro t ht_low ht_up x
    have h_δ_le : min δ T ≤ δ := min_le_left _ _
    have h_δT_le : min δ T ≤ T := min_le_right _ _
    have ht_lowδ : T - δ < t := by
      have : T - min δ T ≤ T - (min δ T) := le_refl _
      linarith [ht_low, h_δ_le]
    have h_scalar := hbound t ht_lowδ ht_up
    -- Need `0 < t` for `M_nonneg` / `omega_bounded_by_M`.
    have ht_pos : 0 < t := by
      have : T - min δ T ≥ T - T := by linarith
      -- `T - min δ T ≥ 0` and `t > T - min δ T`, so `t > 0`.
      linarith [ht_low, h_δT_le, H.T_pos]
    -- |ω| ≤ M(t), so (T-t) · |ω| ≤ (T-t) · M(t) ≤ ε.
    have h_omega_le := H.omega_bounded_by_M t (le_of_lt ht_pos) ht_up x
    -- (T-t) > 0.
    have h_Tmt_pos : 0 < T - t := by linarith
    -- Derive |ω| ≤ ε / (T - t).
    have : (T - t) * Real.sqrt (Vec3.dot (vorticity u t x) (vorticity u t x))
            ≤ ε := by
      calc (T - t) * Real.sqrt (Vec3.dot (vorticity u t x) (vorticity u t x))
          ≤ (T - t) * H.M t :=
            mul_le_mul_of_nonneg_left h_omega_le (le_of_lt h_Tmt_pos)
        _ ≤ ε := h_scalar
    rwa [le_div_iff₀ h_Tmt_pos, mul_comm]
  exact seregin_type_one_exclusion ax h_subTypeI_omega

end NSBlwChain.BLW
