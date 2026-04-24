-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.BLW.MdotODEInequality
import NSBlwChain.BLW.ChainThread
import NSBlwChain.BLW.ODEToSeregin

/-!
# Theorem 3, conditional structural threading

Top-level conditional regularity theorem on the new
`NSEvolutionAxioms`-based chain.  Bridges:

* the *envelope-form* sub-Type-I rate `(T - t) · M(t) ≤ ε`
  (output of `SubTypeOneRate.subTypeI_rate_of_log_blowup` /
  `ODEToSeregin.subTypeI_from_ode_hypothesis`),
* together with the *envelope dominance*
  `|ω(t, x)| ≤ M(t)` for all `(t, x)`,

to the *pointwise* sub-Type-I form

  `∀ ε > 0, ∃ δ > 0, ∀ t ∈ (T-δ, T), ∀ x, |ω(t, x)| ≤ ε / (T - t)`,

then applies `seregin_type_one_exclusion` (via
`ChainThread.extends_past_T_of_subTypeI`) to obtain a smooth
extension past `T`.

## Bridge lemma

* `pointwise_subTypeI_from_envelope_subTypeI` — purely scalar
  bridge: divide `(T-t) · M(t) ≤ ε` by `T - t > 0` and chain with
  `|ω(t,x)| ≤ M(t)` to land `|ω(t,x)| ≤ ε / (T-t)`.

## Top-level

* `NS_regularity_extension_from_log_blowup` — composes the bridge
  with `subTypeI_rate_of_log_blowup` and `extends_past_T_of_subTypeI`
  to produce the final smooth-extension conclusion.

## Hypotheses (all classical / per-OPEN.md status):

* `NSEvolutionAxioms u ν T` (structural).
* Envelope dominance: `|ω(t, x)| ≤ M(t)` everywhere on `(0, T)`.
* Integrated bound: `(T-t) · M(t) · log M(t) ≤ 1/4` on `(0, T)`
  (output of `Mdot_le_4Msq_logM_scalar` + `ODEIntegration_Discharge`).
* Log positivity / log-blowup encoding (per `subTypeI_rate_of_log_blowup`).

The integrated bound itself derives from
`Mdot_le_4Msq_logM_scalar` (commit 10) by ODE integration; that link
is provided by existing `ODEIntegration_Discharge` machinery, which
this file does not re-derive.
-/

namespace NSBlwChain.BLW

open Real

/-- **Bridge: envelope-form sub-Type-I → pointwise sub-Type-I.**

    From the envelope-form sub-Type-I rate `(T-t) · M(t) ≤ ε` plus
    the envelope dominance `|ω(t, x)| ≤ M(t)` everywhere, conclude
    the pointwise sub-Type-I rate `|ω(t, x)| ≤ ε / (T-t)`.

    Pure scalar arithmetic + `Real.sqrt` non-negativity. -/
theorem pointwise_subTypeI_from_envelope_subTypeI
    {u : VelocityField} {T : ℝ}
    {M : ℝ → ℝ}
    (h_dom : ∀ t : ℝ, 0 < t → t < T → ∀ x : Vec3,
      Real.sqrt (Vec3.dot (vorticity u t x) (vorticity u t x)) ≤ M t)
    (h_env_subTypeI :
      ∀ ε : ℝ, 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ t : ℝ, T - δ < t → t < T →
            (T - t) * M t ≤ ε)
    (h_M_nonneg : ∀ t : ℝ, 0 < t → t < T → 0 ≤ M t)
    (hT_pos : 0 < T) :
    ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧
        ∀ t : ℝ, T - δ < t → t < T →
          ∀ x : Vec3,
            Real.sqrt (Vec3.dot (vorticity u t x) (vorticity u t x))
              ≤ ε / (T - t) := by
  intro ε hε
  obtain ⟨δ, hδ_pos, h_env⟩ := h_env_subTypeI ε hε
  -- Clamp δ to also be ≤ T so `t > T - δ` implies `t > 0`.
  refine ⟨min δ T, lt_min hδ_pos hT_pos, ?_⟩
  intro t ht_low ht_up x
  have hδ_le : min δ T ≤ δ := min_le_left δ T
  have hT_le : min δ T ≤ T := min_le_right δ T
  have ht_low' : T - δ < t := by
    have h₁ : T - δ ≤ T - min δ T := by linarith
    linarith
  have ht_pos : 0 < t := by linarith
  have h_Tmt_pos : 0 < T - t := by linarith
  -- Apply envelope sub-Type-I.
  have h_env_t : (T - t) * M t ≤ ε := h_env t ht_low' ht_up
  -- Divide by T - t > 0 to get M t ≤ ε / (T - t).
  have h_Mt_le : M t ≤ ε / (T - t) :=
    (le_div_iff₀ h_Tmt_pos).mpr (by linarith)
  -- Compose with envelope dominance.
  have h_ω_le_M := h_dom t ht_pos ht_up x
  exact le_trans h_ω_le_M h_Mt_le

/-- **Top-level conditional regularity from log-blowup.**

    Given:

    * `ax : NSEvolutionAxioms u ν T`,
    * envelope dominance of `|ω|` by `M`,
    * the integrated bound `(T-t) · M · log M ≤ 1/4` on `(0, T)`,
    * log-positivity of `M`,
    * the log-blowup-rate encoding via `δ_of_ε`,

    apply the chain

      `subTypeI_rate_of_log_blowup` ⇒ envelope-form sub-Type-I
      `pointwise_subTypeI_from_envelope_subTypeI` ⇒ pointwise sub-Type-I
      `seregin_type_one_exclusion` ⇒ smooth extension past `T`.

    Concludes: there exists `T' > T` and an extended velocity field
    `u'` agreeing with `u` on `[0, T)`, with `NSEvolutionAxioms u' ν T'`. -/
theorem NS_regularity_extension_from_log_blowup
    {u : VelocityField} {ν T : ℝ} (ax : NSEvolutionAxioms u ν T)
    {M : ℝ → ℝ}
    (h_dom : ∀ t : ℝ, 0 < t → t < T → ∀ x : Vec3,
      Real.sqrt (Vec3.dot (vorticity u t x) (vorticity u t x)) ≤ M t)
    (h_bound :
      ∀ t : ℝ, 0 < t → t < T →
        (T - t) * M t * Real.log (M t) ≤ 1 / 4)
    (h_logM_pos : ∀ t : ℝ, 0 < t → t < T → 0 < Real.log (M t))
    (h_M_nonneg : ∀ t : ℝ, 0 < t → t < T → 0 ≤ M t)
    (δ_of_ε : ℝ → ℝ)
    (δ_pos : ∀ ε : ℝ, 0 < ε → 0 < δ_of_ε ε)
    (δ_le : ∀ ε : ℝ, 0 < ε → δ_of_ε ε ≤ T)
    (h_log_large :
      ∀ ε : ℝ, 0 < ε →
        ∀ t : ℝ, T - δ_of_ε ε < t → t < T →
          1 / (4 * ε) ≤ Real.log (M t)) :
    ∃ T' : ℝ, T < T' ∧
      ∃ u' : VelocityField, NSEvolutionAxioms u' ν T' ∧
        ∀ t : ℝ, 0 ≤ t → t < T → ∀ x : Vec3, u' t x = u t x := by
  -- Step 1: envelope-form sub-Type-I via subTypeI_rate_of_log_blowup.
  have h_env_subTypeI :
      ∀ ε : ℝ, 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ t : ℝ, T - δ < t → t < T → (T - t) * M t ≤ ε :=
    subTypeI_rate_of_log_blowup h_bound h_logM_pos h_M_nonneg ax.T_pos
      δ_of_ε δ_pos δ_le h_log_large
  -- Step 2: pointwise sub-Type-I via the bridge.
  have h_pt_subTypeI :
      ∀ ε : ℝ, 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ t : ℝ, T - δ < t → t < T →
            ∀ x : Vec3,
              Real.sqrt (Vec3.dot (vorticity u t x) (vorticity u t x))
                ≤ ε / (T - t) :=
    pointwise_subTypeI_from_envelope_subTypeI h_dom h_env_subTypeI
      h_M_nonneg ax.T_pos
  -- Step 3: apply Seregin via regularity_extension_exists.
  exact regularity_extension_exists ax h_pt_subTypeI

end NSBlwChain.BLW
