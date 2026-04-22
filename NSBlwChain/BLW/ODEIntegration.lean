-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.BLW.SubTypeOneRate

/-!
# ODE integration for the sub-Type-I rate

This file isolates the **ODE-integration** step in §12.4 of the
companion paper (paper path `paper/ns_regularity.md`, step 7→8):

  Given a scalar envelope `M : ℝ → ℝ` satisfying the differential
  inequality
  `d/dt M(t) ≤ 4 · M(t)² · log M(t)`  (a.e. on `(t₀, T)`)
  together with `M > 1` and a log-blow-up hypothesis at `T⁻`,
  derive the integrated pointwise bound
  `(T - t) · M(t) · log M(t) ≤ 1 / 4`
  on a one-sided neighborhood of `T`.

## Scope — hypothesis-consumer form

The **full** real-analysis derivation (via the substitution
`v(t) := 1/M(t)` with `v̇ ≥ 4 · log v` and an integration-by-parts
computation yielding the constant `1/4`) is genuinely involved; a
first-class mathlib formalization would require `MeasureTheory.ODE`
infrastructure that is outside the tractable scope of this session.

Instead, this file follows the same pattern as
`BLW/ChainHypotheses.lean`: we bundle the analytical inputs into a
`DifferentialInequalityBundle` structure and **take** the integrated
conclusion as a field of the bundle.  The theorem
`integrated_bound_of_differential` is then a clean re-export, and
upstream code (`SubTypeOneRate`, `ODEToSeregin`, `ChainHypotheses`)
consumes the re-exported scalar inequality in the exact form its
existing interfaces require.

When the full ODE integration is later closed, only the bundle's
constructor changes; no downstream code moves.

## Contents

* `DifferentialInequalityBundle` — packages the scalar function,
  the singular time, the differential-inequality field, the
  log-blow-up field, and the integrated-form field.
* `integrated_bound_of_differential` — hypothesis-consumer: delivers
  `(T - t) · M · log M ≤ 1/4` from the bundle.
* `log_M_pos_of_bundle` — auxiliary extractor for `log M > 0` from
  the `M > 1` field.
* `subTypeI_rate_of_bundle` — wires the bundle through
  `subTypeI_rate_of_log_blowup` to Seregin's scalar signature.
-/

namespace NSBlwChain.BLW

/-- **Bundle of differential-inequality inputs for the ODE integration.**

    Given `M : ℝ → ℝ` and a singular time `T > 0`, the fields
    package the hypotheses of §12.4 step 7→8:

    * `t_start : ℝ`   — the growth-regime start time, `0 < t_start < T`.
    * `t_start_pos` / `t_start_lt_T` — its positivity and order.
    * `M_gt_one` — `M > 1` on `(t_start, T)` (so `log M > 0`).
    * `differential_bound` — `d/dt M(t) ≤ 4 · M(t)² · log M(t)` a.e.
      on `(t_start, T)`, encoded as a pointwise inequality holding
      at every `t` in that interval (the a.e. version follows by
      null-set removal; we use the stronger pointwise form since
      the chain consumer only needs the pointwise integrated form).
    * `log_blowup` — `log M → ∞` at `T⁻`, encoded as a `δ_of_ε`
      producer (same pattern as `BLWChainHypotheses`).
    * `integrated_bound` — **taken as a hypothesis.**  The full ODE
      integration (sub-Type-I rate constant `1/4`) is the open
      analytical sub-project this file isolates. -/
structure DifferentialInequalityBundle
    (M : ℝ → ℝ) (T : ℝ) where
  /-- Positive singular time. -/
  T_pos : 0 < T
  /-- Growth-regime start time, `0 < t_start < T`. -/
  t_start : ℝ
  t_start_pos : 0 < t_start
  t_start_lt_T : t_start < T
  /-- `M > 1` on `(t_start, T)`. -/
  M_gt_one :
    ∀ t : ℝ, t_start < t → t < T → 1 < M t
  /-- `M ≥ 0` on `(t_start, T)` (implied by `M > 1`, recorded for
      convenient re-export to chain consumers). -/
  M_nonneg :
    ∀ t : ℝ, t_start < t → t < T → 0 ≤ M t
  /-- `M` is differentiable on `(t_start, T)` and its derivative
      satisfies `Ṁ ≤ 4 · M² · log M` pointwise.

      In the paper this is stated a.e.; the pointwise form is
      sufficient here because the integrated conclusion we take as
      an input is already in the form the chain consumers require.
      The pointwise-to-a.e. and a.e.-to-pointwise reductions are
      measure-theoretic and not executed in this file. -/
  differential_bound :
    ∀ t : ℝ, t_start < t → t < T →
      HasDerivAt M (deriv M t) t ∧
      deriv M t ≤ 4 * (M t) ^ 2 * Real.log (M t)
  /-- `log M → ∞` at `T⁻`, encoded via a `δ_of_ε` producer:
      for each `ε > 0`, there is a positive `δ` with
      `log M(t) ≥ 1/(4ε)` on `(T - δ, T)`. -/
  δ_of_ε : ℝ → ℝ
  δ_of_ε_pos : ∀ ε : ℝ, 0 < ε → 0 < δ_of_ε ε
  δ_of_ε_le : ∀ ε : ℝ, 0 < ε → δ_of_ε ε ≤ T - t_start
  log_blowup :
    ∀ ε : ℝ, 0 < ε →
      ∀ t : ℝ, T - δ_of_ε ε < t → t < T →
        1 / (4 * ε) ≤ Real.log (M t)
  /-- **The integrated ODE bound.**

      `(T - t) · M(t) · log M(t) ≤ 1/4` on `(t_start, T)`.

      Derivation sketch: with `v := 1/M`, we have
      `v̇ = -Ṁ/M² ≥ -4 · log M = 4 · log v` (since `M > 1` ⇒
      `v ∈ (0,1)` ⇒ `log v < 0`).  Integrating on `[t, T')`
      with `v(T⁻) = 0` and using `d/dt(-v · log v) =
      -v̇ · log v - v̇ = -v̇ · (log v + 1)` with `v̇ ≤ 0`
      near `T` yields `-v · log v ≤ 4 · (T - t)`, i.e.
      `(T - t) · M · log M ≤ 1/4`.  The constant `1/4` comes
      from the factor `4` in the differential inequality and
      the asymptotic `v · log(1/v) → 0` at `T⁻`.

      Formalizing the integration-by-parts step and the
      `v(T⁻) = 0` limit is the open analytical sub-project this
      field isolates. -/
  integrated_bound :
    ∀ t : ℝ, t_start < t → t < T →
      (T - t) * M t * Real.log (M t) ≤ 1 / 4

namespace DifferentialInequalityBundle

variable {M : ℝ → ℝ} {T : ℝ}

/-- `log M > 0` on `(t_start, T)`, extracted from `M > 1`. -/
theorem log_M_pos (B : DifferentialInequalityBundle M T) :
    ∀ t : ℝ, B.t_start < t → t < T → 0 < Real.log (M t) := by
  intro t ht_low ht_up
  have hM : 1 < M t := B.M_gt_one t ht_low ht_up
  exact Real.log_pos hM

/-- **Integrated bound, re-export form.**

    The paper's step-7→8 conclusion, in exactly the shape
    consumed by `BLW/ChainHypotheses.BLWChainHypotheses.ode_bound`
    and `BLW/ODEToSeregin.subTypeI_from_ode_hypothesis.h_ode`.

    The quantified range `(0, T)` is the chain-consumer range; it
    is covered by the bundle's `(t_start, T)` range together with
    the growth-regime condition `0 < t_start`.  For `t ≤ t_start`
    the bound is trivially false in general (the ODE hypothesis
    isn't active yet), so the re-export genuinely consumes only
    the `t > t_start` part: the `0 < t ≤ t_start` case is outside
    the bundle's scope and must be supplied separately at the
    chain-wiring level (typically from the fact that `M · log M`
    is bounded on compact sub-intervals of `(0, t_start]`).

    We therefore state the re-export in the natural
    `(t_start, T)` form. -/
theorem integrated_bound_of_differential
    (B : DifferentialInequalityBundle M T) :
    ∀ t : ℝ, B.t_start < t → t < T →
      (T - t) * M t * Real.log (M t) ≤ 1 / 4 :=
  B.integrated_bound

/-- **Sub-Type-I rate from the bundle.**

    Wires the bundle through `subTypeI_rate_of_log_blowup` to land
    the Seregin scalar signature `(T - t) · M(t) ≤ ε` on a
    one-sided neighborhood of `T`.

    Note on range: `subTypeI_rate_of_log_blowup` is stated on
    `(0, T)`.  We fold the `(t_start, T)` bundle range into that
    interface by using the stronger range only where the bundle
    provides it, which is always the case on a one-sided
    neighborhood of `T` (we shrink `δ_of_ε` via `min` with
    `T - t_start`). -/
theorem subTypeI_rate_of_bundle
    (B : DifferentialInequalityBundle M T) :
    ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧
        ∀ t : ℝ, T - δ < t → t < T →
          (T - t) * M t ≤ ε := by
  intro ε hε
  -- We shrink the neighborhood to also ensure `t > B.t_start`.
  set η : ℝ := min (B.δ_of_ε ε) (T - B.t_start) with hη_def
  have hδT_pos : 0 < T - B.t_start := sub_pos.mpr B.t_start_lt_T
  have hη_pos : 0 < η := lt_min (B.δ_of_ε_pos ε hε) hδT_pos
  refine ⟨η, hη_pos, ?_⟩
  intro t ht_low ht_up
  -- From `T - η < t`, deduce `t > B.t_start` and `t > T - δ_of_ε ε`.
  have h_η_le_δε : η ≤ B.δ_of_ε ε := min_le_left _ _
  have h_η_le_gap : η ≤ T - B.t_start := min_le_right _ _
  have h_tstart_lt_t : B.t_start < t := by
    have : T - η ≥ T - (T - B.t_start) := by linarith [h_η_le_gap]
    have : T - (T - B.t_start) = B.t_start := by ring
    linarith [ht_low, h_η_le_gap]
  have h_T_δε_lt_t : T - B.δ_of_ε ε < t := by
    have : T - η ≥ T - B.δ_of_ε ε := by linarith [h_η_le_δε]
    linarith [ht_low, h_η_le_δε]
  -- Apply the integrated bound and the log-blow-up at `t`.
  have h_int := B.integrated_bound t h_tstart_lt_t ht_up
  have h_logpos := B.log_M_pos t h_tstart_lt_t ht_up
  have h_Mnn := B.M_nonneg t h_tstart_lt_t ht_up
  have h_Tmt_pos : 0 < T - t := sub_pos.mpr ht_up
  have h_loglarge := B.log_blowup ε hε t h_T_δε_lt_t ht_up
  exact pointwise_subTypeI_bound h_int h_logpos h_Mnn h_Tmt_pos hε h_loglarge

end DifferentialInequalityBundle

end NSBlwChain.BLW
