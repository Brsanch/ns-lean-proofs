-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.BLW.PerTimeInstantPipeline
import NSBlwChain.BLW.SpatialArgmaxFromDecay
import NSBlwChain.Setup.ClassicalAxioms

set_option diagnostics true
set_option diagnostics.threshold 100

/-!
# `PerTimeInstantData` constructors

Two structural constructors that compose existing pieces into the
`PerTimeInstantData` bundle, reducing the *primitive* hypothesis
list a downstream consumer must supply.

## Constructor 1: `ofExplicitArgmax`

Given an explicit argmax function `xStar : ℝ → Vec3` and the four
analytical hypotheses (envelope dominance, envelope attainment,
growth regime, differentiability with `Mdot`, saturating ODE),
produce the bundle by direct structure construction.  This is
field-renaming convenience for downstream call sites that already
have `xStar` in hand.

## Constructor 2: `ofDecayContinuity_withCanonicalEnvelope`

Given continuity + cocompact decay of `|ω(τ, ·)|²` at every interior
`τ` plus a *positivity-witness* function (a `y₀(τ)` with
`|ω(τ, y₀)|² > 0`), constructs the argmax `xStar` via
`exists_argmax_of_continuous_tendsto_zero` (proven this session)
+ `Classical.choose`.  The user supplies the canonical envelope
function `M : ℝ → ℝ` matching the argmax-attained value, plus the
remaining structural hypotheses.

Both constructors discharge `xStar` and `envelope_attained` from
analytical hypotheses, leaving the genuinely-classical
`saturating_ODE` and `M_diff` as the only multi-session leaves.

## Main results

* `PerTimeInstantData.ofExplicitArgmax` — convenience constructor.
* `PerTimeInstantData.ofDecayContinuity_withCanonicalEnvelope` —
  argmax-deriving constructor.
-/

namespace NSBlwChain.BLW

open NSBlwChain
open scoped BigOperators

/-- **Convenience constructor: `PerTimeInstantData` from explicit fields.**

    Direct structure construction with named arguments.  Useful when
    `xStar` is already in hand from a different argument (e.g.
    classical NS regularity argument that constructs the local
    blowup point explicitly). -/
noncomputable def PerTimeInstantData.ofExplicitArgmax
    {u : VelocityField} {ν T : ℝ} {M Mdot : ℝ → ℝ} {t_start : ℝ}
    (xStar : ℝ → Vec3)
    (h_dom : ∀ τ : ℝ, 0 < τ → τ < T →
      ∀ x : Vec3,
        Real.sqrt (Vec3.dot (vorticity u τ x) (vorticity u τ x))
          ≤ M τ)
    (h_attained : ∀ τ : ℝ, t_start < τ → τ < T →
      Real.sqrt (Vec3.dot (vorticity u τ (xStar τ))
                          (vorticity u τ (xStar τ))) = M τ)
    (h_growth : ∀ τ : ℝ, t_start < τ → τ < T → 1 < M τ)
    (h_diff : ∀ τ : ℝ, t_start < τ → τ < T →
      HasDerivAt M (Mdot τ) τ)
    (h_sat : ∀ τ : ℝ, t_start < τ → τ < T →
      4 * (M τ) ^ 2 * Real.log (M τ) ≤ Mdot τ) :
    PerTimeInstantData u ν T M Mdot t_start :=
  { xStar := xStar
    envelope_dom := h_dom
    envelope_attained := h_attained
    M_gt_one := h_growth
    M_diff := h_diff
    saturating_ODE := h_sat }

/-- **Argmax-deriving constructor.**

    Given:
    * continuity of `|ω(τ, ·)|²` at every interior `τ ∈ (0, T)`,
    * a positivity-witness `y₀ : ℝ → Vec3` with `|ω(τ, y₀ τ)|² > 0`
      at every interior `τ`,
    * a cocompact-decay hypothesis on `|ω(τ, ·)|²` at every interior
      `τ`,
    * the canonical envelope identity (M τ = sup of |ω| at the
      derived argmax) plus the remaining structural fields,

    construct the bundle by extracting `xStar` from
    `exists_argmax_of_continuous_tendsto_zero` (proven this session)
    via `Classical.choose`. -/
noncomputable def PerTimeInstantData.ofDecayContinuity_withCanonicalEnvelope
    {u : VelocityField} {ν T : ℝ} {M Mdot : ℝ → ℝ} {t_start : ℝ}
    (h_cont : ∀ τ : ℝ, 0 < τ → τ < T →
      Continuous (fun y =>
        Vec3.dot (vorticity u τ y) (vorticity u τ y)))
    (y0 : ℝ → Vec3)
    (h_y0_pos : ∀ τ : ℝ, 0 < τ → τ < T →
      0 < Vec3.dot (vorticity u τ (y0 τ)) (vorticity u τ (y0 τ)))
    (h_decay : ∀ τ : ℝ, 0 < τ → τ < T →
      Filter.Tendsto (fun y =>
        Vec3.dot (vorticity u τ y) (vorticity u τ y))
        (Filter.cocompact Vec3) (nhds 0))
    -- Extracted-argmax version of the M-attainment hypothesis:
    (h_attained_at_argmax :
      ∀ τ : ℝ, t_start < τ → τ < T →
        ∀ xStar : Vec3,
          (∀ y : Vec3,
            Vec3.dot (vorticity u τ y) (vorticity u τ y)
              ≤ Vec3.dot (vorticity u τ xStar) (vorticity u τ xStar)) →
          Real.sqrt (Vec3.dot (vorticity u τ xStar)
                              (vorticity u τ xStar)) = M τ)
    (h_dom :
      ∀ τ : ℝ, 0 < τ → τ < T →
        ∀ x : Vec3,
          Real.sqrt (Vec3.dot (vorticity u τ x) (vorticity u τ x))
            ≤ M τ)
    (h_growth : ∀ τ : ℝ, t_start < τ → τ < T → 1 < M τ)
    (h_diff : ∀ τ : ℝ, t_start < τ → τ < T →
      HasDerivAt M (Mdot τ) τ)
    (h_sat : ∀ τ : ℝ, t_start < τ → τ < T →
      4 * (M τ) ^ 2 * Real.log (M τ) ≤ Mdot τ) :
    PerTimeInstantData u ν T M Mdot t_start := by
  -- Build the per-τ argmax existence statement.
  have h_argmax_exists : ∀ τ : ℝ, 0 < τ → τ < T →
      ∃ xStar : Vec3,
        ∀ y : Vec3,
          Vec3.dot (vorticity u τ y) (vorticity u τ y)
            ≤ Vec3.dot (vorticity u τ xStar) (vorticity u τ xStar) := by
    intro τ hτ_pos hτ_T
    exact exists_argmax_of_continuous_tendsto_zero
      (h_cont τ hτ_pos hτ_T) (h_decay τ hτ_pos hτ_T)
      (h_y0_pos τ hτ_pos hτ_T)
  -- Choose xStar pointwise (using Decidable-elim on the τ ∈ (0, T)
  -- condition: outside the interval we use a junk default).
  let xStar : ℝ → Vec3 := fun τ =>
    if h : 0 < τ ∧ τ < T then
      Classical.choose (h_argmax_exists τ h.1 h.2)
    else (0 : Vec3)
  have h_xStar_spec : ∀ τ : ℝ, ∀ (h_pos : 0 < τ) (h_T : τ < T),
      ∀ y : Vec3,
        Vec3.dot (vorticity u τ y) (vorticity u τ y)
          ≤ Vec3.dot (vorticity u τ (xStar τ))
                     (vorticity u τ (xStar τ)) := by
    intro τ hτ_pos hτ_T y
    show Vec3.dot (vorticity u τ y) (vorticity u τ y)
          ≤ Vec3.dot (vorticity u τ (xStar τ))
                     (vorticity u τ (xStar τ))
    have h_select : xStar τ = Classical.choose
        (h_argmax_exists τ hτ_pos hτ_T) := by
      simp [xStar, hτ_pos, hτ_T]
    rw [h_select]
    exact Classical.choose_spec (h_argmax_exists τ hτ_pos hτ_T) y
  refine PerTimeInstantData.ofExplicitArgmax xStar h_dom ?_ h_growth h_diff h_sat
  -- envelope_attained from the supplied h_attained_at_argmax.
  intro τ hτ_start hτ_T
  have hτ_pos : 0 < τ := lt_of_le_of_lt (le_refl 0)
    (by linarith [hτ_start] : (0 : ℝ) < τ)
  exact h_attained_at_argmax τ hτ_start hτ_T (xStar τ)
    (h_xStar_spec τ hτ_pos hτ_T)

end NSBlwChain.BLW
