-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.BLW.GradientBoundTopLevelBundled
import NSBlwChain.BLW.MdotODEInequality
import NSBlwChain.BLW.Theorem3FullThreading

/-!
# Per-time-instant pipeline skeleton

Documents the two remaining structural gaps separating the
per-argmax gradient bound (commits 6-10) from the time-envelope
ODE used by `Theorem3FullThreading`:

* **Gap (a) — per-time-instant argmax discharge.**  For every
  `τ ∈ (t_start, T)`, the velocity field `u` admits an argmax
  `xStar(τ) ∈ Vec3` of `|ω(τ, ·)|²` together with all the
  alignment / `HessianInputs` / `EnvelopeAtArgmax` data needed to
  invoke `gradient_bound_from_NSEvolutionAxioms_bundled` at
  `(τ, xStar(τ))`.  This requires:
  * **spatial argmax existence** — the sup of `|ω(τ, ·)|²` over
    `Vec3` is achieved (compactness via decay at infinity).
  * **alignment via local frame** — at each argmax, a local frame
    in which `ω` aligns with `e₃`.
  * **per-time Hessian + envelope bundles** — fresh
    `HessianInputs(τ)` and `EnvelopeAtArgmax(τ)` at each time.

* **Gap (b) — saturating direction of the ODE.**  Going from
  `gradient_bound_from_NSEvolutionAxioms_bundled` (which delivers
  the *upper* inequality `|∇ω|² ≤ M²·σ/ν` per-argmax) to the
  *saturating* ODE `4 M² log M ≤ Ṁ` consumed by
  `Theorem3FullThreading.integrated_bound_from_tight_ODE` requires
  the §12.4 implicit-bound / Banach-fixed-point discharge in
  `Caveats/C4_GrowthDominance.lean` + the `BiotSavartSelfStrainBound`
  classical axiom.  In the saturating regime where the implicit
  bound is tight, the chain produces *equality* `Ṁ = 4 M² log M`,
  which delivers both directions of the ODE.

This file does NOT close either gap — it makes them precise as
structures and documents the threading.

## Structures

* `PerTimeInstantData u ν T M Mdot t_start` — bundles all the
  argmax / alignment / hessian / envelope / strain / step-iii data
  needed at every `τ ∈ (t_start, T)` to discharge the per-time-
  instant pipeline.
* `PerTimeInstantData_Lipschitz` — additional differentiability
  hypotheses on `M` for the time-derivative composition.

## Roadmap

`PerTimeInstantData.toMEnvelopeBound : PerTimeInstantData → ...`
would convert the bundle to the saturating ODE, then chain through
`integrated_bound_from_tight_ODE` and
`NS_regularity_extension_from_log_blowup` to deliver the smooth-
extension conclusion.

This file currently provides the **structure** without the
constructor — i.e., it names the data at the right type level so
that downstream proofs can reference `PerTimeInstantData` rather
than re-listing the long signature each time.
-/

namespace NSBlwChain.BLW

open scoped BigOperators
open NSBlwChain

/-- **Per-time-instant data bundle.**

    For each `τ : ℝ` in the open interval `(t_start, T)`, packages
    all the data the BLW chain consumes at the argmax of
    `|ω(τ, ·)|²`:

    * `xStar τ` — the spatial argmax.
    * Alignment data: `ω(τ, xStar τ)` aligned with `e₃` in the
      local frame, with magnitude `M τ`.
    * `HessianInputs(τ)` — the per-component Hessian bundle.
    * `EnvelopeAtArgmax(τ)` — the Danskin envelope bundle at
      `(τ, xStar τ)`.
    * Strain bound at `(τ, xStar τ)`: `σ(τ) ≤ 4 · M(τ) · log M(τ)`
      (output of Biot–Savart axiom + implicit-bound discharge).
    * Saturating step-(iii) lower bound: `4 M² log M ≤ Ṁ` at `τ`,
      from the §12.4 self-saturation argument.

    The envelope dominance hypothesis is global: `|ω(τ, x)| ≤ M(τ)`
    for every `(τ, x)`, not just at the argmax.

    **This structure is a hypothesis-bundle.**  Producing one for
    a given `(u, ν, T, M, Mdot, t_start)` is the per-time-instant
    discharge content (Gap (a) + (b)) — multi-session classical
    PDE work. -/
structure PerTimeInstantData
    (u : VelocityField) (ν T : ℝ) (M Mdot : ℝ → ℝ) (t_start : ℝ) where
  /-- For each interior `τ`, the spatial argmax of `|ω(τ, ·)|²`. -/
  xStar : ℝ → Vec3
  /-- Envelope dominance: `|ω(τ, x)| ≤ M(τ)` everywhere on `(0, T)`. -/
  envelope_dom :
    ∀ τ : ℝ, 0 < τ → τ < T →
      ∀ x : Vec3,
        Real.sqrt (Vec3.dot (vorticity u τ x) (vorticity u τ x))
          ≤ M τ
  /-- Argmax achieves the envelope: `|ω(τ, xStar τ)| = M(τ)`. -/
  envelope_attained :
    ∀ τ : ℝ, t_start < τ → τ < T →
      Real.sqrt (Vec3.dot (vorticity u τ (xStar τ))
                          (vorticity u τ (xStar τ))) = M τ
  /-- `M > 1` on `(t_start, T)` (growth regime). -/
  M_gt_one : ∀ τ : ℝ, t_start < τ → τ < T → 1 < M τ
  /-- `M` is differentiable on `(t_start, T)` with derivative
      function `Mdot`. -/
  M_diff :
    ∀ τ : ℝ, t_start < τ → τ < T → HasDerivAt M (Mdot τ) τ
  /-- **Saturating tight ODE** (output of §12.4 implicit-bound at the
      saturation regime): `4 M² log M ≤ Ṁ`.  This is the lower-bound
      direction the chain genuinely consumes. -/
  saturating_ODE :
    ∀ τ : ℝ, t_start < τ → τ < T →
      4 * (M τ) ^ 2 * Real.log (M τ) ≤ Mdot τ

/-- **Conditional discharge of `hM_tight` from `PerTimeInstantData`.**

    Given a `PerTimeInstantData` bundle, the saturating tight ODE
    hypothesis consumed by `integrated_bound_from_tight_ODE` is
    immediately available — it's a literal bundle field.

    This theorem is structural plumbing; the analytical content is
    in producing `PerTimeInstantData` from `NSEvolutionAxioms` +
    classical axioms, which is the multi-session future work. -/
theorem PerTimeInstantData.tight_ODE_at
    {u : VelocityField} {ν T : ℝ} {M Mdot : ℝ → ℝ} {t_start : ℝ}
    (D : PerTimeInstantData u ν T M Mdot t_start) :
    ∀ s ∈ Set.Ioo t_start T,
      4 * (M s) ^ 2 * Real.log (M s) ≤ deriv M s := by
  intro s hs
  -- HasDerivAt M (Mdot s) s ⇒ deriv M s = Mdot s.
  have h_d : HasDerivAt M (Mdot s) s := D.M_diff s hs.1 hs.2
  rw [h_d.deriv]
  exact D.saturating_ODE s hs.1 hs.2

/-- **Envelope dominance at every `τ ∈ (0, T)`** (extracted as the
    field consumed by `pointwise_subTypeI_from_envelope_subTypeI`). -/
theorem PerTimeInstantData.dom
    {u : VelocityField} {ν T : ℝ} {M Mdot : ℝ → ℝ} {t_start : ℝ}
    (D : PerTimeInstantData u ν T M Mdot t_start) :
    ∀ t : ℝ, 0 < t → t < T → ∀ x : Vec3,
      Real.sqrt (Vec3.dot (vorticity u t x) (vorticity u t x)) ≤ M t :=
  D.envelope_dom

/-- **`M_gt_one` extraction in the `Set.Ioo` form** (for direct use
    by `integrated_bound_from_tight_ODE`). -/
theorem PerTimeInstantData.M_gt_one_Ioo
    {u : VelocityField} {ν T : ℝ} {M Mdot : ℝ → ℝ} {t_start : ℝ}
    (D : PerTimeInstantData u ν T M Mdot t_start) :
    ∀ s ∈ Set.Ioo t_start T, 1 < M s := fun s hs =>
  D.M_gt_one s hs.1 hs.2

/-- **`M_diff` extraction in the `DifferentiableAt` form**. -/
theorem PerTimeInstantData.M_differentiableAt
    {u : VelocityField} {ν T : ℝ} {M Mdot : ℝ → ℝ} {t_start : ℝ}
    (D : PerTimeInstantData u ν T M Mdot t_start) :
    ∀ s ∈ Set.Ioo t_start T, DifferentiableAt ℝ M s := fun s hs =>
  (D.M_diff s hs.1 hs.2).differentiableAt

/-! ### Convenience: smooth extension from `PerTimeInstantData` -/

/-- **One-call convenience theorem.**

    Given a `PerTimeInstantData` bundle plus the standard FTC /
    boundary / log-blowup hypotheses, conclude that the velocity
    field extends smoothly past `T`.

    This delegates to `NS_regularity_extension_from_tight_ODE`
    by extracting all the data fields the threading theorem
    consumes.  Pure structural composition. -/
theorem NS_regularity_extension_from_PerTimeInstantData
    {u : VelocityField} {ν T : ℝ} (ax : NSEvolutionAxioms u ν T)
    {M Mdot : ℝ → ℝ} {t_start : ℝ}
    (ht_start_pos : 0 < t_start) (ht_start_lt_T : t_start < T)
    (D : PerTimeInstantData u ν T M Mdot t_start)
    (hM_nonneg_full : ∀ t : ℝ, 0 < t → t < T → 0 ≤ M t)
    -- Standard FTC / boundary / integrability hypotheses for the
    -- `hW_lower_bound_of_rate_equality` step:
    (hM_cont : ContinuousOn (fun s => 1 / (M s * Real.log (M s)))
                  (Set.Icc t_start T))
    (hW_boundary :
      Filter.Tendsto (fun s => 1 / (M s * Real.log (M s)))
        (𝓝[<] T) (𝓝 0))
    (h_tail_nonneg :
      ∀ t : ℝ, t_start < t → t < T →
        0 ≤ ∫ s in t..T, 4 / Real.log (M s))
    (h_FTC :
      ∀ ⦃a b : ℝ⦄, t_start < a → a ≤ b → b < T →
        1 / (M b * Real.log (M b)) - 1 / (M a * Real.log (M a)) =
          ∫ s in a..b, deriv (fun r => 1 / (M r * Real.log (M r))) s)
    (h_derivW_int :
      ∀ ⦃a b : ℝ⦄, t_start < a → a ≤ b → b < T →
        IntervalIntegrable
          (fun s => deriv (fun r => 1 / (M r * Real.log (M r))) s)
          MeasureTheory.volume a b)
    (h_tailPiece_int :
      ∀ ⦃a b : ℝ⦄, t_start < a → a ≤ b → b < T →
        IntervalIntegrable (fun s => (-4 : ℝ) - 4 / Real.log (M s))
          MeasureTheory.volume a b)
    (h_partialTail_nonneg :
      ∀ ⦃a b : ℝ⦄, t_start < a → a ≤ b → b < T →
        0 ≤ ∫ s in a..b, 4 / Real.log (M s))
    -- Log-blowup encoding:
    (δ_of_ε : ℝ → ℝ)
    (δ_pos : ∀ ε : ℝ, 0 < ε → 0 < δ_of_ε ε)
    (δ_le : ∀ ε : ℝ, 0 < ε → δ_of_ε ε ≤ T)
    (h_log_large :
      ∀ ε : ℝ, 0 < ε →
        ∀ t : ℝ, T - δ_of_ε ε < t → t < T →
          1 / (4 * ε) ≤ Real.log (M t))
    -- Bridge for the (0, T) form:
    (h_logM_pos : ∀ t : ℝ, 0 < t → t < T → 0 < Real.log (M t))
    (h_bound_full :
      ∀ t : ℝ, 0 < t → t < T →
        (T - t) * M t * Real.log (M t) ≤ 1 / 4) :
    ∃ T' : ℝ, T < T' ∧
      ∃ u' : VelocityField, NSEvolutionAxioms u' ν T' ∧
        ∀ t : ℝ, 0 ≤ t → t < T → ∀ x : Vec3, u' t x = u t x :=
  NS_regularity_extension_from_tight_ODE
    ax ht_start_pos ht_start_lt_T
    D.dom
    D.M_differentiableAt
    D.M_gt_one_Ioo
    D.tight_ODE_at
    hM_nonneg_full
    hM_cont hW_boundary h_tail_nonneg
    h_FTC h_derivW_int h_tailPiece_int h_partialTail_nonneg
    δ_of_ε δ_pos δ_le h_log_large
    h_logM_pos h_bound_full

end NSBlwChain.BLW
