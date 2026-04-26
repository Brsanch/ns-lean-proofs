-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Setup.VectorFields
import NSBlwChain.Setup.NSHypothesis

/-!
# Spatial argmax existence on `Vec3` from decay-at-infinity

Genuine analytical content: prove that a continuous function
`f : Vec3 → ℝ` that tends to `0` at the cocompact filter and is
strictly positive at some point achieves its maximum at some
`xStar : Vec3`.

This is the **compactness-via-decay** lemma that the
`PerTimeInstantData.xStar` constructor needs at every `τ ∈ (0, T)`
to produce a spatial argmax of `|ω(τ, ·)|²`.  Together with
joint continuity of `(τ, y) ↦ |ω(τ, y)|²` (from `vorticity_contDiff`)
and polynomial decay (from `DecayAtInfinity` in `ClassicalAxioms`),
this lemma converts the per-τ analytical content into the
`xStar τ` field of `PerTimeInstantData`.

## Strategy

* From `Tendsto f (cocompact Vec3) (𝓝 0)`: outside some compact
  set `K`, `f < f y₀ / 2`.
* `K ∪ {y₀}` is compact.
* `IsCompact.exists_isMaxOn` gives a max `xStar` on `K ∪ {y₀}`.
* `f xStar ≥ f y₀ > f y₀ / 2 > f y` for `y ∉ K`, so `xStar` is also
  the global max.

## Main result

* `exists_argmax_of_continuous_tendsto_zero` — the decay-to-argmax
  lemma.
-/

namespace NSBlwChain.BLW

open Filter Topology NSBlwChain
open scoped BigOperators

/-- **Spatial argmax from decay at infinity (continuous case).**

    Given a continuous `f : Vec3 → ℝ` that tends to `0` at the
    `cocompact` filter and is strictly positive at some `y₀`, there
    exists `xStar : Vec3` at which `f` achieves its maximum over the
    whole space.

    The strict-positivity hypothesis ensures the global max is
    strictly positive (and hence not attained "at infinity" where
    `f → 0`); without it, the conclusion is trivial (take `xStar :=
    y₀` and use `f y ≤ 0` from decay, but this requires one-sided
    bounds at infinity which are not assumed). -/
theorem exists_argmax_of_continuous_tendsto_zero
    {f : Vec3 → ℝ}
    (hf_cont : Continuous f)
    (hf_decay : Tendsto f (cocompact Vec3) (𝓝 0))
    {y₀ : Vec3} (hy₀_pos : 0 < f y₀) :
    ∃ xStar : Vec3, ∀ y : Vec3, f y ≤ f xStar := by
  -- Step 1: from the decay, find a compact set `K` such that
  -- `f y < f y₀ / 2` outside `K`.
  have h_eps : 0 < f y₀ / 2 := half_pos hy₀_pos
  have h_decay_form :
      ∀ᶠ y in cocompact Vec3, |f y - 0| < f y₀ / 2 := by
    have := (Metric.tendsto_nhds.mp hf_decay) (f y₀ / 2) h_eps
    simpa using this
  rw [Filter.eventually_iff] at h_decay_form
  -- `h_decay_form : {y | |f y - 0| < f y₀/2} ∈ cocompact Vec3`.
  -- A set is in `cocompact` iff its complement is compact.
  rw [Filter.mem_cocompact] at h_decay_form
  obtain ⟨K, hK_cpt, hK_sub⟩ := h_decay_form
  -- `hK_sub : Kᶜ ⊆ {y | |f y - 0| < f y₀ / 2}`.
  -- Step 2: `K ∪ {y₀}` is compact.
  have hKy₀_cpt : IsCompact (K ∪ {y₀}) := hK_cpt.union isCompact_singleton
  -- Step 3: `K ∪ {y₀}` is non-empty (contains `y₀`).
  have hKy₀_ne : (K ∪ {y₀}).Nonempty := ⟨y₀, Or.inr rfl⟩
  -- Step 4: max on `K ∪ {y₀}` exists by compactness + continuity.
  obtain ⟨xStar, hxStar_in, hxStar_max⟩ :=
    hKy₀_cpt.exists_isMaxOn hKy₀_ne hf_cont.continuousOn
  -- `hxStar_max : ∀ y ∈ K ∪ {y₀}, f y ≤ f xStar`.
  refine ⟨xStar, ?_⟩
  intro y
  -- Two cases: `y ∈ K ∪ {y₀}` (then `hxStar_max` directly) or
  --            `y ∉ K ∪ {y₀}` (then `y ∉ K`, so `f y < f y₀ / 2`).
  by_cases hy_in : y ∈ K ∪ {y₀}
  · exact hxStar_max hy_in
  · -- `y ∉ K ∪ {y₀}` means `y ∉ K` (in particular).
    have hy_notin_K : y ∉ K := fun h => hy_in (Or.inl h)
    have hy_in_compl : y ∈ (Kᶜ : Set Vec3) := hy_notin_K
    have h_y_decay : |f y - 0| < f y₀ / 2 := hK_sub hy_in_compl
    -- So `f y < f y₀ / 2 < f y₀ ≤ f xStar` (since `y₀ ∈ K ∪ {y₀}`).
    have h_fy_lt : f y < f y₀ / 2 := by
      have := abs_lt.mp h_y_decay
      linarith
    have h_fy₀_le : f y₀ ≤ f xStar :=
      hxStar_max (Or.inr rfl)
    linarith

/-- **Spatial argmax for `|ω|²` over `Vec3` from polynomial decay.**

    Specialization to the squared-vorticity field that the BLW chain
    needs.  Assumes:
    * `(t, y) ↦ |ω(t, y)|²` is continuous in `y` at fixed `t`,
    * the field decays at infinity (encoded as `Tendsto ... (𝓝 0)`),
    * `|ω(t, ·)|²` is strictly positive at some witness point.

    Conclusion: there exists `xStar` at which `|ω(t, xStar)|²` is the
    maximum.

    This is the operational form of the classical "smooth NS solution
    on `\mathbb R³` with vorticity decay achieves its `L^∞` max" — a
    standard PDE fact, formalized here from compactness-via-decay
    primitives. -/
theorem exists_vorticity_argmax_of_decay
    {u : VelocityField} {t : ℝ}
    (h_cont : Continuous (fun y =>
      Vec3.dot (vorticity u t y) (vorticity u t y)))
    (h_decay : Tendsto
      (fun y => Vec3.dot (vorticity u t y) (vorticity u t y))
      (cocompact Vec3) (𝓝 0))
    {y₀ : Vec3} (hy₀_pos :
      0 < Vec3.dot (vorticity u t y₀) (vorticity u t y₀)) :
    ∃ xStar : Vec3,
      ∀ y : Vec3,
        Vec3.dot (vorticity u t y) (vorticity u t y)
          ≤ Vec3.dot (vorticity u t xStar) (vorticity u t xStar) :=
  exists_argmax_of_continuous_tendsto_zero h_cont h_decay hy₀_pos

end NSBlwChain.BLW
