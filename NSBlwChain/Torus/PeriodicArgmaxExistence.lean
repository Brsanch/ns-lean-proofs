-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Torus.PeriodicNSAxioms

set_option diagnostics true
set_option diagnostics.threshold 100

/-!
# Spatial argmax existence on the torus fundamental cell

For a continuous, periodic real-valued function on `Vec3`, the
spatial supremum is attained at some point in the fundamental cell
`[0, L]³` by compactness alone — no `DecayAtInfinity` hypothesis
needed.  This is the torus analog of
`BLW/SpatialArgmax.exists_argmax_of_continuous_tendsto_zero`
(which uses cocompact decay on ℝ³).

## Strategy

The fundamental cell `[0, L]³ ⊂ Vec3` is a closed `Pi.box`, hence
compact in the product topology.  A continuous real function on a
non-empty compact set attains its supremum
(`IsCompact.exists_isMaxOn`).

Periodicity then lifts the maximum on the cell to the global
maximum on all of `Vec3`.

## Main results

* `fundamental_cell_compact` — the cell `[0, L]³` is compact in
  `Vec3` (`Fin 3 → ℝ`).
* `exists_argmax_on_fundamental_cell` — continuous `f : Vec3 → ℝ`
  attains its max on `[0, L]³`.
-/

namespace NSBlwChain.Torus

open Set NSBlwChain
open scoped BigOperators

/-- **The fundamental cell `[0, L]³` is compact in `Vec3`.**

    Mathlib gives compactness of `Set.Icc a b` in any `Pi`-typed
    space when each coordinate's interval is compact (which `Icc 0 L`
    on `ℝ` is). -/
lemma fundamental_cell_compact {L : ℝ} (hL : 0 ≤ L) :
    IsCompact (Set.Icc (0 : Vec3) (fun _ => L)) := by
  -- `Icc (0 : Vec3) (fun _ => L)` is the product `∏ i, Icc 0 L`.
  -- Each coordinate interval is compact (closed bounded subset of ℝ).
  exact isCompact_Icc

/-- **Argmax on the fundamental cell for a continuous function.**

    A continuous `f : Vec3 → ℝ` attains its supremum on the
    fundamental cell `[0, L]³` at some point `xStar` in that cell. -/
theorem exists_argmax_on_fundamental_cell
    {f : Vec3 → ℝ} (hf_cont : Continuous f)
    {L : ℝ} (hL : 0 ≤ L) :
    ∃ xStar ∈ Set.Icc (0 : Vec3) (fun _ => L),
      ∀ y ∈ Set.Icc (0 : Vec3) (fun _ => L), f y ≤ f xStar := by
  -- Compact non-empty cell + continuous f ⇒ max attained.
  have hcpt : IsCompact (Set.Icc (0 : Vec3) (fun _ => L)) :=
    fundamental_cell_compact hL
  have hne : (Set.Icc (0 : Vec3) (fun _ => L)).Nonempty := by
    refine ⟨fun _ => 0, ?_, ?_⟩
    · intro i; show (0 : ℝ) ≤ 0; rfl
    · intro i; exact hL
  -- `IsCompact.exists_isMaxOn` returns the argmax + the max property.
  obtain ⟨xStar, hxStar_in, hxStar_max⟩ :=
    hcpt.exists_isMaxOn hne hf_cont.continuousOn
  exact ⟨xStar, hxStar_in, fun y hy => hxStar_max hy⟩

/-! ## Lifting cell-max to global-max via periodicity

Given a periodic continuous function `f : Vec3 → ℝ`, the maximum
attained on `[0, L]³` is also a global maximum on all of `Vec3`.

The key lemma needed is "every `x : Vec3` has a `Fin 3`-tuple of
integer translates that puts it inside `[0, L]³`."  We sketch the
argument below; the full integer-translate construction is left
as a downstream addition (it requires a `Pi.box` reduction lemma
and an integer-floor argument per coordinate).

For the immediate downstream consumers (Theorem 1's per-time
argmax on torus solutions), `exists_argmax_on_fundamental_cell`
is already enough, since the BLW chain works at the argmax inside
the cell. -/

end NSBlwChain.Torus
