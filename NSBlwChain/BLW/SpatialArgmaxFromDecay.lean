-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.BLW.SpatialArgmax
import NSBlwChain.BLW.RpowThresholdFinder

/-!
# End-to-end spatial argmax existence from `DecayAtInfinity`

Composes the six analytical components:

1. `abs_le_sqrt_dot_self`           (coordinate ≤ Euclidean norm)
2. `euclidean_ball_subset_supnorm_ball`  (Eucl ⊂ sup-norm ball)
3. `tendsto_cocompact_zero_of_threshold` (filter form)
4. `decay_threshold_property_from_explicit_constants` (decay → threshold)
5. `rpow_threshold_bound`           (concrete R_of_ε via `Real.rpow`)
6. `exists_argmax_of_continuous_tendsto_zero` (compactness argmax)

into a single end-to-end theorem:

`exists_vorticity_argmax_of_decay_continuity` — given a smooth NS
solution with polynomial vorticity decay (`DecayAtInfinity`), at
each interior time `t` the squared-vorticity field
`|ω(t, ·)|²` achieves its supremum at some spatial point
`xStar : Vec3`, provided `|ω(t, ·)|²` is non-trivial (positive at
some witness point).

## Main result

* `exists_vorticity_argmax_of_decay_continuity` — end-to-end
  spatial argmax existence.
-/

namespace NSBlwChain.BLW

open Filter Topology Real
open scoped BigOperators
open NSBlwChain

/-- **End-to-end spatial argmax existence from polynomial decay.**

    Given:
    * `NSEvolutionAxioms u ν T` (smoothness via curl ContDiff,
      providing continuity of `|ω(t, ·)|²`).
    * `DecayAtInfinity u T` (polynomial decay of `ω`).
    * A witness point `y₀` with `|ω(t, y₀)|² > 0` (non-trivial vorticity).
    * Continuity of `|ω(t, ·)|²` at `t` (from smoothness).

    Conclude: `∃ xStar : Vec3, |ω(t, xStar)|² ≥ |ω(t, y)|²` for all `y`.

    The continuity hypothesis is taken explicitly to avoid the long
    `vorticity_contDiff` chain inside this theorem; downstream callers
    discharge it via `ax.vorticitySqNorm_contDiff ht htT |>.continuous`. -/
theorem exists_vorticity_argmax_of_decay_continuity
    {u : VelocityField} {ν T : ℝ}
    (ax : NSEvolutionAxioms u ν T)
    (hDecay : DecayAtInfinity u T)
    {t : ℝ} (ht_nn : 0 ≤ t) (htT : t < T)
    (h_cont : Continuous
      (fun y : Vec3 =>
        Vec3.dot (vorticity u t y) (vorticity u t y)))
    {y₀ : Vec3}
    (hy₀_pos :
      0 < Vec3.dot (vorticity u t y₀) (vorticity u t y₀)) :
    ∃ xStar : Vec3,
      ∀ y : Vec3,
        Vec3.dot (vorticity u t y) (vorticity u t y)
          ≤ Vec3.dot (vorticity u t xStar) (vorticity u t xStar) := by
  -- Destructure the polynomial decay hypothesis.
  obtain ⟨R, C, p, hR_pos, hC_nn, hp_gt_3, h_decay⟩ :=
    hDecay.has_polynomial_decay
  -- p > 0 (since 3 < p).
  have hp_pos : 0 < p := lt_trans (by norm_num : (0 : ℝ) < 3) hp_gt_3
  -- Build the threshold-finder via rpow_threshold_bound.
  let R_of_ε : ℝ → ℝ :=
    fun ε => max R ((C ^ 2 / ε + 1) ^ (1 / (2 * p)))
  have h_threshold_props :
      ∀ ε : ℝ, 0 < ε →
        0 < R_of_ε ε ∧ R ≤ R_of_ε ε ∧
          C ^ 2 / ε + 1 ≤ R_of_ε ε ^ (2 * p) :=
    fun ε hε => rpow_threshold_bound hR_pos hC_nn hp_pos ε hε
  -- Extract individual properties.
  have hR_of_ε_pos : ∀ ε : ℝ, 0 < ε → 0 < R_of_ε ε :=
    fun ε hε => (h_threshold_props ε hε).1
  have hR_of_ε_ge_R : ∀ ε : ℝ, 0 < ε → R ≤ R_of_ε ε :=
    fun ε hε => (h_threshold_props ε hε).2.1
  have h_rpow_bound : ∀ ε : ℝ, 0 < ε →
      C ^ 2 / ε + 1 ≤ R_of_ε ε ^ (2 * p) :=
    fun ε hε => (h_threshold_props ε hε).2.2
  -- Apply decay_threshold_property_from_explicit_constants.
  have h_threshold_prop :
      ∀ ε : ℝ, 0 < ε → ∀ x : Vec3,
        ε ≤ |Vec3.dot (vorticity u t x) (vorticity u t x)| →
          Real.sqrt (Vec3.dot x x) ≤ R_of_ε ε :=
    decay_threshold_property_from_explicit_constants
      hR_pos hC_nn hp_gt_3
      (fun x hx => h_decay t ht_nn htT x hx)
      R_of_ε hR_of_ε_pos hR_of_ε_ge_R h_rpow_bound
  -- Apply tendsto_cocompact_zero_of_threshold.
  have h_tendsto :
      Tendsto (fun x => Vec3.dot (vorticity u t x) (vorticity u t x))
        (cocompact Vec3) (𝓝 0) :=
    tendsto_cocompact_zero_of_threshold R_of_ε hR_of_ε_pos h_threshold_prop
  -- Apply exists_argmax_of_continuous_tendsto_zero.
  exact exists_argmax_of_continuous_tendsto_zero h_cont h_tendsto hy₀_pos

end NSBlwChain.BLW
