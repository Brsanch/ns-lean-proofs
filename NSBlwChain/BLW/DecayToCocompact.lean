-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Setup.NSHypothesis
import NSBlwChain.Setup.ClassicalAxioms

/-!
# `DecayAtInfinity` → cocompact-tendsto-zero bridge

Genuine analytical content: bridges polynomial decay to the
cocompact-tendsto-zero form consumed by
`SpatialArgmax.exists_argmax_of_continuous_tendsto_zero`.

## Strategy (hypothesis form)

The bridge needs a **threshold-finder** `R_of_ε : ℝ → ℝ` mapping
each tolerance `ε > 0` to a radius `R_of_ε ε ≥ R` outside of which
the squared-vorticity field is `< ε`.  Producing such a finder
from `DecayAtInfinity`'s polynomial-decay constants `(R, C, p)` is
real-power arithmetic that is delegated to a helper file
(`Real.rpow` machinery on `(C² / ε)^{1/(2p)}`).

The bridge itself is then structural composition:

* For each `ε > 0`, the set `{x : |ω(t, x)|² ≥ ε}` is contained in
  the Euclidean closed ball of radius `R_of_ε ε`.
* The Euclidean ball is contained in the sup-norm closed ball
  (since `|x_i| ≤ √(Vec3.dot x x)` per coordinate).
* The sup-norm closed ball is compact (`isCompact_closedBall` in
  the proper space `Fin 3 → ℝ`).
* Hence `{x : |ω(t, x)|² < ε}` is in `cocompact Vec3`.

## Main results

* `abs_le_sqrt_dot_self` — coordinate-wise `|x_i| ≤ ‖x‖_2`.
* `tendsto_cocompact_zero_of_threshold` — bridge from a generic
  threshold-finder to `Tendsto _ (cocompact) (𝓝 0)`.
-/

namespace NSBlwChain.BLW

open Filter Topology
open scoped BigOperators
open NSBlwChain

/-- **Coordinate `≤` Euclidean-norm bound.**  For any `x : Vec3`
    and `i : Fin 3`, `|x i| ≤ √(Vec3.dot x x)`.  This is the
    classical `|x_i| ≤ ‖x‖_2` inequality. -/
lemma abs_le_sqrt_dot_self (x : Vec3) (i : Fin 3) :
    |x i| ≤ Real.sqrt (Vec3.dot x x) := by
  have h_xi_sq_le : (x i) ^ 2 ≤ Vec3.dot x x := by
    unfold Vec3.dot
    rw [Fin.sum_univ_three]
    have h0 : 0 ≤ x 0 * x 0 := mul_self_nonneg _
    have h1 : 0 ≤ x 1 * x 1 := mul_self_nonneg _
    have h2 : 0 ≤ x 2 * x 2 := mul_self_nonneg _
    fin_cases i
    all_goals (simp [pow_two]; linarith)
  -- |x i| = √((x i)²) ≤ √(Vec3.dot x x).
  have hxi_eq : |x i| = Real.sqrt ((x i) ^ 2) := (Real.sqrt_sq_eq_abs (x i)).symm
  rw [hxi_eq]
  exact Real.sqrt_le_sqrt h_xi_sq_le

/-- **Euclidean ball ⊆ sup-norm closed ball.**  If
    `√(Vec3.dot x x) ≤ R'`, then `x ∈ Metric.closedBall 0 R'`
    (sup-norm closed ball on `Fin 3 → ℝ`). -/
lemma euclidean_ball_subset_supnorm_ball
    {R' : ℝ} (hR' : 0 ≤ R') (x : Vec3)
    (hx : Real.sqrt (Vec3.dot x x) ≤ R') :
    x ∈ Metric.closedBall (0 : Vec3) R' := by
  rw [Metric.mem_closedBall, dist_zero_right]
  rw [pi_norm_le_iff_of_nonneg hR']
  intro i
  show |x i| ≤ R'
  exact le_trans (abs_le_sqrt_dot_self x i) hx

/-- **Bridge from threshold-finder to cocompact-tendsto-zero.**

    Given a threshold function `R_of_ε : ℝ → ℝ` with
    `R_of_ε ε > 0` and the property that `|f x| ≥ ε` implies
    `√(Vec3.dot x x) ≤ R_of_ε ε`, conclude
    `Tendsto f (cocompact Vec3) (𝓝 0)`.

    This is the structural composition: `{x : |f x| ≥ ε}` is
    contained in the Euclidean ball of radius `R_of_ε ε`, which is
    contained in the sup-norm closed ball, which is compact in the
    proper space `Vec3`.  Hence `{x : |f x| < ε}` is cocompact. -/
theorem tendsto_cocompact_zero_of_threshold
    {f : Vec3 → ℝ}
    (R_of_ε : ℝ → ℝ)
    (hR_pos : ∀ ε : ℝ, 0 < ε → 0 < R_of_ε ε)
    (h_threshold :
      ∀ ε : ℝ, 0 < ε → ∀ x : Vec3,
        ε ≤ |f x| →
          Real.sqrt (Vec3.dot x x) ≤ R_of_ε ε) :
    Tendsto f (cocompact Vec3) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [Filter.eventually_iff, Filter.mem_cocompact]
  refine ⟨Metric.closedBall (0 : Vec3) (R_of_ε ε),
    isCompact_closedBall _ _, ?_⟩
  -- Goal: x ∈ closedBallᶜ → x ∈ {y | dist (f y) 0 < ε}.
  intro x hx_compl
  -- hx_compl : x ∈ closedBallᶜ, i.e., x ∉ closedBall.
  -- Goal: dist (f x) 0 < ε.  Contrapositive: if ε ≤ dist (f x) 0,
  -- then x ∈ closedBall, contradicting hx_compl.
  by_contra h_ge
  have h_le : ε ≤ dist (f x) 0 := not_lt.mp h_ge
  have h_dist : dist (f x) 0 = |f x| := by simp
  rw [h_dist] at h_le
  have h_sqrt_le : Real.sqrt (Vec3.dot x x) ≤ R_of_ε ε :=
    h_threshold ε hε x h_le
  have h_in_ball : x ∈ Metric.closedBall (0 : Vec3) (R_of_ε ε) :=
    euclidean_ball_subset_supnorm_ball (le_of_lt (hR_pos ε hε)) x h_sqrt_le
  exact hx_compl h_in_ball

end NSBlwChain.BLW
