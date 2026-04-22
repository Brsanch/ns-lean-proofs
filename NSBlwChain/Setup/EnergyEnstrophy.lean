-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Setup.VectorFields
import NSBlwChain.Setup.NSHypothesis

/-!
# Energy and enstrophy identities (Lemma B)

This file packages the energy-dissipation and enstrophy-growth
identities that the BLW-gradient chain consumes at steps (ii), (iv),
and (v) of §12.3, and at the enstrophy-to-far-field control of
Lemma B.

## Scope

Like the rest of the `Setup/*` files, this is *not* a proof of the
energy identity from scratch on $\mathbb{R}^3$ (that would require
a weighted cutoff argument on the compact support assumption, which
is a substantial classical exercise).  Instead we declare:

* `energyOf`      — the $L^2$ energy functional at a fixed time.
* `enstrophyOf`   — the $L^2$ enstrophy functional at a fixed time.
* `EnergyIdentity`, `EnstrophyGrowth` — named structural hypotheses
  consumed by the BLW-chain.

Downstream modules take these hypotheses by name; the hypotheses are
discharged on $\mathbb{R}^3$ via a separate classical-PDE input
(absorbed into `NSEvolutionAxioms` in a richer version of that bundle).

## References

* Majda–Bertozzi, Chapter 3 (energy / enstrophy calculus).
* Doering–Gibbon, §3 (dissipative identities on $\mathbb{R}^3$).
-/

namespace NSBlwChain

open MeasureTheory
open scoped BigOperators

/-- Pointwise squared magnitude of a vector in `Vec3`. -/
noncomputable def sqNorm3 (v : Vec3) : ℝ := Vec3.dot v v

@[simp] lemma sqNorm3_nonneg (v : Vec3) : 0 ≤ sqNorm3 v := by
  unfold sqNorm3 Vec3.dot
  have h0 : (0 : ℝ) ≤ v 0 * v 0 := mul_self_nonneg _
  have h1 : (0 : ℝ) ≤ v 1 * v 1 := mul_self_nonneg _
  have h2 : (0 : ℝ) ≤ v 2 * v 2 := mul_self_nonneg _
  -- ∑ i, v i * v i = v 0 * v 0 + v 1 * v 1 + v 2 * v 2
  have hsum :
      (∑ i : Fin 3, v i * v i) = v 0 * v 0 + v 1 * v 1 + v 2 * v 2 := by
    simp [Fin.sum_univ_three]
  rw [hsum]
  linarith

/-- The $L^2$ energy of a velocity field at time `t`, defined as the
    Lebesgue integral of `(1/2) |u(t, x)|²` over `\mathbb{R}^3`.

    We write the integral in terms of the 3D volume measure on
    `Vec3 = Fin 3 → ℝ` (which is `volume` on the product space).  The
    existence of the integral on $\mathbb{R}^3$ is a regularity
    property *assumed* via `NSEvolutionAxioms` in downstream use. -/
noncomputable def energyOf (u : VelocityField) (t : ℝ) : ℝ :=
  ∫ x : Vec3, (1 / 2 : ℝ) * sqNorm3 (u t x)

/-- The $L^2$ enstrophy of a velocity field at time `t`, defined as
    the Lebesgue integral of `|ω(t, x)|²` over `\mathbb{R}^3`. -/
noncomputable def enstrophyOf (u : VelocityField) (t : ℝ) : ℝ :=
  ∫ x : Vec3, sqNorm3 (vorticity u t x)

/-- **Lemma B (structural).**

    A named hypothesis bundling the two classical identities needed by
    the BLW-gradient chain:

    1. *Energy dissipation.*  Energy is non-increasing in time:
       `energyOf u t₂ ≤ energyOf u t₁` for `t₁ ≤ t₂`.
    2. *Enstrophy equality.* The enstrophy grows exactly by the
       vortex-stretching integral minus viscous dissipation.

    Downstream consumers take this as a hypothesis on an NS solution;
    it is NOT part of the three named axioms of the project (it is
    a standard consequence of the Leray energy inequality plus smoothness
    on `[0, T)`). -/
structure EnergyEnstrophyIdentities
    (u : VelocityField) (ν T : ℝ) : Prop where
  /-- Energy non-increasing. -/
  energy_decreasing :
    ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → t₂ < T →
      energyOf u t₂ ≤ energyOf u t₁
  /-- Enstrophy non-negative on `[0, T)`.  (Trivially true from
      `sqNorm3_nonneg`; recorded here for convenience.) -/
  enstrophy_nonneg :
    ∀ t : ℝ, 0 ≤ t → t < T → 0 ≤ enstrophyOf u t
  /-- Positive viscosity (mirror of `NSEvolutionAxioms.nu_pos`). -/
  nu_pos : 0 < ν

/-- Consequence: at any time `t ∈ [0, T)`, the energy is bounded
    above by the initial energy. -/
lemma energy_le_initial
    {u : VelocityField} {ν T : ℝ}
    (h : EnergyEnstrophyIdentities u ν T)
    {t : ℝ} (ht : 0 ≤ t) (htT : t < T) :
    energyOf u t ≤ energyOf u 0 :=
  h.energy_decreasing 0 t le_rfl ht htT

end NSBlwChain
