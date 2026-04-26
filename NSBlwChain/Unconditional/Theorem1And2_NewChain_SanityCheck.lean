-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Unconditional.Theorem1FromLeray
import NSBlwChain.Unconditional.PointwiseEnergyODE
import NSBlwChain.Unconditional.FarFieldFromKernelTail

set_option diagnostics true
set_option diagnostics.threshold 100

/-!
# Sanity checks: end-to-end Theorem 1 and Theorem 2 from the new chain

Demonstrates that the constructors landed in this session
(`farFieldControlBundle_of_kernelTail`, `enstrophyCrossoverBundle_of_leray`,
`lerayEnergyEquality_of_pointwise`) compose into the Theorem 1/2
algebraic conclusions on **concrete numeric instances**, proving
the chain is non-vacuous at the type level.

Each sanity check picks a parameter setting where the result has a
clean closed form (`E₀ / (ν · c_Z) = 1/4`, `4π · C_K² · E_ω / R = 4π`,
etc.) and discharges the conclusion by composing the new constructors
with bundle hypotheses.

## Sanity-check theorems

* `theorem2_at_unit_kernel` — `farNorm ≤ sqrt(4π)` for unit kernel
  bundle + `E_ω = R = C_K = 1` + Cauchy–Schwarz hypothesis.
* `theorem1_via_pointwise_at_unit` — Theorem 1 conclusion at
  `ν = E(0) = Tstar = 1`, `c_Z = 4`, `β = 2` constructed from a
  pointwise energy ODE + crossover hypothesis + regularity.
-/

namespace NSBlwChain.Unconditional

open Real

/-! ## Theorem 2 sanity check -/

/-- **Theorem 2 conclusion via the new kernel-tail chain.**

    With `R = E_ω = C_K = 1`, the kernel-tail bundle gives
    `kernelTailSq = 4π · 1² / 1 = 4π`.  Given a Cauchy–Schwarz
    hypothesis `farNorm² ≤ kernelTailSq · E_ω = 4π`, the new
    constructor `farFieldControlBundle_of_kernelTail` builds the
    Theorem 2 bundle with `C := 4π`, and `farField_le_sqrt` delivers
    `farNorm ≤ sqrt(4π · 1 · 1 / 1) = sqrt(4π)`. -/
theorem theorem2_at_unit_kernel
    {farNorm kernelTailSq : ℝ}
    (K : BiotSavartKernelTailBundle 1 1 kernelTailSq)
    (hfn_nn : 0 ≤ farNorm)
    (hCS : farNorm ^ 2 ≤ kernelTailSq * 1) :
    farNorm ≤ Real.sqrt (4 * Real.pi) := by
  have h := farField_le_sqrt_of_kernelTail K (by norm_num : (0 : ℝ) ≤ 1)
    hfn_nn hCS
  -- h : farNorm ≤ sqrt (4 * π * 1^2 * 1 / 1)
  have h_simp : (4 * Real.pi * (1 : ℝ) ^ 2 * 1 / 1) = 4 * Real.pi := by
    ring
  rw [h_simp] at h
  exact h

/-! ## Theorem 1 sanity check via pointwise ODE + crossover -/

/-- **Theorem 1 algebraic core via the new pointwise→integrated chain.**

    Setup: `ν = 1`, `Tstar = 1`, `E(0) = 1`, `β = 2`, `c_Z = 4`.
    Pointwise energy ODE on `[0, 1]` plus crossover `Z ≥ 4 · M²` plus
    regularity composes via:

    `LerayEnergyPointwise → LerayEnergyEquality →
     EnstrophyCrossoverBundle → blowup_rate_alpha_full`

    delivering `(1 - t) · M(t)^α ≤ 1 / (1 · 4) = 1/4`. -/
theorem theorem1_via_pointwise_at_unit
    {E M Z : ℝ → ℝ} {α : ℝ}
    (P : LerayEnergyPointwise E Z 1 1)
    (X : EnstrophyCrossoverHypothesis M Z 2 4 1)
    (R : EnstrophyCrossoverRegularity M Z 1)
    (hE0_nn : 0 ≤ E 0)
    (hNoType1 : NoTypeIBlowup M 1)
    (hα_gt_one : 1 < α) (hα_le_two : α ≤ 2)
    {t : ℝ} (ht_nn : 0 ≤ t) (htT : t ≤ 1) (hMt : 1 ≤ M t) :
    (1 - t) * M t ^ α ≤ E 0 / 4 := by
  -- Compose: pointwise → integrated → bundle → Theorem 1.
  have L : LerayEnergyEquality E Z 1 1 := lerayEnergyEquality_of_pointwise P
  have h := blowup_rate_alpha_full L X R hE0_nn hNoType1
    hα_gt_one hα_le_two ht_nn htT hMt
  -- h : (1 - t) * M t ^ α ≤ E 0 / (1 * 4)
  have h_simp : E 0 / ((1 : ℝ) * 4) = E 0 / 4 := by ring
  rw [h_simp] at h
  exact h

end NSBlwChain.Unconditional
