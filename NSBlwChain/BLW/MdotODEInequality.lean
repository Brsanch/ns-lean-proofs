-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.BLW.GradientBoundLogForm

/-!
# `Mdot ≤ 4 · M² · log M` — §12.4 ODE inequality

Scalar-level composition of:

* **Step (iii) ODE inequality**: at every growth-regime argmax of
  `|ω|²`, the envelope's time-derivative satisfies `Mdot ≤ M · σ`
  (after alignment / max-principle drops the viscous `ν · ω · Δω`
  term, which is `≤ 0`).

* **Strain bound** (Biot–Savart axiom 1 + §12.4 implicit-bound /
  Banach-fixed-point discharge for `1 ≤ M`): `σ ≤ 4 · M · log M`.

producing the `§12.4` ODE inequality

  `Mdot ≤ 4 · M² · log M`,

which is the input to `ODEIntegration` / `ODEToSeregin` for the
sub-Type-I rate.

## Main result

* `Mdot_le_4Msq_logM_scalar` — pure real-arithmetic composition.
-/

namespace NSBlwChain.BLW

open Real

/-- **§12.4 ODE inequality (scalar form).**

    From the step-(iii) envelope inequality `Mdot ≤ M · σ` and the
    Biot–Savart–implicit-bound output `σ ≤ 4 · M · log M`, with
    `0 ≤ M`, conclude `Mdot ≤ 4 · M² · log M`. -/
theorem Mdot_le_4Msq_logM_scalar
    {M σ Mdot : ℝ}
    (hM_nn : 0 ≤ M)
    (h_step_iii : Mdot ≤ M * σ)
    (h_strain : σ ≤ 4 * M * Real.log M) :
    Mdot ≤ 4 * M ^ 2 * Real.log M := by
  -- Step 1: `M · σ ≤ M · (4 · M · log M)` (multiply strain by M ≥ 0).
  have h_step :
      M * σ ≤ M * (4 * M * Real.log M) :=
    mul_le_mul_of_nonneg_left h_strain hM_nn
  -- Step 2: simplify RHS to `4 · M² · log M`.
  have h_rhs_eq :
      M * (4 * M * Real.log M) = 4 * M ^ 2 * Real.log M := by ring
  rw [h_rhs_eq] at h_step
  -- Step 3: chain.
  exact le_trans h_step_iii h_step

/-- **§12.4 ODE inequality with explicit non-negativity tracking.**

    Same as `Mdot_le_4Msq_logM_scalar` but additionally records
    `0 ≤ Mdot` (growth regime) and `0 ≤ 4 · M² · log M` (consumed
    by the ODE-integration step downstream, which needs both sides
    non-negative for the differential-inequality transfer to a
    bound on `1 / (M · log M)`). -/
theorem Mdot_le_4Msq_logM_scalar_growth
    {M σ Mdot : ℝ}
    (hM_nn : 0 ≤ M)
    (hlogM_nn : 0 ≤ Real.log M)
    (hMdot_nn : 0 ≤ Mdot)
    (h_step_iii : Mdot ≤ M * σ)
    (h_strain : σ ≤ 4 * M * Real.log M) :
    0 ≤ Mdot ∧ Mdot ≤ 4 * M ^ 2 * Real.log M
      ∧ 0 ≤ 4 * M ^ 2 * Real.log M := by
  refine ⟨hMdot_nn, ?_, ?_⟩
  · exact Mdot_le_4Msq_logM_scalar hM_nn h_step_iii h_strain
  · have hM2_nn : 0 ≤ M ^ 2 := sq_nonneg M
    have : 0 ≤ 4 * M ^ 2 := by linarith
    exact mul_nonneg this hlogM_nn

end NSBlwChain.BLW
