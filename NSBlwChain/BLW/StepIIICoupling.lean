-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.BLW.EnvelopeAtArgmax
import NSBlwChain.BLW.MdotODEInequality

/-!
# Step-(iii) scalar coupling: `Mdot ≤ M · σ`

Bridges:

* **Commit 8** (`EnvelopeAtArgmax.deriv_scalar_half_eq`): the
  envelope identity `deriv(|ω(_, xStar)|² / 2) t = M · Mdot`.

* **Commit 10** (`Mdot_le_4Msq_logM_scalar`): the §12.4 ODE
  inequality, which takes `Mdot ≤ M · σ` as a hypothesis.

The bridge content — derive `Mdot ≤ M · σ` — uses three further
pieces that the upstream BLW capstone consumes internally:

1. **Vorticity equation at `(t, xStar)`**:
   `∂_t ω = (ω · ∇)u + ν · Δω` (vector identity).
2. **Strain identity under alignment**:
   `ω · (ω · ∇)u (xStar) = M² · σ`  (paper §12.3 strain-alignment).
3. **Laplacian-alignment + max-principle**:
   `ω · Δω(xStar) = M · Δω₃(xStar)` (alignment) and
   `Δω₃(xStar) ≤ 0` (max principle on `|ω|²` at the argmax).

The chain at scalar level is:

```
M · Mdot = deriv(|ω(_, xStar)|²/2) t            [Danskin / envelope id]
         = ω(xStar) · ∂_t ω(xStar)               [chain rule + half-square]
         = ω · (ω·∇)u + ν · ω · Δω               [vorticity equation]
         = M² · σ + ν · M · Δω₃                  [strain + Laplace alignment]
         ≤ M² · σ                                [Δω₃ ≤ 0 and ν, M ≥ 0]
```

Dividing by `M > 0` gives `Mdot ≤ M · σ`.

This file proves the **scalar form** of this chain — pure
arithmetic given the four scalar identities + sign hypothesis.

## Main result

* `Mdot_le_M_sigma_scalar` — the algebraic step-(iii) coupling.
* `Mdot_le_4Msq_logM_via_step_iii` — composition with strain
  bound producing the §12.4 ODE inequality with `Mdot ≤ M · σ`
  derived (instead of taken as input).
-/

namespace NSBlwChain.BLW

open Real

/-- **Step-(iii) scalar coupling: `Mdot ≤ M · σ`.**

    From the four scalar identities of step (iii) at the argmax,
    derive the envelope-time-derivative bound `Mdot ≤ M · σ`. -/
theorem Mdot_le_M_sigma_scalar
    {M Mdot σ ν Δω₃ derivPsi : ℝ}
    (hM_pos : 0 < M)
    (hν_nn : 0 ≤ ν)
    (h_envelope : M * Mdot = derivPsi)
    (h_step_iii : derivPsi = M ^ 2 * σ + ν * M * Δω₃)
    (h_lap_nonpos : Δω₃ ≤ 0) :
    Mdot ≤ M * σ := by
  -- Step 1: combine envelope + step-iii to express M·Mdot.
  have h_eq : M * Mdot = M ^ 2 * σ + ν * M * Δω₃ := by
    rw [h_envelope]; exact h_step_iii
  -- Step 2: ν·M·Δω₃ ≤ 0 from Δω₃ ≤ 0 and ν, M ≥ 0.
  have h_νM_nn : 0 ≤ ν * M := mul_nonneg hν_nn (le_of_lt hM_pos)
  have h_visc_nonpos : ν * M * Δω₃ ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos h_νM_nn h_lap_nonpos
  -- Step 3: M·Mdot ≤ M²·σ.
  have h_M_Mdot_le : M * Mdot ≤ M ^ 2 * σ := by
    rw [h_eq]; linarith
  -- Step 4: divide by M > 0.
  have h_M_ne : M ≠ 0 := ne_of_gt hM_pos
  -- Rewrite M² · σ = M · (M · σ).
  have h_rhs_eq : M ^ 2 * σ = M * (M * σ) := by ring
  rw [h_rhs_eq] at h_M_Mdot_le
  -- Cancel M on the left.
  exact (mul_le_mul_left hM_pos).mp h_M_Mdot_le

/-- **§12.4 ODE inequality with step-(iii) coupling internalized.**

    Combines `Mdot_le_M_sigma_scalar` with the strain bound `σ ≤
    4 · M · log M` to deliver `Mdot ≤ 4 · M² · log M` directly from
    the four step-(iii) scalar identities + the strain bound — no
    separate `Mdot ≤ M · σ` hypothesis required. -/
theorem Mdot_le_4Msq_logM_via_step_iii
    {M Mdot σ ν Δω₃ derivPsi : ℝ}
    (hM_pos : 0 < M)
    (hν_nn : 0 ≤ ν)
    (hlogM_nn : 0 ≤ Real.log M)
    (h_envelope : M * Mdot = derivPsi)
    (h_step_iii : derivPsi = M ^ 2 * σ + ν * M * Δω₃)
    (h_lap_nonpos : Δω₃ ≤ 0)
    (h_strain : σ ≤ 4 * M * Real.log M) :
    Mdot ≤ 4 * M ^ 2 * Real.log M := by
  have h_step :=
    Mdot_le_M_sigma_scalar hM_pos hν_nn h_envelope h_step_iii h_lap_nonpos
  exact Mdot_le_4Msq_logM_scalar (le_of_lt hM_pos) h_step h_strain

end NSBlwChain.BLW
