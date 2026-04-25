-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Unconditional.Theorem2

/-!
# `FarFieldControlBundle` essential constructor

The `FarFieldControlBundle` defined in `Theorem2.lean` records three
inequality fields:

* `kernelTailSq_le : kernelTailSq ≤ C / R` (Biot–Savart kernel tail);
* `farNorm_sq_le_cauchy_schwarz : farNorm² ≤ kernelTailSq · E_ω`
  (Cauchy–Schwarz on the tail convolution);
* `farNorm_sq_le_direct : farNorm² ≤ C · E_ω / R` (direct chain).

The third is **redundant** — it follows from the first two via
transitivity (multiplying the kernel-tail bound by `E_ω ≥ 0`):

  `farNorm² ≤ kernelTailSq · E_ω ≤ (C/R) · E_ω = C · E_ω / R`.

This file provides a constructor that takes only the two genuine
analytical hypotheses and discharges the redundant field
internally.  Reduces the bundle's analytical surface from 3
inequalities to 2.

## Main result

* `FarFieldControlBundle.mk_essential` — constructor taking the
  two essential inequalities + non-negativity / positivity, with
  the redundant `farNorm_sq_le_direct` discharged by transitivity.
-/

namespace NSBlwChain.Unconditional

/-- **Essential constructor for `FarFieldControlBundle`.**

    Takes the two analytically-genuine inequalities (kernel-tail
    `L²`-bound + Cauchy–Schwarz on the tail) and discharges the
    redundant direct bound `farNorm² ≤ C · E_ω / R` by transitivity. -/
def FarFieldControlBundle.mk_essential
    {R E_ω C farNorm kernelTailSq : ℝ}
    (R_pos : 0 < R)
    (E_nonneg : 0 ≤ E_ω)
    (C_pos : 0 < C)
    (farNorm_nonneg : 0 ≤ farNorm)
    (kernelTailSq_nonneg : 0 ≤ kernelTailSq)
    (kernelTailSq_le : kernelTailSq ≤ C / R)
    (farNorm_sq_le_cauchy_schwarz : farNorm ^ 2 ≤ kernelTailSq * E_ω) :
    FarFieldControlBundle R E_ω C farNorm kernelTailSq := by
  refine
    { R_pos := R_pos
    , E_nonneg := E_nonneg
    , C_pos := C_pos
    , farNorm_nonneg := farNorm_nonneg
    , kernelTailSq_nonneg := kernelTailSq_nonneg
    , kernelTailSq_le := kernelTailSq_le
    , farNorm_sq_le_cauchy_schwarz := farNorm_sq_le_cauchy_schwarz
    , farNorm_sq_le_direct := ?_ }
  -- Discharge `farNorm² ≤ C · E_ω / R` by transitivity.
  -- Step 1: `kernelTailSq · E_ω ≤ (C/R) · E_ω`.
  have h_step1 : kernelTailSq * E_ω ≤ (C / R) * E_ω :=
    mul_le_mul_of_nonneg_right kernelTailSq_le E_nonneg
  -- Step 2: `(C/R) · E_ω = C · E_ω / R`.
  have h_eq : (C / R) * E_ω = C * E_ω / R := by ring
  -- Compose.
  calc farNorm ^ 2
      ≤ kernelTailSq * E_ω := farNorm_sq_le_cauchy_schwarz
    _ ≤ (C / R) * E_ω := h_step1
    _ = C * E_ω / R := h_eq

/-- **Sanity check: the essential constructor reproduces
    `farField_le_sqrt`.**  Composing the constructor with the
    algebraic core yields the same conclusion as a direct bundle. -/
theorem farField_le_sqrt_via_essential
    {R E_ω C farNorm kernelTailSq : ℝ}
    (R_pos : 0 < R)
    (E_nonneg : 0 ≤ E_ω)
    (C_pos : 0 < C)
    (farNorm_nonneg : 0 ≤ farNorm)
    (kernelTailSq_nonneg : 0 ≤ kernelTailSq)
    (kernelTailSq_le : kernelTailSq ≤ C / R)
    (farNorm_sq_le_cauchy_schwarz : farNorm ^ 2 ≤ kernelTailSq * E_ω) :
    farNorm ≤ Real.sqrt (C * E_ω / R) :=
  farField_le_sqrt
    (FarFieldControlBundle.mk_essential R_pos E_nonneg C_pos
      farNorm_nonneg kernelTailSq_nonneg
      kernelTailSq_le farNorm_sq_le_cauchy_schwarz)

end NSBlwChain.Unconditional
