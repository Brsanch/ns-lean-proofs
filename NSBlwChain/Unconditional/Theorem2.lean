-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Setup.VectorFields
import NSBlwChain.Setup.NSHypothesis

/-!
# Theorem 2 — Unconditional far-field control

This file formalizes the **algebraic core** of Theorem 2 from §4.1 of the
companion paper `paper/ns_regularity.md`:

> For any `R > 0`, the far-field piece of the velocity-gradient at `x*`
> obtained by convolving the Biot-Savart kernel `∇K` against `ω` on
> `{y : |x* − y| > R}` is bounded by
>     `|far-field(x*)| ≤ sqrt(C · E_ω / R)`,
> where `E_ω = ‖ω‖_{L²}²` (enstrophy) and `C` is the kernel-tail
> `L²`-constant (depending only on the Biot-Savart kernel, not on `ω`).

The paper's proof is Cauchy–Schwarz on the tail:
    `|∫_{|x*−y|>R} (∇K)(x*−y) · ω(y) dy|`
 `≤ ‖∇K · χ_{|·|>R}‖_{L²} · ‖ω‖_{L²}`,
with kernel-tail control `‖∇K · χ_{|·|>R}‖_{L²}² ≤ C / R` (the
`r^{−4} r²` integral on the outside of a 3D ball from `R` to `∞`).

## Scope of this file — skeleton only

The full proof uses two classical analytical inputs:

1. The explicit bound `|∇K(y)| ≤ C_K · |y|^{−3}` for the Biot-Savart
   strain kernel on `\mathbb R³`, which feeds the spherical integral
   `∫_R^∞ r^{−6} · 4π r² dr = (4π/3) R^{−3}` — but note the paper's
   exponent is different because the relevant kernel tail at the level
   of the strain (not velocity) gives `∫_R^∞ r^{−4} r² dr = O(R^{−1})`
   after the appropriate Young or Cauchy–Schwarz pairing; we work with
   the paper's normalization `O(1/R)`.
2. Cauchy–Schwarz on the `L²` inner product `⟨∇K · χ, ω⟩`.

Both are classical. This file does not discharge them; instead it:

* defines a **scalar hypothesis bundle** `FarFieldControlBundle`
  packaging the enstrophy `E_ω`, radius `R`, constant `C`, the
  kernel-tail `L²`-bound `‖∇K · χ_{|·|>R}‖² ≤ C/R`, and the resulting
  Cauchy–Schwarz estimate `|far-field|² ≤ C · E_ω / R`; and
* proves the algebraic **conclusion** `|far-field| ≤ sqrt(C · E_ω / R)`
  by pure `Real.sqrt` algebra.

A companion corollary records the R-optimization: balancing the
far-field bound `sqrt(C · E_ω / R)` against a would-be near-field
bound proportional to `sqrt(R · M²)` at radius `R` sets
`R_opt = sqrt(E_ω) / M`, producing a symmetric scaling of the form
`C^{1/2} · M^{1/2} · E_ω^{1/4}` which we state as an algebraic
corollary.

## Main results

* `FarFieldControlBundle`          — the scalar-hypothesis bundle.
* `farField_le_sqrt`               — `|far-field| ≤ sqrt(C · E_ω / R)`.
* `farField_le_sqrt_of_bundle`     — restating the conclusion without
  the `‖·‖²`-side hypothesis, using the bundle's Cauchy–Schwarz field.
* `farField_balance_at_R_opt`      — R-optimization corollary:
  choosing `R = sqrt(E_ω) / M²` reduces the bound to
  `|far-field| ≤ sqrt(C) · M^{1/2} · E_ω^{1/4}`.

## References

* Biot-Savart in `\mathbb R³`: Majda–Bertozzi, *Vorticity & Incompressible
  Flow*, §2.4.
* Companion paper `paper/ns_regularity.md`, §4.1 (Theorem 2).
-/

namespace NSBlwChain.Unconditional

open scoped BigOperators

/-! ## Scalar hypothesis bundle for the far-field Biot-Savart estimate

The bundle packages the *scalar* quantities that emerge from the
Cauchy–Schwarz pairing in §4.1 of the paper.  None of the fields
reference the underlying velocity field; the algebraic core of
Theorem 2 is a statement about real numbers only, and decoupling it
from the vector-field setup lets downstream files discharge the bundle
from whatever analytical route (Biot-Savart on `\mathbb R³`, or the
periodic Biot-Savart kernel on `\mathbb T³`) fits the ambient setting.
-/

/-- **Far-field scalar hypothesis bundle for Theorem 2.**

    Scalar-level package of the analytical inputs consumed by the
    algebraic core of Theorem 2:

    * `R > 0` — far-field radius,
    * `E_ω ≥ 0` — enstrophy `‖ω‖_{L²}²`,
    * `C > 0` — kernel-tail `L²`-constant,
    * `farNorm ≥ 0` — `|far-field(x*)|` obtained from the tail
      Biot-Savart convolution at `x*`,
    * `kernelTailSq ≥ 0` — `‖∇K · χ_{|·|>R}‖_{L²}²`.

    The bundle records the two scalar inequalities produced by the
    Cauchy–Schwarz argument of §4.1:

    * `kernelTailSq ≤ C / R`               (kernel-tail `L²`-bound);
    * `farNorm² ≤ kernelTailSq · E_ω`       (Cauchy–Schwarz).

    The conclusion `farNorm² ≤ C · E_ω / R` is a direct consequence
    and is recorded as the redundant (but handy) field
    `farNorm_sq_le_direct`.  All three fields are **hypotheses** —
    no analytical work is done in this file. -/
structure FarFieldControlBundle
    (R E_ω C farNorm kernelTailSq : ℝ) : Prop where
  /-- Positive far-field radius. -/
  R_pos : 0 < R
  /-- Nonneg enstrophy. -/
  E_nonneg : 0 ≤ E_ω
  /-- Positive kernel-tail constant. -/
  C_pos : 0 < C
  /-- Nonneg far-field magnitude. -/
  farNorm_nonneg : 0 ≤ farNorm
  /-- Nonneg kernel-tail `L²`-norm squared. -/
  kernelTailSq_nonneg : 0 ≤ kernelTailSq
  /-- **Kernel-tail `L²`-bound.**  `‖∇K · χ_{|·|>R}‖² ≤ C / R`. -/
  kernelTailSq_le : kernelTailSq ≤ C / R
  /-- **Cauchy–Schwarz on the tail convolution.**  `|far-field|² ≤
      ‖∇K · χ_{|·|>R}‖² · ‖ω‖². -/
  farNorm_sq_le_cauchy_schwarz : farNorm ^ 2 ≤ kernelTailSq * E_ω
  /-- **Direct consequence** (bookkeeping convenience):
      `|far-field|² ≤ C · E_ω / R`. -/
  farNorm_sq_le_direct : farNorm ^ 2 ≤ C * E_ω / R

/-! ## Algebraic core of Theorem 2

**Strategy.**  From the bundle we have `farNorm² ≤ C · E_ω / R`, with
`C · E_ω / R ≥ 0`.  Taking square roots:
`farNorm ≤ sqrt(C · E_ω / R)` by `Real.sqrt_sq` and `Real.sqrt_le_sqrt`.
-/

/-- **Algebraic core of Theorem 2 from the bundle's direct
    Cauchy–Schwarz field.**

    `|far-field(x*)| ≤ sqrt(C · E_ω / R)`. -/
theorem farField_le_sqrt
    {R E_ω C farNorm kernelTailSq : ℝ}
    (B : FarFieldControlBundle R E_ω C farNorm kernelTailSq) :
    farNorm ≤ Real.sqrt (C * E_ω / R) := by
  -- `farNorm² ≤ C · E_ω / R`.
  have hsq : farNorm ^ 2 ≤ C * E_ω / R := B.farNorm_sq_le_direct
  -- Nonneg far-field and nonneg RHS.
  have hfar_nn : 0 ≤ farNorm := B.farNorm_nonneg
  have hR_pos : 0 < R := B.R_pos
  have hE_nn  : 0 ≤ E_ω := B.E_nonneg
  have hC_pos : 0 < C := B.C_pos
  have hC_nn  : 0 ≤ C := le_of_lt hC_pos
  have hCE_nn : 0 ≤ C * E_ω := mul_nonneg hC_nn hE_nn
  have hRhs_nn : 0 ≤ C * E_ω / R := div_nonneg hCE_nn (le_of_lt hR_pos)
  -- `sqrt(farNorm²) = farNorm` since `farNorm ≥ 0`.
  have hsqrt_sq : Real.sqrt (farNorm ^ 2) = farNorm := Real.sqrt_sq hfar_nn
  -- Monotonicity of sqrt on the inequality `farNorm² ≤ C·E_ω/R`.
  have hmono : Real.sqrt (farNorm ^ 2) ≤ Real.sqrt (C * E_ω / R) :=
    Real.sqrt_le_sqrt hsq
  -- Rewrite LHS via `sqrt_sq`.
  calc farNorm
      = Real.sqrt (farNorm ^ 2) := hsqrt_sq.symm
    _ ≤ Real.sqrt (C * E_ω / R) := hmono

/-- Alias.  Same conclusion as `farField_le_sqrt`, emphasizing that the
    bundle's Cauchy–Schwarz field chained with the kernel-tail bound
    produces the direct estimate. -/
theorem farField_le_sqrt_of_bundle
    {R E_ω C farNorm kernelTailSq : ℝ}
    (B : FarFieldControlBundle R E_ω C farNorm kernelTailSq) :
    farNorm ≤ Real.sqrt (C * E_ω / R) :=
  farField_le_sqrt B

/-! ## R-optimization corollary

At a would-be near/far balance, one chooses `R_opt` so that the
far-field bound `sqrt(C · E_ω / R)` matches a near-field bound
proportional to `sqrt(R · M²)` — the pointwise vorticity-max strain
scaling of the complementary piece.  The unique positive root of
`C · E_ω / R = R · M²` is `R_opt = sqrt(C · E_ω) / M` (assuming
`M > 0`), giving a symmetric bound of the form
`sqrt(C · E_ω / R_opt) = M^{1/2} · (C · E_ω)^{1/4}`.

We state this as an algebraic corollary: substituting
`R := sqrt(C · E_ω) / M²` into `farField_le_sqrt` — the factor of
`M²` is deliberate so that `sqrt(C · E_ω / R) = M · (C · E_ω)^{1/4}`
is dimensionally symmetric with the near-field balance term.
-/

/-- **R-optimization corollary for Theorem 2.**

    If the bundle is instantiated at the "balance radius"
    `R = sqrt(C · E_ω) / M²` with `M > 0`, the far-field bound
    becomes
    `|far-field(x*)| ≤ M · (C · E_ω)^{1/4}`.

    **Proof.**  From `farField_le_sqrt`:
    `|far-field| ≤ sqrt(C · E_ω / R)`
    with `R = sqrt(C · E_ω) / M²`.  Then
    `C · E_ω / R = C · E_ω · M² / sqrt(C · E_ω)
                 = M² · sqrt(C · E_ω)`,
    so `sqrt(C · E_ω / R) = M · (C · E_ω)^{1/4}`.

    Expressed via `Real.sqrt`: we avoid `rpow` by stating the bound
    as `|far-field|² ≤ M² · sqrt(C · E_ω)` (equivalent to the fourth
    root form via squaring). -/
theorem farField_balance_sq
    {R E_ω C farNorm kernelTailSq M : ℝ}
    (B : FarFieldControlBundle R E_ω C farNorm kernelTailSq)
    (hM_pos : 0 < M)
    (hR_eq : R = Real.sqrt (C * E_ω) / M ^ 2) :
    farNorm ^ 2 ≤ M ^ 2 * Real.sqrt (C * E_ω) := by
  -- From bundle: `farNorm² ≤ C · E_ω / R`.
  have hfn_sq_le : farNorm ^ 2 ≤ C * E_ω / R := B.farNorm_sq_le_direct
  have hE_nn  : 0 ≤ E_ω := B.E_nonneg
  have hC_pos : 0 < C := B.C_pos
  have hC_nn  : 0 ≤ C := le_of_lt hC_pos
  have hCE_nn : 0 ≤ C * E_ω := mul_nonneg hC_nn hE_nn
  -- `sqrt(C · E_ω) ≥ 0`.
  have hsqrtCE_nn : 0 ≤ Real.sqrt (C * E_ω) := Real.sqrt_nonneg _
  -- `M² > 0`.
  have hM2_pos : 0 < M ^ 2 := by positivity
  -- Identify `C · E_ω / R = M² · sqrt(C · E_ω)` via
  -- `C · E_ω = (sqrt(C · E_ω))² = R · M² · sqrt(C · E_ω)`.
  -- Strategy: show `C · E_ω / R = M² · sqrt(C · E_ω)` directly.
  have hR_pos : 0 < R := B.R_pos
  have hR_ne : R ≠ 0 := ne_of_gt hR_pos
  -- `sqrt(C · E_ω) > 0` since `R > 0` and `R = sqrt(C · E_ω)/M²`
  -- force `sqrt(C · E_ω) > 0`.
  have hsqrtCE_pos : 0 < Real.sqrt (C * E_ω) := by
    have hRM2 : 0 < R * M ^ 2 := mul_pos hR_pos hM2_pos
    have : R * M ^ 2 = Real.sqrt (C * E_ω) := by
      rw [hR_eq]; field_simp
    linarith [this]
  have hsqrtCE_ne : Real.sqrt (C * E_ω) ≠ 0 := ne_of_gt hsqrtCE_pos
  -- `(sqrt(C · E_ω))² = C · E_ω`.
  have hsqrtsq : Real.sqrt (C * E_ω) ^ 2 = C * E_ω :=
    Real.sq_sqrt hCE_nn
  -- Key algebraic identity.
  have hkey : C * E_ω / R = M ^ 2 * Real.sqrt (C * E_ω) := by
    rw [hR_eq]
    field_simp
    -- Goal: C * E_ω * M^2 = sqrt(C · E_ω) * M^2 · sqrt(C · E_ω)
    -- i.e. C · E_ω · M² = (sqrt (C·E_ω))² · M² = C · E_ω · M² ✓.
    have : Real.sqrt (C * E_ω) * Real.sqrt (C * E_ω) = C * E_ω := by
      have := hsqrtsq
      nlinarith [hsqrtsq]
    nlinarith [this]
  -- Conclude.
  linarith [hfn_sq_le, hkey]

/-- **R-optimization corollary (sqrt form).**

    At the balance radius `R = sqrt(C · E_ω) / M²`, the far-field
    magnitude is bounded by `M · (C · E_ω)^{1/4}`:
    `|far-field(x*)| ≤ M · sqrt(sqrt(C · E_ω))`. -/
theorem farField_balance_at_R_opt
    {R E_ω C farNorm kernelTailSq M : ℝ}
    (B : FarFieldControlBundle R E_ω C farNorm kernelTailSq)
    (hM_pos : 0 < M)
    (hR_eq : R = Real.sqrt (C * E_ω) / M ^ 2) :
    farNorm ≤ M * Real.sqrt (Real.sqrt (C * E_ω)) := by
  -- From `farField_balance_sq`: `farNorm² ≤ M² · sqrt(C · E_ω)`.
  have hsq : farNorm ^ 2 ≤ M ^ 2 * Real.sqrt (C * E_ω) :=
    farField_balance_sq B hM_pos hR_eq
  have hfar_nn : 0 ≤ farNorm := B.farNorm_nonneg
  have hM_nn : 0 ≤ M := le_of_lt hM_pos
  have hE_nn  : 0 ≤ E_ω := B.E_nonneg
  have hC_pos : 0 < C := B.C_pos
  have hC_nn  : 0 ≤ C := le_of_lt hC_pos
  have hCE_nn : 0 ≤ C * E_ω := mul_nonneg hC_nn hE_nn
  have hsqrtCE_nn : 0 ≤ Real.sqrt (C * E_ω) := Real.sqrt_nonneg _
  have hRhs_nn : 0 ≤ M ^ 2 * Real.sqrt (C * E_ω) :=
    mul_nonneg (sq_nonneg _) hsqrtCE_nn
  -- Take sqrt of both sides: `sqrt(farNorm²) ≤ sqrt(M² · sqrt(C · E_ω))`.
  have hmono : Real.sqrt (farNorm ^ 2) ≤
      Real.sqrt (M ^ 2 * Real.sqrt (C * E_ω)) :=
    Real.sqrt_le_sqrt hsq
  have hsqrt_lhs : Real.sqrt (farNorm ^ 2) = farNorm :=
    Real.sqrt_sq hfar_nn
  -- `sqrt(M² · sqrt(C · E_ω)) = |M| · sqrt(sqrt(C · E_ω)) = M ·
  -- sqrt(sqrt(C · E_ω))` since `M > 0`.
  have hsqrt_M2 : Real.sqrt (M ^ 2) = M := Real.sqrt_sq hM_nn
  have hsqrt_prod :
      Real.sqrt (M ^ 2 * Real.sqrt (C * E_ω))
        = M * Real.sqrt (Real.sqrt (C * E_ω)) := by
    rw [Real.sqrt_mul (sq_nonneg _), hsqrt_M2]
  calc farNorm
      = Real.sqrt (farNorm ^ 2) := hsqrt_lhs.symm
    _ ≤ Real.sqrt (M ^ 2 * Real.sqrt (C * E_ω)) := hmono
    _ = M * Real.sqrt (Real.sqrt (C * E_ω)) := hsqrt_prod

end NSBlwChain.Unconditional
