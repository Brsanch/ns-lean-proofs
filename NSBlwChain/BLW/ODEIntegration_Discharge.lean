-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.BLW.ODEIntegration

/-!
# ODE integration discharge — substitution reduction

This file partially discharges **OPEN.md item 1**: the
`integrated_bound` field of `DifferentialInequalityBundle` (§12.4
step 7→8 of the companion paper) is reduced to a **single clean
residual** via the substitution `w(t) := 1/(M(t) · log M(t))`.

## Mathematical content

The paper's §12.4 step 7→8 derivation proceeds by the substitution
`w := 1/(M · log M)` and the observation that, given the ODE
inequality `Ṁ ≤ 4 · M² · log M` and `M > 1`, the derivative of `w`
satisfies `ẇ ≥ -4 - 4/log M`.  Integrating from `t` to `T` with the
boundary value `w(T⁻) = 0` (which follows from `M · log M → ∞` at
`T⁻`) and absorbing the lower-order `4/log M` term yields

  `w(t) ≥ 4 · (T - t)`   for `t` near `T`.

Equivalently, since `M · log M > 0`:

  `4 · (T - t) ≤ 1 / (M(t) · log M(t))`

Multiplying both sides by `M · log M > 0`:

  `4 · (T - t) · M(t) · log M(t) ≤ 1`,

i.e., `(T - t) · M(t) · log M(t) ≤ 1/4`.

This is exactly the `integrated_bound` field.

## Scope of this discharge

This file performs the **algebraic** half of the reduction: given
the substituted bound `w(t) ≥ 4(T-t)` as a hypothesis, it produces
`(T-t) · M · log M ≤ 1/4` via a short chain of lemmas on `ℝ`.

The remaining **analytical** half — deriving `w(t) ≥ 4(T-t)` from
the a.e. ODE inequality `Ṁ ≤ 4 M² log M`, the log-blowup
`log M → ∞` at `T⁻`, and an FTC/chain-rule step on `w = 1/(M log M)`
— is isolated as the single hypothesis `hW_lower_bound` of the new
constructor `DifferentialInequalityBundle.ofSubstitutedBound`.

This mirrors the partial-progress pattern used for other caveats in
this repository: the structural chain runs end-to-end, and the
remaining open analytical input is **one** cleanly-stated residual
(the substitution-level FTC step), not a multi-line open derivation.

## Contents

* `integrated_bound_of_substituted_bound` — the algebraic core:
  `w(t) ≥ 4(T-t)` with `M · log M > 0` implies
  `(T-t) · M · log M ≤ 1/4`.
* `DifferentialInequalityBundle.ofSubstitutedBound` — constructor
  that takes the raw ODE-inequality data plus the substitution-level
  residual `hW_lower_bound` and produces the full bundle with
  `integrated_bound` discharged.

## Residual hypothesis

```lean
hW_lower_bound :
  ∀ t : ℝ, t_start < t → t < T →
    4 * (T - t) ≤ 1 / (M t * Real.log (M t))
```

This is the single "one FTC + chain-rule + limit" residual that
stands between this file and an unconditional discharge of
OPEN.md item 1.

## References

* Companion paper §12.4 step 7→8 (path `paper/ns_regularity.md`).
* `BLW/ODEIntegration.lean` — the bundle definition.
* `Caveats/C1_FTC_Discharge.lean` — analogous partial discharge
  pattern for the growth-moment bundle.
-/

namespace NSBlwChain.BLW

open Real

/-- **Algebraic core of the substitution discharge.**

    Given the substitution-level bound `4·(T-t) ≤ 1/(M · log M)`
    at a single point `t`, together with positivity `0 < M · log M`,
    conclude `(T - t) · M · log M ≤ 1/4`.

    Proof: multiply both sides of `4·(T-t) ≤ 1/(M·log M)` by the
    positive quantity `M·log M`, obtaining `4·(T-t)·M·log M ≤ 1`,
    and divide by 4. -/
theorem integrated_bound_of_substituted_bound
    {Tmt M_t log_M_t : ℝ}
    (h_prod_pos : 0 < M_t * log_M_t)
    (h_w : 4 * Tmt ≤ 1 / (M_t * log_M_t)) :
    Tmt * M_t * log_M_t ≤ 1 / 4 := by
  -- Step 1: multiply the hypothesis `4·Tmt ≤ 1/(M·logM)` by
  -- `M·logM > 0` to clear the denominator.
  have h_mul : 4 * Tmt * (M_t * log_M_t) ≤ 1 := by
    have := mul_le_mul_of_nonneg_right h_w (le_of_lt h_prod_pos)
    -- `4·Tmt · (M_t·logM_t) ≤ (1/(M_t·logM_t)) · (M_t·logM_t) = 1`
    have h_cancel : 1 / (M_t * log_M_t) * (M_t * log_M_t) = 1 :=
      one_div_mul_cancel (ne_of_gt h_prod_pos)
    calc 4 * Tmt * (M_t * log_M_t)
        ≤ 1 / (M_t * log_M_t) * (M_t * log_M_t) := this
      _ = 1 := h_cancel
  -- Step 2: divide by 4 and rearrange.  Algebraic manipulation:
  --   4·Tmt·(M·logM) ≤ 1  ⇔  Tmt·M·logM ≤ 1/4.
  linarith

/-- **Substitution-level residual, quantified form.**

    Given the substitution-level bound `4·(T-t) ≤ 1/(M(t)·log M(t))`
    on `(t_start, T)` together with `M > 1` (hence `M · log M > 0`)
    on `(t_start, T)`, conclude the integrated bound
    `(T-t) · M · log M ≤ 1/4` on `(t_start, T)`.

    This is the full quantified form consumed by the bundle
    constructor. -/
theorem integrated_bound_of_hW_lower_bound
    {M : ℝ → ℝ} {T t_start : ℝ}
    (hM_gt_one : ∀ t : ℝ, t_start < t → t < T → 1 < M t)
    (hW : ∀ t : ℝ, t_start < t → t < T →
      4 * (T - t) ≤ 1 / (M t * Real.log (M t))) :
    ∀ t : ℝ, t_start < t → t < T →
      (T - t) * M t * Real.log (M t) ≤ 1 / 4 := by
  intro t ht_low ht_up
  have hM1 : 1 < M t := hM_gt_one t ht_low ht_up
  have hM_pos : 0 < M t := lt_trans zero_lt_one hM1
  have hlog_pos : 0 < Real.log (M t) := Real.log_pos hM1
  have h_prod_pos : 0 < M t * Real.log (M t) := mul_pos hM_pos hlog_pos
  have h_w := hW t ht_low ht_up
  exact integrated_bound_of_substituted_bound h_prod_pos h_w

/-- **Constructor: `DifferentialInequalityBundle` from substituted bound.**

    Assembles a `DifferentialInequalityBundle` from the raw ODE-inequality
    data plus the single substitution-level residual
    `hW_lower_bound : ∀ t ∈ (t_start, T), 4·(T-t) ≤ 1/(M·log M)`.

    The `integrated_bound` field is discharged by
    `integrated_bound_of_hW_lower_bound`; no other bundle field changes.

    **Partial-progress status.**  This constructor reduces OPEN.md
    item 1 (ODE integration §12.4 step 7→8) to a single clean
    analytical residual: the substitution-level FTC step producing
    the lower bound `w(t) ≥ 4(T-t)` for `w := 1/(M·log M)`.  Full
    unconditional discharge requires closing that step via mathlib's
    `intervalIntegral` FTC machinery applied to the composition
    `1/(M·log M)`, plus the boundary-limit `w(T⁻) = 0` from
    `log M → ∞`.  That derivation is the remaining open item. -/
noncomputable def DifferentialInequalityBundle.ofSubstitutedBound
    {M : ℝ → ℝ} {T : ℝ}
    (hT_pos : 0 < T)
    (t_start : ℝ) (ht_start_pos : 0 < t_start)
    (ht_start_lt_T : t_start < T)
    (hM_gt_one : ∀ t : ℝ, t_start < t → t < T → 1 < M t)
    (hM_nonneg : ∀ t : ℝ, t_start < t → t < T → 0 ≤ M t)
    (h_diff : ∀ t : ℝ, t_start < t → t < T →
      HasDerivAt M (deriv M t) t ∧
      deriv M t ≤ 4 * (M t) ^ 2 * Real.log (M t))
    (δ_of_ε : ℝ → ℝ)
    (hδ_pos : ∀ ε : ℝ, 0 < ε → 0 < δ_of_ε ε)
    (hδ_le : ∀ ε : ℝ, 0 < ε → δ_of_ε ε ≤ T - t_start)
    (h_log_blowup :
      ∀ ε : ℝ, 0 < ε →
        ∀ t : ℝ, T - δ_of_ε ε < t → t < T →
          1 / (4 * ε) ≤ Real.log (M t))
    (hW_lower_bound :
      ∀ t : ℝ, t_start < t → t < T →
        4 * (T - t) ≤ 1 / (M t * Real.log (M t))) :
    DifferentialInequalityBundle M T where
  T_pos := hT_pos
  t_start := t_start
  t_start_pos := ht_start_pos
  t_start_lt_T := ht_start_lt_T
  M_gt_one := hM_gt_one
  M_nonneg := hM_nonneg
  differential_bound := h_diff
  δ_of_ε := δ_of_ε
  δ_of_ε_pos := hδ_pos
  δ_of_ε_le := hδ_le
  log_blowup := h_log_blowup
  integrated_bound :=
    integrated_bound_of_hW_lower_bound hM_gt_one hW_lower_bound

/-! ## Sanity examples

Demonstrates that `integrated_bound_of_substituted_bound` produces
a well-formed inequality on simple test inputs. -/

/-- Sanity check: at `Tmt = 1/8`, `M · log M = 2`, we have
    `4·(1/8) = 1/2 ≤ 1/2 = 1/2 = 1/(M·logM)` is the edge case. -/
example :
    ((1 : ℝ) / 8) * 2 ≤ 1 / 4 := by norm_num

/-- Sanity check: the algebraic core applied to concrete numbers.
    `Tmt = 1/8`, `M_t · log_M_t = 2`, yields
    `Tmt · M · logM = 1/4 ≤ 1/4`. -/
example :
    ((1 : ℝ) / 8) * 1 * 2 ≤ 1 / 4 := by
  have : (0 : ℝ) < 1 * 2 := by norm_num
  have hw : (4 : ℝ) * (1 / 8) ≤ 1 / (1 * 2) := by norm_num
  exact integrated_bound_of_substituted_bound this hw

/-! ## Remaining analytical residual

The single open analytical step is the following substitution-level
FTC + limit argument.  It is **not** proven in this file.

Target lemma (OPEN):

  Given `M : ℝ → ℝ` satisfying `M > 1` on `(t_start, T)`, the
  a.e. pointwise bound `deriv M t ≤ 4 · (M t)² · log (M t)`, the
  log-blowup `log M → ∞` at `T⁻`, and sufficient regularity for
  chain-rule differentiability of `w := fun t => 1/(M t · log (M t))`,
  the function `w` satisfies `4 · (T - t) ≤ w(t)` on `(t_start, T)`.

Derivation outline:

1.  Differentiate `w = 1/(M · log M)` on `(t_start, T)` via the
    quotient rule and `HasDerivAt` primitives.  The pointwise
    identity is
    `ẇ = -(Ṁ · log M + Ṁ)/(M · log M)² = -Ṁ · (log M + 1)/(M · log M)²`.

2.  Substitute `Ṁ ≤ 4 · M² · log M` to obtain
    `ẇ ≥ -4 · (log M + 1)/log M = -4 - 4/log M`.

3.  Integrate from `t` to `T⁻` using mathlib's
    `intervalIntegral.integral_eq_sub_of_hasDerivAt` (FTC),
    combined with the a.e.-to-pointwise bridge via the
    hypothesis that the integrand is bounded.

4.  Take the limit `T⁻` of `w`.  From `log M → ∞` and `M > 1`,
    `M · log M → ∞`, hence `w → 0`.

5.  Absorb the `∫_t^T 4/log M ds` tail: since `log M → ∞` and
    the interval `[t, T)` is bounded, the tail is `o(T - t)` as
    `t → T⁻`.  Hence the leading-order bound is
    `w(t) ≥ 4·(T - t)`, which is exactly `hW_lower_bound`.

Each of steps 1-5 is a concrete mathlib-backed calculation; their
packaging into a single lemma is the remaining open work.  The
`ofSubstitutedBound` constructor of this file *consumes* the
output of that lemma and delivers the full bundle. -/

end NSBlwChain.BLW
