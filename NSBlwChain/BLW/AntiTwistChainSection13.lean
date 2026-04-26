-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.BLW.MdotODEInequality

set_option diagnostics true
set_option diagnostics.threshold 100

/-!
# Anti-twist BLW §13 — twist-quenched ODE inequality

Formalizes the **anti-twist correction** to the §12.4 ODE inequality
described in `paper/ns_regularity.md` (line 989–993):

  `Ṁ ≤ (4 - c_w · w²) · M² · log M`

where:

* `w ≥ 0` is the twist parameter of the vortex tube,
* `c_w > 0` is the **twist-quench coefficient** (whose derivation
  from the underlying anti-twist cancellation structure of paper
  §D.1–§D.2 is left as a named hypothesis here — see the bundle's
  `c_w_derivation_pending` docstring),
* the constraint `c_w · w² < 4` keeps the effective coefficient
  `k := 4 - c_w · w²` strictly positive.

The point of this file:

1. Extract the **scalar-only generic** version of
   `MdotODEInequality.Mdot_le_4Msq_logM_scalar` (which is hard-coded
   to `k = 4`) to an arbitrary non-negative coefficient `k`.

2. Package the anti-twist hypothesis as `AntiTwistBundle` whose
   only field beyond positivity is the **twist-quenched strain
   bound** `σ ≤ k · M · log M`.

3. Compose to deliver the corrected ODE conclusion.

The structural takeaway: the existing §12.4 ODE-integration chain
in `Theorem3FullThreading.lean` accepts any positive coefficient `k`
in place of `4`, so anti-twist routes the regularity proof through
the same `(T - t) · M · log M ≤ 1/k` mechanism with a smaller
constant.

## Main results

* `Mdot_le_kMsq_logM_scalar` — generic ODE inequality.
* `AntiTwistBundle` — twist-quench hypothesis bundle.
* `AntiTwistBundle.k_pos` — derived positivity of `k = 4 - c_w·w²`.
* `AntiTwistBundle.Mdot_bound` — corrected ODE conclusion.
-/

namespace NSBlwChain.BLW

open Real

/-- **Generic ODE inequality with arbitrary non-negative coefficient.**

    From step-(iii) `Mdot ≤ M · σ` and a generic strain bound
    `σ ≤ k · M · log M` with `0 ≤ M`, conclude
    `Mdot ≤ k · M² · log M`.

    Mirrors `MdotODEInequality.Mdot_le_4Msq_logM_scalar` exactly
    except for the abstract coefficient `k`. -/
theorem Mdot_le_kMsq_logM_scalar
    {M σ Mdot k : ℝ}
    (hM_nn : 0 ≤ M)
    (h_step_iii : Mdot ≤ M * σ)
    (h_strain : σ ≤ k * M * Real.log M) :
    Mdot ≤ k * M ^ 2 * Real.log M := by
  -- Step 1: M · σ ≤ M · (k · M · log M).
  have h_step :
      M * σ ≤ M * (k * M * Real.log M) :=
    mul_le_mul_of_nonneg_left h_strain hM_nn
  -- Step 2: simplify RHS to k · M² · log M.
  have h_rhs_eq :
      M * (k * M * Real.log M) = k * M ^ 2 * Real.log M := by ring
  rw [h_rhs_eq] at h_step
  -- Step 3: chain.
  exact le_trans h_step_iii h_step

/-! ## Anti-twist hypothesis bundle (paper §13) -/

/-- **Anti-twist scalar hypothesis bundle.**

    Packages the twist-quench correction to the §12.4 ODE
    inequality:

    * `w` — twist parameter of the vortex tube,
    * `c_w` — quench coefficient,
    * `w_nn`, `c_w_pos` — positivity,
    * `quench_lt_four` — strict bound `c_w · w² < 4` ensuring the
      effective coefficient `k := 4 - c_w · w²` stays positive,
    * `M_nn` — `0 ≤ M`,
    * `step_iii` — step-(iii) coupling `Mdot ≤ M · σ` (output of
      `BLW.Mdot_le_M_sigma_scalar`),
    * `quenched_strain_bound` — the **anti-twist-corrected strain
      bound** `σ ≤ (4 - c_w · w²) · M · log M`.

    The `quenched_strain_bound` is the structural output of the
    anti-twist cancellation in `paper/ns_regularity_blw_derivations.md`
    §D.1–§D.2; it is taken as a named hypothesis here.  Once a
    rigorous derivation of `c_w` from the empirical 10/10 antiparallel
    `\bar\omega_\phi` snapshot becomes available, the
    `quenched_strain_bound` can be replaced by a constructor from
    upstream.  See `c_w_derivation_pending`. -/
structure AntiTwistBundle
    (M σ Mdot w c_w : ℝ) : Prop where
  /-- Non-negative twist parameter. -/
  w_nn       : 0 ≤ w
  /-- Positive quench coefficient. -/
  c_w_pos    : 0 < c_w
  /-- **Quench strict bound.**  `c_w · w² < 4` keeps the effective
      coefficient `k = 4 - c_w · w²` strictly positive. -/
  quench_lt_four : c_w * w ^ 2 < 4
  /-- Non-negative envelope. -/
  M_nn       : 0 ≤ M
  /-- Step-(iii) coupling. -/
  step_iii   : Mdot ≤ M * σ
  /-- **Twist-quenched strain bound.**
      `σ ≤ (4 - c_w · w²) · M · log M`. -/
  quenched_strain_bound :
    σ ≤ (4 - c_w * w ^ 2) * M * Real.log M

/-- **Derived positivity of the effective coefficient.**

    From `c_w · w² < 4`, conclude `0 < 4 - c_w · w²`. -/
theorem AntiTwistBundle.k_pos
    {M σ Mdot w c_w : ℝ}
    (A : AntiTwistBundle M σ Mdot w c_w) :
    0 < 4 - c_w * w ^ 2 := by
  linarith [A.quench_lt_four]

/-- **Anti-twist ODE conclusion (paper §13 corrected inequality).**

    From the anti-twist bundle:

    `Mdot ≤ (4 - c_w · w²) · M² · log M`.

    Equivalently: `Mdot ≤ k · M² · log M` with `k := 4 - c_w · w²`,
    a strictly smaller coefficient than the no-twist `4`. -/
theorem AntiTwistBundle.Mdot_bound
    {M σ Mdot w c_w : ℝ}
    (A : AntiTwistBundle M σ Mdot w c_w) :
    Mdot ≤ (4 - c_w * w ^ 2) * M ^ 2 * Real.log M :=
  Mdot_le_kMsq_logM_scalar A.M_nn A.step_iii A.quenched_strain_bound

/-- **Anti-twist quench gain over the no-twist case.**

    `(4 - c_w · w²) ≤ 4` always (equality at `w = 0`).  Thus the
    anti-twist ODE is **strictly stronger** than the no-twist
    `Mdot ≤ 4 · M² · log M` whenever `c_w · w² > 0` and
    `0 < log M` (the growth regime). -/
theorem AntiTwistBundle.bound_le_no_twist
    {M σ Mdot w c_w : ℝ}
    (A : AntiTwistBundle M σ Mdot w c_w)
    (h_logM_nn : 0 ≤ Real.log M) :
    (4 - c_w * w ^ 2) * M ^ 2 * Real.log M
      ≤ 4 * M ^ 2 * Real.log M := by
  have h_w_sq_nn : 0 ≤ w ^ 2 := sq_nonneg w
  have h_quench_nn : 0 ≤ c_w * w ^ 2 :=
    mul_nonneg (le_of_lt A.c_w_pos) h_w_sq_nn
  -- (4 - q) ≤ 4 since q ≥ 0.
  have h_le : (4 - c_w * w ^ 2 : ℝ) ≤ 4 := by linarith
  -- Multiply through by M² · log M ≥ 0.
  have hM2_nn : 0 ≤ M ^ 2 := sq_nonneg M
  have hM2_logM_nn : 0 ≤ M ^ 2 * Real.log M :=
    mul_nonneg hM2_nn h_logM_nn
  nlinarith [h_le, hM2_logM_nn]

/-! ## Notes on `c_w` derivation

The twist-quench coefficient `c_w` is the proportionality constant
arising from the cancellation of the `(\bar\omega_\phi)^{(s)} +
(\bar\omega_\phi)^{(a)}` decomposition under cylindrical symmetry
(paper `ns_regularity_blw_derivations.md` §D.1).  The empirical
record (10/10 antiparallel snapshots in `paper/ns_regularity.md`
line 826) suggests `c_w` is uniformly bounded below by an
`O(1)` constant, but extracting this rigorously requires the
fixed-point argument promised in §D.2 to terminate at a positive
lower bound.  Both the existence of `c_w > 0` and the strict
`c_w · w² < 4` constraint are taken as named hypotheses in
`AntiTwistBundle`. -/

end NSBlwChain.BLW
