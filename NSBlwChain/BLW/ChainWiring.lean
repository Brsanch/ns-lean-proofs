-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Caveats.C4_ImplicitBound
import NSBlwChain.BLW.Capstone

/-!
# Chain wiring — bridging Capstone to C4

This file provides the interface bridge between the per-time
composition witness of `BLW/Capstone.lean` and the implicit-bound
machinery of `Caveats/C4_ImplicitBound.lean`.

## The issue

`BLWChainPerTime.self_consistent` concludes (with the placeholder
constants `C_L = 1`, `L = 2` from the axiom witness):

  `σ ≤ M · (2 + log 2 + (1/2) · log(σ/ν))`.

`C4_ImplicitBound.ImplicitBoundBundle.hImplicit` expects:

  `σ ≤ M · (1 + log L + (1/2) · log(σ/ν)) + K`.

The two forms agree if we set `L := 2 · e` and `K := 0`, because
`log(2 · e) = log 2 + 1`, so

  `M · (1 + log(2e) + (1/2) log(σ/ν)) = M · (2 + log 2 + (1/2) log(σ/ν))`.

## Contents

* `BLWChainPerTime.toImplicitBoundBundle` — constructs an
  `ImplicitBoundBundle` from the per-time witness, given a lower
  bound `1 ≤ M` and a positivity hypothesis on `σ`.

With this bridge, the per-time gradient bound of Theorem 12.2
connects in one call to the implicit-bound step (C4.2): downstream
code can go `w.toImplicitBoundBundle hM hσ |>.σ_le_of_largeness
  hLarge` to land `σ ≤ 4 M log M`.

## Scope

This is pure structural wiring — no analytical content added.  The
largeness hypothesis `hLarge` of `σ_le_of_largeness` still needs to
be discharged by the Banach / convexity argument of §C4, which is a
separate pass.
-/

namespace NSBlwChain.BLW

open NSBlwChain NSBlwChain.Caveats

/-- Construct an `ImplicitBoundBundle` from a per-time BLW witness.

    With `L := 2·e` and `K := 0`, the `hImplicit` inequality matches
    `BLWChainPerTime.self_consistent` exactly. -/
noncomputable def BLWChainPerTime.toImplicitBoundBundle
    {u : VelocityField} {ν T : ℝ} (w : BLWChainPerTime u ν T)
    (hM : 1 ≤ w.a.M) (hσ : 0 < w.a.sigma) :
    ImplicitBoundBundle where
  ν := w.a.ν
  L := 2 * Real.exp 1
  M := w.a.M
  σ := w.a.sigma
  K := 0
  hν_pos := w.a.nu_pos
  hL_pos := by
    have h1 : (0 : ℝ) < 2 := by norm_num
    have h2 : (0 : ℝ) < Real.exp 1 := Real.exp_pos _
    exact mul_pos h1 h2
  hM_ge_one := hM
  hσ_pos := hσ
  hK_nonneg := le_refl 0
  hImplicit := by
    have h_self := w.self_consistent hσ
    -- h_self : σ ≤ M * (1 + 1 + log 2 + (1/2) * log(σ/ν))
    -- target: σ ≤ M * (1 + log(2*e) + (1/2) * log(σ/ν)) + 0
    have h_log : Real.log (2 * Real.exp 1) = Real.log 2 + 1 := by
      have h2 : (2 : ℝ) ≠ 0 := by norm_num
      have he : Real.exp 1 ≠ 0 := Real.exp_ne_zero _
      rw [Real.log_mul h2 he, Real.log_exp]
    rw [h_log]
    linarith [h_self]

/-- One-line corollary: if the largeness hypothesis holds on the
    bridged bundle, `σ ≤ 4 M log M`. -/
theorem BLWChainPerTime.sigma_le_4M_log_M
    {u : VelocityField} {ν T : ℝ} (w : BLWChainPerTime u ν T)
    (hM : 1 ≤ w.a.M) (hσ : 0 < w.a.sigma)
    (hLarge :
      1 + Real.log (2 * Real.exp 1)
        + (1 / 2) * Real.log (w.a.sigma / w.a.ν)
          ≤ 4 * Real.log w.a.M - 0 / w.a.M) :
    w.a.sigma ≤ 4 * w.a.M * Real.log w.a.M := by
  exact (w.toImplicitBoundBundle hM hσ).σ_le_of_largeness hLarge

end NSBlwChain.BLW
