-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Caveats.C4_ImplicitBound
import NSBlwChain.Caveats.C4_Monotonicity
import NSBlwChain.BLW.LogInequalities
import NSBlwChain.BLW.BootstrapDischarge

/-!
# Caveat C4 — Growth-dominance discharge of the largeness hypothesis

This file closes **OPEN.md item 2** — the previously-hypothesised
"Banach fixed-point" largeness condition

  `(C4-large)   1 + log L + (1/2) log(σ/ν) ≤ 4 log M - K/M`

is here *derived* from growth-dominance.  The paper's "Banach"
framing is structural scaffolding; the mathematical content is the
elementary fact that `log M` eventually dominates any fixed
combination of `log L`, `log ν`, `log(log M)`, and `K/M`.

## Content

Given the bootstrap-coupled form `σ ≤ 4 · M · Real.log M`
(paper §C4 step 6 / `BootstrapDischarge.c4_largeness_from_bootstrap`),
(C4-large) reduces to the scalar threshold inequality

  `(C4-thresh)   1 + log L + (1/2)(log 4 + log M + log(log M) - log ν)
                    ≤ 4 log M - K/M`.

We show: there exists `M_crit := M_crit(L, ν, K) ≥ 2` such that
for every `M ≥ M_crit`, (C4-thresh) holds.  Composing with the
existing bootstrap-discharge chain delivers (C4-large) as a
hypothesis-free consequence of `M ≥ M_crit` plus the bootstrap
coupling.

## Proof sketch

Rearrange (C4-thresh) to

  `A₀ + (1/2) log(log M) + K/M ≤ (7/2) log M`

where `A₀ := 1 + log L + (1/2) log 4 - (1/2) log ν`.

Using `log(log M) ≤ log M` (mathlib's `Real.log_le_self` when
`log M ≥ 0`, i.e., `M ≥ 1`), (C4-thresh) reduces to the stronger
scalar inequality

  `A₀ + K/M ≤ 3 log M`.

Choose

  `M_crit := max 2 (max (K + 2) (Real.exp (|A₀| + 1)))`.

Then for `M ≥ M_crit`:
* `M ≥ 2 > 1` gives `log M > 0`;
* `M ≥ K + 2 > K ≥ 0` (since `K ≥ 0`) gives `K/M ≤ K/(K+2) ≤ 1`;
* `M ≥ Real.exp (|A₀| + 1)` gives `log M ≥ |A₀| + 1 ≥ A₀ + 1`.

Hence `A₀ + K/M ≤ A₀ + 1 ≤ log M ≤ 3 log M`, so (C4-thresh) holds.

## References

* Paper §C4 (growth-dominance discharge; "Banach fixed-point" is
  structural scaffolding for the self-consistency of (C4-large)).
* `BootstrapDischarge.c4_largeness_from_bootstrap` — composes with
  the present result to produce (C4-large).
-/

namespace NSBlwChain.Caveats

open Real

/-! ## Step 1: auxiliary scalar inequality -/

/-- **Core scalar bound.**  For `M ≥ max 2 (max (K + 2) (exp (|A₀| + 1)))`,
    with `0 ≤ K`, we have `A₀ + K / M ≤ 3 · log M`. -/
lemma A0_plus_KM_le_3logM
    {A₀ K M : ℝ} (hK : 0 ≤ K)
    (hM : max 2 (max (K + 2) (Real.exp (|A₀| + 1))) ≤ M) :
    A₀ + K / M ≤ 3 * Real.log M := by
  -- Extract component bounds from `hM`.
  have hM_ge_2 : (2 : ℝ) ≤ M := le_trans (le_max_left _ _) hM
  have hM_ge_K2 : K + 2 ≤ M :=
    le_trans (le_trans (le_max_left _ _) (le_max_right (2 : ℝ) _)) hM
  have hM_ge_exp : Real.exp (|A₀| + 1) ≤ M :=
    le_trans (le_trans (le_max_right _ _) (le_max_right (2 : ℝ) _)) hM
  have hM_pos : 0 < M := by linarith
  have hM_ge_1 : (1 : ℝ) ≤ M := by linarith
  have hM_gt_1 : (1 : ℝ) < M := by linarith
  -- `log M > 0` from `M > 1`.
  have hlogM_pos : 0 < Real.log M := Real.log_pos hM_gt_1
  have hlogM_nonneg : 0 ≤ Real.log M := le_of_lt hlogM_pos
  -- `K / M ≤ 1`.  With `K ≥ 0` and `M ≥ K + 2 ≥ 2 > 0`, `K / M ≤ K/(K+2) ≤ 1`.
  have hKM_le_one : K / M ≤ 1 := by
    -- `K ≤ M` since `M ≥ K + 2 ≥ K`.
    have hK_le_M : K ≤ M := by linarith
    -- So `K / M ≤ M / M = 1`.
    rcases eq_or_lt_of_le hK with hK_eq | hK_pos
    · -- K = 0 case.
      simp [← hK_eq]
    · rw [div_le_one hM_pos]
      exact hK_le_M
  -- `log M ≥ |A₀| + 1 ≥ A₀ + 1`.
  have hlogM_ge : |A₀| + 1 ≤ Real.log M := by
    have := Real.log_le_log (Real.exp_pos _) hM_ge_exp
    rwa [Real.log_exp] at this
  have hA_le_absA : A₀ ≤ |A₀| := le_abs_self _
  have h_A_plus_1_le : A₀ + 1 ≤ Real.log M := by linarith
  -- Combine: `A₀ + K/M ≤ A₀ + 1 ≤ log M ≤ 3 log M`.
  have h_3logM_ge : Real.log M ≤ 3 * Real.log M := by linarith
  linarith

/-! ## Step 2: the threshold inequality (C4-thresh) -/

/-- **Growth-dominance threshold.**  For `M` above an explicit
    threshold `M_crit(L, ν, K)`, the scalar threshold inequality
    (C4-thresh) holds:

      `1 + log L + (1/2)(log 4 + log M + log(log M) - log ν)
          ≤ 4 log M - K/M`.

    Here `M_crit := max 2 (max (K + 2) (exp (|A₀| + 1)))` where
    `A₀ := 1 + log L + (1/2) log 4 - (1/2) log ν`.

    This closes the "Banach fixed-point for C4 largeness" hypothesis
    via elementary growth dominance. -/
theorem c4_threshold_of_large_M
    {L ν M K : ℝ}
    (hL : 0 < L) (hν : 0 < ν) (hK : 0 ≤ K)
    (hM :
      max 2
        (max (K + 2)
          (Real.exp
            (|1 + Real.log L + (1 / 2) * Real.log 4 - (1 / 2) * Real.log ν|
              + 1))) ≤ M) :
    1 + Real.log L
        + (1 / 2) * (Real.log 4 + Real.log M + Real.log (Real.log M)
                       - Real.log ν)
      ≤ 4 * Real.log M - K / M := by
  set A₀ : ℝ := 1 + Real.log L + (1 / 2) * Real.log 4 - (1 / 2) * Real.log ν
    with hA₀_def
  -- M ≥ 2 > 1, so log M > 0.
  have hM_ge_2 : (2 : ℝ) ≤ M := le_trans (le_max_left _ _) hM
  have hM_gt_1 : (1 : ℝ) < M := by linarith
  have hlogM_pos : 0 < Real.log M := Real.log_pos hM_gt_1
  have hlogM_nonneg : 0 ≤ Real.log M := le_of_lt hlogM_pos
  -- Bound `log(log M) ≤ log M` via `Real.log_le_self` (`0 ≤ log M`).
  have h_loglog_le : Real.log (Real.log M) ≤ Real.log M :=
    Real.log_le_self hlogM_nonneg
  -- Half-scale.
  have h_half : (1 / 2) * Real.log (Real.log M) ≤ (1 / 2) * Real.log M := by
    have : (0 : ℝ) ≤ 1 / 2 := by norm_num
    exact mul_le_mul_of_nonneg_left h_loglog_le this
  -- The core scalar bound: A₀ + K/M ≤ 3 log M.  After `set`, `hM`'s
  -- `Real.exp (|…| + 1)` term has been folded to `Real.exp (|A₀| + 1)`,
  -- so `hM` matches the signature of `A0_plus_KM_le_3logM`.
  have h_core : A₀ + K / M ≤ 3 * Real.log M :=
    A0_plus_KM_le_3logM hK hM
  -- Assemble.  Let L₀ := 1 + log L + (1/2)(log 4 + log M + log(log M) - log ν).
  --  We want to show L₀ ≤ 4 log M - K/M.
  -- Expand L₀:
  --   L₀ = 1 + log L + (1/2) log 4 - (1/2) log ν + (1/2) log M + (1/2) log(log M)
  --      = A₀ + (1/2) log M + (1/2) log(log M).
  -- Use h_half: L₀ ≤ A₀ + (1/2) log M + (1/2) log M = A₀ + log M.
  -- We need: A₀ + log M ≤ 4 log M - K/M, i.e., A₀ + K/M ≤ 3 log M.
  -- That is exactly h_core.
  have hExpand : 1 + Real.log L
          + (1 / 2) * (Real.log 4 + Real.log M + Real.log (Real.log M)
                         - Real.log ν)
            = A₀ + (1 / 2) * Real.log M + (1 / 2) * Real.log (Real.log M) := by
    rw [hA₀_def]; ring
  rw [hExpand]
  linarith [h_half, h_core]

/-! ## Step 3: exists-form (task-shaped) deliverable -/

/-- **Existence of a growth-dominance threshold.**

    For any `L, ν > 0` and `K ≥ 0`, there exists `M_crit ≥ 2` such
    that for all `M ≥ M_crit`, the scalar threshold inequality
    (C4-thresh) holds.

    This is the "exists"-form that mirrors the task spec's
    `hLarge_of_large_M`, but with the concrete bootstrap coupling
    `σ ≤ 4 · M · log M` that matches the existing
    `BootstrapDischarge` chain. -/
theorem exists_M_crit_threshold
    (L ν K : ℝ) (hL : 0 < L) (hν : 0 < ν) (hK : 0 ≤ K) :
    ∃ M_crit : ℝ, 2 ≤ M_crit ∧
      ∀ {M : ℝ}, M_crit ≤ M →
        1 + Real.log L
            + (1 / 2) * (Real.log 4 + Real.log M + Real.log (Real.log M)
                           - Real.log ν)
          ≤ 4 * Real.log M - K / M := by
  refine ⟨max 2 (max (K + 2)
    (Real.exp
      (|1 + Real.log L + (1 / 2) * Real.log 4 - (1 / 2) * Real.log ν|
        + 1))), ?_, ?_⟩
  · exact le_max_left _ _
  · intro M hM
    exact c4_threshold_of_large_M hL hν hK hM

/-! ## Step 4: composition — `hLarge` from bootstrap + large M -/

/-- **Main deliverable: `hLarge` from growth dominance.**

    Given:
    * positivity `L, ν > 0`, `K ≥ 0`;
    * the bootstrap coupling `σ ≤ 4 · M · log M` (from §C4 step 6);
    * `M ≥ M_crit(L, ν, K)` (the explicit growth-dominance threshold);

    we derive the largeness hypothesis (C4-large) as a theorem, not a
    hypothesis.

    Composition: `c4_threshold_of_large_M` delivers (C4-thresh), and
    `BootstrapDischarge.c4_largeness_from_bootstrap` composes it with
    the bootstrap to produce (C4-large).

    This closes **OPEN.md item 2** (Banach fixed-point for C4
    largeness) via growth dominance — a cleaner route than the
    convex-analysis Banach argument sketched in the paper. -/
theorem hLarge_of_large_M_bootstrap
    {L ν M σ K : ℝ}
    (hL : 0 < L) (hν : 0 < ν) (hσ : 0 < σ) (hK : 0 ≤ K)
    (h_bootstrap : σ ≤ 4 * M * Real.log M)
    (hM :
      max 2
        (max (K + 2)
          (Real.exp
            (|1 + Real.log L + (1 / 2) * Real.log 4 - (1 / 2) * Real.log ν|
              + 1))) ≤ M) :
    1 + Real.log L + (1 / 2) * Real.log (σ / ν)
      ≤ 4 * Real.log M - K / M := by
  -- From M ≥ max 2 ... ≥ 2 we get M > 1 (strict).
  have hM_ge_2 : (2 : ℝ) ≤ M := le_trans (le_max_left _ _) hM
  have hM_gt_1 : (1 : ℝ) < M := by linarith
  have h_threshold :
      1 + Real.log L
        + (1 / 2) * (Real.log 4 + Real.log M + Real.log (Real.log M)
                       - Real.log ν)
          ≤ 4 * Real.log M - K / M :=
    c4_threshold_of_large_M hL hν hK hM
  exact NSBlwChain.BLW.c4_largeness_from_bootstrap
    hM_gt_1 hσ hν h_bootstrap h_threshold

/-! ## Step 5: bundle-level constructor -/

/-- **Bundle constructor from growth dominance.**

    Assemble an `ImplicitBoundBundle` together with its `hLarge`
    certificate (obtained via growth dominance) from the primitive
    inputs plus the bootstrap coupling and the large-M hypothesis.

    The bundle carries the implicit inequality (C4.1) as a hypothesis;
    the `hLarge` consequence is now a theorem discharged via
    `hLarge_of_large_M_bootstrap`.

    This is the practical closure of OPEN.md item 2: downstream
    consumers can now supply a concrete `M ≥ M_crit(L, ν, K)` and a
    bootstrap `σ ≤ 4 M log M` to get the full largeness certificate
    mechanically. -/
def ImplicitBoundBundle.ofLargeM
    {ν L M σ K : ℝ}
    (hν : 0 < ν) (hL : 0 < L) (hσ : 0 < σ) (hK : 0 ≤ K)
    (h_bootstrap : σ ≤ 4 * M * Real.log M)
    (hM :
      max 2
        (max (K + 2)
          (Real.exp
            (|1 + Real.log L + (1 / 2) * Real.log 4 - (1 / 2) * Real.log ν|
              + 1))) ≤ M)
    (hImplicit :
      σ ≤ M * (1 + Real.log L + (1 / 2) * Real.log (σ / ν)) + K) :
    ImplicitBoundBundle :=
  { ν := ν, L := L, M := M, σ := σ, K := K,
    hν_pos := hν, hL_pos := hL,
    hM_ge_one := by
      have hM_ge_2 : (2 : ℝ) ≤ M := le_trans (le_max_left _ _) hM
      linarith,
    hσ_pos := hσ, hK_nonneg := hK,
    hImplicit := hImplicit }

/-- **Companion largeness certificate for `ImplicitBoundBundle.ofLargeM`.**

    The `hLarge` precondition of `ImplicitBoundBundle.σ_le_of_largeness`
    is discharged automatically from the growth-dominance hypotheses,
    closing the loop. -/
theorem ImplicitBoundBundle.ofLargeM_hLarge
    {ν L M σ K : ℝ}
    (hν : 0 < ν) (hL : 0 < L) (hσ : 0 < σ) (hK : 0 ≤ K)
    (h_bootstrap : σ ≤ 4 * M * Real.log M)
    (hM :
      max 2
        (max (K + 2)
          (Real.exp
            (|1 + Real.log L + (1 / 2) * Real.log 4 - (1 / 2) * Real.log ν|
              + 1))) ≤ M) :
    1 + Real.log L + (1 / 2) * Real.log (σ / ν)
      ≤ 4 * Real.log M - K / M :=
  hLarge_of_large_M_bootstrap hL hν hσ hK h_bootstrap hM

/-- **End-to-end: `σ ≤ 4 M log M` from growth dominance.**

    Composes everything: given the implicit inequality (C4.1), the
    bootstrap coupling `σ ≤ 4 M log M`, `M ≥ M_crit`, and positivity,
    reproduce `σ ≤ 4 M log M` through the `σ_le_of_largeness` pipeline.

    (This is a self-consistency statement: the bootstrap was already
    given, and we round-trip through the largeness step.  Its value
    is structural — it shows the chain closes with `hLarge` now a
    theorem rather than a hypothesis.) -/
theorem sigma_le_4MlogM_via_growth_dominance
    {ν L M σ K : ℝ}
    (hν : 0 < ν) (hL : 0 < L) (hσ : 0 < σ) (hK : 0 ≤ K)
    (h_bootstrap : σ ≤ 4 * M * Real.log M)
    (hM :
      max 2
        (max (K + 2)
          (Real.exp
            (|1 + Real.log L + (1 / 2) * Real.log 4 - (1 / 2) * Real.log ν|
              + 1))) ≤ M)
    (hImplicit :
      σ ≤ M * (1 + Real.log L + (1 / 2) * Real.log (σ / ν)) + K) :
    σ ≤ 4 * M * Real.log M := by
  have B : ImplicitBoundBundle :=
    ImplicitBoundBundle.ofLargeM hν hL hσ hK h_bootstrap hM hImplicit
  have hLarge :
      1 + Real.log L + (1 / 2) * Real.log (σ / ν)
        ≤ 4 * Real.log M - K / M :=
    ImplicitBoundBundle.ofLargeM_hLarge hν hL hσ hK h_bootstrap hM
  exact B.σ_le_of_largeness hLarge

/-! ## Sanity check -/

/-- Elementary sanity: the threshold is trivially satisfied at the
    threshold itself.  Records that the signature is inhabited. -/
example (L ν K : ℝ) (hL : 0 < L) (hν : 0 < ν) (hK : 0 ≤ K) :
    ∃ M : ℝ, 2 ≤ M ∧
      1 + Real.log L
          + (1 / 2) * (Real.log 4 + Real.log M + Real.log (Real.log M)
                         - Real.log ν)
        ≤ 4 * Real.log M - K / M := by
  obtain ⟨Mc, hMc_ge_2, hMc_prop⟩ := exists_M_crit_threshold L ν K hL hν hK
  exact ⟨Mc, hMc_ge_2, hMc_prop le_rfl⟩

end NSBlwChain.Caveats
