-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib

set_option diagnostics true
set_option diagnostics.threshold 100

/-!
# Running supremum on `[0, t]` (real-valued)

Provides a clean wrapper

  `runningSupOn f t := sSup (f '' Set.Icc 0 t)`

with the two structural facts the Theorem 1 chain consumes for the
`M : ℝ → ℝ` field of `EnstrophyCrossoverBundle`:

1. **Monotonicity in `t`** — running supremum is non-decreasing.
2. **Pointwise ≥ `f`** — `f t ≤ runningSupOn f t` whenever `t ∈ [0, T]`.

These are the only two algebraic properties of `M_mono` and a
companion `M_ge_f` that downstream consumers need; the boundedness /
nonneg / `M_nonneg` properties follow from positivity of `f`.

Self-contained mathlib-backed lemmas; no NS-specific content.

## Main results

* `runningSupOn`         — the running-sup function.
* `runningSupOn_mono`    — non-decreasing.
* `runningSupOn_ge_self` — `f t ≤ runningSupOn f T` for `t ∈ [0, T]`.
* `runningSupOn_nonneg`  — `0 ≤ runningSupOn f t` when `f` is
                            non-negative on `[0, t]`.
-/

namespace NSBlwChain.Unconditional

open Set

/-- **Running supremum of `f : ℝ → ℝ` over `[0, t]`.** -/
noncomputable def runningSupOn (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  sSup (f '' Icc 0 t)

/-- **Running supremum is non-decreasing in `t`.**

    For `0 ≤ s ≤ t`, the image set is monotone in containment, so
    `sSup` is too. -/
theorem runningSupOn_mono
    (f : ℝ → ℝ)
    (hf_bdd : ∀ T : ℝ, BddAbove (f '' Icc 0 T))
    {s t : ℝ} (hs_nn : 0 ≤ s) (hst : s ≤ t) :
    runningSupOn f s ≤ runningSupOn f t := by
  unfold runningSupOn
  have hsubset : f '' Icc 0 s ⊆ f '' Icc 0 t :=
    Set.image_mono (Icc_subset_Icc le_rfl hst)
  -- `f '' Icc 0 s` is non-empty (contains `f 0`) and bounded above.
  have hne : (f '' Icc 0 s).Nonempty :=
    ⟨f 0, mem_image_of_mem f ⟨le_rfl, hs_nn⟩⟩
  have hbdd_t : BddAbove (f '' Icc 0 t) := hf_bdd t
  exact csSup_le_csSup hbdd_t hne hsubset

/-- **`f t ≤ runningSupOn f T`** for `t ∈ [0, T]`. -/
theorem runningSupOn_ge_self
    (f : ℝ → ℝ)
    (hf_bdd : ∀ T : ℝ, BddAbove (f '' Icc 0 T))
    {T t : ℝ} (ht_nn : 0 ≤ t) (htT : t ≤ T) :
    f t ≤ runningSupOn f T := by
  unfold runningSupOn
  have hmem : f t ∈ f '' Icc 0 T :=
    mem_image_of_mem f ⟨ht_nn, htT⟩
  exact le_csSup (hf_bdd T) hmem

/-- **`runningSupOn` is non-negative when `f` is non-negative on `[0, t]`.** -/
theorem runningSupOn_nonneg
    (f : ℝ → ℝ)
    (hf_bdd : ∀ T : ℝ, BddAbove (f '' Icc 0 T))
    (hf_nn : ∀ s : ℝ, 0 ≤ s → 0 ≤ f s)
    {t : ℝ} (ht_nn : 0 ≤ t) :
    0 ≤ runningSupOn f t := by
  -- `f 0 ≤ runningSupOn f t` and `0 ≤ f 0`.
  have h_f0_le : f 0 ≤ runningSupOn f t :=
    runningSupOn_ge_self f hf_bdd le_rfl ht_nn
  have h_f0_nn : 0 ≤ f 0 := hf_nn 0 le_rfl
  linarith

end NSBlwChain.Unconditional
