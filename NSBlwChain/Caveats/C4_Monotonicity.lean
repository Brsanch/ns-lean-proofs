-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Caveats.C4_ImplicitBound

/-!
# Caveat C4 — Monotonicity of the largeness hypothesis

This file records two **scalar monotonicity observations** about the
largeness hypothesis

  `(C4-large)   1 + log L + (1/2) log(σ/ν) ≤ 4 log M - K/M`

that powers the convexity / Banach fixed-point step of Proposition C4
(see `C4_ImplicitBound.lean` for the main hypothesis-consumer result).

## Mathematical content

### 1. Monotonicity in `σ`

Because `(1/2) log(·/ν)` is monotone increasing in its argument, the
left-hand side of (C4-large) is monotone in `σ`.  Consequently, if
(C4-large) holds at `σ = σ₂`, it also holds at any `σ₁` with
`0 < σ₁ ≤ σ₂`.  In plain words: *smaller `σ` satisfies the same
largeness hypothesis with room to spare.*

### 2. Bootstrapping from the concluded form

Suppose we already know `σ ≤ 4 M log M` (the conclusion of
Proposition C4).  Then (C4-large) at the implicit `σ` is implied by
the stronger scalar inequality

  `(C4-large⋆)   1 + log L + (1/2) log(4 M log M / ν) ≤ 4 log M - K/M`

purely by monotonicity in `σ`.  Thus the entire largeness hypothesis
reduces to a scalar check on `(L, ν, M, K)` alone — no knowledge of
`σ` beyond the given bound is needed.

### 3. Explicit threshold

When `M ≥ M_0(L, ν, K)` for a suitable threshold, (C4-large⋆) holds
and therefore so does (C4-large).  A full explicit formula for
`M_0` is cumbersome (the inequality is implicit in `log M`); we
record the hypothesis-consumer form, matching the style of the
other §C4 lemmas.

## What this file contains

* `largeness_monotone_in_sigma` — (1) above, monotonicity in `σ`.
* `largeness_of_sigma_upper_bound` — (2) above, reduction of
  (C4-large) at implicit `σ` to the scalar (C4-large⋆) using
  `σ ≤ 4 M log M`.
* `c4_largeness_of_threshold` — (3) above, hypothesis-consumer form:
  given (C4-large⋆) and `σ ≤ 4 M log M`, conclude (C4-large).

The Banach fixed-point argument itself is **not** reproved here; that
is the content of §C4 of the companion note.  These lemmas record the
trivial scalar plumbing around it.

## References

* Companion paper §C4, largeness hypothesis and Banach fixed-point.
* `C4_ImplicitBound.lean` for `σ_le_of_largeness` (the algebraic step).
-/

namespace NSBlwChain.Caveats

open Real

/-! ## Core monotonicity lemma -/

/-- **Monotonicity of the largeness hypothesis in `σ`.**

    The left-hand side of (C4-large),
    `1 + log L + (1/2) log(σ/ν)`, is monotone increasing in `σ`
    (for `σ > 0`, `ν > 0`).  Therefore if the largeness hypothesis
    holds at some `σ₂ > 0`, it also holds at any `σ₁` with
    `0 < σ₁ ≤ σ₂`.

    This is useful in the Banach fixed-point argument: the largest
    fixed point dominates all smaller candidates. -/
theorem largeness_monotone_in_sigma
    {ν L M K σ₁ σ₂ : ℝ}
    (hν_pos : 0 < ν)
    (hσ₁_pos : 0 < σ₁)
    (hσ₁_le_σ₂ : σ₁ ≤ σ₂)
    (hLarge₂ :
      1 + Real.log L + (1/2) * Real.log (σ₂ / ν)
        ≤ 4 * Real.log M - K / M) :
    1 + Real.log L + (1/2) * Real.log (σ₁ / ν)
      ≤ 4 * Real.log M - K / M := by
  have hσ₂_pos : 0 < σ₂ := lt_of_lt_of_le hσ₁_pos hσ₁_le_σ₂
  -- Monotonicity of division by ν > 0.
  have hdiv_le : σ₁ / ν ≤ σ₂ / ν := by
    have : 0 < ν⁻¹ := inv_pos.mpr hν_pos
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hσ₁_le_σ₂ (le_of_lt this)
  -- Positivity of σ₁/ν.
  have hσ₁ν_pos : 0 < σ₁ / ν := div_pos hσ₁_pos hν_pos
  -- Monotonicity of log on positives.
  have hlog_le : Real.log (σ₁ / ν) ≤ Real.log (σ₂ / ν) :=
    Real.log_le_log hσ₁ν_pos hdiv_le
  -- Scale by 1/2 ≥ 0 and add `1 + log L` on both sides.
  have hhalf_le : (1/2) * Real.log (σ₁ / ν) ≤ (1/2) * Real.log (σ₂ / ν) :=
    mul_le_mul_of_nonneg_left hlog_le (by norm_num)
  linarith

/-! ## Bootstrapping from the concluded form -/

/-- **Reduction of (C4-large) at implicit `σ` to the scalar
    (C4-large⋆) using `σ ≤ 4 M log M`.**

    Given `σ ≤ 4 M log M` (the concluded form of Proposition C4)
    and the scalar inequality `(C4-large⋆)` in the variables
    `(L, ν, M, K)` alone, we conclude (C4-large) at the original
    `σ`.  No other information about `σ` is used.

    Combined with the hypothesis-consumer theorem
    `σ_le_of_largeness` from `C4_ImplicitBound`, this shows the
    Banach fixed-point circle closes: the implicit `σ` is bounded
    by `4 M log M` iff the scalar (C4-large⋆) holds.

    **Note.** This lemma assumes the `σ ≤ 4 M log M` bound as a
    hypothesis (so-called "bootstrapping form"); the Banach argument
    itself is what turns (C4-large⋆) into the actual bound.  Here we
    only record the monotone-reduction half. -/
theorem largeness_of_sigma_upper_bound
    {ν L M K σ : ℝ}
    (hν_pos : 0 < ν)
    (hσ_pos : 0 < σ)
    (hσ_le : σ ≤ 4 * M * Real.log M)
    (hStar :
      1 + Real.log L + (1/2) * Real.log (4 * M * Real.log M / ν)
        ≤ 4 * Real.log M - K / M) :
    1 + Real.log L + (1/2) * Real.log (σ / ν)
      ≤ 4 * Real.log M - K / M :=
  largeness_monotone_in_sigma hν_pos hσ_pos hσ_le hStar

/-! ## Explicit-threshold form (hypothesis-consumer) -/

/-- **`c4_largeness_of_threshold` — hypothesis-consumer form of
    Proposition C4 under an explicit scalar threshold.**

    Given:
    * the concluded bound `σ ≤ 4 M log M`;
    * the scalar largeness hypothesis `(C4-large⋆)` in `(L, ν, M, K)`;

    we produce the largeness hypothesis `(C4-large)` at the implicit
    `σ`, which is the input expected by
    `ImplicitBoundBundle.σ_le_of_largeness`.

    In downstream use, a consumer supplies a threshold `M_0` (as a
    hypothesis) and a proof that `M ≥ M_0` implies `(C4-large⋆)`.
    This file does not attempt to derive `M_0` explicitly from
    `(L, ν, K)` — the inequality is implicit in `log M`, and an
    explicit symbolic threshold requires `Real.log` inversion
    machinery that does not simplify cleanly at this stage.

    The shape here matches the existing `σ_le_of_largeness` style: a
    named scalar inequality is consumed, and the implicit bound is
    produced. -/
theorem c4_largeness_of_threshold
    {ν L M K σ : ℝ}
    (hν_pos : 0 < ν)
    (hσ_pos : 0 < σ)
    (hσ_le : σ ≤ 4 * M * Real.log M)
    (hScalar :
      1 + Real.log L + (1/2) * Real.log (4 * M * Real.log M / ν)
        ≤ 4 * Real.log M - K / M) :
    1 + Real.log L + (1/2) * Real.log (σ / ν)
      ≤ 4 * Real.log M - K / M :=
  largeness_of_sigma_upper_bound hν_pos hσ_pos hσ_le hScalar

/-! ## Packaging against `ImplicitBoundBundle` -/

/-- **Closed-loop form, on the bundle.**

    Starting from an `ImplicitBoundBundle` (so the implicit
    inequality (C4.1) and positivity of `σ, ν` hold) plus:
    * a prior bound `σ ≤ 4 M log M` (bootstrap hypothesis);
    * the scalar largeness hypothesis (C4-large⋆);

    we recover the original `σ ≤ 4 M log M` via
    `ImplicitBoundBundle.σ_le_of_largeness`.  The loop closes: the
    bootstrap hypothesis is reproduced exactly.

    This is essentially a self-consistency tautology at the algebraic
    level — it does **not** replace the Banach fixed-point argument.
    It documents that, given the Banach bound, the scalar (C4-large⋆)
    is the *only* input needed to the bundle-level consumer. -/
theorem ImplicitBoundBundle.σ_le_of_scalar_largeness
    (B : ImplicitBoundBundle)
    (hσ_le : B.σ ≤ 4 * B.M * Real.log B.M)
    (hScalar :
      1 + Real.log B.L
          + (1/2) * Real.log (4 * B.M * Real.log B.M / B.ν)
        ≤ 4 * Real.log B.M - B.K / B.M) :
    B.σ ≤ 4 * B.M * Real.log B.M := by
  -- Upgrade the scalar hypothesis to the full largeness hypothesis
  -- at the implicit σ, via monotonicity.
  have hLarge :
      1 + Real.log B.L + (1/2) * Real.log (B.σ / B.ν)
        ≤ 4 * Real.log B.M - B.K / B.M :=
    c4_largeness_of_threshold B.hν_pos B.hσ_pos hσ_le hScalar
  -- Feed into the standard C4 bundle consumer.
  exact B.σ_le_of_largeness hLarge

/-! ## Sanity check

A trivial existence: the monotonicity lemma applied to `σ₁ = σ₂` is
the identity on the hypothesis.  Records that the signature is
inhabited for the degenerate diagonal. -/

example
    {ν L M K σ : ℝ}
    (hν_pos : 0 < ν) (hσ_pos : 0 < σ)
    (h :
      1 + Real.log L + (1/2) * Real.log (σ / ν)
        ≤ 4 * Real.log M - K / M) :
    1 + Real.log L + (1/2) * Real.log (σ / ν)
      ≤ 4 * Real.log M - K / M :=
  largeness_monotone_in_sigma hν_pos hσ_pos (le_refl σ) h

end NSBlwChain.Caveats
