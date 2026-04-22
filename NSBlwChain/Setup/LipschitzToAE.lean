-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib

/-!
# Lipschitz → differentiable a.e.

This file packages Rademacher's theorem as a thin wrapper adapted to
the `LipschitzWith` / `LipschitzOnWith` interface of mathlib, and the
specific one-variable form consumed by the BLW-gradient ODE argument
in `Caveats/C2_Envelope.lean` and `BLW/LogAbsorption.lean`.

## Scope

The full Rademacher theorem (Lipschitz functions on `ℝⁿ` are Fréchet
differentiable a.e.) is in mathlib as
`LipschitzWith.ae_differentiableAt` for the Euclidean case.  For the
BLW-gradient chain we need only the one-dimensional specialization:

* A Lipschitz function `M : ℝ → ℝ` is differentiable at a.e. `t`.
* At every differentiability point, `HasDerivAt M (deriv M t) t` holds.

The wrappers below re-export these facts in forms convenient for
downstream use without introducing new notation.

## Reference

* Evans–Gariepy, *Measure Theory and Fine Properties of Functions*,
  Theorem 3.2 (Rademacher).
-/

namespace NSBlwChain.Setup

open Filter MeasureTheory
open scoped Topology

/-- **Rademacher (one-dimensional form).**

    A Lipschitz function `M : ℝ → ℝ` is differentiable at almost every
    point `t ∈ ℝ` (with respect to Lebesgue measure).  In particular,
    `HasDerivAt M (deriv M t) t` holds for a.e. `t`. -/
lemma ae_hasDerivAt_of_lipschitz
    {K : NNReal} {M : ℝ → ℝ} (hM : LipschitzWith K M) :
    ∀ᵐ t : ℝ, HasDerivAt M (deriv M t) t := by
  -- mathlib: `LipschitzWith.ae_differentiableAt` gives `DifferentiableAt ℝ M t`
  -- a.e., which packages into `HasDerivAt M (deriv M t) t`.
  have h := hM.ae_differentiableAt
  filter_upwards [h] with t ht
  exact ht.hasDerivAt

/-- Boilerplate: a Lipschitz constant is finite, so `K < ∞` as an
    `ℝ≥0∞`.  This is trivial but recurs enough that we name it. -/
lemma lipschitzWith_edist_lt_top
    {K : NNReal} {M : ℝ → ℝ} (_ : LipschitzWith K M) :
    (K : ℝ≥0∞) < ⊤ := ENNReal.coe_lt_top

end NSBlwChain.Setup
