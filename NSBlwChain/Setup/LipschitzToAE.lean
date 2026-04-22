-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib

/-!
# Lipschitz → differentiable a.e. (stub)

This file will package Rademacher's theorem (Lipschitz functions on
$\mathbb{R}$ are Fréchet differentiable a.e.) in a form convenient
for the BLW-gradient ODE argument in `Caveats/C2_Envelope.lean` and
`BLW/LogAbsorption.lean`.

Currently this is a *stub*: the Rademacher-form lemma
`ae_hasDerivAt_of_lipschitz` hit a typeclass-resolution issue under
mathlib 4.29.0 when stated with an unqualified `LipschitzWith` over
`ℝ → ℝ`.  The downstream consumer (`Caveats/C2_AeOde.lean`, planned)
can state the Rademacher conclusion as a *hypothesis* on `M` and
defer the discharge to a later pass.

The single lemma below is a trivial finiteness sanity-check, useful
only to confirm the file compiles against the current mathlib.

## Reference

* Evans–Gariepy, *Measure Theory and Fine Properties of Functions*,
  Theorem 3.2 (Rademacher).
-/

namespace NSBlwChain.Setup

/-- Boilerplate: a Lipschitz constant is finite, so `K < ∞` as an
    `ENNReal` (= `ℝ≥0∞`).  Trivial, but recurs enough to be named. -/
lemma lipschitzWith_edist_lt_top
    {α β : Type*} [PseudoEMetricSpace α] [PseudoEMetricSpace β]
    {K : NNReal} {f : α → β} (_ : LipschitzWith K f) :
    (K : ENNReal) < ⊤ := ENNReal.coe_lt_top

end NSBlwChain.Setup
