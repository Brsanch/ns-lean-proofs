-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib

/-!
# Chain rule for `(M t)² / 2`

Small calculus helper.  For `M : ℝ → ℝ` differentiable at `t`:

  `d/dt [(M(t))² / 2] = M(t) · dM/dt(t)`.

Used by `BLW/EnvelopeIdentity.lean` to connect `M² / 2`'s derivative
to the product `M · Ṁ`.

## Contents

* `hasDerivAt_sqHalf_of_hasDerivAt` — from `HasDerivAt M m t`, derive
  `HasDerivAt (fun τ => (M τ)² / 2) (M t · m) t`.

* `deriv_sqHalf_eq` — the `deriv` version.
-/

namespace NSBlwChain.BLW

/-- Chain rule: if `HasDerivAt M m t`, then
    `HasDerivAt (fun τ => (M τ)² / 2) (M t * m) t`. -/
theorem hasDerivAt_sqHalf_of_hasDerivAt
    {M : ℝ → ℝ} {m t : ℝ} (hM : HasDerivAt M m t) :
    HasDerivAt (fun τ : ℝ => (M τ) ^ 2 / 2) (M t * m) t := by
  have h_sq : HasDerivAt (fun τ : ℝ => (M τ) ^ 2) (2 * M t * m) t := by
    have := hM.pow 2
    simpa [pow_two, two_mul, mul_comm, mul_assoc] using this
  have h_div : HasDerivAt (fun τ : ℝ => (M τ) ^ 2 / 2) ((2 * M t * m) / 2) t :=
    h_sq.div_const 2
  have h_eq : (2 * M t * m) / 2 = M t * m := by ring
  rw [h_eq] at h_div
  exact h_div

/-- `deriv` form of the chain rule for `(M τ)² / 2`. -/
theorem deriv_sqHalf_eq
    {M : ℝ → ℝ} {t : ℝ} (hM : DifferentiableAt ℝ M t) :
    deriv (fun τ : ℝ => (M τ) ^ 2 / 2) t = M t * deriv M t :=
  (hasDerivAt_sqHalf_of_hasDerivAt hM.hasDerivAt).deriv

end NSBlwChain.BLW
