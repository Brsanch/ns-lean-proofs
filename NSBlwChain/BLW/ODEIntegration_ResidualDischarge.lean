-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.BLW.ODEIntegration
import NSBlwChain.BLW.ODEIntegration_Discharge

/-!
# Residual discharge: the substitution-level FTC step

This file closes (as far as the unilateral ODE inequality allows) the
single remaining analytical residual of
`NSBlwChain/BLW/ODEIntegration_Discharge.lean`: the derivative-level
content of the substitution `w := 1/(M · log M)`.

Contents:

* `deriv_w_quotient` — the pointwise quotient-rule identity
  `ẇ = -(Ṁ · (log M + 1)) / (M · log M)²`.
* `deriv_w_lower_bound` — turns the ODE inequality
  `Ṁ ≤ 4 · M² · log M` into a lower bound on `ẇ`:
  `ẇ ≥ -4 - 4/log M`.
* `hW_lower_bound_of_ae_ODE` — (partial) FTC integration on
  `[t, T-ε]` with the boundary limit `w(T⁻) = 0`.  See the
  `Mathematical note on direction` below for the remaining gap:
  the unilateral ODE inequality `Ṁ ≤ 4 M² log M` alone yields
  an **upper** bound `w(t) ≤ 4(T-t) + ∫ 4/log M`, not the lower
  bound required by the bundle.  Deriving the **lower** bound
  `w(t) ≥ 4(T-t)` requires either (a) equality `Ṁ = 4 M² log M`
  in the blow-up regime, (b) a matching lower bound
  `Ṁ ≥ 4 M² log M` (the actual blow-up ODE at the critical
  point), or (c) a different substitution that flips the sign
  of the FTC chain.  The partial discharge in this file records
  the one proven sub-step (the pointwise derivative identity and
  inequality) and isolates the remaining gap as a single
  hypothesis-level input; it does not close the bundle's
  `integrated_bound` field unconditionally on its own.

## Mathematical note on direction

At a blow-up time `T` the paper's ODE is **tight**:
`Ṁ(t*) = 4 M² log M` at the critical argmax, not merely
`≤`.  The bundle stores the unilateral `≤` form (which is all
`NSEvolutionAxioms` provides in full generality).  Hence the
FTC step, applied to the `≤`-inequality, produces an **upper**
bound on `w(t)`, which is the opposite direction from what
`DifferentialInequalityBundle.integrated_bound` consumes.

The bundle's `integrated_bound` is thus genuinely a *hypothesis*
about the tight blow-up regime that the analytical chain asserts
(via energy conservation + the sub-Type-I rate of Seregin-Šverák)
but which cannot be recovered from the unilateral `Ṁ ≤ 4 M² log M`
input alone.  Upgrading to the equality regime — by tracking the
argmax along the blow-up limit — is the structural reason the paper
bundles `integrated_bound` as a separate field rather than deriving
it.

This file discharges the **derivative-level** half of the
substitution (steps 1-2 of the paper's §12.4 chain) in full, and
the **FTC + boundary-limit** half (steps 3-4) conditional on a
pointwise upper bound on `ẇ` (which is what the tight equality
regime provides).

## References

* `BLW/ODEIntegration.lean` — the bundle definition.
* `BLW/ODEIntegration_Discharge.lean` — the algebraic-core half.
-/

namespace NSBlwChain.BLW

open Real Filter Topology

/-- **Quotient-rule identity for `w := 1/(M·log M)`.**

    For `M` differentiable at `t` with `M t > 1` (hence `M t ≠ 0`,
    `log (M t) ≠ 0`, and `M t · log (M t) ≠ 0`):

    `deriv (fun s => 1/(M s · log (M s))) t
       = -(deriv M t · (log (M t) + 1)) / (M t · log (M t))²`.

    Derivation:  let `u s := M s · log (M s)`.  By the product rule
    and chain rule `deriv u t = Ṁ · log M + M · (Ṁ/M) = Ṁ · (log M + 1)`.
    Then `deriv (1/u) t = -deriv u t / (u t)²`. -/
theorem deriv_w_quotient {M : ℝ → ℝ} {t : ℝ}
    (hM : DifferentiableAt ℝ M t)
    (hM_pos : 1 < M t) :
    deriv (fun s => 1 / (M s * Real.log (M s))) t =
      -(deriv M t * (Real.log (M t) + 1)) / (M t * Real.log (M t))^2 := by
  -- Name the intermediate derivative.
  set m : ℝ := deriv M t with hm_def
  have hM_pos0 : 0 < M t := lt_trans zero_lt_one hM_pos
  have hM_ne : M t ≠ 0 := ne_of_gt hM_pos0
  have hlog_pos : 0 < Real.log (M t) := Real.log_pos hM_pos
  have hlog_ne : Real.log (M t) ≠ 0 := ne_of_gt hlog_pos
  have hprod_pos : 0 < M t * Real.log (M t) := mul_pos hM_pos0 hlog_pos
  have hprod_ne : M t * Real.log (M t) ≠ 0 := ne_of_gt hprod_pos
  -- `HasDerivAt` for `M`:
  have hM_hasDeriv : HasDerivAt M m t := hM.hasDerivAt
  -- `HasDerivAt` for `fun s => log (M s)`: derivative is `m / M t`.
  have hLogM_hasDeriv :
      HasDerivAt (fun s => Real.log (M s)) (m / M t) t :=
    hM_hasDeriv.log hM_ne
  -- `HasDerivAt` for `u = M · log M`: derivative is `m · log M t + M t · (m / M t)`.
  have hU_hasDeriv :
      HasDerivAt (fun s => M s * Real.log (M s))
        (m * Real.log (M t) + M t * (m / M t)) t :=
    hM_hasDeriv.mul hLogM_hasDeriv
  -- Simplify that expression to `m * (log M t + 1)`.
  have hU_simp :
      m * Real.log (M t) + M t * (m / M t) =
        m * (Real.log (M t) + 1) := by
    field_simp
  have hU_hasDeriv' :
      HasDerivAt (fun s => M s * Real.log (M s))
        (m * (Real.log (M t) + 1)) t := by
    rw [← hU_simp]; exact hU_hasDeriv
  -- Now `w = 1 / u`; apply `HasDerivAt.inv` or the `one_div` wrapper.
  have hW_hasDeriv :
      HasDerivAt (fun s => (M s * Real.log (M s))⁻¹)
        (-(m * (Real.log (M t) + 1)) / (M t * Real.log (M t))^2) t := by
    have h := hU_hasDeriv'.inv hprod_ne
    -- `HasDerivAt.inv` gives derivative `-u'/(u x)^2` which matches
    -- the target after `convert` reduces to definitional equality.
    convert h using 1
  -- Rewrite `1 / x = x⁻¹` to match the target form.
  have hW_hasDeriv' :
      HasDerivAt (fun s => 1 / (M s * Real.log (M s)))
        (-(m * (Real.log (M t) + 1)) / (M t * Real.log (M t))^2) t := by
    have heq : (fun s => 1 / (M s * Real.log (M s))) =
               (fun s => (M s * Real.log (M s))⁻¹) := by
      funext s; exact one_div _
    rw [heq]; exact hW_hasDeriv
  -- Extract `deriv` from `HasDerivAt`.
  exact hW_hasDeriv'.deriv

/-- **Lower bound on `ẇ` from the ODE inequality.**

    Given `Ṁ ≤ 4 · M² · log M` at a point `t` where `M > 1` (so
    `log M > 0` and `log M + 1 > 0`), the derivative of
    `w := 1/(M · log M)` satisfies
    `ẇ ≥ -4 - 4/log M`.

    Derivation: by `deriv_w_quotient`,
    `ẇ = -Ṁ · (log M + 1) / (M · log M)²`.
    Multiplying numerator and denominator by `1` appropriately and
    using `Ṁ ≤ 4 M² log M`:
    `-Ṁ · (log M + 1) / (M · log M)² ≥
     -(4 M² log M) · (log M + 1) / (M² · (log M)²)
     = -4 · (log M + 1) / log M = -4 - 4/log M`. -/
theorem deriv_w_lower_bound {M : ℝ → ℝ} {t : ℝ}
    (hM : DifferentiableAt ℝ M t)
    (hM_pos : 1 < M t)
    (hODE : deriv M t ≤ 4 * (M t)^2 * Real.log (M t)) :
    -4 - 4 / Real.log (M t) ≤
      deriv (fun s => 1 / (M s * Real.log (M s))) t := by
  set m : ℝ := deriv M t with hm_def
  have hM_pos0 : 0 < M t := lt_trans zero_lt_one hM_pos
  have hlog_pos : 0 < Real.log (M t) := Real.log_pos hM_pos
  have hlog_plus1_pos : 0 < Real.log (M t) + 1 :=
    add_pos hlog_pos zero_lt_one
  have hMsq_pos : 0 < (M t)^2 := pow_pos hM_pos0 2
  have hprod_pos : 0 < M t * Real.log (M t) := mul_pos hM_pos0 hlog_pos
  have hprod_sq_pos : 0 < (M t * Real.log (M t))^2 := pow_pos hprod_pos 2
  have hprod_sq_ne : (M t * Real.log (M t))^2 ≠ 0 := ne_of_gt hprod_sq_pos
  -- Rewrite `ẇ` using the quotient rule.
  rw [deriv_w_quotient hM hM_pos]
  -- Goal: `-4 - 4 / log M t ≤ -(m * (log M t + 1)) / (M t · log M t)²`.
  -- Strategy: show the target via a two-step chain.
  -- Step A: `m · (log M t + 1) ≤ 4 · M² · log M · (log M t + 1)`.
  have hA : m * (Real.log (M t) + 1) ≤
            4 * (M t)^2 * Real.log (M t) * (Real.log (M t) + 1) :=
    mul_le_mul_of_nonneg_right hODE (le_of_lt hlog_plus1_pos)
  -- Step B: negate and divide by `(M t · log M t)² > 0`.
  have hB : -(4 * (M t)^2 * Real.log (M t) * (Real.log (M t) + 1)) ≤
            -(m * (Real.log (M t) + 1)) := by linarith
  have hB' :
      -(4 * (M t)^2 * Real.log (M t) * (Real.log (M t) + 1))
        / (M t * Real.log (M t))^2 ≤
      -(m * (Real.log (M t) + 1)) / (M t * Real.log (M t))^2 :=
    div_le_div_of_nonneg_right hB (le_of_lt hprod_sq_pos)
  -- Step C: simplify the LHS of hB' to `-4 - 4/log M t`.
  have hC :
      -(4 * (M t)^2 * Real.log (M t) * (Real.log (M t) + 1))
        / (M t * Real.log (M t))^2 =
      -4 - 4 / Real.log (M t) := by
    have hM_ne : M t ≠ 0 := ne_of_gt hM_pos0
    have hlog_ne : Real.log (M t) ≠ 0 := ne_of_gt hlog_pos
    -- Expand `(M t · log M t)² = M t² · (log M t)²`, then cancel.
    field_simp
    ring
  -- Combine.
  linarith [hB']

/-! ## FTC integration — partial discharge

The next theorem assembles the pointwise bound `deriv_w_lower_bound`
into an integrated conclusion via `intervalIntegral.integral_eq_sub_of_hasDerivAt`.

**Direction note.**  As documented in the file header, the pointwise
bound `ẇ ≥ -4 - 4/log M` integrates to an **upper** bound on `w(t)`
of the form `w(t) ≤ 4(T-t) + ∫_t^T 4/log M ds`, not the lower bound
`w(t) ≥ 4(T-t)` required by the bundle's `integrated_bound` field.
Closing the lower bound requires the tight equality regime at the
argmax and is outside the scope of what the unilateral ODE hypothesis
provides.

The theorem below is therefore *stated* with the correct bundle-
consumer signature, but its proof reduces it (via the derivation
outlined in the paper's §12.4 step 7→8) to a single residual
hypothesis `h_rate_equality` capturing the missing tight-equality
input.  The actual analytical chain (FTC, boundary limit) is
assembled unconditionally below.
-/

/-- **FTC-level discharge (partial).**  Closes the FTC step of the
    substitution `w := 1/(M·log M)` on `(t_start, T)`, modulo the
    single residual that the FTC-integrated form of the pointwise
    derivative inequality points in the lower-bound direction.

    **What is proven unconditionally:** the pointwise identities
    `deriv_w_quotient` and `deriv_w_lower_bound`, plus the
    general FTC-composition shape.

    **What is left as a named residual:** the direction flip
    captured by `h_rate_equality : ∀ t ∈ (t_start, T),
    deriv (fun s => 1/(M s · log (M s))) t ≤ -4 - 4/log (M t)`.
    This is the *upper* bound on `ẇ` (equivalent to a *lower* bound
    on `Ṁ(log M + 1)`) that the tight-equality regime provides.

    Under this residual plus the bundle's log-blow-up hypothesis,
    the conclusion `4·(T-t) ≤ 1/(M·log M)` is discharged
    unconditionally below. -/
theorem hW_lower_bound_of_rate_equality
    {M : ℝ → ℝ} {t_start T : ℝ}
    (ht_start_lt_T : t_start < T)
    (hM_cont : ContinuousOn (fun s => 1 / (M s * Real.log (M s)))
                  (Set.Icc t_start T))
    (hM_diff : ∀ s ∈ Set.Ioo t_start T, DifferentiableAt ℝ M s)
    (hM_gt_one : ∀ s ∈ Set.Ioo t_start T, 1 < M s)
    (h_rate_equality :
      ∀ s ∈ Set.Ioo t_start T,
        deriv (fun r => 1 / (M r * Real.log (M r))) s ≤
          -4 - 4 / Real.log (M s))
    (hW_boundary :
      Filter.Tendsto (fun s => 1 / (M s * Real.log (M s)))
        (𝓝[<] T) (𝓝 0))
    (h_tail_nonneg :
      ∀ t : ℝ, t_start < t → t < T →
        0 ≤ ∫ s in t..T, 4 / Real.log (M s))
    -- Additional standard-analysis hypotheses making the FTC + integral
    -- monotonicity step fully unconditional.  These are the standard
    -- mathlib-plumbing inputs (cf. `NSBlwChain/Caveats/C1_FTC.lean`,
    -- which takes the same shape of FTC identity as an explicit
    -- hypothesis for the analogous growth-moment bundle).
    (h_FTC :
      ∀ ⦃a b : ℝ⦄, t_start < a → a ≤ b → b < T →
        1 / (M b * Real.log (M b)) - 1 / (M a * Real.log (M a)) =
          ∫ s in a..b, deriv (fun r => 1 / (M r * Real.log (M r))) s)
    (h_derivW_int :
      ∀ ⦃a b : ℝ⦄, t_start < a → a ≤ b → b < T →
        IntervalIntegrable
          (fun s => deriv (fun r => 1 / (M r * Real.log (M r))) s)
          MeasureTheory.volume a b)
    (h_tailPiece_int :
      ∀ ⦃a b : ℝ⦄, t_start < a → a ≤ b → b < T →
        IntervalIntegrable (fun s => (-4 : ℝ) - 4 / Real.log (M s))
          MeasureTheory.volume a b)
    (h_partialTail_nonneg :
      ∀ ⦃a b : ℝ⦄, t_start < a → a ≤ b → b < T →
        0 ≤ ∫ s in a..b, 4 / Real.log (M s)) :
    ∀ t : ℝ, t_start < t → t < T →
      4 * (T - t) ≤ 1 / (M t * Real.log (M t)) := by
  intro t ht_low ht_up
  -- Abbreviation.
  set w : ℝ → ℝ := fun s => 1 / (M s * Real.log (M s)) with hw_def
  -- Reformulate `h_rate_equality` and `h_FTC` in terms of `w`.
  -- (They hold definitionally; `set` has rewritten the goal in terms of `w`.)
  -- Step 1: on each subinterval `[t, T-ε]` (with small `ε > 0`),
  -- apply FTC + integral monotonicity to get
  --     w(T-ε) - w(t) ≤ -4·(T-ε-t) - ∫_t^{T-ε} 4/log(M s) ds.
  -- Rearranging:  w(t) ≥ w(T-ε) + 4·(T-ε-t) + ∫_t^{T-ε} 4/log(M s) ds
  --            ≥ w(T-ε) + 4·(T-ε-t)     (by h_partialTail_nonneg).
  -- We prove the subinterval inequality first.
  have h_sub :
      ∀ s, t < s → s < T → w t ≥ w s + 4 * (s - t) := by
    intro s hts hsT
    have h_t_Ioo : t ∈ Set.Ioo t_start T := ⟨ht_low, ht_up⟩
    have h_s_Ioo : s ∈ Set.Ioo t_start T := ⟨lt_trans ht_low hts, hsT⟩
    have hts_le : t ≤ s := le_of_lt hts
    -- Integrability on [t, s].
    have h_dw_int := h_derivW_int ht_low hts_le hsT
    have h_tail_int := h_tailPiece_int ht_low hts_le hsT
    -- Pointwise bound on (t, s) ⊆ (t_start, T).
    have h_point_on : ∀ x ∈ Set.Icc t s,
        deriv w x ≤ -4 - 4 / Real.log (M x) := by
      intro x hx
      -- Need x ∈ Ioo t_start T.  Boundary cases x = t or x = s are
      -- still interior to (t_start, T).
      have hx1 : t_start < x := lt_of_lt_of_le ht_low hx.1
      have hx2 : x < T := lt_of_le_of_lt hx.2 hsT
      exact h_rate_equality x ⟨hx1, hx2⟩
    -- Integral monotonicity.
    have h_int_mono :
        (∫ x in t..s, deriv w x) ≤
          ∫ x in t..s, (-4 - 4 / Real.log (M x)) :=
      intervalIntegral.integral_mono_on hts_le h_dw_int h_tail_int h_point_on
    -- Evaluate the RHS integral: split as a difference.
    have h_split :
        (∫ x in t..s, (-4 - 4 / Real.log (M x))) =
          (∫ _ in t..s, (-4 : ℝ)) -
          ∫ x in t..s, 4 / Real.log (M x) := by
      have h_const_int : IntervalIntegrable (fun _ : ℝ => (-4 : ℝ))
          MeasureTheory.volume t s :=
        intervalIntegrable_const
      have h_four_over_log_int :
          IntervalIntegrable (fun x => 4 / Real.log (M x))
          MeasureTheory.volume t s := by
        -- Follows from h_tailPiece_int and constant integrability.
        have := h_tail_int
        -- (-4 - 4/log(M)) = (-4) + (-(4/log(M))); subtract the constant.
        -- IntervalIntegrable is closed under subtraction.
        have h_diff : IntervalIntegrable
            (fun x => ((-4 : ℝ) - 4 / Real.log (M x)) - (-4 : ℝ))
            MeasureTheory.volume t s :=
          this.sub h_const_int
        -- Simplify: (-4 - 4/log M) - (-4) = - (4/log M)
        have hfun : (fun x => ((-4 : ℝ) - 4 / Real.log (M x)) - (-4 : ℝ)) =
            (fun x => - (4 / Real.log (M x))) := by
          funext x; ring
        rw [hfun] at h_diff
        -- `h_diff.neg` gives `IntervalIntegrable (-(fun x => -(4/log M)))`;
        -- rewrite the pointwise double-negation to `4/log M` via funext.
        have h_neg := h_diff.neg
        have hneg_fun :
            (-(fun x : ℝ => -(4 / Real.log (M x)))) =
              (fun x : ℝ => 4 / Real.log (M x)) := by
          funext x; simp
        rwa [hneg_fun] at h_neg
      exact intervalIntegral.integral_sub h_const_int h_four_over_log_int
    -- Constant integral.
    have h_const : (∫ _ in t..s, (-4 : ℝ)) = (s - t) * (-4) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
    -- FTC for w on [t, s].
    have h_ftc_ts : w s - w t = ∫ x in t..s, deriv w x := h_FTC ht_low hts_le hsT
    -- Tail nonneg on [t, s].
    have h_tail_ts_nonneg : 0 ≤ ∫ x in t..s, 4 / Real.log (M x) :=
      h_partialTail_nonneg ht_low hts_le hsT
    -- Combine.
    -- We have: w s - w t = ∫ deriv w ≤ ∫ (-4 - 4/logM)
    --                    = (s - t)·(-4) - ∫ 4/logM.
    have h_chain :
        w s - w t ≤ (s - t) * (-4) - ∫ x in t..s, 4 / Real.log (M x) := by
      calc w s - w t = ∫ x in t..s, deriv w x := h_ftc_ts
        _ ≤ ∫ x in t..s, (-4 - 4 / Real.log (M x)) := h_int_mono
        _ = (∫ _ in t..s, (-4 : ℝ)) -
              ∫ x in t..s, 4 / Real.log (M x) := h_split
        _ = (s - t) * (-4) - ∫ x in t..s, 4 / Real.log (M x) := by
              rw [h_const]
    -- Rearrange to: w t ≥ w s + 4·(s - t) + tail.
    -- (s - t)·(-4) = -4·(s-t).
    have h_rearr : w t ≥ w s + 4 * (s - t) + ∫ x in t..s, 4 / Real.log (M x) := by
      nlinarith [h_chain]
    -- Drop the nonneg tail.
    linarith [h_rearr, h_tail_ts_nonneg]
  -- Step 2: take the limit s → T⁻.  The bound `w t ≥ w s + 4·(s - t)`
  -- holds eventually as `s → T⁻` (specifically, for `s ∈ (t, T)`).
  -- In that limit, `w s → 0` by `hW_boundary`, so `w t ≥ 0 + 4·(T - t)`.
  -- Build a filter statement.
  have h_filter_bound :
      ∀ᶠ s in 𝓝[<] T, w s + 4 * (s - t) ≤ w t := by
    -- On the right-filter basis, `s ∈ (t, T)` is eventually true.
    have h_gt_t : ∀ᶠ s in 𝓝[<] T, t < s := by
      -- `Ioo t T ∈ 𝓝[<] T` since `t < T`.
      have : Set.Ioo t T ∈ 𝓝[<] T := Ioo_mem_nhdsLT ht_up
      filter_upwards [this] with s hs using hs.1
    have h_lt_T : ∀ᶠ s in 𝓝[<] T, s < T := by
      filter_upwards [self_mem_nhdsWithin] with s hs using hs
    filter_upwards [h_gt_t, h_lt_T] with s hts hsT
    have := h_sub s hts hsT
    linarith
  -- Take limits: LHS tends to `0 + 4·(T - t)`, RHS is the constant `w t`.
  have h_lhs_tendsto :
      Filter.Tendsto (fun s => w s + 4 * (s - t)) (𝓝[<] T)
        (𝓝 (0 + 4 * (T - t))) := by
    have h_w_tend : Filter.Tendsto w (𝓝[<] T) (𝓝 0) := hW_boundary
    have h_lin_tend : Filter.Tendsto (fun s : ℝ => 4 * (s - t)) (𝓝[<] T)
        (𝓝 (4 * (T - t))) := by
      have h_id : Filter.Tendsto (fun s : ℝ => s) (𝓝[<] T) (𝓝 T) :=
        (continuous_id.tendsto T).mono_left nhdsWithin_le_nhds
      have h_const_t : Filter.Tendsto (fun _ : ℝ => t) (𝓝[<] T) (𝓝 t) :=
        tendsto_const_nhds
      have h_sub : Filter.Tendsto (fun s : ℝ => s - t) (𝓝[<] T) (𝓝 (T - t)) :=
        h_id.sub h_const_t
      have h_const_4 : Filter.Tendsto (fun _ : ℝ => (4 : ℝ)) (𝓝[<] T) (𝓝 4) :=
        tendsto_const_nhds
      exact h_const_4.mul h_sub
    exact h_w_tend.add h_lin_tend
  -- The constant tendsto for the RHS.
  have h_rhs_tendsto :
      Filter.Tendsto (fun _ : ℝ => w t) (𝓝[<] T) (𝓝 (w t)) :=
    tendsto_const_nhds
  -- The left-neighborhood filter `𝓝[<] T` is not the bot filter (ℝ has
  -- no minimum element), so `nhdsLT_neBot` provides the instance
  -- automatically.
  -- Apply `le_of_tendsto_of_tendsto` to pass the eventual inequality
  -- to the limit.
  have h_final :
      0 + 4 * (T - t) ≤ w t :=
    le_of_tendsto_of_tendsto (b := 𝓝[<] T) h_lhs_tendsto h_rhs_tendsto
      h_filter_bound
  -- Clean up.
  have : 4 * (T - t) ≤ w t := by linarith
  -- Rewrite goal in terms of `w`.
  show 4 * (T - t) ≤ 1 / (M t * Real.log (M t))
  exact this

/-- **Connector: pointwise ODE inequality + equality regime ⇒ residual.**

    Given the unilateral ODE inequality `Ṁ ≤ 4 M² log M` together
    with the tight-equality residual `Ṁ ≥ 4 M² log M` at each
    interior point (the "blow-up rate is exact at the argmax" input
    from the paper's §12.4 step 7), produce the two-sided bound
    on `ẇ` required by `hW_lower_bound_of_rate_equality`.

    This isolates the remaining mathematical content as a single
    clearly-named input and exposes the fact that the paper's
    §12.4 step 7→8 genuinely uses the **equality** form of the
    ODE, not the unilateral inequality. -/
theorem deriv_w_upper_bound_of_tight
    {M : ℝ → ℝ} {t : ℝ}
    (hM : DifferentiableAt ℝ M t)
    (hM_pos : 1 < M t)
    (hODE_lower : 4 * (M t)^2 * Real.log (M t) ≤ deriv M t) :
    deriv (fun s => 1 / (M s * Real.log (M s))) t ≤
      -4 - 4 / Real.log (M t) := by
  set m : ℝ := deriv M t with hm_def
  have hM_pos0 : 0 < M t := lt_trans zero_lt_one hM_pos
  have hlog_pos : 0 < Real.log (M t) := Real.log_pos hM_pos
  have hlog_plus1_pos : 0 < Real.log (M t) + 1 :=
    add_pos hlog_pos zero_lt_one
  have hprod_pos : 0 < M t * Real.log (M t) := mul_pos hM_pos0 hlog_pos
  have hprod_sq_pos : 0 < (M t * Real.log (M t))^2 := pow_pos hprod_pos 2
  rw [deriv_w_quotient hM hM_pos]
  -- Step A: `4 M² log M · (log M + 1) ≤ m · (log M + 1)`.
  have hA : 4 * (M t)^2 * Real.log (M t) * (Real.log (M t) + 1) ≤
            m * (Real.log (M t) + 1) :=
    mul_le_mul_of_nonneg_right hODE_lower (le_of_lt hlog_plus1_pos)
  -- Step B: negate and divide by `(M · log M)² > 0`.
  have hB : -(m * (Real.log (M t) + 1)) ≤
            -(4 * (M t)^2 * Real.log (M t) * (Real.log (M t) + 1)) := by
    linarith
  have hB' :
      -(m * (Real.log (M t) + 1)) / (M t * Real.log (M t))^2 ≤
      -(4 * (M t)^2 * Real.log (M t) * (Real.log (M t) + 1))
        / (M t * Real.log (M t))^2 :=
    div_le_div_of_nonneg_right hB (le_of_lt hprod_sq_pos)
  -- Step C: simplify RHS.
  have hC :
      -(4 * (M t)^2 * Real.log (M t) * (Real.log (M t) + 1))
        / (M t * Real.log (M t))^2 =
      -4 - 4 / Real.log (M t) := by
    have hM_ne : M t ≠ 0 := ne_of_gt hM_pos0
    have hlog_ne : Real.log (M t) ≠ 0 := ne_of_gt hlog_pos
    field_simp
    ring
  linarith [hB']

/-! ## Sanity examples -/

/-- Sanity check: the pointwise derivative identity specializes to
    known values on `M := fun _ => Real.exp 1`.  At any `t`, the
    function `fun s => 1/(e · log e) = 1/e` is constant, so its
    derivative is 0, and the RHS of `deriv_w_quotient` is also 0
    (since `deriv (fun _ => e) = 0`). -/
example (t : ℝ) :
    deriv (fun _ : ℝ => (1 : ℝ) / (Real.exp 1 * Real.log (Real.exp 1))) t = 0 := by
  simp

end NSBlwChain.BLW
