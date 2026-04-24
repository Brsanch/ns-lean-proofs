-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.BLW.GradientBoundFromNSAxiomsHessianBundled
import NSBlwChain.BLW.HessianInputsBundle

/-!
# Top-level convenience capstone — one call, NS-axioms side

Single end-to-end theorem wiring
`HessianInputs.ofNSEvolutionAxioms` into
`gradient_bound_from_ns_axioms_time_analytic_hessian_bundled`.

## Signature summary

Inputs (all structural / definitional):

* `NSEvolutionAxioms u ν T` — the NS smoothness / div-free / vorticity
  bundle.
* `0 < t < T`, spatial point `xStar`.
* `IsLocalMax (|ω(t, ·)|²) xStar` — argmax of `|ω|²` at `xStar`.
* Alignment: `ω(x*)_0 = 0`, `ω(x*)_1 = 0`, `ω(x*)_2 = M`.
* Positivity `0 < M`, growth `0 ≤ Mdot`.
* Four definitional matchings (scalar abstracts → physical quantities):
  - `h_omega_lap_def`, `h_laplace3_def`, `h_σ_def`
  - `h_trace_sum_def`, `h_lap3_sum_def`
* Three total-matchings tying `gradSqNorm`, `omega_laplace_omega`,
  `hessian_trace_sqNorm` to concrete Fin 3 × Fin 3 slice-sum
  formulas.
* Envelope bundle: `M_fn`, `h_M_fn_at_t`, `h_M_fn_deriv`,
  `h_env_dom`, `h_env_hit`, `h_slice_diff`.

Conclusion: `gradSqNorm ≤ M² · σ / ν`.

**Everything else** — per-component smoothness, slice
`HasDerivAt` witnesses, time-differentiability of vorticity
components, per-component Hessian identities — is auto-discharged
from `NSEvolutionAxioms` + the `NS_time_analyticity` classical
axiom.

## Main result

* `gradient_bound_from_NSEvolutionAxioms` — the one-call end-to-end
  NS-axioms-side capstone.
-/

namespace NSBlwChain.BLW

open Filter Topology
open scoped BigOperators
open NSBlwChain

/-- **Top-level NS-axioms-side gradient-bound capstone.**

    One-call end-to-end theorem.  Takes the NS bundle plus structural
    hypotheses plus the definitional matchings, constructs the
    `HessianInputs` bundle internally via
    `HessianInputs.ofNSEvolutionAxioms`, and delegates to
    `gradient_bound_from_ns_axioms_time_analytic_hessian_bundled`.

    The scalar `gradSqNorm` concludes `≤ M² · σ / ν` — Theorem 12.2
    of the companion paper `paper/ns_regularity.md`, specialized to
    the argmax of `|ω(t, ·)|²` under the local-frame alignment with
    `ω₃`. -/
theorem gradient_bound_from_NSEvolutionAxioms
    {u : VelocityField} {ν T : ℝ} (ax : NSEvolutionAxioms u ν T)
    (t : ℝ) (ht0 : 0 < t) (htT : t < T)
    (xStar : Vec3)
    (hmax : IsLocalMax
      (fun y : Vec3 => Vec3.dot (vorticity u t y) (vorticity u t y))
      xStar)
    (M σ Mdot gradSqNorm laplaceOmega3
      omega_laplace_omega hessian_trace_sqNorm : ℝ)
    (hM_pos : 0 < M)
    -- Alignment:
    (hω0 : vorticity u t xStar 0 = 0)
    (hω1 : vorticity u t xStar 1 = 0)
    (hω2 : vorticity u t xStar 2 = M)
    -- Alignment-algebra definitions:
    (h_omega_lap_def :
      omega_laplace_omega
        = Vec3.dot (vorticity u t xStar)
            (fun j => vectorLaplacian (vorticity u t) xStar j))
    (h_laplace3_def :
      laplaceOmega3 = vectorLaplacian (vorticity u t) xStar 2)
    (h_σ_def :
      σ = partialDeriv (fun y => u t y 2) 2 xStar)
    -- Sign definitions:
    (h_trace_sum_def :
      hessian_trace_sqNorm
        = ∑ i : Fin 3, deriv (deriv (slice
            (fun y => Vec3.dot (vorticity u t y) (vorticity u t y))
            xStar i)) 0)
    (h_lap3_sum_def :
      laplaceOmega3
        = ∑ i : Fin 3, deriv (deriv (slice
            (fun y => vorticity u t y 2) xStar i)) 0)
    -- HessianInputs total matchings (3):
    (h_gradSq_match :
      gradSqNorm
        = ∑ k : Fin 3, ∑ i : Fin 3,
            (deriv (slice (fun y => vorticity u t y k) xStar i) 0) ^ 2)
    (h_omega_lap_match :
      omega_laplace_omega
        = ∑ k : Fin 3,
            vorticity u t xStar k
              * (∑ i : Fin 3,
                  deriv (deriv
                    (slice (fun y => vorticity u t y k) xStar i)) 0))
    (h_trace_match :
      hessian_trace_sqNorm
        = ∑ k : Fin 3, ∑ i : Fin 3,
            deriv (deriv (fun s =>
              (slice (fun y => vorticity u t y k) xStar i s) ^ 2)) 0)
    -- Envelope (Danskin):
    (M_fn : ℝ → ℝ)
    (h_M_fn_at_t : M_fn t = M)
    (h_M_fn_deriv : HasDerivAt M_fn Mdot t)
    (h_env_dom : ∀ y τ,
      Vec3.dot (vorticity u τ y) (vorticity u τ y) / 2
        ≤ (M_fn τ) ^ 2 / 2)
    (h_env_hit :
      Vec3.dot (vorticity u t xStar) (vorticity u t xStar) / 2
        = (M_fn t) ^ 2 / 2)
    (h_slice_diff :
      DifferentiableAt ℝ
        (fun τ => Vec3.dot (vorticity u τ xStar)
                           (vorticity u τ xStar) / 2) t)
    -- Growth regime:
    (h_growth_nonneg : 0 ≤ Mdot) :
    gradSqNorm ≤ M ^ 2 * σ / ν := by
  -- Construct HessianInputs from NSEvolutionAxioms smoothness.
  have H :
      HessianInputs u t xStar
        gradSqNorm omega_laplace_omega hessian_trace_sqNorm :=
    HessianInputs.ofNSEvolutionAxioms
      ax (le_of_lt ht0) htT xStar
      gradSqNorm omega_laplace_omega hessian_trace_sqNorm
      h_gradSq_match h_omega_lap_match h_trace_match
  -- Delegate to the Hessian-bundled capstone.
  exact gradient_bound_from_ns_axioms_time_analytic_hessian_bundled
    ax t ht0 htT xStar hmax
    M σ Mdot gradSqNorm laplaceOmega3
    omega_laplace_omega hessian_trace_sqNorm
    hM_pos hω0 hω1 hω2
    h_omega_lap_def h_laplace3_def h_σ_def
    h_trace_sum_def h_lap3_sum_def
    M_fn h_M_fn_at_t h_M_fn_deriv h_env_dom h_env_hit h_slice_diff
    H h_growth_nonneg

end NSBlwChain.BLW
