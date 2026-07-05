-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Torus.EpsteinZetaZ3

/-!
# Torus correction: 3D Epstein-zeta lattice sum (paper §12.4 step 4, §D.4)

On the periodic torus `T^3_L`, the Biot-Savart kernel replaces the
free-space Green's function `G_∞(x) = 1/(4π|x|)` by the periodic
Green's function `G^per_L`. Writing

  `G^per_L(x) = G_∞(x) + H_L(x)`

(see Proposition D.4.4 of `paper/ns_regularity_blw_derivations.md`)
the smooth correction `H_L` is controlled by the 3D lattice Epstein-zeta
sum
  `ζ_{ℤ^3}(s) := ∑_{n ∈ ℤ^3 \ {0}} |n|^{-s}`
for integer `s ≥ 4` (absolutely convergent after one Taylor-remainder
subtraction that upgrades the `|n|^{-3}` decay to `|n|^{-4}`).

Tabulated value (Glasser-Zucker, *J. Phys. A* 13, 1980):

  `ζ_{ℤ^3}(4) ≈ 16.533`.

The concrete consequence used in §12.4 step 4 is the pointwise bound

  `|R_L(x*)| ≤ C_2 · M`, where `C_2 = 3 · ζ_{ℤ^3}(3) / (4π)`

(Corollary D.4.5, equation (D.4.9)). This packages into the near/far
log-absorption chain as

  `|σ(x*)| ≤ M · (1 + C_2 + log(L/δ_ν))`.

The lattice-sum bound `LatticeSumBounded` is now the **real** statement and
is discharged unconditionally in `NSBlwChain/Torus/EpsteinZetaZ3.lean`
(`latticeSum_le_latticeZetaConstZ3`, zero axioms). The remaining hypothesis
in this file is the pointwise torus correction `|R_L| ≤ C_2 · M`
(`TorusCorrectionBundle`); the algebraic composition (near + far + torus)
is proven unconditionally.

Remaining open discharge (see end of file):

* Construct a concrete witness of `TorusCorrectionBundle` (i.e. derive
  the bound `|R_L| ≤ C_2 · M` from the Ewald decomposition + energy-
  enstrophy bound + an `EpsteinZetaBundle` at `s = 3`). Requires
  mathlib-level Green's-function machinery not yet present.

## References

* `paper/ns_regularity.md` §12.4 step 4.
* `paper/ns_regularity_blw_derivations.md` §D.4 (Ewald splitting,
  Prop D.4.4 smoothness, Cor D.4.5 torus correction bound).
* SQG companion pattern: `HasLatticeZetaBound` in
  `sqg-lean-proofs/SqgIdentity/RieszTorus.lean` §11.25.F–§11.26.H.
-/

namespace NSBlwChain.Torus

/-! ### Epstein-zeta scalar bundle -/

/-- **3D lattice Epstein-zeta bound** (real proposition).

`LatticeSumBounded s C` says: for every finite `A ⊆ ℤ³ \ {0}`,

  `∑_{a ∈ A} ‖a‖^{-s} ≤ C`,

where `‖·‖ = latticeNormZ3` is the Euclidean norm on `ℤ³ = (Fin 3 → ℤ)`.

This **replaces** the former `:= True` placeholder. It is the genuine
lattice-sum statement, discharged unconditionally (for the paper's `s = 4`)
by `EpsteinZetaZ3.latticeSum_le_latticeZetaConstZ3` — no axioms, no `sorry`. -/
def LatticeSumBounded (s : ℕ) (C : ℝ) : Prop :=
  ∀ A : Finset (Fin 3 → ℤ), (0 : Fin 3 → ℤ) ∉ A →
    ∑ a ∈ A, (latticeNormZ3 a) ^ (-(s : ℝ)) ≤ C

/-- **Epstein-zeta lattice bundle.**

Packages a 3D lattice Epstein-zeta bound at integer exponent `s`:

  `∑_{a ∈ A} ‖a‖^{-s} ≤ C_s` for every finite `A ⊆ ℤ³ \ {0}`.

For our use (§D.4.7 + Taylor-remainder upgrade) the relevant exponent is
`s = 4`. The `latticeSumBounded` field now carries the **real** statement
(`LatticeSumBounded`), discharged in `exampleBundleAt4` via the concrete
`EpsteinZetaZ3` proof.

Fields:

* `s` — integer exponent `≥ 2` (typically `3` or `4`).
* `C_s` — a scalar upper bound for the lattice sum.
* `s_ge_two` — `2 ≤ s`.
* `nonneg` — `0 ≤ C_s`.
* `latticeSumBounded` — the real per-finset bound `LatticeSumBounded s C_s`.

Note: `EpsteinZetaBundle` is a **data-carrying** structure, not
`Prop`-valued: the scalar `s` and `C_s` are data.
-/
structure EpsteinZetaBundle where
  /-- Lattice-sum exponent (integer, `≥ 2`). -/
  s : ℕ
  /-- Upper bound on the lattice sum. -/
  C_s : ℝ
  /-- `s` is at least 2 (absolute convergence needs `s > 3`, i.e. `s ≥ 4`;
      we allow `s = 3` for the conditionally-convergent statement). -/
  s_ge_two : 2 ≤ s
  /-- The bound constant is nonnegative. -/
  nonneg : 0 ≤ C_s
  /-- The lattice sum `∑_{a ∈ A} ‖a‖^{-s} ≤ C_s` over every finite
      `A ⊆ ℤ³ \ {0}`. Now the **real** statement (`LatticeSumBounded`),
      not a `True` placeholder; discharged at `s = 4` in `exampleBundleAt4`. -/
  latticeSumBounded : LatticeSumBounded s C_s

/-! ### Sanity-check scalar bundle at `s = 4` -/

/-- Tabulated numerical value (Glasser-Zucker 1980): `ζ_{ℤ^3}(4) ≈ 16.533`. -/
noncomputable def epsteinZetaZ3At4 : ℝ := 16.533

/-- Safe rounded-up over-estimate of the tabulated value, kept for reference. -/
def epsteinZetaZ3At4_upper : ℝ := 17

/-- **Example bundle** at `s = 4`, carrying the genuinely-proved unconditional
constant `latticeZetaConstZ3 4` (`= 54·ζ(2) = 9π² ≈ 88.8`, the crude
shell-counting over-estimate; the exact sum is `≈ 16.533`). The
`latticeSumBounded` field is discharged by the concrete 3D lattice-zeta
theorem, so this bundle is **no longer a placeholder**. -/
noncomputable def exampleBundleAt4 : EpsteinZetaBundle where
  s := 4
  C_s := latticeZetaConstZ3 ((4 : ℕ) : ℝ)
  s_ge_two := by decide
  nonneg := latticeZetaConstZ3_nonneg _
  latticeSumBounded := fun A hA => latticeSum_le_latticeZetaConstZ3_four A hA

/-! ### Torus correction scalar bundle -/

/-- **Torus Biot-Savart correction bundle.**

Packages the near-origin torus correction from §D.4 of the paper. On
`T^3_L`, the periodic Biot-Savart kernel splits as `G^per_L = G_∞ + H_L`
(equation D.4.5), and Corollary D.4.5 gives

  `|R_L(x*)| ≤ C_2 · M`, `C_2 = 3 · ζ_{ℤ^3}(3) / (4π)`

where `M = ‖ω‖_∞` and `R_L` is the difference between the torus and
free-space Biot-Savart evaluations at the argmax `x*`.

Fields:

* `M` — vorticity-sup envelope at the current time.
* `L` — torus side length.
* `ν` — viscosity.
* `C_2` — the torus-correction constant, nominally `3 · C_s / (4π)`
  where `C_s` is sourced from a sibling `EpsteinZetaBundle` at `s = 3`.
* `RL` — the torus-correction magnitude at `x*`.
* `M_pos` — `0 < M` (so `x*` is genuinely concentrated).
* `L_pos` — `0 < L`.
* `ν_pos` — `0 < ν`.
* `C_2_nonneg` — `0 ≤ C_2`.
* `RL_bound` — the pointwise inequality `|R_L| ≤ C_2 · M`, **taken as
  hypothesis**. This is equation (D.4.9) of the derivations file;
  discharging it requires Ewald splitting + energy-enstrophy bound.

Discharging `RL_bound` on a concrete model is the principal open task.
-/
structure TorusCorrectionBundle where
  /-- Vorticity-sup envelope. -/
  M : ℝ
  /-- Torus side length. -/
  L : ℝ
  /-- Viscosity. -/
  ν : ℝ
  /-- Torus correction constant, `C_2 = 3 · C_s / (4π)`. -/
  C_2 : ℝ
  /-- Torus-correction magnitude at argmax. -/
  RL : ℝ
  /-- `0 < M`. -/
  M_pos : 0 < M
  /-- `0 < L`. -/
  L_pos : 0 < L
  /-- `0 < ν`. -/
  ν_pos : 0 < ν
  /-- `0 ≤ C_2`. -/
  C_2_nonneg : 0 ≤ C_2
  /-- **Hypothesis** (paper D.4.9): `|R_L| ≤ C_2 · M`. -/
  RL_bound : |RL| ≤ C_2 * M

/-! ### Algebraic consequence: corrected near/far + torus bound -/

/-- **Torus-corrected σ bound (paper §12.4 step 5).**

Given:

* a `TorusCorrectionBundle` carrying `M`, `C_2`, and `|R_L| ≤ C_2 · M`;
* a near-field log bound `σ_near_far ≤ M · (1 + log(L/δ_ν))` (structural
  input from §12.4 steps 2+3);
* the algebraic decomposition `σ = σ_near_far + R_L` (structural input
  from the splitting of the Biot-Savart integral at `r = δ_ν` and the
  free-space / periodic kernel difference);

then
  `σ ≤ M · (1 + C_2 + log(L/δ_ν))`.

The proof is purely algebraic: triangle-inequality on `σ` plus the two
hypothesis bounds. Annotated `noncomputable` as it composes `Real.log`.
-/
theorem torus_corrected_bound
    (b : TorusCorrectionBundle)
    (σ : ℝ) (σ_near_far : ℝ) (δ_ν : ℝ)
    (h_decompose : σ = σ_near_far + b.RL)
    (h_near_far : σ_near_far ≤ b.M * (1 + Real.log (b.L / δ_ν))) :
    σ ≤ b.M * (1 + b.C_2 + Real.log (b.L / δ_ν)) := by
  -- σ = σ_near_far + R_L ≤ σ_near_far + |R_L|
  have h_RL_abs : b.RL ≤ |b.RL| := le_abs_self _
  have h_RL_bound : b.RL ≤ b.C_2 * b.M := le_trans h_RL_abs b.RL_bound
  -- Combine:  σ ≤ M(1 + log(L/δ_ν)) + C_2 · M
  have h_combine :
      σ_near_far + b.RL ≤ b.M * (1 + Real.log (b.L / δ_ν)) + b.C_2 * b.M := by
    exact add_le_add h_near_far h_RL_bound
  -- Rearrange:  M(1 + log(L/δ_ν)) + C_2·M = M(1 + C_2 + log(L/δ_ν))
  have h_rearrange :
      b.M * (1 + Real.log (b.L / δ_ν)) + b.C_2 * b.M
        = b.M * (1 + b.C_2 + Real.log (b.L / δ_ν)) := by ring
  calc σ = σ_near_far + b.RL := h_decompose
    _ ≤ b.M * (1 + Real.log (b.L / δ_ν)) + b.C_2 * b.M := h_combine
    _ = b.M * (1 + b.C_2 + Real.log (b.L / δ_ν)) := h_rearrange

/-! ### Lifting an Epstein-zeta bundle to the nominal `C_2`

Given `EpsteinZetaBundle` with exponent `s = 3`, the paper formula
`C_2 = 3 · C_s / (4π)` gives the torus-correction constant. This is a
small scalar lemma — it does *not* discharge `RL_bound`, only connects
the constants. -/

/-- Nominal `C_2` constant from an Epstein-zeta bundle:
    `C_2 = 3 · C_s / (4π)`. -/
noncomputable def c2_of (z : EpsteinZetaBundle) : ℝ :=
  3 * z.C_s / (4 * Real.pi)

/-- `C_2` is nonnegative whenever `C_s ≥ 0`. -/
lemma c2_of_nonneg (z : EpsteinZetaBundle) : 0 ≤ c2_of z := by
  unfold c2_of
  have h4pi_pos : (0 : ℝ) < 4 * Real.pi := by positivity
  have h3Cs : 0 ≤ 3 * z.C_s := by
    have : (0 : ℝ) ≤ 3 := by norm_num
    exact mul_nonneg this z.nonneg
  exact div_nonneg h3Cs (le_of_lt h4pi_pos)

/-! ### Sanity-check examples -/

/-- At `s = 4`, `exampleBundleAt4` carries the proved unconditional constant
`latticeZetaConstZ3 4`, and `c2_of` reads it off definitionally. -/
example : c2_of exampleBundleAt4 = 3 * latticeZetaConstZ3 ((4 : ℕ) : ℝ) / (4 * Real.pi) := by
  unfold c2_of
  rfl

/-- Concrete example: with `M = 1, L = 1, ν = 1, C_2 = 5, R_L = 3`,
the torus-corrected bound `σ ≤ 1 · (1 + 5 + log(1)) = 6` follows
from `σ_near_far ≤ 1 · (1 + log(1)) = 1`, `R_L ≤ 5`, and `σ = 1 + 3`. -/
example :
    let b : TorusCorrectionBundle :=
      { M := 1, L := 1, ν := 1, C_2 := 5, RL := 3,
        M_pos := by norm_num,
        L_pos := by norm_num,
        ν_pos := by norm_num,
        C_2_nonneg := by norm_num,
        RL_bound := by
          show |(3 : ℝ)| ≤ 5 * 1
          rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
          norm_num }
    (1 + 3 : ℝ) ≤ b.M * (1 + b.C_2 + Real.log (b.L / 1)) := by
  intro b
  have h : Real.log ((1 : ℝ) / 1) = 0 := by
    simp [Real.log_one]
  rw [h]
  show (1 + 3 : ℝ) ≤ 1 * (1 + 5 + 0)
  norm_num

/-! ### Open discharges

Listed here rather than in a separate `OPEN.md` entry for local
traceability. `LatticeSumBounded` is now discharged (see below); the
remaining hypothesis is `TorusCorrectionBundle.RL_bound`, whose
*mathematical* content lives in §D.4 of the paper.

1. **`LatticeSumBounded s C_s` — DISCHARGED.** Now the real statement
   `∀ finite A ⊆ ℤ³ \ {0}, ∑_{a ∈ A} ‖a‖^{-s} ≤ C`, proved unconditionally
   for every `s > 3` in `NSBlwChain/Torus/EpsteinZetaZ3.lean`
   (`latticeSum_le_latticeZetaConstZ3`; witness at `s = 4` via
   `latticeSum_le_latticeZetaConstZ3_four`, wired into `exampleBundleAt4`).
   Route (the ℤ³ mirror of the SQG project's §11.26.A–H): partition
   `ℤ³ \ {0}` into `ℓ∞`-annular shells (`|shell k| ≤ 6(2k+1)² ≤ 54k²`,
   Euclidean norm `≥ k`), bound each shell sum by `54 k^{-(s-2)}`, and sum
   via `Real.summable_one_div_nat_rpow` (`s > 3 ⟹ s - 2 > 1`). The proved
   constant `latticeZetaConstZ3 s = 54·ζ(s-2)` is loose (`9π² ≈ 88.8` at
   `s = 4` vs the exact `ζ_{ℤ³}(4) ≈ 16.533`); the consumer needs only
   finiteness.

2. **`TorusCorrectionBundle.RL_bound` discharge.** A concrete construction
   of `TorusCorrectionBundle` from a given NS configuration requires:
   (a) Ewald splitting of `G^per_L` (§D.4.2);
   (b) Smoothness + `L^∞` bound on `H_L` via Proposition D.4.4;
   (c) Energy-enstrophy bound `‖ω‖_{L^1} ≤ L^{3/2} · E_0^{1/2}` used to
       trade `1/L^3` for `1/L^{3/2}` in the sharper form (D.4.10).
   These are classical but not trivially in mathlib. Proposed to defer
   to a companion file `Torus/EwaldSplitting.lean` (not yet scaffolded).

3. **Connection to the BLW gradient chain (§12.4).** Once a concrete
   `TorusCorrectionBundle` is available, `torus_corrected_bound` above
   feeds directly into `NSBlwChain/BLW/LogAbsorption.lean` step 5 to
   replace its free-space assumption with the torus-adjusted inequality.
   Wiring is purely mechanical.
-/

end NSBlwChain.Torus
