-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import FourierAnalysis.LatticeZeta

/-!
# Concrete 3D Epstein-zeta lattice bound (d = 3 instance of the shared theorem)

The 3D lattice Epstein-zeta bound that `NSBlwChain/Torus/EpsteinZeta.lean` needs
(discharging its former `LatticeSumBounded := True` placeholder) is now the
**`d = 3` instance** of the arbitrary-dimension theorem
`FourierAnalysis.latticeSum_le_latticeZetaConstD`, proved once in the shared
`fourier_analysis` package (also `require`d by `sqg-lean-proofs`, which
instantiates it at `d = 2`). The previous ~300-LOC bespoke ℤ³ shell proof is
replaced by this thin instantiation — one theorem, two dimensions.

  for `s > 3` and every finite `A ⊆ ℤ³ \ {0}`:
    `∑_{a ∈ A} ‖a‖^{-s} ≤ latticeZetaConstZ3 s`,

with `latticeZetaConstZ3 s = FourierAnalysis.latticeZetaConstD 3 s = 54·ζ(s-2)`
(the shared constant `2·d·3^{d-1}·ζ(p-(d-1))` at `d = 3, p = s`; a loose
shell-counting over-estimate — the exact `ζ_{ℤ³}(4) ≈ 16.533`, this gives
`54·ζ(2) = 9π² ≈ 88.8` at `s = 4`). The consumer needs only finiteness.
-/

namespace NSBlwChain.Torus

/-- Euclidean norm on `ℤ³`, i.e. the shared `FourierAnalysis.latticeNormD` at `d = 3`. -/
noncomputable abbrev latticeNormZ3 (n : Fin 3 → ℤ) : ℝ := FourierAnalysis.latticeNormD n

/-- The 3D lattice-zeta constant, i.e. the shared `latticeZetaConstD` at `d = 3`. -/
noncomputable abbrev latticeZetaConstZ3 (s : ℝ) : ℝ := FourierAnalysis.latticeZetaConstD 3 s

lemma latticeZetaConstZ3_nonneg (s : ℝ) : 0 ≤ latticeZetaConstZ3 s :=
  FourierAnalysis.latticeZetaConstD_nonneg 3 s

/-- **3D lattice Epstein-zeta bound** — the `d = 3` instance of
`FourierAnalysis.latticeSum_le_latticeZetaConstD`. Unconditional, zero axioms. -/
theorem latticeSum_le_latticeZetaConstZ3 {s : ℝ} (hs : 3 < s)
    (A : Finset (Fin 3 → ℤ)) (hA0 : (0 : Fin 3 → ℤ) ∉ A) :
    ∑ a ∈ A, (latticeNormZ3 a) ^ (-s) ≤ latticeZetaConstZ3 s :=
  FourierAnalysis.latticeSum_le_latticeZetaConstD (by norm_num) (by exact_mod_cast hs) A hA0

/-- Convenience specialization at the paper's exponent `s = 4`. -/
theorem latticeSum_le_latticeZetaConstZ3_four
    (A : Finset (Fin 3 → ℤ)) (hA0 : (0 : Fin 3 → ℤ) ∉ A) :
    ∑ a ∈ A, (latticeNormZ3 a) ^ (-((4 : ℕ) : ℝ)) ≤ latticeZetaConstZ3 ((4 : ℕ) : ℝ) :=
  latticeSum_le_latticeZetaConstZ3 (by norm_num) A hA0

end NSBlwChain.Torus
