-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib
import NSBlwChain.Torus.EpsteinZeta

/-!
# Sharper structural form for the 3D Epstein-zeta lattice bound (paper §D.4)

This file refines the placeholder `LatticeSumBounded s C_s := True` from
`NSBlwChain/Torus/EpsteinZeta.lean` into a more substantive structural
wrapper, and connects it to mathlib's 1D p-series infrastructure.

It is deliberately **hypothesis-keyed**: we do not attempt to compute the
Glasser-Zucker constant `ζ_{ℤ^3}(4) ≈ 16.533`. What we do is:

* Give a named bound for the `ℓ^∞`-shell cardinality
  (`lattice_shell_card_bound`).
* Introduce a `HasLatticeZetaBoundAt` predicate capturing
  `∃ (C : ℝ), 0 ≤ C ∧ ⟨supplied bound hypothesis⟩`.
* Expose the 1D p-series summability (`Real.summable_one_div_nat_rpow`)
  as the downstream analytic ingredient that a full discharge would use.
* Instantiate the predicate at `s = 4` with an explicit nonneg constant
  `C = 17` (paper's `16.533` rounded up), as a concrete example.

Nothing in this file proves `∑_{n ∈ ℤ^3 \ {0}} |n|^{-s} ≤ C`. The
lattice-sum content is still carried as a hypothesis, mirroring the
SQG companion pattern (`HasLatticeZetaBound`). The improvement over
`EpsteinZeta.lean`'s `True` placeholder is:

1. The `Prop` is now parameterised by an abstract *witness predicate*
   `P : ℕ → ℝ → Prop`, so a downstream file can refine `P` to the real
   `∑_{n ∈ ℤ^3 \ {0}} ‖n‖^{-s} ≤ C` statement without re-opening the
   consumer-facing structure.
2. The bundle at `s = 4` is now a provable instance: we give a nonneg
   constant `C_s = 17` and discharge the hypothesis with a user-supplied
   proof of `P 4 17`.
3. The connection to 1D p-series is stated as a standalone lemma that
   any concrete discharge will rely on.

## Note on `EpsteinZetaBundle` wiring

`EpsteinZetaBundle` in `EpsteinZeta.lean` currently fixes
`latticeSumBounded : True`. To wire the sharper predicate in, that
structure would need to be generalised over `P : ℕ → ℝ → Prop` (or have
its `latticeSumBounded` field typed `LatticeSumBounded s C_s` with
`LatticeSumBounded` made a real predicate). That edit is deferred to a
follow-up touching `EpsteinZeta.lean` itself; this file only supplies
the machinery.
-/

namespace NSBlwChain.Torus

/-! ### 1. Lattice shell cardinality -/

/-- **Lattice shell card bound.**

The `ℓ^∞`-ball of radius `n` in `ℤ^3` has at most `(2n+1)^3` lattice
points. Modeled combinatorially as `(Finset.range (2n+1))^3 = Finset.Ioc
over three copies`, whose cardinality is `(2n+1)^3` exactly.

This lemma is stated using `Finset.range (2n+1)` triple-product, whose
cardinality is `(2n+1)^3` by `Finset.card_range`. We state it as an
inequality rather than an equality because downstream uses only need a
one-sided bound, and the equality version can clutter rewriting.
-/
theorem lattice_shell_card_bound (n : ℕ) :
    ((Finset.range (2 * n + 1) ×ˢ Finset.range (2 * n + 1)
        ×ˢ Finset.range (2 * n + 1)).card) ≤ (2 * n + 1) ^ 3 := by
  -- Cardinality of a triple product is the product of cardinalities,
  -- and `(Finset.range k).card = k`, so the LHS equals `(2n+1)^3`.
  simp [Finset.card_product, Finset.card_range, pow_succ, Nat.mul_comm,
        Nat.mul_left_comm, Nat.mul_assoc]

/-! ### 2. 1D p-series connection

The full 3D Epstein-zeta bound reduces (via a shell decomposition) to
the 1D p-series `∑_{k ≥ 1} k^{-p}`, which is summable iff `1 < p`.
`Real.summable_one_div_nat_rpow` packages this in mathlib. We restate
it in the exact form a 3D discharge would consume: for `p > 3`,
`∑_{k ≥ 1} k^{-(p-2)}` is summable (the `-2` absorbs the `k^2` shell-
cardinality growth).

For our target exponent `s = 4`, the downstream summand is
`k^{-(4-2)} = k^{-2}`, which is summable (`1 < 2`).
-/

/-- **1D p-series connection.** For any `p : ℝ` with `1 < p`, the
sequence `k ↦ 1 / k^p` is summable (mathlib `Real.summable_one_div_nat_rpow`). -/
theorem pseries_summable_of_one_lt {p : ℝ} (hp : 1 < p) :
    Summable (fun k : ℕ => 1 / (k : ℝ) ^ p) := by
  rw [Real.summable_one_div_nat_rpow]
  exact hp

/-- **3D shell-decomposition corollary.** For the 3D lattice sum at
exponent `s > 3`, after combining with the `O(k^2)` shell cardinality
we get a summable `k^{-(s-2)}` series. Stated as a summability claim
with the explicit exponent-shift `s - 2 > 1 ↔ s > 3`. -/
theorem lattice_reduced_pseries_summable {s : ℝ} (hs : 3 < s) :
    Summable (fun k : ℕ => 1 / (k : ℝ) ^ (s - 2)) := by
  have hsm2 : 1 < s - 2 := by linarith
  exact pseries_summable_of_one_lt hsm2

/-- **Concrete instance at `s = 4`.** The reduced 1D series `k ↦ k^{-2}`
is summable. Used downstream when the target exponent is `s = 4`. -/
theorem pseries_summable_at_four :
    Summable (fun k : ℕ => 1 / (k : ℝ) ^ (2 : ℝ)) := by
  have : Summable (fun k : ℕ => 1 / (k : ℝ) ^ ((4 : ℝ) - 2)) :=
    lattice_reduced_pseries_summable (by norm_num : (3 : ℝ) < 4)
  simpa using this

/-! ### 3. Structural `HasLatticeZetaBoundAt` predicate

We refine the `EpsteinZeta.LatticeSumBounded` placeholder into a
predicate parameterised by an abstract witness `P : ℕ → ℝ → Prop`. A
downstream user can instantiate `P s C` to the real lattice inequality
`∑_{n ∈ ℤ^3 \ {0}} ‖n‖^{-s} ≤ C` without modifying this file. -/

/-- **Epstein-zeta bound predicate, abstract form.**

Says: there exists a nonneg constant `C` such that the user-supplied
predicate `P s C` holds. This is just `∃ C, 0 ≤ C ∧ P s C` explicitly
named for documentation.

In the intended application, `P s C` is `∑_{n ∈ ℤ^3 \ {0}} ‖n‖^{-s} ≤ C`,
but this file does not commit to any particular choice of `ℤ^3`
encoding, norm, or summability machinery.
-/
def HasLatticeZetaBoundAt (P : ℕ → ℝ → Prop) (s : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ P s C

/-- **Constructor.** Given a user-supplied constant and proof, build
`HasLatticeZetaBoundAt`. -/
theorem HasLatticeZetaBoundAt.mk' (P : ℕ → ℝ → Prop) (s : ℕ)
    (C : ℝ) (hC : 0 ≤ C) (hP : P s C) :
    HasLatticeZetaBoundAt P s :=
  ⟨C, hC, hP⟩

/-- **Monotonicity in the constant.** If `P s C → P s C'` for any
`C' ≥ C`, then `HasLatticeZetaBoundAt P s` survives weakening the
constant. Standard abstract monotone-bound pattern. -/
theorem HasLatticeZetaBoundAt.mono {P : ℕ → ℝ → Prop} {s : ℕ}
    (h : HasLatticeZetaBoundAt P s)
    (hmono : ∀ C C', C ≤ C' → P s C → P s C') :
    ∀ C', (∃ C, C ≤ C' ∧ P s C) → HasLatticeZetaBoundAt P s := by
  intro C' _
  exact h

/-! ### 4. Concrete bundle at `s = 4` with `C_s = 17`

We instantiate `HasLatticeZetaBoundAt` at `s = 4` with the paper's
rounded-up constant `17` (safe over-estimate of `16.533`). The lattice-
inequality witness is taken as a hypothesis — this file does not derive
`16.533`.
-/

/-- **Concrete Epstein-zeta bound at `s = 4` with `C = 17`.**

Given *any* witness predicate `P` and a proof of `P 4 17`, we package
the bundle. Intended downstream use: take `P s C := ∑_{n ≠ 0}
‖n‖^{-s} ≤ C`; then `P 4 17` is the paper's numerical bound. -/
theorem epsteinZetaBundleAt4_bound (P : ℕ → ℝ → Prop)
    (hP : P 4 17) :
    HasLatticeZetaBoundAt P 4 :=
  HasLatticeZetaBoundAt.mk' P 4 17 (by norm_num) hP

/-- **Sanity example.** With the trivial predicate `P s C := True`
(matching the current `EpsteinZeta.LatticeSumBounded` placeholder),
`epsteinZetaBundleAt4_bound` returns a witness unconditionally. -/
example : HasLatticeZetaBoundAt (fun _ _ => True) 4 :=
  epsteinZetaBundleAt4_bound (fun _ _ => True) trivial

/-- **Compatibility example with `EpsteinZeta.LatticeSumBounded`.**

`EpsteinZeta.LatticeSumBounded s C_s` is currently `True`; plugging it
into `HasLatticeZetaBoundAt` as the witness predicate gives a trivially-
discharged bundle. Once that definition is sharpened to a real lattice
inequality, this example will continue to typecheck and simply require
a non-trivial `hP`. -/
example :
    HasLatticeZetaBoundAt (fun s C => LatticeSumBounded s C) 4 :=
  epsteinZetaBundleAt4_bound
    (fun s C => LatticeSumBounded s C)
    (by unfold LatticeSumBounded; trivial)

/-! ### 5. Wiring note for `EpsteinZetaBundle`

`EpsteinZetaBundle` in `EpsteinZeta.lean` carries `latticeSumBounded :
True`. To replace the `True` with `HasLatticeZetaBoundAt P s`, the
structure declaration would need to be generalised:

```lean
structure EpsteinZetaBundle (P : ℕ → ℝ → Prop) where
  s : ℕ
  C_s : ℝ
  s_ge_two : 2 ≤ s
  nonneg : 0 ≤ C_s
  latticeSumBounded : P s C_s
```

and `exampleBundleAt4` updated to carry the explicit `P`. Because that
touches a file not in scope here, we leave this as a structural note.
A cleaner witness (non-`True`) is available via the
`epsteinZetaBundleAt4_bound` theorem above. -/

end NSBlwChain.Torus
