-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).

import Mathlib

/-!
# Concrete 3D Epstein-zeta lattice bound (discharges `EpsteinZeta.LatticeSumBounded`)

This file proves, **unconditionally and with zero axioms**, the 3D lattice
Epstein-zeta bound that `NSBlwChain/Torus/EpsteinZeta.lean` previously carried
as the vacuous placeholder `LatticeSumBounded s C := True`:

  for every real `s > 3` and every finite `A ⊆ ℤ³ \ {0}`,
    `∑_{a ∈ A} ‖a‖^{-s} ≤ latticeZetaConstZ3 s`,

where `‖·‖` is the Euclidean norm on `ℤ³ = (Fin 3 → ℤ)` and

  `latticeZetaConstZ3 s := 54 · ∑'_{k} k^{-(s-2)}`.

Both the constant's finiteness (`s > 3 ⟹ s - 2 > 1`, a `p`-series) and the
per-finset bound are proved here. For the paper's `s = 4` application this
gives a genuine, if loose, constant `latticeZetaConstZ3 4 = 54 · ζ(2) = 9π²`
(≈ 88.8) — the tabulated Glasser–Zucker value `ζ_{ℤ³}(4) ≈ 16.533` is the
*exact* sum; `9π²` is the crude shell-counting over-estimate this proof yields.
The consumer (`torus_corrected_bound`) only needs *a* finite upper bound.

## Strategy (mirrors the SQG project's `RieszTorus.lean` §11.26.A–H, ℤ² → ℤ³)

Partition `ℤ³ \ {0}` by `ℓ∞`-radius into annular shells. On shell `k` the
`ℓ∞`-boundary has `≤ 6·(2k+1)² ≤ 54 k²` points (for `k ≥ 1`) and Euclidean
norm `≥ k`, so

  `∑_{a ∈ shell k} ‖a‖^{-s} ≤ 54 k² · k^{-s} = 54 k^{-(s-2)}`.

Summing over `k ≥ 1` gives `54 · ∑ k^{-(s-2)}`, finite for `s > 3` via
mathlib's `Real.summable_one_div_nat_rpow`. Any finite `A ⊆ ℤ³ \ {0}` is
covered by the (finite) union of the shells its points land in, and the
shells are pairwise disjoint, so the finite sum is bounded by the `tsum`.

## References

* `sqg-lean-proofs/SqgIdentity/RieszTorus.lean` §11.26.A–H (the ℤ² original).
* `NSBlwChain/Torus/EpsteinZeta.lean` open discharge #1 (this closes it).
* `paper/ns_regularity_blw_derivations.md` §D.4.
-/

namespace NSBlwChain.Torus

/-! ### 1. Euclidean lattice norm on `ℤ³` -/

/-- Squared Euclidean norm of a `ℤ³` lattice point. -/
noncomputable def latticeNormSqZ3 (n : Fin 3 → ℤ) : ℝ :=
  ∑ i : Fin 3, (n i : ℝ) ^ 2

/-- Euclidean norm of a `ℤ³` lattice point. -/
noncomputable def latticeNormZ3 (n : Fin 3 → ℤ) : ℝ :=
  Real.sqrt (latticeNormSqZ3 n)

lemma latticeNormSqZ3_nonneg (n : Fin 3 → ℤ) : 0 ≤ latticeNormSqZ3 n :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma latticeNormZ3_nonneg (n : Fin 3 → ℤ) : 0 ≤ latticeNormZ3 n :=
  Real.sqrt_nonneg _

/-- Each coordinate's absolute value is bounded by the Euclidean norm. -/
lemma abs_coord_le_latticeNormZ3 (n : Fin 3 → ℤ) (j : Fin 3) :
    |(n j : ℝ)| ≤ latticeNormZ3 n := by
  have h_sq : (n j : ℝ) ^ 2 ≤ latticeNormSqZ3 n :=
    Finset.single_le_sum (f := fun i => (n i : ℝ) ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  calc |(n j : ℝ)| = Real.sqrt ((n j : ℝ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (latticeNormSqZ3 n) := Real.sqrt_le_sqrt h_sq
    _ = latticeNormZ3 n := rfl

/-! ### 2. Annular `ℓ∞`-shell in `ℤ³` -/

/-- Annular shell at `ℓ∞`-radius `k`: nonzero lattice points with all
coordinates in `[-k, k]` and at least one coordinate of absolute value `k`. -/
noncomputable def annularShellZ3 (k : ℕ) : Finset (Fin 3 → ℤ) :=
  (Fintype.piFinset fun _ : Fin 3 => Finset.Icc (-(k : ℤ)) (k : ℤ)).filter
    (fun m => m ≠ 0 ∧ (|m 0| = (k : ℤ) ∨ |m 1| = (k : ℤ) ∨ |m 2| = (k : ℤ)))

lemma mem_annularShellZ3_iff (k : ℕ) (m : Fin 3 → ℤ) :
    m ∈ annularShellZ3 k ↔
      (∀ i : Fin 3, |m i| ≤ (k : ℤ)) ∧ m ≠ 0
        ∧ (|m 0| = (k : ℤ) ∨ |m 1| = (k : ℤ) ∨ |m 2| = (k : ℤ)) := by
  unfold annularShellZ3
  simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc]
  constructor
  · rintro ⟨h_Icc, h_ne, h_max⟩
    exact ⟨fun i => abs_le.mpr (h_Icc i), h_ne, h_max⟩
  · rintro ⟨h_max, h_ne, h_eq⟩
    exact ⟨fun i => ⟨(abs_le.mp (h_max i)).1, (abs_le.mp (h_max i)).2⟩, h_ne, h_eq⟩

/-- On shell `k`, the Euclidean norm is at least `k`. -/
lemma latticeNormZ3_ge_of_mem (k : ℕ) (m : Fin 3 → ℤ)
    (hm : m ∈ annularShellZ3 k) : (k : ℝ) ≤ latticeNormZ3 m := by
  rw [mem_annularShellZ3_iff] at hm
  obtain ⟨_, _, hmax⟩ := hm
  have coord : ∀ i : Fin 3, |m i| = (k : ℤ) → (k : ℝ) ≤ latticeNormZ3 m := by
    intro i hi
    have h_abs : |(m i : ℝ)| = (k : ℝ) := by
      have h_cast : ((|m i| : ℤ) : ℝ) = ((k : ℤ) : ℝ) := by exact_mod_cast hi
      simpa [Int.cast_abs] using h_cast
    calc (k : ℝ) = |(m i : ℝ)| := h_abs.symm
      _ ≤ latticeNormZ3 m := abs_coord_le_latticeNormZ3 m i
  rcases hmax with h | h | h
  · exact coord 0 h
  · exact coord 1 h
  · exact coord 2 h

/-- Shell at level `0` is empty. -/
lemma annularShellZ3_zero : annularShellZ3 0 = ∅ := by
  unfold annularShellZ3
  apply Finset.eq_empty_of_forall_notMem
  intro m hm
  rw [Finset.mem_filter, Fintype.mem_piFinset] at hm
  obtain ⟨h_Icc, h_ne, _⟩ := hm
  apply h_ne
  funext i
  have h := h_Icc i
  rw [Finset.mem_Icc, Nat.cast_zero, neg_zero] at h
  exact le_antisymm h.2 h.1

/-- Cardinality bound: `|shell k| ≤ 6·(2k+1)²`.

The shell is contained in the union over the three coordinate directions of
`{m : |m i| = k}`; each such single-coordinate slice has at most
`2·(2k+1)²` points (`m i = ±k`, the other two coordinates free in a set of
size `2k+1`). -/
lemma card_annularShellZ3_le (k : ℕ) :
    (annularShellZ3 k).card ≤ 6 * (2 * k + 1) ^ 2 := by
  classical
  unfold annularShellZ3
  -- Step 1: drop `m ≠ 0` (enlarges the set).
  have h_sub :
      (Finset.filter
          (fun m : Fin 3 → ℤ =>
            m ≠ 0 ∧ (|m 0| = (k : ℤ) ∨ |m 1| = (k : ℤ) ∨ |m 2| = (k : ℤ)))
          (Fintype.piFinset fun _ : Fin 3 => Finset.Icc (-(k : ℤ)) (k : ℤ))).card
      ≤ (Finset.filter
          (fun m : Fin 3 → ℤ => |m 0| = (k : ℤ) ∨ |m 1| = (k : ℤ) ∨ |m 2| = (k : ℤ))
          (Fintype.piFinset fun _ : Fin 3 => Finset.Icc (-(k : ℤ)) (k : ℤ))).card := by
    apply Finset.card_le_card
    intro m hm
    simp only [Finset.mem_filter] at hm ⊢
    exact ⟨hm.1, hm.2.2⟩
  refine le_trans h_sub ?_
  -- Single-coordinate slice bound: `|{m : |m i| = k}| ≤ 2·(2k+1)²`.
  have h_each : ∀ i : Fin 3,
      (Finset.filter (fun m : Fin 3 → ℤ => |m i| = (k : ℤ))
        (Fintype.piFinset fun _ : Fin 3 => Finset.Icc (-(k : ℤ)) (k : ℤ))).card
        ≤ 2 * (2 * k + 1) ^ 2 := by
    intro i
    have h_filter_split :
        Finset.filter (fun m : Fin 3 → ℤ => |m i| = (k : ℤ))
            (Fintype.piFinset fun _ : Fin 3 => Finset.Icc (-(k : ℤ)) (k : ℤ))
          = Finset.filter (fun m : Fin 3 → ℤ => m i = (k : ℤ) ∨ m i = -(k : ℤ))
            (Fintype.piFinset fun _ : Fin 3 => Finset.Icc (-(k : ℤ)) (k : ℤ)) := by
      apply Finset.filter_congr
      intro m _
      rw [abs_eq (by positivity : (0 : ℤ) ≤ (k : ℤ))]
    rw [h_filter_split, Finset.filter_or]
    refine le_trans (Finset.card_union_le _ _) ?_
    have h_card_pt : ∀ a : ℤ,
        (Finset.filter (fun m : Fin 3 → ℤ => m i = a)
          (Fintype.piFinset fun _ : Fin 3 => Finset.Icc (-(k : ℤ)) (k : ℤ))).card
          ≤ (2 * k + 1) ^ 2 := by
      intro a
      by_cases ha : a ∈ Finset.Icc (-(k : ℤ)) (k : ℤ)
      · rw [Fintype.card_filter_piFinset_eq_of_mem
          (s := fun _ : Fin 3 => Finset.Icc (-(k : ℤ)) (k : ℤ)) i ha]
        rw [Finset.prod_const]
        have h_erase_card : ((Finset.univ : Finset (Fin 3)).erase i).card = 2 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
              Fintype.card_fin]
        rw [h_erase_card, Int.card_Icc]
        have h_toNat : ((k : ℤ) + 1 - -(k : ℤ)).toNat = 2 * k + 1 := by omega
        rw [h_toNat]
      · have h_empty : Finset.filter (fun m : Fin 3 → ℤ => m i = a)
            (Fintype.piFinset fun _ : Fin 3 => Finset.Icc (-(k : ℤ)) (k : ℤ)) = ∅ :=
          Fintype.filter_piFinset_of_notMem
            (fun _ : Fin 3 => Finset.Icc (-(k : ℤ)) (k : ℤ)) i a ha
        rw [h_empty, Finset.card_empty]
        positivity
    have h_k := h_card_pt (k : ℤ)
    have h_neg_k := h_card_pt (-(k : ℤ))
    omega
  -- Step 2: split the (right-associated) ternary disjunction and sum the
  -- three slice bounds.
  rw [Finset.filter_or]
  refine le_trans (Finset.card_union_le _ _) ?_
  rw [Finset.filter_or]
  have hunion := Finset.card_union_le
    (Finset.filter (fun m : Fin 3 → ℤ => |m 1| = (k : ℤ))
      (Fintype.piFinset fun _ : Fin 3 => Finset.Icc (-(k : ℤ)) (k : ℤ)))
    (Finset.filter (fun m : Fin 3 → ℤ => |m 2| = (k : ℤ))
      (Fintype.piFinset fun _ : Fin 3 => Finset.Icc (-(k : ℤ)) (k : ℤ)))
  have e0 := h_each 0
  have e1 := h_each 1
  have e2 := h_each 2
  omega

/-! ### 3. Per-shell rpow bound -/

/-- For `k ≥ 1` and `s > 3`,
`∑_{m ∈ shell k} ‖m‖^{-s} ≤ 54 · k^{-(s-2)}`. -/
lemma sum_annularShellZ3_rpow_le {s : ℝ} (hs : 3 < s) {k : ℕ} (hk : 1 ≤ k) :
    ∑ m ∈ annularShellZ3 k, (latticeNormZ3 m) ^ (-s)
      ≤ 54 * (1 / (k : ℝ) ^ (s - 2)) := by
  have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk
  have hk_nn : (0 : ℝ) ≤ k := le_of_lt hk_pos
  have hk_one : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hs_nn : (0 : ℝ) ≤ s := by linarith
  -- Pointwise: `(‖m‖)^{-s} ≤ k^{-s}` on the shell.
  have h_pointwise : ∀ m ∈ annularShellZ3 k,
      (latticeNormZ3 m) ^ (-s) ≤ ((k : ℝ) ^ (-s)) := by
    intro m hm
    have h_lb : (k : ℝ) ≤ latticeNormZ3 m := latticeNormZ3_ge_of_mem k m hm
    have h_m_pos : 0 < latticeNormZ3 m := lt_of_lt_of_le hk_pos h_lb
    rw [Real.rpow_neg hk_nn, Real.rpow_neg (le_of_lt h_m_pos)]
    exact inv_anti₀ (Real.rpow_pos_of_pos hk_pos _)
      (Real.rpow_le_rpow hk_nn h_lb hs_nn)
  -- Combine `k²·k^{-s} = k^{-(s-2)}`.
  have h_pow : (k : ℝ) ^ (2 : ℕ) * (k : ℝ) ^ (-s) = 1 / (k : ℝ) ^ (s - 2) := by
    rw [← Real.rpow_natCast (k : ℝ) 2, ← Real.rpow_add hk_pos]
    rw [show ((2 : ℕ) : ℝ) + (-s) = -(s - 2) by push_cast; ring]
    rw [Real.rpow_neg hk_nn, inv_eq_one_div]
  have h_card_real : (((6 * (2 * k + 1) ^ 2 : ℕ)) : ℝ) ≤ 54 * (k : ℝ) ^ (2 : ℕ) := by
    push_cast
    nlinarith [hk_one, sq_nonneg ((k : ℝ) - 1),
      mul_nonneg (by linarith : (0 : ℝ) ≤ (k : ℝ) - 1) (by linarith : (0 : ℝ) ≤ 5 * (k : ℝ) + 1)]
  calc ∑ m ∈ annularShellZ3 k, (latticeNormZ3 m) ^ (-s)
      ≤ ∑ _m ∈ annularShellZ3 k, ((k : ℝ) ^ (-s)) := Finset.sum_le_sum h_pointwise
    _ = (annularShellZ3 k).card * ((k : ℝ) ^ (-s)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (((6 * (2 * k + 1) ^ 2 : ℕ)) : ℝ) * ((k : ℝ) ^ (-s)) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hk_nn _)
        exact_mod_cast card_annularShellZ3_le k
    _ ≤ 54 * (k : ℝ) ^ (2 : ℕ) * ((k : ℝ) ^ (-s)) := by
        apply mul_le_mul_of_nonneg_right h_card_real (Real.rpow_nonneg hk_nn _)
    _ = 54 * (1 / (k : ℝ) ^ (s - 2)) := by rw [mul_assoc, h_pow]

/-! ### 4. The lattice-zeta constant and the main bound -/

/-- The 3D lattice-zeta constant: `54 · ∑'_k k^{-(s-2)}`. Finite for `s > 3`. -/
noncomputable def latticeZetaConstZ3 (s : ℝ) : ℝ :=
  54 * ∑' (k : ℕ), 1 / ((k : ℝ) ^ (s - 2))

lemma latticeZetaConstZ3_nonneg (s : ℝ) : 0 ≤ latticeZetaConstZ3 s := by
  unfold latticeZetaConstZ3
  apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 54)
  apply tsum_nonneg
  intro k
  exact div_nonneg zero_le_one (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-! ### 4b. Shell-index function and its properties -/

/-- `ℓ∞`-radius of a lattice point. -/
def shellOfZ3 (m : Fin 3 → ℤ) : ℕ :=
  max (max (|m 0|).toNat (|m 1|).toNat) (|m 2|).toNat

lemma shellOfZ3_pos_of_ne_zero (m : Fin 3 → ℤ) (hm : m ≠ 0) : 1 ≤ shellOfZ3 m := by
  unfold shellOfZ3
  by_cases h0 : m 0 = 0
  · by_cases h1 : m 1 = 0
    · by_cases h2 : m 2 = 0
      · exact absurd (funext fun i => by fin_cases i <;> [exact h0; exact h1; exact h2]) hm
      · have hb : 1 ≤ (|m 2|).toNat := by have := abs_pos.mpr h2; omega
        exact le_trans hb (le_max_right _ _)
    · have hb : 1 ≤ (|m 1|).toNat := by have := abs_pos.mpr h1; omega
      exact le_trans hb (le_trans (le_max_right _ _) (le_max_left _ _))
  · have hb : 1 ≤ (|m 0|).toNat := by have := abs_pos.mpr h0; omega
    exact le_trans hb (le_trans (le_max_left _ _) (le_max_left _ _))

lemma mem_annularShellZ3_shellOf (m : Fin 3 → ℤ) (hm : m ≠ 0) :
    m ∈ annularShellZ3 (shellOfZ3 m) := by
  rw [mem_annularShellZ3_iff]
  refine ⟨?_, hm, ?_⟩
  · intro i
    have key : ∀ j : Fin 3, (|m j|).toNat ≤ shellOfZ3 m →
        |m j| ≤ ((shellOfZ3 m : ℕ) : ℤ) := by
      intro j hj
      have h_cast : ((|m j|).toNat : ℤ) = |m j| := Int.toNat_of_nonneg (abs_nonneg _)
      calc |m j| = ((|m j|).toNat : ℤ) := h_cast.symm
        _ ≤ ((shellOfZ3 m : ℕ) : ℤ) := by exact_mod_cast hj
    fin_cases i
    · exact key 0 (by unfold shellOfZ3; exact le_trans (le_max_left _ _) (le_max_left _ _))
    · exact key 1 (by unfold shellOfZ3; exact le_trans (le_max_right _ _) (le_max_left _ _))
    · exact key 2 (by unfold shellOfZ3; exact le_max_right _ _)
  · have attain : ∀ j : Fin 3, shellOfZ3 m = (|m j|).toNat → |m j| = ((shellOfZ3 m : ℕ) : ℤ) := by
      intro j hj
      have h_cast : ((|m j|).toNat : ℤ) = |m j| := Int.toNat_of_nonneg (abs_nonneg _)
      rw [hj]; exact h_cast.symm
    rcases max_choice (max (|m 0|).toNat (|m 1|).toNat) (|m 2|).toNat with h | h
    · rcases max_choice (|m 0|).toNat (|m 1|).toNat with h' | h'
      · exact Or.inl (attain 0 (by unfold shellOfZ3; rw [h, h']))
      · exact Or.inr (Or.inl (attain 1 (by unfold shellOfZ3; rw [h, h'])))
    · exact Or.inr (Or.inr (attain 2 (by unfold shellOfZ3; rw [h])))

lemma annularShellZ3_disjoint {k₁ k₂ : ℕ} (hne : k₁ ≠ k₂) :
    Disjoint (annularShellZ3 k₁) (annularShellZ3 k₂) := by
  rw [Finset.disjoint_left]
  intro m hm1 hm2
  rw [mem_annularShellZ3_iff] at hm1 hm2
  obtain ⟨h_Icc1, _, h_max1⟩ := hm1
  obtain ⟨h_Icc2, _, h_max2⟩ := hm2
  apply hne
  have a0 := h_Icc1 0; have a1 := h_Icc1 1; have a2 := h_Icc1 2
  have b0 := h_Icc2 0; have b1 := h_Icc2 1; have b2 := h_Icc2 2
  rcases h_max1 with h₁ | h₁ | h₁ <;> rcases h_max2 with h₂ | h₂ | h₂ <;>
    · have hz : (k₁ : ℤ) = (k₂ : ℤ) := by omega
      exact_mod_cast hz

/-- **Main bound.** For `s > 3`, every finite `A ⊆ ℤ³ \ {0}` satisfies
`∑_{a ∈ A} ‖a‖^{-s} ≤ latticeZetaConstZ3 s`. Unconditional, zero axioms. -/
theorem latticeSum_le_latticeZetaConstZ3 {s : ℝ} (hs : 3 < s)
    (A : Finset (Fin 3 → ℤ)) (hA0 : (0 : Fin 3 → ℤ) ∉ A) :
    ∑ a ∈ A, (latticeNormZ3 a) ^ (-s) ≤ latticeZetaConstZ3 s := by
  classical
  set K : Finset ℕ := A.image shellOfZ3 with hK_def
  -- Cover `A` by the shells its points land in.
  have h_sub : A ⊆ K.biUnion annularShellZ3 := by
    intro m hm
    have hm_ne : m ≠ 0 := fun h => hA0 (h ▸ hm)
    rw [Finset.mem_biUnion]
    exact ⟨shellOfZ3 m, Finset.mem_image.mpr ⟨m, hm, rfl⟩,
      mem_annularShellZ3_shellOf m hm_ne⟩
  have h_nn_term : ∀ a : Fin 3 → ℤ, 0 ≤ (latticeNormZ3 a) ^ (-s) :=
    fun a => Real.rpow_nonneg (latticeNormZ3_nonneg a) _
  have h_ext : ∑ a ∈ A, (latticeNormZ3 a) ^ (-s)
      ≤ ∑ a ∈ K.biUnion annularShellZ3, (latticeNormZ3 a) ^ (-s) :=
    Finset.sum_le_sum_of_subset_of_nonneg h_sub (fun a _ _ => h_nn_term a)
  -- Decompose the biUnion over pairwise-disjoint shells.
  have h_pairwise : (↑K : Set ℕ).PairwiseDisjoint annularShellZ3 :=
    fun _ _ _ _ hne => annularShellZ3_disjoint hne
  have h_biUnion :
      ∑ a ∈ K.biUnion annularShellZ3, (latticeNormZ3 a) ^ (-s)
        = ∑ k ∈ K, ∑ a ∈ annularShellZ3 k, (latticeNormZ3 a) ^ (-s) :=
    Finset.sum_biUnion h_pairwise
  rw [h_biUnion] at h_ext
  -- Every shell index in `K` is `≥ 1`.
  have h_k_pos : ∀ k ∈ K, 1 ≤ k := by
    intro k hk
    rw [hK_def, Finset.mem_image] at hk
    obtain ⟨m, hm, rfl⟩ := hk
    exact shellOfZ3_pos_of_ne_zero m (fun h => hA0 (h ▸ hm))
  -- Per-shell bound.
  have h_shell_bd : ∀ k ∈ K,
      ∑ a ∈ annularShellZ3 k, (latticeNormZ3 a) ^ (-s)
        ≤ 54 * (1 / (k : ℝ) ^ (s - 2)) :=
    fun k hk => sum_annularShellZ3_rpow_le hs (h_k_pos k hk)
  have h_shell_sum :
      ∑ k ∈ K, ∑ a ∈ annularShellZ3 k, (latticeNormZ3 a) ^ (-s)
        ≤ ∑ k ∈ K, 54 * (1 / (k : ℝ) ^ (s - 2)) :=
    Finset.sum_le_sum h_shell_bd
  -- Bridge the finite shell-index sum to the defining `tsum`.
  have h_summ : Summable (fun k : ℕ => 1 / ((k : ℝ) ^ (s - 2))) := by
    rw [Real.summable_one_div_nat_rpow]; linarith
  have h_nn_f : ∀ k : ℕ, 0 ≤ 1 / ((k : ℝ) ^ (s - 2)) :=
    fun k => div_nonneg zero_le_one (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have h_tsum : ∑ k ∈ K, 1 / ((k : ℝ) ^ (s - 2))
      ≤ ∑' (k : ℕ), 1 / ((k : ℝ) ^ (s - 2)) :=
    h_summ.sum_le_tsum K (fun k _ => h_nn_f k)
  calc ∑ a ∈ A, (latticeNormZ3 a) ^ (-s)
      ≤ ∑ k ∈ K, ∑ a ∈ annularShellZ3 k, (latticeNormZ3 a) ^ (-s) := h_ext
    _ ≤ ∑ k ∈ K, 54 * (1 / (k : ℝ) ^ (s - 2)) := h_shell_sum
    _ = 54 * ∑ k ∈ K, 1 / ((k : ℝ) ^ (s - 2)) := by rw [Finset.mul_sum]
    _ ≤ 54 * ∑' (k : ℕ), 1 / ((k : ℝ) ^ (s - 2)) :=
        mul_le_mul_of_nonneg_left h_tsum (by norm_num)
    _ = latticeZetaConstZ3 s := by rw [latticeZetaConstZ3]

/-- Convenience specialization at the paper's exponent `s = 4`. -/
theorem latticeSum_le_latticeZetaConstZ3_four
    (A : Finset (Fin 3 → ℤ)) (hA0 : (0 : Fin 3 → ℤ) ∉ A) :
    ∑ a ∈ A, (latticeNormZ3 a) ^ (-((4 : ℕ) : ℝ)) ≤ latticeZetaConstZ3 ((4 : ℕ) : ℝ) :=
  latticeSum_le_latticeZetaConstZ3 (by norm_num : (3 : ℝ) < ((4 : ℕ) : ℝ)) A hA0

end NSBlwChain.Torus
