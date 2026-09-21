import LittlewoodInverse.SlabCover
import LittlewoodInverse.FiniteCoverGluing
import LittlewoodInverse.CommonHeights

open scoped BigOperators

namespace LittlewoodInverse

variable (q : ℕ) [NeZero q]

noncomputable def inflatedSlabPartition (M : ℕ) (hM : 0 < M)
    (C : Finset (ZMod q × ℤ)) (U : Finset ℤ)
    (hU : ∀ b u, boundaryValue C (b, u) ≠ 0 → u ∈ U) :
    FiniteSetPartition (blockInflation q M C) where
  Index := U
  part i := blockInflation q M (cellSlab C U i)
  disjoint := by
    intro a b hab
    exact blockInflation_disjoint hM
      (cellSlab_disjoint C U a.property b.property (fun he => hab (Subtype.ext he)))
  covers := by
    intro x
    have he : blockInflation q M C = U.biUnion (fun a => blockInflation q M (cellSlab C U a)) := by
      rw [← blockInflation_biUnion, cellSlabs_cover C U hU]
    rw [he]
    simp only [Finset.mem_biUnion, Subtype.exists, exists_prop]

/-- All quantitative parameters are chosen before the modulus, cell set,
inflation length, and slab decomposition. The inputs here are just a bound on
the number of boundary heights and on the actual residue-slice norms. -/
theorem block_cover_of_height_bounds (v B ε : ℝ) (hv : 0 < v) (hB : 1 ≤ B)
    (hε : 0 < ε) (hε1 : ε < 1) : ∃ c D : ℝ, 0 < c ∧ 0 < D ∧
      ∀ (q : ℕ) [NeZero q] (M : ℕ), 0 < M →
        ∀ C : Finset (ZMod q × ℤ), C.Nonempty → ∀ U : Finset ℤ,
          (∀ b u, boundaryValue C (b, u) ≠ 0 → u ∈ U) →
          (U.card : ℝ) ≤ v →
          (∀ u ∈ U, cyclicLittlewoodNorm q (cellResidues C u) ≤ B) →
            AlmostCover (blockInflation q M C) ε c D := by
  obtain ⟨c, D, hc, hD, hcover⟩ := uniform_slab_cover B (ε / 2) hB
    (by positivity) (by linarith)
  refine ⟨c * (ε / (2 * v)), max D (v * D), by positivity,
    lt_of_lt_of_le hD (le_max_left _ _), ?_⟩
  intro q _ M hM C hC U hU hcount hnorm
  let P := inflatedSlabPartition q M hM C U hU
  have hA : (blockInflation q M C).Nonempty := by
    apply Finset.card_pos.mp
    rw [blockInflation_card q hM C]
    exact Nat.mul_pos hM hC.card_pos
  apply bounded_partition_almost_cover hA P hv (by simpa [P, inflatedSlabPartition] using hcount)
    hε hc.le hD.le
  intro i hi
  change {u // u ∈ U} at i
  change (blockInflation q M (cellSlab C U i.val)).Nonempty at hi
  change AlmostCover (blockInflation q M (cellSlab C U i.val)) (ε / 2) c D
  rw [inflated_cellSlab M hM] at hi ⊢
  have hp := hi.card_pos
  rw [arithmeticSlab_card] at hp
  have hX : 0 < (cellResidues C i.val).card := by
    by_contra h
    have he : (cellResidues C i.val).card = 0 := by omega
    simp only [he, zero_mul, lt_self_iff_false] at hp
  have hL : 0 < M * (nextSlabHeight U i.val - i.val).toNat := by
    by_contra h
    have he : M * (nextSlabHeight U i.val - i.val).toNat = 0 := by omega
    simp only [he, mul_zero, lt_self_iff_false] at hp
  exact hcover q (cellResidues C i.val) _ _ (Finset.card_pos.mp hX) hL (hnorm i.val i.property)

/-- The long-block terminal covering theorem, with all constants chosen
uniformly before the modulus and the actual integer set. -/
theorem long_block_almost_cover (K ε : ℝ) (hK : 1 ≤ K)
    (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ (N₀ : ℕ) (c D : ℝ), 0 < c ∧ 0 < D ∧
      ∀ (q : ℕ) [NeZero q] (M : ℕ), 0 < M →
        ∀ C : Finset (ZMod q × ℤ), C.Nonempty → C.card ≤ M →
          N₀ ≤ (blockInflation q M C).card →
          littlewoodNorm (blockInflation q M C) ≤
            K * Real.log ((blockInflation q M C).card : ℝ) →
          AlmostCover (blockInflation q M C) ε c D := by
  obtain ⟨k, hk, hheight⟩ := exists_boundary_height_bound
  let S := 8 * Real.pi * K
  let v := Real.exp (k * S)
  let B := max 1 (v * S)
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hv : 0 < v := Real.exp_pos _
  obtain ⟨c, D, hc, hD, hcover⟩ := block_cover_of_height_bounds v B ε hv
    (le_max_left _ _) hε hε1
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (Real.exp (32 * Real.pi + 4))
  refine ⟨N₀, c, D, hc, hD, ?_⟩
  intro q _ M hM C hC hMC hlarge hnorm
  have hcard : Real.exp (32 * Real.pi + 4) ≤ ((blockInflation q M C).card : ℝ) :=
    hN₀.trans (by exact_mod_cast hlarge)
  have hbudget : boundaryNorm q C ≤ S :=
    constant_boundary_budget q hC hMC (by linarith) hcard hnorm
  have hvcount : ((boundaryHeights C).card : ℝ) ≤ v := by
    calc
      _ ≤ Real.exp (k * boundaryNorm q C) := hheight q C
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hbudget hk.le)
  apply hcover q M hM C hC (boundaryHeights C)
    (fun b u hu => (mem_boundaryHeights C u).mpr ⟨b, hu⟩) hvcount
  intro u _hu
  calc
    _ ≤ (boundaryHeights C).card * boundaryNorm q C := cellResidues_norm_le_boundary q C u
    _ ≤ v * S := mul_le_mul hvcount hbudget (boundaryNorm_nonneg q C) hv.le
    _ ≤ _ := le_max_right _ _

end LittlewoodInverse
