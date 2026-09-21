import Mathlib
import LittlewoodInverse.External

/-!
# Finite repeated extraction

The combinatorial termination argument in Lemma 5.1 of the manuscript.
The local extraction hypothesis is explicit; it will be supplied by BSG.
-/

open scoped BigOperators Pointwise

namespace LittlewoodInverse

theorem finite_peeling {α : Type*} [DecidableEq α]
    (X : Finset α) (P : Finset α → Prop) (a b : ℝ) (ha : 0 < a)
    (extract : ∀ Y ⊆ X, b ≤ (Y.card : ℝ) →
      ∃ Z ⊆ Y, a ≤ (Z.card : ℝ) ∧ P Z) :
    ∃ blocks : Finset (Finset α),
      (∀ Z ∈ blocks, Z ⊆ X ∧ a ≤ (Z.card : ℝ) ∧ P Z) ∧
      (∀ U ∈ blocks, ∀ V ∈ blocks, U ≠ V → Disjoint U V) ∧
      ((X \ blocks.biUnion id).card : ℝ) < b := by
  classical
  induction X using Finset.strongInductionOn with
  | _ X ih =>
    by_cases hsmall : (X.card : ℝ) < b
    · exact ⟨∅, by simp, by simp, by simpa using hsmall⟩
    · obtain ⟨Z, hZX, hsize, hP⟩ := extract X (Finset.Subset.refl _) (le_of_not_gt hsmall)
      have hZ : Z.Nonempty := Finset.card_pos.mp (by exact_mod_cast (ha.trans_le hsize))
      obtain ⟨blocks, hblocks, hdisjoint, hrem⟩ :=
        ih (X \ Z) (Finset.sdiff_ssubset hZX hZ) (fun Y hYX hY =>
          extract Y (hYX.trans Finset.sdiff_subset) hY)
      have hZnot : Z ∉ blocks := by
        intro hz
        obtain ⟨z, hz⟩ := hZ
        exact (Finset.mem_sdiff.mp ((hblocks Z ‹Z ∈ blocks›).1 hz)).2 hz
      refine ⟨insert Z blocks, ?_, ?_, ?_⟩
      · intro U hU
        rcases Finset.mem_insert.mp hU with rfl | hU
        · exact ⟨hZX, hsize, hP⟩
        · exact ⟨((hblocks U hU).1.trans Finset.sdiff_subset), (hblocks U hU).2⟩
      · intro U hU V hV hUV
        by_cases hu : U = Z
        · subst U
          have hv : V ∈ blocks := (Finset.mem_insert.mp hV).resolve_left (Ne.symm hUV)
          exact Finset.disjoint_left.mpr (by
            intro z hzZ hzV
            exact (Finset.mem_sdiff.mp ((hblocks V hv).1 hzV)).2 hzZ)
        · have hu' : U ∈ blocks := (Finset.mem_insert.mp hU).resolve_left hu
          by_cases hv : V = Z
          · subst V
            exact Finset.disjoint_left.mpr (by
              intro z hzU hzZ
              exact (Finset.mem_sdiff.mp ((hblocks U hu').1 hzU)).2 hzZ)
          · exact hdisjoint U hu' V ((Finset.mem_insert.mp hV).resolve_left hv) hUV
      · have heq : X \ (insert Z blocks).biUnion id = (X \ Z) \ blocks.biUnion id := by
          ext x
          simp only [Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_insert, id_eq]
          aesop
        simpa only [heq] using hrem

theorem disjoint_block_count {α : Type*} [DecidableEq α]
    (X : Finset α) (blocks : Finset (Finset α)) (a : ℝ)
    (hsub : ∀ Z ∈ blocks, Z ⊆ X)
    (hsize : ∀ Z ∈ blocks, a ≤ (Z.card : ℝ))
    (hdisjoint : ∀ U ∈ blocks, ∀ V ∈ blocks, U ≠ V → Disjoint U V) :
    (blocks.card : ℝ) * a ≤ (X.card : ℝ) := by
  classical
  calc
    (blocks.card : ℝ) * a = ∑ Z ∈ blocks, a := by simp
    _ ≤ ∑ Z ∈ blocks, (Z.card : ℝ) := Finset.sum_le_sum hsize
    _ = ((blocks.biUnion id).card : ℝ) := by
      rw [Finset.card_biUnion]
      · simp
      · intro U hU V hV hUV
        exact hdisjoint U hU V hV hUV
    _ ≤ (X.card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.biUnion_subset.mpr hsub)

/-- Lemma 5.1 with the BSG constants left explicit.  The size loss is
`c * (η * δ)^C * δ`; it depends only on `η, δ` and absolute BSG constants.
No Fourier norm of a remainder is assumed. -/
theorem hereditary_energy_cover : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ {G : Type} [AddCommGroup G] [DecidableEq G]
      (X : Finset G), X.Nonempty → ∀ η δ : ℝ,
      0 < η → η ≤ 1 → 0 < δ → δ < 1 →
      (∀ Y ⊆ X, Y.Nonempty → η * (Y.card : ℝ)^4 / (X.card : ℝ) ≤
        (additiveEnergy Y : ℝ)) →
      ∃ blocks : Finset (Finset G),
        (∀ Z ∈ blocks, Z ⊆ X ∧ Z.Nonempty ∧
          c * (η * δ)^C * δ * (X.card : ℝ) ≤ (Z.card : ℝ) ∧
          ((sumset Z).card : ℝ) ≤ C * (η * δ)^(-C) * (Z.card : ℝ)) ∧
        (∀ U ∈ blocks, ∀ V ∈ blocks, U ≠ V → Disjoint U V) ∧
        ((X \ blocks.biUnion id).card : ℝ) < δ * (X.card : ℝ) ∧
        (blocks.card : ℝ) * (c * (η * δ)^C * δ) ≤ 1 := by
  obtain ⟨c, C, hc, hC, hBSG⟩ := External.polynomial_bsg
  refine ⟨c, C, hc, hC, ?_⟩
  intro G _ _ X hX η δ hη hη1 hδ hδ1 hhered
  classical
  have hR : 0 < (X.card : ℝ) := by exact_mod_cast hX.card_pos
  have hγ : 0 < η * δ := mul_pos hη hδ
  have hγ1 : η * δ ≤ 1 := by nlinarith
  have hpow : 0 < (η * δ)^C := Real.rpow_pos_of_pos hγ C
  have ha : 0 < c * (η * δ)^C * δ * (X.card : ℝ) := by positivity
  obtain ⟨blocks, hblocks, hdisjoint, hrem⟩ :=
    finite_peeling X (fun Z => ((sumset Z).card : ℝ) ≤ C * (η * δ)^(-C) * (Z.card : ℝ))
      (c * (η * δ)^C * δ * (X.card : ℝ)) (δ * (X.card : ℝ)) ha (by
        intro Y hYX hlarge
        have hYpos : 0 < (Y.card : ℝ) := (mul_pos hδ hR).trans_le hlarge
        have hY : Y.Nonempty := Finset.card_pos.mp (by exact_mod_cast hYpos)
        have he : (η * δ) * (Y.card : ℝ)^3 ≤ (additiveEnergy Y : ℝ) := by
          calc
            (η * δ) * (Y.card : ℝ)^3 = (η * (Y.card : ℝ)^3) * δ := by ring
            _ ≤ (η * (Y.card : ℝ)^3) * ((Y.card : ℝ) / (X.card : ℝ)) := by
              gcongr
              exact (le_div_iff₀ hR).mpr hlarge
            _ = η * (Y.card : ℝ)^4 / (X.card : ℝ) := by ring
            _ ≤ (additiveEnergy Y : ℝ) := hhered Y hYX hY
        obtain ⟨Z, hZY, _, hsize, hdouble⟩ := hBSG Y hY (η * δ) hγ hγ1 he
        refine ⟨Z, hZY, ?_, hdouble⟩
        calc
          c * (η * δ)^C * δ * (X.card : ℝ) =
            (c * (η * δ)^C) * (δ * (X.card : ℝ)) := by ring
          _ ≤ (c * (η * δ)^C) * (Y.card : ℝ) :=
            mul_le_mul_of_nonneg_left hlarge (le_of_lt (mul_pos hc hpow))
          _ ≤ (Z.card : ℝ) := hsize)
  refine ⟨blocks, ?_, hdisjoint, hrem, ?_⟩
  · intro Z hZ
    obtain ⟨hZX, hsize, hdouble⟩ := hblocks Z hZ
    have hn : Z.Nonempty := Finset.card_pos.mp (by exact_mod_cast (ha.trans_le hsize))
    exact ⟨hZX, hn, hsize, hdouble⟩
  · have hcount := disjoint_block_count X blocks
        (c * (η * δ)^C * δ * (X.card : ℝ))
        (fun Z hZ => (hblocks Z hZ).1) (fun Z hZ => (hblocks Z hZ).2.1) hdisjoint
    apply (mul_le_mul_iff_left₀ hR).mp
    nlinarith [hcount]

end LittlewoodInverse
