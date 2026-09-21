import LittlewoodInverse.Statements
import LittlewoodInverse.NormBounds

open scoped symmDiff Pointwise

namespace LittlewoodInverse

theorem card_sdiff_le_symmDiff (A B : Finset ℤ) : (A \ B).card ≤ (A ∆ B).card := by
  rw [Finset.symmDiff_def]
  exact Finset.card_le_card Finset.subset_union_left

theorem card_le_card_add_symmDiff (A B : Finset ℤ) : A.card ≤ B.card + (A ∆ B).card := by
  have hh := Finset.card_sdiff_add_card_inter A B
  have hi := Finset.card_le_card (Finset.inter_subset_right : A ∩ B ⊆ B)
  have hs := card_sdiff_le_symmDiff A B
  omega

/-- The finite stability argument in Corollary 9.3. Intersecting each
covering piece with the new set preserves every covering condition. -/
theorem almostCover_intersect {A B : Finset ℤ} {ε δ c C : ℝ}
    (hB : B.Nonempty) (hc : 0 < c) (hC : 0 ≤ C)
    (hcover : AlmostCover B ε c C)
    (hcard : (A.card : ℝ) ≤ 2*(B.card : ℝ))
    (hsmall : ((A ∆ B).card : ℝ) ≤ c*(B.card : ℝ)/2)
    (hrem : ((A ∆ B).card : ℝ) + ε*(B.card : ℝ) ≤ δ*(A.card : ℝ)) :
    AlmostCover A δ (c/4) (2*C) := by
  classical
  obtain ⟨blocks,hblocks,hdis,hrest,hcount⟩ := hcover
  have hbpos : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
  have hpiece (S : Finset ℤ) (hS : S ∈ blocks) :
      (S.card : ℝ)/2 ≤ ((S ∩ A).card : ℝ) := by
    have hs := (hblocks S hS).1
    have hdel : (S \ A).card ≤ (A ∆ B).card := by
      calc
        _ ≤ (B \ A).card := Finset.card_le_card (Finset.sdiff_subset_sdiff hs (Finset.Subset.refl _))
        _ ≤ (B ∆ A).card := card_sdiff_le_symmDiff B A
        _ = _ := by rw [symmDiff_comm]
    have hsplit : ((S \ A).card : ℝ)+((S ∩ A).card : ℝ) = S.card := by
      exact_mod_cast Finset.card_sdiff_add_card_inter S A
    have hdel' : ((S \ A).card : ℝ) ≤ (A ∆ B).card := by exact_mod_cast hdel
    have hsize := (hblocks S hS).2.2.1
    linarith
  refine ⟨blocks.image (fun S => S ∩ A),?_,?_,?_,?_⟩
  · intro D hD
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hD
    obtain ⟨hs,hsne,hsize,hdouble⟩ := hblocks S hS
    have hh := hpiece S hS
    have hspos : (0 : ℝ) < S.card := by exact_mod_cast hsne.card_pos
    have hne : (S ∩ A).Nonempty := Finset.card_pos.mp (by exact_mod_cast (show
      (0 : ℝ) < (S ∩ A).card by linarith))
    refine ⟨Finset.inter_subset_right,hne,?_,?_⟩
    · have hm := mul_le_mul_of_nonneg_left hcard hc.le
      nlinarith
    · have hsumsub : sumset (S ∩ A) ⊆ sumset S :=
        Finset.add_subset_add Finset.inter_subset_left Finset.inter_subset_left
      have hsum : ((sumset (S ∩ A)).card : ℝ) ≤ (sumset S).card := by
        exact_mod_cast Finset.card_le_card hsumsub
      have hm := mul_le_mul_of_nonneg_left hh hC
      nlinarith
  · intro U hU V hV hUV
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hU
    obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hV
    exact (hdis S hS T hT (fun he => hUV (congrArg (fun S => S ∩ A) he))).mono
      Finset.inter_subset_left Finset.inter_subset_left
  · have hsub : A \ (blocks.image (fun S => S ∩ A)).biUnion id ⊆
        (A \ B) ∪ (B \ blocks.biUnion id) := by
      intro x hx
      have hxa := (Finset.mem_sdiff.mp hx).1
      by_cases hxb : x ∈ B
      · apply Finset.mem_union_right
        refine Finset.mem_sdiff.mpr ⟨hxb,?_⟩
        intro hxu
        obtain ⟨S,hS,hxS⟩ := Finset.mem_biUnion.mp hxu
        exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_biUnion.mpr
          ⟨S ∩ A,Finset.mem_image.mpr ⟨S,hS,rfl⟩,Finset.mem_inter.mpr ⟨hxS,hxa⟩⟩)
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hxa,hxb⟩)
    have hh : ((A \ (blocks.image (fun S => S ∩ A)).biUnion id).card : ℝ) ≤
        ((A \ B).card : ℝ)+((B \ blocks.biUnion id).card : ℝ) := by
      exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hs : ((A \ B).card : ℝ) ≤ (A ∆ B).card := by exact_mod_cast card_sdiff_le_symmDiff A B
    linarith
  · have hh : ((blocks.image (fun S => S ∩ A)).card : ℝ) ≤ blocks.card := by
      exact_mod_cast Finset.card_image_le
    linarith

end LittlewoodInverse
