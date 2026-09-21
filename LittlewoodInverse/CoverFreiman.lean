import LittlewoodInverse.FreimanFinite
import LittlewoodInverse.Statements

open scoped Pointwise

namespace LittlewoodInverse

/-- All parts of the covering conclusion are preserved by a two-Freiman isomorphism. -/
theorem almostCover_freiman_map {A A' : Finset ℤ} {f : ℤ → ℤ}
    (hf : IsAddFreimanIso 2 (A : Set ℤ) (A' : Set ℤ) f)
    {ε c C : ℝ} (hcover : AlmostCover A ε c C) : AlmostCover A' ε c C := by
  classical
  have hA : A.image f = A' := by
    apply Finset.coe_injective
    simpa only [Finset.coe_image] using hf.bijOn.image_eq
  have hcard (B : Finset ℤ) (hB : B ⊆ A) : (B.image f).card = B.card :=
    Finset.card_image_of_injOn (fun x hx y hy hxy => hf.bijOn.injOn (hB hx) (hB hy) hxy)
  have hAcard : A'.card = A.card := by rw [← hA]; exact hcard A (Finset.Subset.refl _)
  obtain ⟨blocks, hb, hd, hr, hn⟩ := hcover
  let mapped := blocks.image (fun B => B.image f)
  have hunionsub : blocks.biUnion id ⊆ A := by
    intro x hx
    obtain ⟨B, hB, hxB⟩ := Finset.mem_biUnion.mp hx
    exact (hb B hB).1 hxB
  have hunion : mapped.biUnion id = (blocks.biUnion id).image f := by
    simp only [mapped, Finset.image_biUnion, Finset.biUnion_image, id_eq]
  refine ⟨mapped, ?_, ?_, ?_, ?_⟩
  · intro D hD
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hD
    obtain ⟨hBA, hBne, hsize, hdouble⟩ := hb B hB
    refine ⟨?_, hBne.image f, ?_, ?_⟩
    · rw [← hA]
      exact Finset.image_subset_image hBA
    · simpa only [hcard B hBA, hAcard] using hsize
    · have hs := freiman_sumset_card hf hBA
      simpa only [sumset, hcard B hBA, ← hs] using hdouble
  · intro D hD E hE hDE
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hD
    obtain ⟨U, hU, rfl⟩ := Finset.mem_image.mp hE
    have hBU : B ≠ U := fun h => hDE (congrArg (fun X : Finset ℤ => X.image f) h)
    apply Finset.disjoint_left.mpr
    intro y hyB hyU
    obtain ⟨b, hbB, rfl⟩ := Finset.mem_image.mp hyB
    obtain ⟨u, huU, hfu⟩ := Finset.mem_image.mp hyU
    have hu : u = b := hf.bijOn.injOn ((hb U hU).1 huU) ((hb B hB).1 hbB) hfu
    subst u
    exact Finset.disjoint_left.mp (hd B hB U hU hBU) hbB huU
  · rw [hunion, ← hA, ← Finset.image_sdiff_of_injOn hf.bijOn.injOn hunionsub,
      hcard _ Finset.sdiff_subset, hcard A (Finset.Subset.refl _)]
    exact hr
  · exact (Nat.cast_le.mpr (Finset.card_image_le : mapped.card ≤ blocks.card)).trans hn

theorem almostCover_freiman_iff {A A' : Finset ℤ} {f : ℤ → ℤ}
    (hf : IsAddFreimanIso 2 (A : Set ℤ) (A' : Set ℤ) f) {ε c C : ℝ} :
    AlmostCover A ε c C ↔ AlmostCover A' ε c C :=
  ⟨almostCover_freiman_map hf, almostCover_freiman_map hf.invFunOn⟩

end LittlewoodInverse
