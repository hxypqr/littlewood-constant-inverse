import LittlewoodInverse.AssemblyBudget
import LittlewoodInverse.Statements

open scoped BigOperators

namespace LittlewoodInverse

theorem almostCover_mono {A : Finset ℤ} {ε ε' c c' C C' : ℝ}
    (h : AlmostCover A ε c C) (hε : ε ≤ ε') (hc : c' ≤ c) (hC : C ≤ C') :
    AlmostCover A ε' c' C' := by
  obtain ⟨blocks, hb, hd, hr, hn⟩ := h
  refine ⟨blocks, ?_, hd, ?_, hn.trans hC⟩
  · intro B hB
    obtain ⟨hs, he, hsize, hdouble⟩ := hb B hB
    exact ⟨hs, he, (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg _)).trans hsize,
      hdouble.trans (mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg _))⟩
  · exact hr.trans (mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg _))

/-- The finite gluing step in Section 8.  Terminal covering theorems provide
the local covers; the two discarded-leaf estimates provide `hdiscard`. -/
theorem assembly_glue_covers {β Δ : ℝ} {A : Finset ℤ}
    (L : AssemblyLeafFamily β Δ A) [DecidableEq L.Index] (s : Finset L.Index)
    {ε η c C δ : ℝ} (hε : 0 ≤ ε) (hc : 0 ≤ c)
    (hsize : ∀ i ∈ s, δ * (A.card : ℝ) ≤ ((L.leaf i).card : ℝ))
    (hdiscard : (∑ i ∈ Finset.univ \ s, ((L.leaf i).card : ℝ)) ≤ η * A.card)
    (hlocal : ∀ i ∈ s, AlmostCover (L.leaf i) ε c C) :
    AlmostCover A (η + ε) (c * δ) (max C ((s.card : ℝ) * C)) := by
  classical
  choose pieces hpieces using fun i : s => hlocal i i.property
  let allPieces := Finset.univ.biUnion pieces
  have hp (i : s) := (hpieces i).1
  have hd (i : s) := (hpieces i).2.1
  have hr (i : s) := (hpieces i).2.2.1
  have hn (i : s) := (hpieces i).2.2.2
  have hmember {B : Finset ℤ} (hB : B ∈ allPieces) : ∃ i : s, B ∈ pieces i := by
    simpa only [allPieces, Finset.mem_biUnion, Finset.mem_univ, true_and] using hB
  refine ⟨allPieces, ?_, ?_, ?_, ?_⟩
  · intro B hB
    obtain ⟨i, hi⟩ := hmember hB
    obtain ⟨hBi, hBne, hBsize, hBd⟩ := hp i B hi
    refine ⟨hBi.trans (L.leaf_subset i), hBne, ?_, ?_⟩
    · calc
        c * δ * (A.card : ℝ) = c * (δ * (A.card : ℝ)) := by ring
        _ ≤ c * ((L.leaf i).card : ℝ) := mul_le_mul_of_nonneg_left (hsize i i.property) hc
        _ ≤ _ := hBsize
    · exact hBd.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _))
  · intro B hB D hD hBD
    obtain ⟨i, hi⟩ := hmember hB
    obtain ⟨j, hj⟩ := hmember hD
    by_cases hij : i = j
    · subst j
      exact hd i B hi D hj hBD
    · exact Finset.disjoint_of_subset_left (hp i B hi).1
        (Finset.disjoint_of_subset_right (hp j D hj).1
          (L.disjoint (fun h => hij (Subtype.ext h))))
  · let discarded := (Finset.univ \ s).biUnion L.leaf
    let localRemainders := Finset.univ.biUnion
      (fun i : s => L.leaf i \ (pieces i).biUnion id)
    have hsub : A \ allPieces.biUnion id ⊆ discarded ∪ localRemainders := by
      intro x hx
      obtain ⟨hxA, hxnot⟩ := Finset.mem_sdiff.mp hx
      obtain ⟨i, hxi⟩ := (L.covers x).mp hxA
      by_cases hi : i ∈ s
      · apply Finset.mem_union_right
        apply Finset.mem_biUnion.mpr
        refine ⟨⟨i, hi⟩, Finset.mem_univ _, Finset.mem_sdiff.mpr ⟨hxi, ?_⟩⟩
        intro hxpieces
        obtain ⟨B, hB, hxB⟩ := Finset.mem_biUnion.mp hxpieces
        apply hxnot
        exact Finset.mem_biUnion.mpr ⟨B,
          Finset.mem_biUnion.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, hB⟩, hxB⟩
      · apply Finset.mem_union_left
        exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hi⟩, hxi⟩
    have hdisc : (discarded.card : ℝ) ≤ η * A.card := by
      calc
        _ ≤ ∑ i ∈ Finset.univ \ s, ((L.leaf i).card : ℝ) := by
          exact_mod_cast (Finset.card_biUnion_le : discarded.card ≤
            ∑ i ∈ Finset.univ \ s, (L.leaf i).card)
        _ ≤ _ := hdiscard
    have hsum : (∑ i : s, ((L.leaf i).card : ℝ)) ≤ (A.card : ℝ) := by
      rw [Finset.sum_coe_sort s (fun i => ((L.leaf i).card : ℝ))]
      have ht := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
        (fun i hi hnot => (Nat.cast_nonneg (L.leaf i).card : (0 : ℝ) ≤ _))
      have he : (∑ i, ((L.leaf i).card : ℝ)) = (A.card : ℝ) := by exact_mod_cast L.sum_card
      exact he ▸ ht
    have hrem : (localRemainders.card : ℝ) ≤ ε * A.card := by
      calc
        _ ≤ ∑ i : s, ((L.leaf i \ (pieces i).biUnion id).card : ℝ) := by
          exact_mod_cast (Finset.card_biUnion_le : localRemainders.card ≤
            ∑ i : s, (L.leaf i \ (pieces i).biUnion id).card)
        _ ≤ ∑ i : s, ε * ((L.leaf i).card : ℝ) := Finset.sum_le_sum fun i _ => hr i
        _ = ε * ∑ i : s, ((L.leaf i).card : ℝ) := (Finset.mul_sum _ _ _).symm
        _ ≤ ε * A.card := mul_le_mul_of_nonneg_left hsum hε
    have hcard : ((A \ allPieces.biUnion id).card : ℝ) ≤
        (discarded.card : ℝ) + (localRemainders.card : ℝ) := by
      exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    nlinarith
  · calc
      (allPieces.card : ℝ) ≤ ∑ i : s, ((pieces i).card : ℝ) := by
        exact_mod_cast (Finset.card_biUnion_le : allPieces.card ≤ ∑ i : s, (pieces i).card)
      _ ≤ ∑ _ : s, C := Finset.sum_le_sum fun i _ => hn i
      _ = (s.card : ℝ) * C := by simp
      _ ≤ _ := le_max_right _ _

end LittlewoodInverse
