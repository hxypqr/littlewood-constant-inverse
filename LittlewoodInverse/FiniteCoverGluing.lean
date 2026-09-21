import LittlewoodInverse.CoverGluing

open scoped BigOperators

namespace LittlewoodInverse

/-- A disjoint partition of an actual finite integer set, permitting empty parts. -/
structure FiniteSetPartition (A : Finset ℤ) where
  Index : Type
  [indexFintype : Fintype Index]
  part : Index → Finset ℤ
  disjoint : Pairwise (fun i j => Disjoint (part i) (part j))
  covers : ∀ x, x ∈ A ↔ ∃ i, x ∈ part i

attribute [instance] FiniteSetPartition.indexFintype

namespace FiniteSetPartition

variable {A : Finset ℤ}

theorem part_subset (L : FiniteSetPartition A) (i : L.Index) : L.part i ⊆ A := by
  intro x hx
  exact (L.covers x).2 ⟨i, hx⟩

theorem sum_card (L : FiniteSetPartition A) : (∑ i, (L.part i).card) = A.card := by
  classical
  have hcover : Finset.univ.biUnion L.part = A := by
    ext x
    simpa using (L.covers x).symm
  calc
    _ = (Finset.univ.biUnion L.part).card := by
      rw [Finset.card_biUnion]
      intro i hi j hj hij
      exact L.disjoint hij
    _ = _ := congrArg Finset.card hcover

end FiniteSetPartition

theorem finite_partition_glue_covers {A : Finset ℤ}
    (L : FiniteSetPartition A) [DecidableEq L.Index] (s : Finset L.Index)
    {ε η c C δ : ℝ} (hε : 0 ≤ ε) (hc : 0 ≤ c)
    (hsize : ∀ i ∈ s, δ * (A.card : ℝ) ≤ ((L.part i).card : ℝ))
    (hdiscard : (∑ i ∈ Finset.univ \ s, ((L.part i).card : ℝ)) ≤ η * A.card)
    (hlocal : ∀ i ∈ s, AlmostCover (L.part i) ε c C) :
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
    refine ⟨hBi.trans (L.part_subset i), hBne, ?_, ?_⟩
    · calc
        c * δ * (A.card : ℝ) = c * (δ * (A.card : ℝ)) := by ring
        _ ≤ c * ((L.part i).card : ℝ) := mul_le_mul_of_nonneg_left (hsize i i.property) hc
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
  · let discarded := (Finset.univ \ s).biUnion L.part
    let localRemainders := Finset.univ.biUnion
      (fun i : s => L.part i \ (pieces i).biUnion id)
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
        _ ≤ ∑ i ∈ Finset.univ \ s, ((L.part i).card : ℝ) := by
          exact_mod_cast (Finset.card_biUnion_le : discarded.card ≤
            ∑ i ∈ Finset.univ \ s, (L.part i).card)
        _ ≤ _ := hdiscard
    have hsum : (∑ i : s, ((L.part i).card : ℝ)) ≤ (A.card : ℝ) := by
      rw [Finset.sum_coe_sort s (fun i => ((L.part i).card : ℝ))]
      have ht := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
        (fun i hi hnot => (Nat.cast_nonneg (L.part i).card : (0 : ℝ) ≤ _))
      have he : (∑ i, ((L.part i).card : ℝ)) = (A.card : ℝ) := by exact_mod_cast L.sum_card
      exact he ▸ ht
    have hrem : (localRemainders.card : ℝ) ≤ ε * A.card := by
      calc
        _ ≤ ∑ i : s, ((L.part i \ (pieces i).biUnion id).card : ℝ) := by
          exact_mod_cast (Finset.card_biUnion_le : localRemainders.card ≤
            ∑ i : s, (L.part i \ (pieces i).biUnion id).card)
        _ ≤ ∑ i : s, ε * ((L.part i).card : ℝ) := Finset.sum_le_sum fun i _ => hr i
        _ = ε * ∑ i : s, ((L.part i).card : ℝ) := (Finset.mul_sum _ _ _).symm
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

/-- Discarding the small parts of a bounded partition converts relative
covers within parts into pieces of linear size in the original set. -/
theorem bounded_partition_almost_cover {A : Finset ℤ} (hA : A.Nonempty)
    (L : FiniteSetPartition A) {v ε c D : ℝ}
    (hv : 0 < v) (hcount : (Fintype.card L.Index : ℝ) ≤ v)
    (hε : 0 < ε) (hc : 0 ≤ c) (hD : 0 ≤ D)
    (hlocal : ∀ i, (L.part i).Nonempty → AlmostCover (L.part i) (ε / 2) c D) :
    AlmostCover A ε (c * (ε / (2 * v))) (max D (v * D)) := by
  classical
  let δ := ε / (2 * v)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hN : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  let s := Finset.univ.filter (fun i => δ * (A.card : ℝ) ≤ (L.part i).card)
  have hs (i : L.Index) : i ∈ s ↔ δ * (A.card : ℝ) ≤ (L.part i).card := by simp [s]
  have hsmall (i : L.Index) (hi : i ∈ Finset.univ \ s) :
      ((L.part i).card : ℝ) ≤ δ * A.card := by
    have hh := (Finset.mem_sdiff.mp hi).2
    exact (lt_of_not_ge (fun h => hh ((hs i).mpr h))).le
  have hsCount : (s.card : ℝ) ≤ v := by
    have hh : s.card ≤ Fintype.card L.Index := Finset.card_le_univ s
    exact (show (s.card : ℝ) ≤ Fintype.card L.Index by exact_mod_cast hh).trans hcount
  have hdiscard : (∑ i ∈ Finset.univ \ s, ((L.part i).card : ℝ)) ≤ (ε / 2) * A.card := by
    calc
      _ ≤ ∑ _i ∈ Finset.univ \ s, δ * (A.card : ℝ) := Finset.sum_le_sum hsmall
      _ = ((Finset.univ \ s).card : ℝ) * (δ * A.card) := by simp
      _ ≤ v * (δ * A.card) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have hh : (Finset.univ \ s).card ≤ Fintype.card L.Index := Finset.card_le_univ _
        exact (show ((Finset.univ \ s).card : ℝ) ≤ Fintype.card L.Index by exact_mod_cast hh).trans hcount
      _ = (ε / 2) * A.card := by dsimp [δ]; field_simp
  have hglue := finite_partition_glue_covers L s (show 0 ≤ ε / 2 by positivity) hc
    (fun i hi => (hs i).mp hi) hdiscard (fun i hi => hlocal i
      (Finset.card_pos.mp (by exact_mod_cast (mul_pos hδ hN).trans_le ((hs i).mp hi))))
  apply almostCover_mono hglue (by linarith) le_rfl
  exact max_le_max le_rfl (mul_le_mul_of_nonneg_right hsCount hD)

end LittlewoodInverse

