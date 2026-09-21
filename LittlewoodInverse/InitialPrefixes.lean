import LittlewoodInverse.PrefixPairing

namespace LittlewoodInverse

noncomputable def initialPrefix (A : Finset ℤ) (n : ℕ) (hn : n ≤ A.card) : Finset ℤ :=
  Finset.univ.image (fun i : Fin n => A.orderEmbOfFin rfl (Fin.castLE hn i))

theorem initialPrefix_card (A : Finset ℤ) (n : ℕ) (hn : n ≤ A.card) :
    (initialPrefix A n hn).card = n := by
  rw [initialPrefix, Finset.card_image_of_injective]
  · simp
  · exact (A.orderEmbOfFin rfl).injective.comp (Fin.castLE_injective hn)

theorem initialPrefix_isInitialSegment (A : Finset ℤ) (n : ℕ) (hn : n ≤ A.card) :
    IsInitialSegment (initialPrefix A n hn) A := by
  classical
  constructor
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact A.orderEmbOfFin_mem rfl _
  · intro a ha b hb hab
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨k, hk⟩ := (A.orderIsoOfFin rfl).surjective ⟨a, ha⟩
    have hka : A.orderEmbOfFin rfl k = a := congrArg Subtype.val hk
    have hkj : k ≤ Fin.castLE hn j := by
      by_contra h
      have hlt := (A.orderEmbOfFin rfl).strictMono (lt_of_not_ge h)
      rw [hka] at hlt
      exact not_lt_of_ge hab hlt
    have hkn : k.val < n := lt_of_le_of_lt hkj j.isLt
    refine Finset.mem_image.mpr ⟨⟨k.val, hkn⟩, Finset.mem_univ _, ?_⟩
    calc
      _ = A.orderEmbOfFin rfl k := congrArg _ (Fin.ext rfl)
      _ = a := hka

end LittlewoodInverse
